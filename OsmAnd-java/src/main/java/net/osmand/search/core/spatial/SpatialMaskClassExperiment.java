package net.osmand.search.core.spatial;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;

import gnu.trove.map.hash.TLongObjectHashMap;
import gnu.trove.set.hash.TLongHashSet;
import net.osmand.search.core.HashSkipTileQuadTree;
import net.osmand.search.core.HashSkipTileQuadTreeJoiner;
import net.osmand.search.core.spatial.SpatialSearchToken.NameIndexAtom;
import net.osmand.search.core.spatial.SpatialStagePipeline.SpatialObjectRes;
import net.osmand.search.core.spatial.SpatialStagePipeline.SpatialPipelineResults;

/**
 * Mask-class cost-based join planner ("theoretical maximum" of the intersection phase).
 *
 * Model. After the match phase every object carries a token mask. Objects with equal
 * masks are interchangeable for the combinatorial part, so:
 *
 * 1. Group N objects into C mask classes (C is typically 30-3000, N is 10k-200k).
 * 2. Which class pairs can combine and what coverage they produce is pure bit algebra
 *    over C^2 class pairs, not N^2 object pairs - computed in microseconds.
 * 3. DP over states: state = combined mask value, partials of a state = concrete
 *    object combinations with their clipped intersection bbox. Expansion action =
 *    (state x class) spatial join, picked from a priority queue by goal-directed
 *    priority: tokens still missing after the join first, estimated join cost second.
 *    A cheap join that gets no closer to full coverage never beats one that does.
 *    When a state gains new partials, its downstream joins are re-enqueued and
 *    re-run as deltas (only the new partials are joined), so late-arriving
 *    combinations still reach completion. k=3 covers reuse cached k=2 partials.
 * 4. The spatial join per action is output-sensitive (skip-tree bucket merge):
 *    O(n1 + n2 + crossings). Total work ~ N + Z where Z = true bbox crossings of
 *    complementary combinations - the lower bound of any full enumeration.
 *
 * Join semantics mirror {@link SpatialStagePipeline#join} (stage-2 self-join /
 * stage-3 area joins) exactly: variant-aware mask combining, expandContestedTokens
 * + acceptPairSemantic on full coverage, clipped combination bboxes for partials.
 * Unlike the token chain, objects join as a whole (their mask already covers all
 * their tokens), so no same-id merging step is needed.
 *
 * Excluded high-frequency masks are NOT dropped here - huge classes are simply
 * never picked by the planner unless they are the only way to finish a cover.
 */
public class SpatialMaskClassExperiment {

	/** Cap of stored partial combinations per state (mirrors OPTIM_LIMIT_INTERSECTIONS). */
	private static final int MAX_PARTIALS_PER_STATE = 5000;
	/** Budget of joins that actually produced crossings (empty joins are nearly free). */
	private static final int MAX_PRODUCTIVE_JOINS = 500;
	/** Hard cap of executed (state x class) actions, productive or not. */
	private static final int MAX_TOTAL_ACTIONS = 20000;
	private static final int MAX_FALLBACK_RESULTS = 500;

	private static class MaskClass {
		final long mask;
		final List<SpatialObjectRes> objs = new ArrayList<>();
		final List<int[]> bboxes = new ArrayList<>();
		final int[] unionBbox = emptyUnion();
		HashSkipTileQuadTree<Integer> tree;

		MaskClass(long mask) {
			this.mask = mask;
		}

		HashSkipTileQuadTree<Integer> tree() {
			if (tree == null) {
				tree = new HashSkipTileQuadTree<>();
				for (int i = 0; i < bboxes.size(); i++) {
					tree.addObject(i, bboxes.get(i), i);
				}
				tree.build();
			}
			return tree;
		}
	}

	private static class Partial {
		final SpatialObjectRes res;
		final int[] bbox;

		Partial(SpatialObjectRes res, int[] bbox) {
			this.res = res;
			this.bbox = bbox;
		}
	}

	private static class State {
		final long mask;
		final int covered;
		/** Seed state: partials are the single objects of the identically-masked class. */
		boolean seed;
		final List<Partial> partials = new ArrayList<>();
		final TLongHashSet dedupe = new TLongHashSet();
		final int[] unionBbox = emptyUnion();
		HashSkipTileQuadTree<Integer> tree;
		int treeSize = -1;

		State(long mask, int covered) {
			this.mask = mask;
			this.covered = covered;
		}

		/** Tree over partials[from..) - entries keep global partial indices (delta joins). */
		HashSkipTileQuadTree<Integer> tree(int from) {
			if (from == 0) {
				if (tree == null || treeSize != partials.size()) {
					tree = buildSlice(0);
					treeSize = partials.size();
				}
				return tree;
			}
			return buildSlice(from);
		}

		private HashSkipTileQuadTree<Integer> buildSlice(int from) {
			HashSkipTileQuadTree<Integer> t = new HashSkipTileQuadTree<>();
			for (int i = from; i < partials.size(); i++) {
				t.addObject(i, partials.get(i).bbox, i);
			}
			t.build();
			return t;
		}
	}

	private static class Action {
		final State state;
		final MaskClass cls;
		final long newMask;
		final long priority;

		Action(State state, MaskClass cls, long newMask, int tokensSize) {
			this.state = state;
			this.cls = cls;
			this.newMask = newMask;
			long missingAfter = tokensSize - SpatialTokenMask.countCoveredTokens(newMask);
			long cost = (long) state.partials.size() * cls.objs.size();
			this.priority = missingAfter * 1_000_000_000_000L + cost;
		}
	}

	/** Stats-only entry (DEV_MASK_CLASS_EXPERIMENT): prints classes, plan and covers. */
	public static void run(SpatialSearchContext ctx, SpatialPipelineResults prep) {
		List<SpatialObjectRes> fallback = new ArrayList<>();
		List<SpatialObjectRes> covers = runJoin(ctx, prep, fallback, true);
		for (int i = 0; i < Math.min(3, covers.size()); i++) {
			SpatialObjectRes res = covers.get(i);
			StringBuilder sb = new StringBuilder();
			for (NameIndexAtom a : res.atoms) {
				if (a != null) {
					sb.append(String.format("['%s' %d] ", a.name, a.id));
				}
			}
			System.out.println("  cover: " + sb);
		}
	}

	/**
	 * Full join mode (DEV_USE_MASK_CLASS_PIPELINE): returns accepted full-coverage
	 * combinations; when none exist, fallbackPartials receives the best partial
	 * combinations (maximum covered tokens) as stage-style results.
	 */
	public static List<SpatialObjectRes> runJoin(SpatialSearchContext ctx, SpatialPipelineResults prep,
			List<SpatialObjectRes> fallbackPartials, boolean verbose) {
		long t0 = System.nanoTime();
		final int tokensSize = prep.tokens.size();
		final boolean logs = ctx.stats.printLogs;

		// ---- 1. Mask classes ----
		TLongObjectHashMap<MaskClass> byMask = new TLongObjectHashMap<>();
		int totalObjs = 0;
		for (SpatialObjectRes obj : prep.objectsById.valueCollection()) {
			if (obj.mainAtom1 == null || obj.mainAtom1.coords == null || obj.mainAtom1.coords.bbox31 == null) {
				continue;
			}
			MaskClass mc = byMask.get(obj.mainMask);
			if (mc == null) {
				mc = new MaskClass(obj.mainMask);
				byMask.put(obj.mainMask, mc);
			}
			mc.objs.add(obj);
			mc.bboxes.add(obj.mainAtom1.coords.bbox31);
			growUnion(mc.unionBbox, obj.mainAtom1.coords.bbox31);
			totalObjs++;
		}
		List<MaskClass> classes = new ArrayList<>(byMask.valueCollection());
		classes.sort(Comparator.comparingInt(c -> -c.objs.size()));
		if (logs && verbose) {
			System.out.printf("MASKDP CLASSES (%.2f ms): %,d objects -> %,d mask classes\n",
					(System.nanoTime() - t0) / 1e6, totalObjs, classes.size());
			for (int i = 0; i < Math.min(8, classes.size()); i++) {
				MaskClass c = classes.get(i);
				System.out.printf("  class %s : %,d objs\n",
						SpatialObjectRes.formatMaskTokens(c.mask, prep.tokens), c.objs.size());
			}
		}

		// ---- 2. DP over mask states ----
		Map<Long, State> states = new LinkedHashMap<>();
		for (MaskClass c : classes) {
			int covered = SpatialTokenMask.countCoveredTokens(c.mask);
			if (covered >= tokensSize) {
				continue; // full single objects are STEP 1 results, not join seeds
			}
			State s = states.computeIfAbsent(c.mask, m -> new State(m, covered));
			s.seed = true;
			for (int i = 0; i < c.objs.size() && s.partials.size() < MAX_PARTIALS_PER_STATE; i++) {
				s.partials.add(new Partial(c.objs.get(i), c.bboxes.get(i)));
				growUnion(s.unionBbox, c.bboxes.get(i));
			}
		}
		PriorityQueue<Action> queue = new PriorityQueue<>(Comparator.comparingLong(a -> a.priority));
		for (State s : new ArrayList<>(states.values())) {
			enqueueActions(s, states, classes, tokensSize, queue);
		}

		List<SpatialObjectRes> accepted = new ArrayList<>();
		// (state x class) -> how many of the state's partials were already joined;
		// re-enqueued actions join only the delta added since the last execution
		Map<Long, Integer> executedUpTo = new HashMap<>();
		long crossings = 0;
		int joins = 0, actions = 0;
		long tDp = System.nanoTime();
		while (!queue.isEmpty() && joins < MAX_PRODUCTIVE_JOINS && actions < MAX_TOTAL_ACTIONS
				&& accepted.isEmpty()) {
			Action a = queue.poll();
			if (a.state.partials.isEmpty()) {
				continue;
			}
			long execKey = a.state.mask * 31 + a.cls.mask;
			final int from = executedUpTo.getOrDefault(execKey, 0);
			if (from >= a.state.partials.size()) {
				continue; // no new partials since the previous execution
			}
			executedUpTo.put(execKey, a.state.partials.size());
			// spatially disjoint sides can never cross - skip without building trees
			if (!unionIntersects(a.state.unionBbox, a.cls.unionBbox)) {
				continue;
			}
			actions++;
			final boolean fullTarget = SpatialTokenMask.countCoveredTokens(a.newMask) == tokensSize;
			State target = fullTarget ? null : states.get(a.newMask);
			boolean newState = !fullTarget && target == null;
			if (newState) {
				target = new State(a.newMask, SpatialTokenMask.countCoveredTokens(a.newMask));
				states.put(a.newMask, target);
			}
			final State ts = target;
			final int tsSizeBefore = ts == null ? 0 : ts.partials.size();
			final MaskClass mc = a.cls;
			final State src = a.state;
			long[] counters = new long[1];
			final boolean[] stopEarly = new boolean[] { false };
			HashSkipTileQuadTreeJoiner<Integer, Integer> joiner = new HashSkipTileQuadTreeJoiner<>(mc.tree(),
					src.tree(from));
			joiner.joinAllBuckets((e1, e2) -> {
				if (stopEarly[0]) {
					return;
				}
				counters[0]++;
				SpatialObjectRes o2 = mc.objs.get(e1.obj);
				Partial p = src.partials.get(e2.obj);
				SpatialObjectRes o1 = p.res;
				// mask semantics identical to SpatialStagePipeline.join()
				long m1, m2, combinedMask;
				if (o1.variants == null && o2.variants == null) {
					m1 = o1.mainMask;
					m2 = o2.mainMask;
					if (!SpatialTokenMask.allowed(m1, m2)) {
						return;
					}
					combinedMask = SpatialTokenMask.combine(m1, m2);
				} else {
					long[] best = SpatialTokenMask.bestAllowedCombine(o1.variants(), o2.variants());
					if (best == null) {
						return;
					}
					combinedMask = best[0];
					m1 = best[1];
					m2 = best[2];
				}
				if (SpatialTokenMask.countCoveredTokens(combinedMask) == tokensSize) {
					for (long[] resolved : SpatialTokenMask.expandContestedTokens(m1, m2)) {
						long resolvedMask = SpatialTokenMask.combine(resolved[0], resolved[1]);
						SpatialObjectRes res = new SpatialObjectRes(resolvedMask, resolved[0], resolved[1], o1, o2);
						if (SpatialStagePipeline.acceptPairSemantic(ctx, res)) {
							accepted.add(res);
							if (ctx.settings.PIPELINE_STOP_ON_FIRST_COMPLETE) {
								stopEarly[0] = true;
							}
						}
					}
					return;
				}
				if (ts == null || ts.partials.size() >= MAX_PARTIALS_PER_STATE) {
					return;
				}
				SpatialObjectRes res = new SpatialObjectRes(combinedMask, m1, m2, o1, o2);
				if (res.mainAtom1 == null) {
					return;
				}
				long key = combinedMask;
				for (NameIndexAtom atm : res.atoms) {
					if (atm != null) {
						key ^= atm.id * 0x9E3779B97F4A7C15L;
					}
				}
				if (!ts.dedupe.add(key)) {
					return;
				}
				int[] clipped = intersectBbox(p.bbox, mc.bboxes.get(e1.obj));
				ts.partials.add(new Partial(res, clipped));
				growUnion(ts.unionBbox, clipped);
			});
			crossings += counters[0];
			if (counters[0] > 0) {
				joins++;
			}
			if (logs && verbose && (counters[0] > 0 || fullTarget)) {
				System.out.printf("MASKDP JOIN%s %d: %s (%,d) x %s (%,d) -> %s : %,d crossings, %s\n",
						fullTarget ? "*" : "", joins,
						SpatialObjectRes.formatMaskTokens(src.mask, prep.tokens), src.partials.size(),
						SpatialObjectRes.formatMaskTokens(mc.mask, prep.tokens), mc.objs.size(),
						SpatialObjectRes.formatMaskTokens(a.newMask, prep.tokens), counters[0],
						fullTarget ? accepted.size() + " accepted" : (ts.partials.size() + " partials"));
			}
			if (ts != null && ts.partials.size() > tsSizeBefore) {
				// state got new partials: (re-)enqueue its actions, they run as delta joins
				enqueueActions(ts, states, classes, tokensSize, queue);
			}
		}
		// ---- 3. Fallback: best partial coverage when no full cover exists ----
		if (accepted.isEmpty() && fallbackPartials != null) {
			int bestCovered = 0;
			for (State s : states.values()) {
				if (!s.partials.isEmpty() && s.covered > bestCovered) {
					bestCovered = s.covered;
				}
			}
			for (State s : states.values()) {
				if (s.covered != bestCovered) {
					continue;
				}
				for (Partial p : s.partials) {
					// combos only - single objects are covered by earlier stages
					if (p.res.mainAtom2 != null && fallbackPartials.size() < MAX_FALLBACK_RESULTS) {
						fallbackPartials.add(p.res);
					}
				}
			}
		}
		if (logs) {
			System.out.printf("MASKDP DONE (%.1f ms total, %.1f ms joins): %,d/%,d joins, Z=%,d crossings,"
					+ " %,d states, %,d accepted, %,d fallback\n", (System.nanoTime() - t0) / 1e6,
					(System.nanoTime() - tDp) / 1e6, joins, actions, crossings, states.size(), accepted.size(),
					fallbackPartials == null ? 0 : fallbackPartials.size());
		}
		return accepted;
	}

	private static void enqueueActions(State s, Map<Long, State> states, List<MaskClass> classes, int tokensSize,
			PriorityQueue<Action> queue) {
		for (MaskClass c : classes) {
			if (s.seed && Long.compareUnsigned(c.mask, s.mask) < 0) {
				State other = states.get(c.mask);
				if (other != null && other.seed) {
					continue; // symmetric seed x seed pair - the other order is enqueued
				}
			}
			if (!SpatialTokenMask.allowed(s.mask, c.mask)) {
				continue;
			}
			long comb = SpatialTokenMask.combine(s.mask, c.mask);
			if (SpatialTokenMask.countCoveredTokens(comb) > s.covered) {
				queue.add(new Action(s, c, comb, tokensSize));
			}
		}
	}

	private static int[] intersectBbox(int[] a, int[] b) {
		return new int[] { Math.max(a[0], b[0]), Math.max(a[1], b[1]), Math.min(a[2], b[2]),
				Math.min(a[3], b[3]) };
	}

	private static int[] emptyUnion() {
		return new int[] { Integer.MAX_VALUE, Integer.MAX_VALUE, Integer.MIN_VALUE, Integer.MIN_VALUE };
	}

	private static void growUnion(int[] union, int[] bbox) {
		union[0] = Math.min(union[0], bbox[0]);
		union[1] = Math.min(union[1], bbox[1]);
		union[2] = Math.max(union[2], bbox[2]);
		union[3] = Math.max(union[3], bbox[3]);
	}

	private static boolean unionIntersects(int[] a, int[] b) {
		return a[0] <= b[2] && a[2] >= b[0] && a[1] <= b[3] && a[3] >= b[1];
	}
}
