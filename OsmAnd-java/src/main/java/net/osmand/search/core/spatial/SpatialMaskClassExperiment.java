package net.osmand.search.core.spatial;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;

import gnu.trove.map.hash.TLongObjectHashMap;
import gnu.trove.set.hash.TLongHashSet;
import net.osmand.search.core.HashSkipTileQuadTree;
import net.osmand.search.core.HashSkipTileQuadTreeJoiner;
import net.osmand.search.core.spatial.SpatialStagePipeline.SpatialObjectRes;
import net.osmand.search.core.spatial.SpatialStagePipeline.SpatialPipelineResults;

/**
 * DEV experiment: mask-class driven cost-based join planner (answering "what is the
 * theoretical maximum of the intersection phase").
 *
 * Model. After the match phase every object carries a token mask. Objects with equal
 * masks are interchangeable for the combinatorial part, so:
 *
 * 1. Group N objects into C mask classes (C is typically 30-3000, N is 10k-100k).
 * 2. Which class pairs can combine and what coverage they produce is pure bit algebra
 *    over C^2 class pairs, not N^2 object pairs - computed in microseconds.
 * 3. DP over states: state = combined mask value, partials of a state = concrete
 *    object combinations with their intersection bbox. Expansion action = (state x class)
 *    spatial join. Actions are picked from a priority queue by estimated cost
 *    |partials| * |class| - the planner chooses the join order itself, no word-based
 *    heuristics. k=3 automatically reuses cached k=2 partials (states), etc.
 * 4. The spatial join per action is output-sensitive (skip-tree bucket merge):
 *    O(n1 + n2 + crossings). Total work is therefore ~ N + sum of true crossings Z,
 *    which is the information-theoretic lower bound for full enumeration.
 *
 * The experiment prints class stats, plans and executes joins, and reports Z and
 * timing so it can be compared with the incremental chain on the same query.
 * Semantics are mask+bbox only (no acceptIntersection type filtering, no same-id
 * self merge) - counts are upper bounds of the accepted set.
 */
public class SpatialMaskClassExperiment {

	/** Cap of stored partial combinations per state (mirrors OPTIM_LIMIT_INTERSECTIONS). */
	private static final int MAX_PARTIALS_PER_STATE = 5000;
	private static final int MAX_JOIN_ACTIONS = 500;

	private static class MaskClass {
		final long mask;
		final List<SpatialObjectRes> objs = new ArrayList<>();
		final List<int[]> bboxes = new ArrayList<>();
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
		final SpatialObjectRes[] members;
		final int[] bbox;

		Partial(SpatialObjectRes[] members, int[] bbox) {
			this.members = members;
			this.bbox = bbox;
		}
	}

	private static class State {
		final long mask;
		final int covered;
		final List<Partial> partials = new ArrayList<>();
		final TLongHashSet dedupe = new TLongHashSet();
		HashSkipTileQuadTree<Integer> tree; // rebuilt lazily when partials change
		int treeSize = -1;

		State(long mask, int covered) {
			this.mask = mask;
			this.covered = covered;
		}

		HashSkipTileQuadTree<Integer> tree() {
			if (tree == null || treeSize != partials.size()) {
				tree = new HashSkipTileQuadTree<>();
				for (int i = 0; i < partials.size(); i++) {
					tree.addObject(i, partials.get(i).bbox, i);
				}
				tree.build();
				treeSize = partials.size();
			}
			return tree;
		}
	}

	private static class Action {
		final State state;
		final MaskClass cls;
		final long newMask;
		final long priority;

		/**
		 * Goal-directed cost: primary key = tokens still missing after the join
		 * (drive towards full coverage), secondary = estimated join cost.
		 * A cheap join that gets no closer to the goal never beats a join that does.
		 */
		Action(State state, MaskClass cls, long newMask, int tokensSize) {
			this.state = state;
			this.cls = cls;
			this.newMask = newMask;
			long missingAfter = tokensSize - SpatialTokenMask.countCoveredTokens(newMask);
			long cost = (long) state.partials.size() * cls.objs.size();
			this.priority = missingAfter * 1_000_000_000_000L + cost;
		}
	}

	public static void run(SpatialSearchContext ctx, SpatialPipelineResults prep) {
		long t0 = System.nanoTime();
		final int tokensSize = prep.tokens.size();

		// ---- 1. Mask classes ----
		TLongObjectHashMap<MaskClass> byMask = new TLongObjectHashMap<>();
		int totalObjs = 0;
		int withVariants = 0;
		for (SpatialObjectRes obj : prep.objectsById.valueCollection()) {
			if (obj.mainAtom1 == null || obj.mainAtom1.coords == null || obj.mainAtom1.coords.bbox31 == null) {
				continue;
			}
			if (obj.variants != null) {
				withVariants++;
			}
			MaskClass mc = byMask.get(obj.mainMask);
			if (mc == null) {
				mc = new MaskClass(obj.mainMask);
				byMask.put(obj.mainMask, mc);
			}
			mc.objs.add(obj);
			mc.bboxes.add(obj.mainAtom1.coords.bbox31);
			totalObjs++;
		}
		List<MaskClass> classes = new ArrayList<>(byMask.valueCollection());
		classes.sort(Comparator.comparingInt(c -> -c.objs.size()));
		long tClasses = System.nanoTime();
		System.out.printf("MASKDP CLASSES (%.2f ms): %,d objects -> %,d mask classes (%,d objs with variants)\n",
				(tClasses - t0) / 1e6, totalObjs, classes.size(), withVariants);
		for (int i = 0; i < Math.min(8, classes.size()); i++) {
			MaskClass c = classes.get(i);
			System.out.printf("  class %s : %,d objs\n",
					SpatialObjectRes.formatMaskTokens(c.mask, prep.tokens), c.objs.size());
		}

		// ---- 2. k=2 complementarity over class pairs (pure bit algebra) ----
		int compl2 = 0, fullPairs2 = 0;
		long worstCasePairs = 0;
		for (int i = 0; i < classes.size(); i++) {
			for (int j = i; j < classes.size(); j++) {
				long m1 = classes.get(i).mask, m2 = classes.get(j).mask;
				if (!SpatialTokenMask.allowed(m1, m2)) {
					continue;
				}
				long comb = SpatialTokenMask.combine(m1, m2);
				int cov = SpatialTokenMask.countCoveredTokens(comb);
				if (cov > SpatialTokenMask.countCoveredTokens(m1) && cov > SpatialTokenMask.countCoveredTokens(m2)) {
					compl2++;
					if (cov == tokensSize) {
						fullPairs2++;
						worstCasePairs += (long) classes.get(i).objs.size() * classes.get(j).objs.size();
					}
				}
			}
		}
		long tCompl = System.nanoTime();
		System.out.printf("MASKDP COMPLEMENT (%.2f ms): %,d class pairs gain coverage, %,d pairs reach full"
				+ " (worst-case %,d obj pairs)\n", (tCompl - tClasses) / 1e6, compl2, fullPairs2, worstCasePairs);

		// ---- 3. Cost-based DP ----
		Map<Long, State> states = new LinkedHashMap<>();
		// seed k=1 layer: each class is a state with single-object partials
		for (MaskClass c : classes) {
			State s = states.computeIfAbsent(c.mask,
					m -> new State(m, SpatialTokenMask.countCoveredTokens(m)));
			for (int i = 0; i < c.objs.size() && s.partials.size() < MAX_PARTIALS_PER_STATE; i++) {
				s.partials.add(new Partial(new SpatialObjectRes[] { c.objs.get(i) }, c.bboxes.get(i)));
			}
		}
		PriorityQueue<Action> queue = new PriorityQueue<>(Comparator.comparingLong(a -> a.priority));
		for (State s : new ArrayList<>(states.values())) {
			enqueueActions(s, classes, tokensSize, queue);
		}

		long crossings = 0, maskAccepted = 0;
		int joins = 0;
		List<Partial> fullCovers = new ArrayList<>();
		// each (state, class) pair is executed at most once
		java.util.Set<Long> executed = new java.util.HashSet<>();
		long tDp = System.nanoTime();
		while (!queue.isEmpty() && joins < MAX_JOIN_ACTIONS && fullCovers.isEmpty()) {
			Action a = queue.poll();
			if (a.state.partials.isEmpty()) {
				continue;
			}
			long execKey = a.state.mask * 31 + a.cls.mask;
			if (!executed.add(execKey)) {
				continue;
			}
			joins++;
			State target = states.get(a.newMask);
			boolean newState = target == null;
			if (newState) {
				target = new State(a.newMask, SpatialTokenMask.countCoveredTokens(a.newMask));
				states.put(a.newMask, target);
			}
			final State ts = target;
			final MaskClass mc = a.cls;
			final State src = a.state;
			long[] counters = new long[2];
			HashSkipTileQuadTreeJoiner<Integer, Integer> joiner = new HashSkipTileQuadTreeJoiner<>(mc.tree(),
					src.tree());
			joiner.joinAllBuckets((e1, e2) -> {
				counters[0]++;
				if (ts.partials.size() >= MAX_PARTIALS_PER_STATE) {
					return;
				}
				SpatialObjectRes obj = mc.objs.get(e1.obj);
				Partial p = src.partials.get(e2.obj);
				for (SpatialObjectRes m : p.members) {
					if (m == obj) {
						return; // no self-merge in the experiment
					}
				}
				counters[1]++;
				long key = obj.mainAtom1.id * 0x9E3779B97F4A7C15L;
				for (SpatialObjectRes m : p.members) {
					key ^= m.mainAtom1.id * 0x9E3779B97F4A7C15L;
				}
				if (!ts.dedupe.add(key)) {
					return;
				}
				int[] bbox = intersectBbox(p.bbox, mc.bboxes.get(e1.obj));
				SpatialObjectRes[] members = new SpatialObjectRes[p.members.length + 1];
				System.arraycopy(p.members, 0, members, 0, p.members.length);
				members[p.members.length] = obj;
				ts.partials.add(new Partial(members, bbox));
			});
			crossings += counters[0];
			maskAccepted += counters[1];
			if (ctx.stats.printLogs) {
				System.out.printf("MASKDP JOIN %d: %s (%,d) x class %s (%,d) -> %s : %,d crossings, %,d partials\n",
						joins, SpatialObjectRes.formatMaskTokens(src.mask, prep.tokens), src.partials.size(),
						SpatialObjectRes.formatMaskTokens(mc.mask, prep.tokens), mc.objs.size(),
						SpatialObjectRes.formatMaskTokens(a.newMask, prep.tokens), counters[0],
						ts.partials.size());
			}
			if (ts.covered == tokensSize && !ts.partials.isEmpty()) {
				fullCovers.addAll(ts.partials);
				break;
			}
			if (newState && !ts.partials.isEmpty()) {
				enqueueActions(ts, classes, tokensSize, queue);
			}
			if (!newState) {
				ts.tree = null; // partials changed - rebuild on next use
			}
		}
		long tEnd = System.nanoTime();
		System.out.printf("MASKDP DONE (%.1f ms total, %.1f ms joins): %,d joins, Z=%,d crossings"
				+ " (%,d mask-accepted), %,d states, %,d full covers\n", (tEnd - t0) / 1e6, (tEnd - tDp) / 1e6,
				joins, crossings, maskAccepted, states.size(), fullCovers.size());
		for (int i = 0; i < Math.min(3, fullCovers.size()); i++) {
			StringBuilder sb = new StringBuilder();
			for (SpatialObjectRes m : fullCovers.get(i).members) {
				sb.append(String.format("['%s' %d] ", m.mainAtom1.name, m.mainAtom1.id));
			}
			System.out.println("  cover: " + sb);
		}
	}

	private static void enqueueActions(State s, List<MaskClass> classes, int tokensSize,
			PriorityQueue<Action> queue) {
		for (MaskClass c : classes) {
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
}
