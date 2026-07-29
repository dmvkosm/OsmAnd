package net.osmand.search.core.spatial;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import gnu.trove.map.hash.TLongObjectHashMap;
import gnu.trove.set.hash.TIntHashSet;
import gnu.trove.set.hash.TLongHashSet;
import net.osmand.search.core.HashSkipTileQuadTree;
import net.osmand.search.core.HashSkipTileQuadTreeJoiner;
import net.osmand.search.core.spatial.SpatialSearchToken.NameIndexAtom;

public class SpatialStagePipeline {

	private final SpatialSearchContext ctx;

	public static int EXCLUDE_MASKS = 8000; // speed up
	public static boolean CHECK_EXCLUDED = false;
	public static int MAX_STEPS = 5; // 1 - fully covered, 2 - 1 intersection, ...

	public SpatialStagePipeline(SpatialSearchContext ctx) {
		this.ctx = ctx;
	}

	public static final int MAX_SUPPORTED_TOKENS = SpatialTokenMask.MAX_TOKENS;
	public static final long STATE_NO_MATCH = SpatialTokenMask.STATE_NO_MATCH;
	public static final long STATE_EXACT_MATCH = SpatialTokenMask.STATE_EXACT;
	public static final long STATE_AMBIGUOUS = SpatialTokenMask.STATE_AMBIGUOUS;

	public static class SpatialObjectRes {
		public final NameIndexAtom[] atoms;
		public NameIndexAtom mainAtom1;
		public NameIndexAtom mainAtom2;

		public long mainMask = 0;
		/** Alternative masks when duplicate query words hit the same object. */
		long[] variants;

		public SpatialObjectRes(int tCount, NameIndexAtom atom, int index) {
			atoms = new NameIndexAtom[tCount];
			mainAtom1 = atom;
			long atomic = atom.atomicObject() ? SpatialTokenMask.ATOMIC_ONE : SpatialTokenMask.ATOMIC_NONE;
			if (atom.atomicObject() && atom.sameNameAreaObj != null) {
				// POI named like its city/street: saturate so it can not pair with another atomic
				atomic = SpatialTokenMask.ATOMIC_TWO;
			}
			long category = atom.isPOI() ? SpatialTokenMask.POI_OBJECT : SpatialTokenMask.POI_NONE;
			if (atom.isPoiCategory()) {
				category = SpatialTokenMask.POI_CATEGORY;
			}
			mainMask = atomic | (category << 2);
			setAtom(atom, index);
		}

		public void mergeSame(NameIndexAtom atom, int tokenIdx) {
			if ((mainAtom1.isPOIRef() || mainAtom1.isBuilding()) && !atom.isPOIRef() && !atom.isBuilding()) {
				mainAtom1 = atom;
			}
			setAtom(atom, tokenIdx);
		}

		/**
		 * Combination of two objects. resolved1/resolved2 are the masks actually
		 * used after variant / ownership resolution; atoms are taken only from
		 * the side that owns each token.
		 */
		public SpatialObjectRes(long mask, long resolved1, long resolved2, SpatialObjectRes s1, SpatialObjectRes s2) {
			atoms = new NameIndexAtom[s1.atoms.length];
			this.mainMask = mask;
			for (int i = 0; i < atoms.length; i++) {
				boolean own1 = SpatialTokenMask.getTokenState(resolved1, i) != STATE_NO_MATCH;
				boolean own2 = SpatialTokenMask.getTokenState(resolved2, i) != STATE_NO_MATCH;
				NameIndexAtom a1 = own1 ? s1.atoms[i] : null;
				NameIndexAtom a2 = own2 ? s2.atoms[i] : null;
				if (a1 != null && !a1.isPOIRef() && !a1.isBuilding()) {
					atoms[i] = a1;
					mainAtom1 = a1;
				} else if (a2 != null && !a2.isPOIRef() && !a2.isBuilding()) {
					// couldn't be both same time
					atoms[i] = a2;
					mainAtom2 = a2;
				} else if (a1 != null) {
					atoms[i] = a1;
				} else if (a2 != null) {
					atoms[i] = a2;
				}
			}
			if (mainAtom1 == null) {
				for (NameIndexAtom a : atoms) {
					if (a != null) {
						mainAtom1 = a;
						break;
					}
				}
			}
		}

		void setAtom(NameIndexAtom atom, int index) {
			atoms[index] = atom;
			mainMask = SpatialTokenMask.setTokenState(mainMask, index,
					atom.isBuilding() || atom.isPOIRef() ? STATE_AMBIGUOUS : STATE_EXACT_MATCH);
		}

		long[] variants() {
			return variants != null ? variants : new long[] { mainMask };
		}

		// --- thin wrappers kept for SpatialStagePipelineStats compatibility ---

		public static long setTokenState(long currentMask, int tokenIdx, long state) {
			return SpatialTokenMask.setTokenState(currentMask, tokenIdx, state);
		}

		public static int countCoveredTokens(long mask) {
			return SpatialTokenMask.countCoveredTokens(mask);
		}

		/** Delegates to {@link SpatialTokenMask#allowed(long, long)}. */
		public static boolean allowed(long m1, long m2) {
			return SpatialTokenMask.allowed(m1, m2);
		}

		/** Loop-free; totalTokens kept for call-site compatibility. */
		public static long combine2BitMasks(long mask1, long mask2, int totalTokens) {
			return SpatialTokenMask.combine(mask1, mask2);
		}

		/**
		 * Helper method to format bitmask bits into a readable list of token words.
		 */
		static String formatMaskTokens(long mask, List<SpatialSearchToken> tokens) {
			List<String> res = new ArrayList<String>();
			long atomicState = mask & 3L;
			if (atomicState == SpatialTokenMask.ATOMIC_ONE) {
				res.add("A1");
			} else if (atomicState == SpatialTokenMask.ATOMIC_TWO) {
				res.add("A2");
			} else if (atomicState == SpatialTokenMask.ATOMIC_NONE) {
				res.add("A0");
			} else {
				res.add("A?"); // undefined atomic state 10
			}
			long poiState = (mask >> 2) & 3L;
			if (poiState == SpatialTokenMask.POI_OBJECT) {
				res.add("POI");
			} else if (poiState == SpatialTokenMask.POI_CATEGORY) {
				res.add("POICAT");
			}
			for (int tokenIndex = 0; tokenIndex < SpatialTokenMask.MAX_TOKENS; tokenIndex++) {
				long tokenState = SpatialTokenMask.getTokenState(mask, tokenIndex);
				if (tokenState != STATE_NO_MATCH) {
					String symbol = tokenState == STATE_EXACT_MATCH ? "W" : "B";
					if (tokens != null && tokenIndex < tokens.size() && tokens.get(tokenIndex) != null) {
						String word = tokens.get(tokenIndex).word;
						res.add(word != null ? word : symbol + tokenIndex);
					} else {
						res.add(symbol + tokenIndex);
					}
				}
			}
			return res.toString();
		}
	}

	private static class MasksStats {
		TLongObjectHashMap<Integer> masks = new TLongObjectHashMap<Integer>();
		public final int intersections;

		public MasksStats(int intersections) {
			this.intersections = intersections;
		}

		int count(long mask) {
			Integer cnt = masks.get(mask);
			if (cnt == null) {
				cnt = 1;
			} else {
				cnt++;
			}
			masks.put(mask, cnt);
			return cnt;
		}

		int count(SpatialObjectRes obj) {
			return count(obj.mainMask);
		}
	}

	public static class SpatialPipelineResults {
		public final List<SpatialSearchToken> tokens;

		public SpatialPipelineResults(List<SpatialSearchToken> tokens) {
			this.tokens = tokens;
		}

		// stage 1
		public final TLongObjectHashMap<SpatialObjectRes> objectsById = new TLongObjectHashMap<>();
		public final TLongObjectHashMap<List<SpatialObjectRes>> excludedMasks = new TLongObjectHashMap<List<SpatialObjectRes>>();

		public final List<MasksStats> masksStats = new ArrayList<>();
		public final HashSkipTileQuadTree<SpatialObjectRes> allObjectsTree = new HashSkipTileQuadTree<>();
		public final HashSkipTileQuadTree<SpatialObjectRes> areaObjectsTree = new HashSkipTileQuadTree<>();
		// stage 2, 3+
		public final List<HashSkipTileQuadTree<SpatialObjectRes>> pairsTree = new ArrayList<>();

		public final List<SpatialSearchResultsList> combinations = new ArrayList<SpatialSearchResultsList>();
	}

	/**
	 * Groups of query token indices with the same word. Objects exact-matched
	 * on several positions of one group get alternative masks so the joiner can
	 * split duplicate words between both sides of a pair.
	 */
	private static int[][] duplicateTokenGroups(List<SpatialSearchToken> tokens) {
		Map<String, List<Integer>> byWord = new LinkedHashMap<>();
		for (int i = 0; i < tokens.size(); i++) {
			String w = tokens.get(i).word;
			if (w != null) {
				byWord.computeIfAbsent(w, k -> new ArrayList<>()).add(i);
			}
		}
		List<int[]> groups = new ArrayList<>();
		for (List<Integer> g : byWord.values()) {
			if (g.size() > 1) {
				int[] arr = new int[g.size()];
				for (int i = 0; i < arr.length; i++) {
					arr[i] = g.get(i);
				}
				groups.add(arr);
			}
		}
		return groups.toArray(new int[0][]);
	}

	private SpatialPipelineResults prepare(List<SpatialSearchToken> tokens) {
		if (tokens.size() > MAX_SUPPORTED_TOKENS) {
			tokens = tokens.subList(0, MAX_SUPPORTED_TOKENS);
		}
		SpatialPipelineResults prep = new SpatialPipelineResults(tokens);
		int totalTokens = tokens.size();
		for (int tokenIdx = 0; tokenIdx < totalTokens; tokenIdx++) {
			SpatialSearchToken token = tokens.get(tokenIdx);
			TIntHashSet deleted = token.getDeletedAtoms();
			for (NameIndexAtom atom : token.atoms) {
				if (deleted.contains(atom.indexInToken)) {
					continue;
				}
				SpatialObjectRes existing = prep.objectsById.get(atom.id);
				if (existing != null) {
					existing.mergeSame(atom, tokenIdx);
				} else {
					prep.objectsById.put(atom.id, new SpatialObjectRes(totalTokens, atom, tokenIdx));
				}
			}
		}
		// alternative masks for duplicate query words
		int[][] dupGroups = duplicateTokenGroups(tokens);
		if (dupGroups.length > 0) {
			long allDupBits = 0;
			for (int[] group : dupGroups) {
				for (int t : group) {
					allDupBits |= 1L << (t * 2 + SpatialTokenMask.HEADER_BITS);
				}
			}
			for (SpatialObjectRes obj : prep.objectsById.valueCollection()) {
				// cheap pre-filter: alternatives only matter for objects with
				// two or more exact matches inside duplicate-word positions
				if (Long.bitCount(SpatialTokenMask.exactLowBits(obj.mainMask) & allDupBits) < 2) {
					continue;
				}
				long[] vars = SpatialTokenMask.duplicateWordAlternatives(obj.mainMask, dupGroups);
				if (vars.length > 1) {
					obj.variants = vars;
				}
			}
		}
		// calculate excluded masks
		MasksStats masksStats = new MasksStats(1);
		for (SpatialObjectRes obj : prep.objectsById.valueCollection()) {
			masksStats.count(obj);
		}
		prep.masksStats.add(masksStats);

		for (SpatialObjectRes obj : prep.objectsById.valueCollection()) {
			Integer cnt = masksStats.masks.get(obj.mainMask);
			if (cnt > EXCLUDE_MASKS) {
				List<SpatialObjectRes> elst = prep.excludedMasks.get(obj.mainMask);
				if (elst == null) {
					elst = new ArrayList<>();
					prep.excludedMasks.put(obj.mainMask, elst);
				}
				elst.add(obj);
				continue;
			}
			prep.allObjectsTree.addObject(obj, obj.mainAtom1.coords.bbox31, obj.mainAtom1.id);
			if (obj.mainAtom1.isGeoArea()) {
				prep.areaObjectsTree.addObject(obj, obj.mainAtom1.coords.bbox31, obj.mainAtom1.id);
			}
		}
		prep.allObjectsTree.build();
		prep.areaObjectsTree.build();

		return prep;
	}

	private boolean validateStageAndFinish(SpatialPipelineResults prep, int[] intStats,
			List<SpatialObjectRes> preResults, int stage, long ptime) throws IOException {

		long time = System.nanoTime();
		if (ctx.stats.printLogs) {
			String intersections = "";
			if (intStats != null) {
				intersections = String.format(" (cross %,d, partial %,d, full %,d)", intStats[0],
						intStats[1] - intStats[2], intStats[2]);
			}
			System.out.printf("PIPELINE STAGE %d FIND (%.1f ms) - %,d results %s \n", stage, (time - ptime) / 1e6,
					preResults.size(), intersections);
		}
		if (ctx.isCancelled()) {
			return true;
		}
		int nonCategoryRes = 0;
		if (!preResults.isEmpty()) {
			SpatialSearchResultsList stageList = createResultList(prep.tokens, preResults);
			stageList.loadObjectsAndCalcBuildings(ctx);
			if (ctx.isCancelled()) {
				return true;
			}
			List<SpatialSearchResult> res = stageList.sortResults(ctx, ctx.settings.DEDUPLICATE_RES);
			int tsize = prep.tokens.size();
			for (SpatialSearchResult r : res) {
				if (!r.isPoiCategory() && r.surplusWords + r.matchedTokens() == tsize) {
					nonCategoryRes++;
				}
			}
			if ((res.size() > 0 && stage == 0) || nonCategoryRes > 0) {
				prep.combinations.add(stageList);
			}
		}
		if (ctx.stats.printLogs) {
			System.out.printf("PIPELINE STAGE %d LOAD (%.1f ms): %d complete results.\n", stage,
					(System.nanoTime() - time) / 1e6, nonCategoryRes);
		}
		if (nonCategoryRes > 0 && ctx.settings.PIPELINE_STOP_ON_FIRST_COMPLETE) {
			return true;
		}
		int[] stops = ctx.settings.MAX_PIPELINE_STAGE_TO_STOP;
		if (stops.length > 0 && nonCategoryRes > stops[Math.min(stops.length, stage) - 1]) {
			return true;
		}
		return false;
	}

	/** Intersection bbox of every atom with coordinates (matches legacy addResult). */
	static int[] intersectionBbox(SpatialObjectRes res) {
		int[] bbox = null;
		if (res.atoms != null) {
			for (NameIndexAtom a : res.atoms) {
				if (a == null || a.coords == null || a.coords.bbox31 == null) {
					continue;
				}
				if (bbox == null) {
					int[] b = a.coords.bbox31;
					bbox = new int[] { b[0], b[1], b[2], b[3] };
				} else {
					SpatialSearchResultsList.clipBbox(bbox, a.coords.bbox31);
				}
			}
		}
		if (bbox == null && res.mainAtom1 != null && res.mainAtom1.coords.bbox31 != null) {
			int[] b = res.mainAtom1.coords.bbox31;
			bbox = new int[] { b[0], b[1], b[2], b[3] };
		}
		return bbox;
	}

	/** Intersection bbox when adding `added` token to partial `parent` (legacy addResult). */
	static int[] intersectionBboxForJoin(SpatialObjectRes parent, SpatialObjectRes added, int addedTokenIdx) {
		return intersectionBboxForJoin(parent, added, addedTokenIdx, -1);
	}

	static int[] intersectionBboxForJoin(SpatialObjectRes parent, SpatialObjectRes added, int addedTokenIdx,
			int leftProjectTokenIdx) {
		NameIndexAtom newAtom = atomAt(added, addedTokenIdx);
		if (newAtom == null || newAtom.coords == null || newAtom.coords.bbox31 == null) {
			return intersectionBbox(parent);
		}
		int[] b = newAtom.coords.bbox31;
		int[] target = new int[] { b[0], b[1], b[2], b[3] };
		if (leftProjectTokenIdx >= 0) {
			NameIndexAtom pa = atomAt(parent, leftProjectTokenIdx);
			if (pa != null && pa.coords != null && pa.coords.bbox31 != null) {
				SpatialSearchResultsList.clipBbox(target, pa.coords.bbox31);
			}
		} else if (parent.atoms != null) {
			for (NameIndexAtom pa : parent.atoms) {
				if (pa != null && pa.coords != null && pa.coords.bbox31 != null) {
					SpatialSearchResultsList.clipBbox(target, pa.coords.bbox31);
				}
			}
		}
		if (target[0] > target[2] || target[1] > target[3]) {
			return null;
		}
		return target;
	}

	static NameIndexAtom atomAt(SpatialObjectRes res, int tokenIdx) {
		if (res.atoms != null && tokenIdx >= 0 && tokenIdx < res.atoms.length) {
			NameIndexAtom a = res.atoms[tokenIdx];
			if (a != null) {
				return a;
			}
		}
		return res.mainAtom1;
	}

	static long incrementalLeftMask(SpatialObjectRes o1, int projectO1TokenIdx) {
		if (projectO1TokenIdx >= 0) {
			return SpatialTokenMask.projectMaskForToken(o1.mainMask, projectO1TokenIdx);
		}
		return SpatialTokenMask.demoteAtomicSaturation(o1.mainMask);
	}

	static long[] incrementalLeftVariants(SpatialObjectRes o1, int projectO1TokenIdx) {
		long[] vars = o1.variants();
		long[] out = new long[vars.length];
		for (int i = 0; i < vars.length; i++) {
			out[i] = projectO1TokenIdx >= 0 ? SpatialTokenMask.projectMaskForToken(vars[i], projectO1TokenIdx)
					: SpatialTokenMask.demoteAtomicSaturation(vars[i]);
		}
		return out;
	}

	static boolean isBboxEmpty(int[] bbox) {
		return bbox == null || bbox[0] > bbox[2] || bbox[1] > bbox[3];
	}

	@SuppressWarnings("unchecked")
	private HashSkipTileQuadTree<SpatialObjectRes>[] buildTokenTrees(SpatialPipelineResults prep, int tokensSize) {
		HashSkipTileQuadTree<SpatialObjectRes>[] trees = new HashSkipTileQuadTree[tokensSize];
		for (int i = 0; i < tokensSize; i++) {
			trees[i] = new HashSkipTileQuadTree<>();
		}
		for (SpatialObjectRes obj : prep.objectsById.valueCollection()) {
			long mask = obj.mainMask;
			int[] bb = obj.mainAtom1.coords.bbox31;
			for (int t = 0; t < tokensSize; t++) {
				if (SpatialTokenMask.getTokenState(mask, t) != STATE_NO_MATCH) {
					trees[t].addObject(obj, bb, obj.mainAtom1.id);
				}
			}
		}
		return trees;
	}

	private int[] sortedTokenIndices(List<SpatialSearchToken> tokens, int tokensSize) {
		Integer[] order = new Integer[tokensSize];
		for (int i = 0; i < tokensSize; i++) {
			order[i] = i;
		}
		Arrays.sort(order, (a, b) -> {
			int cmp = Integer.compare(tokens.get(a).atoms.size(), tokens.get(b).atoms.size());
			return cmp != 0 ? cmp : Integer.compare(a, b);
		});
		int[] result = new int[tokensSize];
		for (int i = 0; i < tokensSize; i++) {
			result[i] = order[i];
		}
		return result;
	}

	/**
	 * Legacy-style rare-first chain: token₀ × token₁ × … instead of one 78k² self-join.
	 */
	private boolean runIncrementalTokenJoin(SpatialPipelineResults prep, int tokensSize, int[] stageRef, long time)
			throws IOException {
		int[] tokenOrder = sortedTokenIndices(prep.tokens, tokensSize);
		HashSkipTileQuadTree<SpatialObjectRes>[] tokenTrees = buildTokenTrees(prep, tokensSize);
		HashSkipTileQuadTree<SpatialObjectRes> current = tokenTrees[tokenOrder[0]];
		current.build();
		boolean exit = false;
		int stage = stageRef[0];
		for (int step = 1; step < tokensSize && !ctx.isCancelled() && !exit; step++) {
			HashSkipTileQuadTree<SpatialObjectRes> next = tokenTrees[tokenOrder[step]];
			if (next.isEmpty()) {
				continue;
			}
			next.build();
			if (ctx.stats.printLogs) {
				System.out.printf("PIPELINE TOKEN JOIN %d/%d '%s' x '%s' - %,d x %,d\n", step, tokensSize - 1,
						prep.tokens.get(tokenOrder[step - 1]).word, prep.tokens.get(tokenOrder[step]).word,
						current.getSize(), next.getSize());
			}
			HashSkipTileQuadTreeJoiner<SpatialObjectRes, SpatialObjectRes> joiner = new HashSkipTileQuadTreeJoiner<>(
					current, next);
			exit = join(prep, stage++, joiner, false, time, step == 1 ? tokenOrder[0] : -1, tokenOrder[step]);
			time = System.nanoTime();
			if (prep.pairsTree.isEmpty()) {
				break;
			}
			current = prep.pairsTree.get(prep.pairsTree.size() - 1);
			current.build();
		}
		stageRef[0] = stage;
		return exit;
	}

	public List<SpatialSearchResultsList> runPipeline(List<SpatialSearchToken> tokens) throws IOException {
		if (tokens == null || tokens.isEmpty()) {
			return Collections.emptyList();
		}
		final int tokensSize = Math.min(tokens.size(), MAX_SUPPORTED_TOKENS);
		long time = System.nanoTime();

		// STEP 0 PREPARE
		int stage = 0;
		SpatialPipelineResults prep = prepare(tokens);
		if (ctx.stats.printLogs) {
			System.out.printf("PIPELINE PREPARE tokens (%.1f ms): %,d objects\n", (System.nanoTime() - time) / 1e6,
					prep.allObjectsTree.getSize());
			if (ctx.settings.DEV_VERBOSE_MASK_STATS) {
				SpatialStagePipelineStats.printTree(prep);
			}
		}
		time = System.nanoTime();
		if (stage++ >= MAX_STEPS || ctx.isCancelled()) {
			return prep.combinations;
		}

		// STEP 1: single objects covering all tokens
		List<SpatialObjectRes> singleResults = new ArrayList<>();
		for (SpatialObjectRes obj : prep.objectsById.valueCollection()) {
			if (SpatialTokenMask.countCoveredTokens(obj.mainMask) == tokensSize) {
				singleResults.add(obj);
			}
		}
		if (validateStageAndFinish(prep, null, singleResults, stage, time)) {
			return prep.combinations;
		}
		time = System.nanoTime();
		if (stage++ >= MAX_STEPS || ctx.isCancelled()) {
			return prep.combinations;
		}

		// STEP 2: pair discovery — incremental token chain (fast) or all×all self-join
		boolean exit;
		if (ctx.settings.DEV_USE_INCREMENTAL_PIPELINE) {
			int[] stageRef = new int[] { stage };
			exit = runIncrementalTokenJoin(prep, tokensSize, stageRef, time);
			stage = stageRef[0];
		} else {
			HashSkipTileQuadTreeJoiner<SpatialObjectRes, SpatialObjectRes> selfJoiner = new HashSkipTileQuadTreeJoiner<>(
					prep.allObjectsTree, prep.allObjectsTree);
			exit = join(prep, stage, selfJoiner, true, time, -1, -1);
			stage++;
		}
		if (ctx.isCancelled() || exit) {
			return prep.combinations;
		}
		time = System.nanoTime();

		// Partial pairs × area objects (city, boundary…)
		for (; stage <= MAX_STEPS && !ctx.isCancelled() && !exit; stage++) {
			HashSkipTileQuadTree<SpatialObjectRes> lastTree = prep.pairsTree.get(prep.pairsTree.size() - 1);
			if (lastTree.isEmpty()) {
				break;
			}
			lastTree.build();
			HashSkipTileQuadTreeJoiner<SpatialObjectRes, SpatialObjectRes> joiner = new HashSkipTileQuadTreeJoiner<>(
					lastTree, prep.areaObjectsTree);
			exit = join(prep, stage, joiner, false, time, -1, -1);
			time = System.nanoTime();
		}
		// check potential missing results
		if (CHECK_EXCLUDED) {
			checkExcluded(tokensSize, prep);
		}

		return prep.combinations;
	}

	private void checkExcluded(final int tokensSize, SpatialPipelineResults prep) throws IOException {
		long[] excl = prep.excludedMasks.keys();
		if (ctx.stats.printLogs) {
			System.out.println("Excluded masks: " + excl.length);
		}
		MasksStats baseMasksStats = prep.masksStats.get(0);
		long time = System.nanoTime();
		// join() below appends to masksStats/pairsTree — iterate a snapshot
		final int statsSnapshot = prep.masksStats.size();
		for (int stage = 1; stage < MAX_STEPS && stage < statsSnapshot; stage++) {
			for (int i = 0; i < statsSnapshot; i++) {
				MasksStats masksStats = prep.masksStats.get(i);
				if (masksStats.intersections != stage) {
					continue;
				}
				HashSkipTileQuadTree<SpatialObjectRes> partialTree = i == 0 ? prep.allObjectsTree
						: prep.pairsTree.get(i - 1);

				TLongHashSet found = new TLongHashSet();
				for (int k = 0; k < excl.length; k++) {
					long maskExcl = excl[k];
					for (long m : masksStats.masks.keys()) {
						if (!SpatialTokenMask.allowed(m, maskExcl)) {
							continue;
						}
						long combined = SpatialTokenMask.combine(m, maskExcl);
						if (SpatialTokenMask.countCoveredTokens(combined) == tokensSize) {
							if (ctx.stats.printLogs) {
								Integer c1 = baseMasksStats.masks.get(maskExcl);
								Integer c2 = masksStats.masks.get(m);
								System.out.printf(
										"Potential results %d intersections - missing %s (%,d) x %s (%,d < %,d ) = %,d \n",
										stage + 1, SpatialObjectRes.formatMaskTokens(maskExcl, prep.tokens), c1,
										SpatialObjectRes.formatMaskTokens(m, prep.tokens), c2, partialTree.getSize(),
										c1 * c2);
							}
							found.add(maskExcl);
						}
					}
				}
				if (found.size() == 0) {
					continue;
				}
				HashSkipTileQuadTree<SpatialObjectRes> exclTree = new HashSkipTileQuadTree<>();
				for (long exclMask : found.toArray()) {
					for (SpatialObjectRes r : prep.excludedMasks.get(exclMask)) {
						exclTree.addObject(r, r.mainAtom1.coords.bbox31, r.mainAtom1.id);
					}
				}
				exclTree.build();

				partialTree.build();
				HashSkipTileQuadTreeJoiner<SpatialObjectRes, SpatialObjectRes> tailJoiner = new HashSkipTileQuadTreeJoiner<>(
						partialTree, exclTree);
				boolean exit = join(prep, stage + 1, tailJoiner, false, time, -1, -1);
				if (ctx.isCancelled() || exit) {
					return;
				}
				time = System.nanoTime();
			}
		}
	}

	private boolean join(SpatialPipelineResults prep, int stage,
			HashSkipTileQuadTreeJoiner<SpatialObjectRes, SpatialObjectRes> joiner, boolean selfJoin, long time,
			int projectO1TokenIdx, int projectO2TokenIdx) throws IOException {
		List<SpatialObjectRes> pairResults = new ArrayList<>();
		final int tokensSize = prep.tokens.size();
		final boolean incremental = projectO2TokenIdx >= 0;
		HashSkipTileQuadTree<SpatialObjectRes> pairsTree = new HashSkipTileQuadTree<>();
		prep.pairsTree.add(pairsTree);
		final MasksStats ms = new MasksStats(stage);
		prep.masksStats.add(ms);
		int[] itStats = new int[] { 0, 0, 0 };
		if (ctx.stats.printLogs) {
			System.out.printf("PIPELINE STAGE %d INTERSECT - %,d x %,d tree...\n", stage,
					joiner.getTree1().getSize(), joiner.getTree2().getSize());
		}
		final boolean[] stopEarly = new boolean[] { false };
		joiner.joinAllBuckets((e1, e2) -> {
			if (stopEarly[0]) {
				return;
			}
			itStats[0]++;
			if (selfJoin && e1.objId == e2.objId) {
				return;
			}
			SpatialObjectRes o1 = e1.obj;
			SpatialObjectRes o2 = e2.obj;
			long m1, m2, combinedMask;
			if (o1.variants == null && o2.variants == null) {
				m1 = incremental ? incrementalLeftMask(o1, projectO1TokenIdx) : o1.mainMask;
				m2 = incremental ? SpatialTokenMask.projectMaskForToken(o2.mainMask, projectO2TokenIdx) : o2.mainMask;
				if (!SpatialTokenMask.allowed(m1, m2)) {
					return;
				}
				combinedMask = incremental ? SpatialTokenMask.combinePartial(m1, m2)
						: SpatialTokenMask.combine(m1, m2);
			} else {
				long[] vars1 = incremental ? incrementalLeftVariants(o1, projectO1TokenIdx) : o1.variants();
				long[] vars2 = o2.variants();
				if (incremental) {
					long[] p2 = new long[vars2.length];
					for (int vi = 0; vi < vars2.length; vi++) {
						p2[vi] = SpatialTokenMask.projectMaskForToken(vars2[vi], projectO2TokenIdx);
					}
					vars2 = p2;
				}
				long[] best = incremental ? SpatialTokenMask.bestAllowedCombinePartial(vars1, vars2)
						: SpatialTokenMask.bestAllowedCombine(vars1, vars2);
				if (best == null) {
					return;
				}
				combinedMask = best[0];
				m1 = best[1];
				m2 = best[2];
			}
			itStats[1]++;
			ms.count(combinedMask);
			if (SpatialTokenMask.countCoveredTokens(combinedMask) == tokensSize) {
				itStats[2]++;
				long fm1 = incremental ? incrementalLeftMask(o1, projectO1TokenIdx) : m1;
				long fm2 = incremental ? SpatialTokenMask.projectMaskForToken(o2.mainMask, projectO2TokenIdx) : m2;
				for (long[] resolved : SpatialTokenMask.expandContestedTokens(fm1, fm2)) {
					long resolvedMask = SpatialTokenMask.combine(resolved[0], resolved[1]);
					SpatialObjectRes res = new SpatialObjectRes(resolvedMask, resolved[0], resolved[1], o1, o2);
					if (acceptPairSemantic(ctx, res)) {
						pairResults.add(res);
						if (ctx.settings.PIPELINE_STOP_ON_FIRST_COMPLETE) {
							stopEarly[0] = true;
						}
					}
				}
				return;
			}
			SpatialObjectRes res = new SpatialObjectRes(combinedMask, m1, m2, o1, o2);
			if (res.mainAtom1 == null) {
				return;
			}
			int[] clippedBBox;
			if (incremental) {
				clippedBBox = intersectionBboxForJoin(o1, o2, projectO2TokenIdx, projectO1TokenIdx);
				if (isBboxEmpty(clippedBBox)) {
					return;
				}
			} else {
				int[] bb = res.mainAtom1.coords.bbox31;
				clippedBBox = new int[] { bb[0], bb[1], bb[2], bb[3] };
				if (res.mainAtom2 != null) {
					SpatialSearchResultsList.clipBbox(clippedBBox, res.mainAtom2.coords.bbox31);
				}
			}
			pairsTree.addObject(res, clippedBBox, -1);
		});

		return validateStageAndFinish(prep, itStats, pairResults, stage, time);
	}

	private SpatialSearchResultsList createResultList(List<SpatialSearchToken> tokens, List<SpatialObjectRes> r) {
		SpatialSearchResultsList singleResults = new SpatialSearchResultsList(tokens);
		for (SpatialObjectRes res : r) {
			singleResults.tileIds.add(res.atoms[0].coords.bboxTileId);
			for (int i = 0; i < res.atoms.length; i++) {
				singleResults.linearResults.add(res.atoms[i]);
			}
		}
		return singleResults;
	}

	/**
	 * Semantic rules not already enforced by the mask header in
	 * {@link SpatialTokenMask#allowed(long, long)}.
	 */
	public static boolean acceptPairSemantic(SpatialSearchContext ctx, SpatialObjectRes pair) {
		NameIndexAtom a1 = pair.mainAtom1;
		NameIndexAtom a2 = pair.mainAtom2;
		if (a1 == null || a2 == null) {
			return true; // deep combination - sides were validated pairwise before
		}
		SpatialTextSearch.SpatialTextSearchSettings settings = ctx.settings;
		if (!settings.SEARCH_STREET_INTERSECTIONS && a1.isStreetBuilding() && a2.isStreetBuilding()) {
			return false;
		}
		if (!settings.SEARCH_POI_INTERSECTIONS && a1.isPOI() && a2.isPOI()) {
			return false;
		}
		return true;
	}
}
