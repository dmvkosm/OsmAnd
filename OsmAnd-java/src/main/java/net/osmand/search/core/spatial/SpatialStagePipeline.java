package net.osmand.search.core.spatial;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import gnu.trove.map.hash.TLongObjectHashMap;
import gnu.trove.set.hash.TIntHashSet;
import gnu.trove.set.hash.TLongHashSet;
import net.osmand.search.core.HashSkipTileQuadTree;
import net.osmand.search.core.HashSkipTileQuadTree.TileEntry;
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
		/** Legacy typeIntersections value for acceptIntersection (0/1/2). */
		int intersectionType = 0;
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

	static int joinNearbyLevel(SpatialObjectRes parent, NameIndexAtom newAtom, int leftProjectTokenIdx) {
		int level = newAtom.nearbyRadius;
		if (leftProjectTokenIdx >= 0) {
			NameIndexAtom pa = atomAt(parent, leftProjectTokenIdx);
			if (pa != null) {
				level = Math.max(level, pa.nearbyRadius);
			}
		} else if (parent.atoms != null) {
			for (NameIndexAtom pa : parent.atoms) {
				if (pa != null) {
					level = Math.max(level, pa.nearbyRadius);
				}
			}
		}
		return level;
	}

	static final class IncrementalCandidate {
		final SpatialObjectRes res;
		final int[] bbox;
		final int level;

		IncrementalCandidate(SpatialObjectRes res, int[] bbox, int level) {
			this.res = res;
			this.bbox = bbox;
			this.level = level;
		}
	}

	/**
	 * Flush radius-bucketed candidates split by intersection type - exact port of the legacy
	 * 3 x addResIntersections calls: plain (type 0) defines newLevel, poi-street (1) and
	 * street-street/poi-poi (2) are capped at that level; count is shared across all types.
	 */
	static int flushIncrementalCandidates(List<IncrementalCandidate>[][] byTypeLevel, int maxLevel,
			HashSkipTileQuadTree<SpatialObjectRes> pairsTree, int limit) {
		int[] count = new int[] { 0 };
		int newLevel = flushCandidatesType(byTypeLevel[0], maxLevel, pairsTree, limit, count);
		flushCandidatesType(byTypeLevel[1], newLevel, pairsTree, limit, count);
		flushCandidatesType(byTypeLevel[2], newLevel, pairsTree, limit, count);
		return newLevel;
	}

	private static int flushCandidatesType(List<IncrementalCandidate>[] byLevel, int maxLevel,
			HashSkipTileQuadTree<SpatialObjectRes> pairsTree, int limit, int[] count) {
		int newLevel = 0;
		for (int level = 0; level <= maxLevel; level++) {
			List<IncrementalCandidate> toAdd = byLevel[level];
			int toAddSize = toAdd == null ? 0 : toAdd.size();
			// legacy: empty levels still advance newLevel while under the limit
			if (count[0] == 0 || (level == 0 && maxLevel > 0) || count[0] + toAddSize < limit) {
				if (toAdd != null) {
					for (IncrementalCandidate c : toAdd) {
						pairsTree.addObject(c.res, c.bbox, -1);
					}
					count[0] += toAddSize;
				}
				newLevel = level;
			} else {
				break;
			}
		}
		return newLevel;
	}

	/**
	 * Legacy {@link SpatialSearchResultsList#acceptIntersectionImpl} for pipeline incremental join.
	 * Parent atoms are ordered newest-first (reverse join chain), matching legacy parent.tokens.
	 */
	static boolean acceptIncrementalJoin(SpatialSearchContext ctx, List<SpatialSearchToken> tokens,
			int[] tokenOrder, int parentTokenCount, SpatialObjectRes parent, int projectO1TokenIdx,
			SpatialSearchToken newToken, NameIndexAtom newAtom, int[] typeOut) {
		SpatialSearchToken[] parentTokens;
		NameIndexAtom[] parentAtoms;
		if (projectO1TokenIdx >= 0) {
			parentTokens = new SpatialSearchToken[] { tokens.get(projectO1TokenIdx) };
			parentAtoms = new NameIndexAtom[] { atomAt(parent, projectO1TokenIdx) };
		} else {
			parentTokens = new SpatialSearchToken[parentTokenCount];
			parentAtoms = new NameIndexAtom[parentTokenCount];
			for (int j = 0; j < parentTokenCount; j++) {
				int sortedIdx = tokenOrder[parentTokenCount - 1 - j];
				parentTokens[j] = tokens.get(sortedIdx);
				parentAtoms[j] = atomAt(parent, sortedIdx);
			}
		}
		return SpatialSearchResultsList.acceptIntersectionImpl(ctx, parentTokens, parentAtoms,
				parent.intersectionType, newToken, newAtom, typeOut);
	}

	static final class PartialEntry {
		final SpatialObjectRes res;
		final int[] bbox;

		PartialEntry(SpatialObjectRes res, int[] bbox) {
			this.res = res;
			this.bbox = bbox;
		}
	}

	static List<PartialEntry> dedupePartialEntries(HashSkipTileQuadTree<SpatialObjectRes> tree) {
		tree.build();
		LinkedHashMap<SpatialObjectRes, PartialEntry> uniq = new LinkedHashMap<>();
		for (TileEntry<SpatialObjectRes> e : tree.getTileEntries()) {
			uniq.putIfAbsent(e.obj, new PartialEntry(e.obj, e.bbox31));
		}
		return new ArrayList<>(uniq.values());
	}

	static HashSkipTileQuadTree<Integer> buildPartialSkipTree(List<PartialEntry> partials) {
		HashSkipTileQuadTree<Integer> skip = new HashSkipTileQuadTree<>();
		for (int i = 0; i < partials.size(); i++) {
			int[] bbox = partials.get(i).bbox;
			if (!isBboxEmpty(bbox)) {
				skip.addObject(i, bbox, i);
			}
		}
		skip.build();
		return skip;
	}

	/** Partials of the chain seed: all objects matching the given token, bbox = matching atom bbox. */
	private List<PartialEntry> buildFirstTokenPartials(SpatialPipelineResults prep, int tokenIdx) {
		List<PartialEntry> entries = new ArrayList<>();
		for (SpatialObjectRes obj : prep.objectsById.valueCollection()) {
			if (SpatialTokenMask.getTokenState(obj.mainMask, tokenIdx) != STATE_NO_MATCH) {
				NameIndexAtom atom = atomAt(obj, tokenIdx);
				if (atom != null && atom.coords != null && atom.coords.bbox31 != null) {
					entries.add(new PartialEntry(obj, atom.coords.bbox31));
				}
			}
		}
		return entries;
	}

	private int[] sortedTokenIndices(List<SpatialSearchToken> tokens, int tokensSize) {
		Integer[] order = new Integer[tokensSize];
		for (int i = 0; i < tokensSize; i++) {
			order[i] = i;
		}
		Arrays.sort(order, (a, b) -> {
			int cmp = Long.compare(chainWeight(tokens.get(a)), chainWeight(tokens.get(b)));
			return cmp != 0 ? cmp : Integer.compare(a, b);
		});
		int[] result = new int[tokensSize];
		for (int i = 0; i < tokensSize; i++) {
			result[i] = order[i];
		}
		return result;
	}

	/**
	 * Incremental join chain order: rare tokens (few atoms) first, deferred tokens last.
	 * Deferred tokens use a large base weight so they join only after partials have
	 * been narrowed by earlier steps and can supply a tight bbox filter.
	 */
	private static long chainWeight(SpatialSearchToken t) {
		if (t.deferredRead) {
			return 1_000_000_000L + t.estimatedDeferredAtoms;
		}
		return t.atoms.size();
	}

	/**
	 * Rare-first incremental token chain (replaces stage-2 all×all self-join).
	 *
	 * Flow:
	 * 1. Sort tokens by chainWeight (small/rare first, deferred common words last).
	 * 2. Seed partials from token₀ objects (buildFirstTokenPartials).
	 * 3. For each next token: if deferred → readDeferredAndIngest with bbox filter
	 *    from surviving partials; then spatial join via joinIncremental (quadTreeSkip).
	 * 4. acceptIncrementalJoin delegates to legacy acceptIntersectionImpl for semantics.
	 * 5. flushIncrementalCandidates mirrors legacy addResIntersections (3 type buckets).
	 *
	 * With OPTIM_DEFER_READ_TOKEN_ATOMS_LIMIT, match time drops because huge tokens
	 * parse only atoms inside partial bboxes instead of the whole country prefix set.
	 */
	private boolean runIncrementalTokenJoin(SpatialPipelineResults prep, int tokensSize, int[] stageRef, long time)
			throws IOException {
		int[] tokenOrder = sortedTokenIndices(prep.tokens, tokensSize);
		if (prep.tokens.get(tokenOrder[0]).deferredRead) {
			// query of only huge tokens - no rare seed, read unfiltered
			readDeferredAndIngest(prep, tokenOrder[0], null);
		}
		List<PartialEntry> parentEntries = buildFirstTokenPartials(prep, tokenOrder[0]);
		boolean exit = false;
		int stage = stageRef[0];
		int[] limitIntersection = new int[] { ctx.limitLocationBboxes.length };
		for (int step = 1; step < tokensSize && !ctx.isCancelled() && !exit; step++) {
			int addedTokenIdx = tokenOrder[step];
			SpatialSearchToken nextToken = prep.tokens.get(addedTokenIdx);
			if (nextToken.deferredRead) {
				long dt = System.nanoTime();
				readDeferredAndIngest(prep, addedTokenIdx, collectFilterBboxes(parentEntries));
				if (ctx.stats.printLogs) {
					System.out.printf("PIPELINE DEFERRED READ '%s' (%.1f ms): %,d/%,d atoms in %,d bboxes\n",
							nextToken.word, (System.nanoTime() - dt) / 1e6, nextToken.atoms.size(),
							nextToken.estimatedDeferredAtoms, parentEntries.size());
				}
			}
			if (nextToken.atoms.isEmpty()) {
				continue;
			}
			if (ctx.stats.printLogs) {
				System.out.printf("PIPELINE TOKEN JOIN %d/%d '%s' x '%s' - %,d x %,d (limit %d)\n", step,
						tokensSize - 1, prep.tokens.get(tokenOrder[step - 1]).word, nextToken.word,
						parentEntries.size(), nextToken.atoms.size(), limitIntersection[0]);
			}
			exit = joinIncremental(prep, stage++, tokenOrder, step, parentEntries,
					step == 1 ? tokenOrder[0] : -1, addedTokenIdx, limitIntersection, time);
			time = System.nanoTime();
			if (prep.pairsTree.isEmpty()) {
				break;
			}
			parentEntries = dedupePartialEntries(prep.pairsTree.get(prep.pairsTree.size() - 1));
			if (parentEntries.isEmpty()) {
				break;
			}
		}
		stageRef[0] = stage;
		return exit;
	}

	/**
	 * Parse a deferred token (bbox-filtered) and merge its atoms into the pipeline object map
	 * so the following joinIncremental step can use token.quadTreeSkip as the right side.
	 */
	private void readDeferredAndIngest(SpatialPipelineResults prep, int tokenIdx, List<int[]> filterBboxes)
			throws IOException {
		SpatialSearchToken token = prep.tokens.get(tokenIdx);
		ctx.readDeferredTokenAtoms(token, filterBboxes);
		TIntHashSet deleted = token.getDeletedAtoms();
		for (NameIndexAtom atom : token.atoms) {
			if (deleted.contains(atom.indexInToken)) {
				continue;
			}
			SpatialObjectRes existing = prep.objectsById.get(atom.id);
			if (existing != null) {
				existing.mergeSame(atom, tokenIdx);
				if (existing.variants != null) {
					// variants were computed in prepare() before this token was read;
					// deferred tokens are never inside duplicate groups, so all variants
					// receive the same new token state as mainMask
					long state = SpatialTokenMask.getTokenState(existing.mainMask, tokenIdx);
					for (int i = 0; i < existing.variants.length; i++) {
						existing.variants[i] = SpatialTokenMask.setTokenState(existing.variants[i], tokenIdx, state);
					}
				}
			} else {
				prep.objectsById.put(atom.id, new SpatialObjectRes(prep.tokens.size(), atom, tokenIdx));
			}
		}
	}

	/**
	 * Bboxes of partial results after the previous join step — used as spatial filter
	 * for the next deferred token read. Up to 256 individual bboxes (precise); above
	 * that a single union bbox to keep filter checks O(1) per atom.
	 */
	static List<int[]> collectFilterBboxes(List<PartialEntry> parents) {
		if (parents.isEmpty()) {
			return null;
		}
		if (parents.size() > 256) {
			int[] union = null;
			for (PartialEntry p : parents) {
				if (isBboxEmpty(p.bbox)) {
					continue;
				}
				if (union == null) {
					union = new int[] { p.bbox[0], p.bbox[1], p.bbox[2], p.bbox[3] };
				} else {
					union[0] = Math.min(union[0], p.bbox[0]);
					union[1] = Math.min(union[1], p.bbox[1]);
					union[2] = Math.max(union[2], p.bbox[2]);
					union[3] = Math.max(union[3], p.bbox[3]);
				}
			}
			return union == null ? null : Collections.singletonList(union);
		}
		List<int[]> res = new ArrayList<>(parents.size());
		for (PartialEntry p : parents) {
			if (!isBboxEmpty(p.bbox)) {
				res.add(p.bbox);
			}
		}
		return res.isEmpty() ? null : res;
	}

	/**
	 * Incremental join using legacy spatial indexing: token.quadTreeSkip x partial skip-tree.
	 */
	private boolean joinIncremental(SpatialPipelineResults prep, int stage, int[] tokenOrder, int parentTokenCount,
			List<PartialEntry> parentEntries, int projectO1TokenIdx, int addedTokenIdx, int[] limitIntersectionRef,
			long time) throws IOException {
		final int tokensSize = prep.tokens.size();
		final SpatialSearchToken addedToken = prep.tokens.get(addedTokenIdx);
		addedToken.quadTreeSkip.build();
		HashSkipTileQuadTree<Integer> parentSkip = buildPartialSkipTree(parentEntries);
		HashSkipTileQuadTreeJoiner<Integer, Integer> joiner = new HashSkipTileQuadTreeJoiner<>(
				addedToken.quadTreeSkip, parentSkip);

		List<SpatialObjectRes> pairResults = new ArrayList<>();
		HashSkipTileQuadTree<SpatialObjectRes> pairsTree = new HashSkipTileQuadTree<>();
		prep.pairsTree.add(pairsTree);
		final MasksStats ms = new MasksStats(stage);
		prep.masksStats.add(ms);
		int[] itStats = new int[] { 0, 0, 0 };
		if (ctx.stats.printLogs) {
			System.out.printf("PIPELINE STAGE %d INTERSECT (legacy skip) - %,d x %,d\n", stage,
					addedToken.atoms.size(), parentEntries.size());
		}
		final int limitIntersection = limitIntersectionRef[0];
		@SuppressWarnings("unchecked")
		final List<IncrementalCandidate>[][] byTypeLevel = new List[3][ctx.limitLocationBboxes.length + 1];
		final boolean[] stopEarly = new boolean[] { false };
		final int[] rejDbg = ctx.settings.DEV_DEBUG_INCREMENTAL_JOIN ? new int[8] : null;

		joiner.joinAllBuckets((e1, e2) -> {
			if (stopEarly[0]) {
				return;
			}
			itStats[0]++;
			int atomIdx = e1.obj;
			int partialIdx = e2.obj;
			if (addedToken.deletedAtoms.contains(atomIdx)) {
				return;
			}
			NameIndexAtom newAtom = addedToken.atoms.get(atomIdx);
			SpatialObjectRes o1 = parentEntries.get(partialIdx).res;
			SpatialObjectRes o2 = prep.objectsById.get(newAtom.id);
			if (o2 == null) {
				if (rejDbg != null) {
					rejDbg[0]++;
				}
				return;
			}
			long m1, m2, combinedMask;
			if (o1.variants == null && o2.variants == null) {
				m1 = incrementalLeftMask(o1, projectO1TokenIdx);
				m2 = SpatialTokenMask.projectMaskForToken(o2.mainMask, addedTokenIdx);
				if (!SpatialTokenMask.allowed(m1, m2)) {
					if (rejDbg != null) {
						rejDbg[1]++;
					}
					return;
				}
				combinedMask = SpatialTokenMask.combinePartial(m1, m2);
			} else {
				long[] vars1 = incrementalLeftVariants(o1, projectO1TokenIdx);
				long[] vars2 = o2.variants();
				long[] p2 = new long[vars2.length];
				for (int vi = 0; vi < vars2.length; vi++) {
					p2[vi] = SpatialTokenMask.projectMaskForToken(vars2[vi], addedTokenIdx);
				}
				long[] best = SpatialTokenMask.bestAllowedCombinePartial(vars1, p2);
				if (best == null) {
					if (rejDbg != null) {
						rejDbg[2]++;
					}
					return;
				}
				combinedMask = best[0];
				m1 = best[1];
				m2 = best[2];
			}
			ms.count(combinedMask);
			int[] typeOut = new int[] { -1 };
			if (SpatialTokenMask.countCoveredTokens(combinedMask) == tokensSize) {
				if (!acceptIncrementalJoin(ctx, prep.tokens, tokenOrder, parentTokenCount, o1, projectO1TokenIdx,
						addedToken, newAtom, typeOut)) {
					return;
				}
				itStats[1]++;
				itStats[2]++;
				long fm1 = incrementalLeftMask(o1, projectO1TokenIdx);
				long fm2 = SpatialTokenMask.projectMaskForToken(o2.mainMask, addedTokenIdx);
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
			int level = joinNearbyLevel(o1, newAtom, projectO1TokenIdx);
			if (level > limitIntersection) {
				if (rejDbg != null) {
					rejDbg[4]++;
				}
				return;
			}
			if (!acceptIncrementalJoin(ctx, prep.tokens, tokenOrder, parentTokenCount, o1, projectO1TokenIdx,
					addedToken, newAtom, typeOut)) {
				if (rejDbg != null) {
					rejDbg[3]++;
				}
				return;
			}
			SpatialObjectRes res = new SpatialObjectRes(combinedMask, m1, m2, o1, o2);
			res.intersectionType = Math.max(0, typeOut[0]);
			if (res.mainAtom1 == null) {
				if (rejDbg != null) {
					rejDbg[5]++;
				}
				return;
			}
			int[] clippedBBox = intersectionBboxForJoin(o1, o2, addedTokenIdx, projectO1TokenIdx);
			if (isBboxEmpty(clippedBBox)) {
				if (rejDbg != null) {
					rejDbg[6]++;
				}
				return;
			}
			int type = res.intersectionType;
			if (byTypeLevel[type][level] == null) {
				byTypeLevel[type][level] = new ArrayList<>();
			}
			byTypeLevel[type][level].add(new IncrementalCandidate(res, clippedBBox, level));
			itStats[1]++;
		});

		limitIntersectionRef[0] = flushIncrementalCandidates(byTypeLevel, limitIntersection, pairsTree,
				ctx.settings.OPTIM_LIMIT_INTERSECTIONS);
		if (rejDbg != null && itStats[0] > 0) {
			System.out.printf("  JOIN DEBUG '%s': cross %,d allowedFail %,d varFail %,d semFail %,d levelFail %,d"
					+ " mainAtomFail %,d bboxFail %,d kept %,d\n", addedToken.word, itStats[0], rejDbg[1], rejDbg[2],
					rejDbg[3], rejDbg[4], rejDbg[5], rejDbg[6], itStats[1]);
		}
		return validateStageAndFinish(prep, itStats, pairResults, stage, time);
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
		if (ctx.settings.DEV_MASK_CLASS_EXPERIMENT) {
			SpatialMaskClassExperiment.run(ctx, prep);
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

		// STEP 2 alternative: mask-class planned joins produce final combinations directly.
		// Note: like the regular pipeline, only full-coverage combinations become results;
		// fallback partials are collected for diagnostics (result assembly is full-cover only).
		if (ctx.settings.DEV_USE_MASK_CLASS_PIPELINE) {
			List<SpatialObjectRes> covers = SpatialMaskClassExperiment.runJoin(ctx, prep, null, false);
			validateStageAndFinish(prep, null, covers, stage, time);
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
			exit = join(prep, stage, selfJoiner, true, time);
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
			exit = join(prep, stage, joiner, false, time);
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
				boolean exit = join(prep, stage + 1, tailJoiner, false, time);
				if (ctx.isCancelled() || exit) {
					return;
				}
				time = System.nanoTime();
			}
		}
	}

	private boolean join(SpatialPipelineResults prep, int stage,
			HashSkipTileQuadTreeJoiner<SpatialObjectRes, SpatialObjectRes> joiner, boolean selfJoin, long time)
			throws IOException {
		List<SpatialObjectRes> pairResults = new ArrayList<>();
		final int tokensSize = prep.tokens.size();
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
			ms.count(combinedMask);
			if (SpatialTokenMask.countCoveredTokens(combinedMask) == tokensSize) {
				itStats[1]++;
				itStats[2]++;
				for (long[] resolved : SpatialTokenMask.expandContestedTokens(m1, m2)) {
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
			itStats[1]++;
			int[] bb = res.mainAtom1.coords.bbox31;
			int[] clippedBBox = new int[] { bb[0], bb[1], bb[2], bb[3] };
			if (res.mainAtom2 != null) {
				SpatialSearchResultsList.clipBbox(clippedBBox, res.mainAtom2.coords.bbox31);
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
