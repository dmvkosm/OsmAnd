# Spatial pipeline: incremental join + deferred common-word read

Stacked on [PR #25535](https://github.com/osmandapp/OsmAnd/pull/25535) (token mask algebra).
Target branch: **`spatialPipeline-mask-fixes`** → then **`spatialPipeline`**.

## What this PR adds

| Piece | Setting | Default |
|-------|---------|---------|
| Rare-first incremental token chain | `DEV_USE_INCREMENTAL_PIPELINE` | `true` |
| Lazy read of huge tokens (rua, travessa…) | `OPTIM_DEFER_READ_TOKEN_ATOMS_LIMIT` | `0` (off) |
| Mask-class cost-based join planner | `DEV_USE_MASK_CLASS_PIPELINE` | `false` |

**Problem:** multi-token address queries spend ~2 s in the match phase decoding and collator-matching every atom of common words (`rua` ≈ 134k in Portugal).

**Approach:**

1. **Incremental join** — join tokens rare→common instead of one all×all self-join; semantics via shared `acceptIntersectionImpl` with legacy search.
2. **Deferred read** — skip collator work for tokens above atom-count threshold in `readAtoms()`; parse them mid-chain only for atoms whose bbox intersects surviving partial results.

Correctness note: multi-word names (`Rua Joaquim Ribeiro de Carvalho`) already cross-add the `rua` atom via `otherTokens` when rare words are read, so the final intersection does not require reading every standalone `rua` in the country.

## Prerequisites

- JDK 17, `-Xmx6g` (Gradle task sets this)
- **`Portugal*.obf`** in a local folder (not in repo): [download.osmand.net](https://download.osmand.net) → put under `maps/`

## How to test

### 1. Unit tests (from mask PR — run first)

```bash
./gradlew :OsmAnd-java:test --tests net.osmand.search.core.spatial.SpatialTokenMaskTest
```

### 2. Portugal integration benchmark

From repo root:

```bash
./gradlew :OsmAnd-java:runSpatialSearchTest \
  -PmapsDir=/path/to/maps \
  -PusePipeline=true \
  -PuseIncrementalPipeline=true \
  -PdeferReadLimit=15000 \
  -PrepeatSearch=3
```

**Expected first result:** `39.7412, -8.8013`  
Query (hardcoded in `SpatialSearchTestAndDocs`): `Travessa Santo António Rua Joaquim Ribeiro Carvalho Portugal`

**Warm timings (approx., JIT warmed):**

| Mode | total | match | compute |
|------|-------|-------|---------|
| legacy (`-PuseIncrementalPipeline=false`) | ~4–6 s | ~2 s | ~1.4 s |
| incremental, no defer (`-PdeferReadLimit=0`) | ~4 s | ~2 s | ~0.3 s |
| incremental + defer 15k | **~1.2 s** | ~0.8 s | ~0.35 s |

Look for log lines:

```
PIPELINE DEFERRED READ 'rua' (... ms): 10,509/133,974 atoms in 10 bboxes
WARM RUN 3: total ... ms | Search Stats ...
```

### 3. Compare modes

```bash
# baseline: legacy intersections inside pipeline off
-PuseIncrementalPipeline=false -PdeferReadLimit=0

# incremental only
-PuseIncrementalPipeline=true -PdeferReadLimit=0

# full optimization (suggested production threshold ~15_000)
-PuseIncrementalPipeline=true -PdeferReadLimit=15000
```

### 4. Other regression queries

See `SPATIAL_PIPELINE_MASK.md` — `4 8 ave paterson`, Philadelphia duplicate words, Dickinson TX.
Any query can be passed via `-Pquery="..."` (overrides the hardcoded one).

### 5. Mask-class join planner (`SpatialMaskClassExperiment`)

Alternative compute path answering "what is the theoretical minimum of the intersection
phase". Objects are grouped into mask classes (equal token masks are combinatorially
interchangeable); a cost-based DP over mask states picks (state × class) spatial joins
from a priority queue (goal first: tokens still missing, cost second), re-running
downstream joins as deltas when a state gains new partials. Join semantics mirror
`join()` exactly (variants, `expandContestedTokens`, `acceptPairSemantic`).

```bash
./gradlew :OsmAnd-java:runSpatialSearchTest -PmapsDir=... -PusePipeline=true \
  -PmaskClassPipeline=true -PrepeatSearch=3
```

Measured (Portugal map, warm):

| Query | joins | Z crossings | join phase |
|-------|-------|-------------|------------|
| Travessa Santo António Rua Joaquim Ribeiro Carvalho Portugal | 2 | 3 | ~11 ms |
| rua santo antonio rua joaquim ribeiro portugal (dup words) | 2 | 5 | ~9 ms |
| rua joaquim ribeiro carvalho porto | 6 | 33 | ~43 ms |

Same top result as the incremental chain on the main query (`39.7412, -8.8013`).
Stats-only mode (prints classes/joins without replacing the pipeline):
`-PmaskClassExperiment=true`.

## Gradle properties

| Property | Maps to |
|----------|---------|
| `-PmapsDir=` | `maps.dir` system property |
| `-PusePipeline=` | `DEV_USE_PIPELINE` |
| `-PuseIncrementalPipeline=` | `DEV_USE_INCREMENTAL_PIPELINE` |
| `-PdeferReadLimit=` | `OPTIM_DEFER_READ_TOKEN_ATOMS_LIMIT` |
| `-PmaskClassPipeline=` | `DEV_USE_MASK_CLASS_PIPELINE` |
| `-PmaskClassExperiment=` | `DEV_MASK_CLASS_EXPERIMENT` (stats only) |
| `-Pquery=` | query override |
| `-PrepeatSearch=` | warm JVM re-runs after first search |

## Files touched (perf commits only)

| File | Role |
|------|------|
| `SpatialStagePipeline.java` | incremental chain, deferred ingest, flush/accept fixes |
| `SpatialSearchContext.java` | defer parse, bbox filter, `readDeferredTokenAtoms` |
| `SpatialSearchResultsList.java` | shared `acceptIntersectionImpl` |
| `SpatialSearchToken.java` | `deferredRead` flag |
| `SpatialTextSearch.java` | `OPTIM_DEFER_READ_TOKEN_ATOMS_LIMIT` |
| `HashSkipTileQuadTree.java` | skip rebuild when unchanged |
| `build.gradle` | `runSpatialSearchTest` task flags |

## Merge order

1. Merge **#25535** (mask algebra + unit tests)
2. Rebase this branch if needed, then merge **#25536**

Author: dmvkmusic@osmand.net
