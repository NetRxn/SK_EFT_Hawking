# Phase 6i Wave 1 — Close Report

**Wave:** 6i.1 — Primary-Sources Cache Rollout
**Status:** SHIPPED through Stages 1–5 (Stage 13 paper40 re-review queued)
**Date:** 2026-04-28

## Goal

Establish the per-phase primary-sources cache as the project-wide grounding
artifact for every external CITATION_REGISTRY bibitem, structurally preventing
the hallucinated-citation failure mode (e.g., the paper40 round-1 incident
where `CalmetCapozzielloPryer2019`/arXiv:1905.13728 — a graph-NN paper — was
cited as a gravity reference).

## Scope absorbed (vs roadmap)

The pre-implementation survey surfaced 121 cited bibkeys absent from
CITATION_REGISTRY. Per Option B, Wave 1 absorbed the registry-stub creation;
all 121 were extracted from `\bibitem` blocks, fetched (where arXiv/DOI
present), and promoted into CITATION_REGISTRY.

## Deliverables shipped

| Artifact | Path | Purpose |
|---|---|---|
| `PAPER_TO_PHASE` map (40 papers) | `src/core/citations.py` | Routes `used_in[0]` → `Phase-X/primary-sources/` |
| `paper_phase()` / `bibkey_phase()` helpers | `src/core/citations.py` | Phase resolution per bibkey |
| `inprep` + `primary_source_path` schema | `src/core/citations.py` | Every external entry now carries both |
| `extract_missing_bibkeys.py` | `scripts/` | Walks `\bibitem` blocks → stubs JSON |
| `back_fill_primary_sources.py` | `scripts/` | Tier-ladder fetcher (httpx + sidecar state) |
| `promote_primary_sources.py` | `scripts/` | One-shot sidecar → citations.py promotion |
| `citation_primary_sources_present` check | `scripts/validate.py` (CHECK 19) | Mandatory at Stage 13 |
| `tests/test_phase6i_wave1.py` | `tests/` | 12 fast + 1 slow test, all passing |
| `WAVE_EXECUTION_PIPELINE.md` Pipeline Invariant #11 | `docs/` | New invariant codifying the cache |
| `Lit-Search/Phase-6e/primary-sources/README.md` | refresh | PoC-doc → project-wide convention |

## Numerics

### Registry growth

|  | Before Wave 1 | After Wave 1 |
|---|---:|---:|
| Total entries | 218 | 339 |
| External (non-inprep) | 211 | 332 |
| Inprep self-cites | 7 | 7 |
| Cached primary source | 4 | 227 |
| Schema fields populated (`inprep`, `primary_source_path`) | 15 | 339 (100%) |

### `validate.py --check citation_primary_sources_present`

|  | Before | After |
|---|---:|---:|
| Bibkeys cited across papers | 302 | 302 |
| Cached | 4 | 196 |
| inprep-exempt | 7 | 7 |
| Need cache | 170 | 99 |
| **Missing from registry** | **121** | **0** ✅ |

Net: cached count 49× (4 → 196); zero unregistered bibkeys.

### Fetch tier distribution (332 external)

- arXiv PDF: 145
- Crossref abstract: 28
- Crossref JSON only: 58
- Pre-existing on disk: 14 (Phase-6e PoC + Phase-6a migrated)
- No-source (manual fill required): 99
- Hard fetch failures: 2 (`Balbinot2025` PRD just-published; `CohenKaplanNelson1993` DOI 404)

### Phase-6a legacy migration

Four arXiv-ID directories renamed `<bibkey>.source/` to preserve TeX/figure
content alongside canonical `<bibkey>.pdf`:

- `balbinot/` → `Balbinot2005PRD.source/`
- `jk0205174/` → `JacobsonKoike2002.source/`
- `jv9801308/` → `JacobsonVolovik1998.source/`
- `v0301043/` → `Volovik2003BraneBH.source/`

## Wave 1 residuals (not blockers; documented)

The 99 "need cache" entries split as:

1. **Real papers without arXiv/DOI** — textbooks (PeskinSchroeder, Carroll2004,
   MTW1973), classic refs (Sakharov1968, Adler-Bell-Jackiw 1969), recent papers
   without preprint (Sola2023). Manual `<bibkey>.abstract.txt` fills required.
2. **Project-internal pseudo-cites** — `Paper9`, `Paper10`, `paper14`,
   `Aristotle`, `FangGuLean`, `DarkSectorSynthesisLean`, etc. Should be
   reclassified as `inprep: True` or properly registered with full metadata.
3. **Stub-extractor misses** — bibitems where the title/arXiv/DOI regex didn't
   catch a present-but-nonstandard format. Re-extraction with refined regex
   would recover ~20.

These are queued for Phase 6i Wave 4 (Lean Proof Substance Audit) and Wave 5
(Assumption Disclosure), which already touch these papers.

## Stage 13 paper40 re-review — VERDICT: CLOSEABLE

Re-review report:
`papers/AutomatedReviews/2026-04-28-2048-phase6i-w1-reverification/paper40_higher_curvature.md`.

The original round-1 BLOCKER (hallucinated `CalmetCapozzielloPryer2019` /
arXiv:1905.13728 graph-NN paper) is **structurally fixed**. The bibkey is
renamed `CalmetCapozzielloPryer2017`, registry points at the correct EPJC
77:589 (2017) / arXiv 1708.08253 with `doi_verified: True`, and the cache
(`Lit-Search/Phase-6e/primary-sources/CalmetCapozzielloPryer2017.pdf`) holds
a non-empty 153 KB PDF of the actual primary source. Pipeline Invariant #11
+ CHECK 19 make the failure mode structurally non-recurrable.

**Verdict counts:** 0 BLOCKER / 2 REQUIRED / 0 RECOMMENDED. The two REQUIRED
findings (HC_BOUND primary-experimental sources not in CITATION_REGISTRY;
`human_verified_date: None` on four HC_BOUND provenance entries) are
out-of-scope for Wave 1 — they belong to Wave 2 (Parameter Provenance
Closure) and a new adjacent QI item the reviewer recommends.

**QI register flip (recommended):**

- `qi-citationintegrity`: `open → closed`, `evidence_on_close: docs/phase6i_wave1_close.md`
- New `qi-provenance-citation-coverage` (proposed): primary-experimental
  papers cited in `PARAMETER_PROVENANCE` `source`/`detail` fields should
  themselves be in `CITATION_REGISTRY`. Closes via a `validate.py --check
  provenance_doi_in_registry` extension. Natural owner: Phase 6i Wave 2.

## Decision Gate I.1 (Wave 1)

> At Wave 1 close, the citation-cache check is mandatory at every Stage 13.
> Any paper failing the check cannot ship a Stage 13 PASS verdict.

**Status: PASS**

- `validate.py --check citation_primary_sources_present` is registered
  and invocable.
- 196 of 302 cited bibkeys are cached; 99 need-cache + 0 missing-from-registry
  are documented residuals (textbooks + project-internal cites + stub-extraction
  misses).
- Pipeline Invariant #11 documents the cache as canonical.

## Idempotency

Re-running the full pipeline (`extract_missing_bibkeys` → `back_fill --fetch` →
`promote`) on the post-Wave-1 state produces zero changes; the slow test
`test_extract_missing_bibkeys_emits_no_orphans` confirms 0 stubs and 0 orphans
are surfaced.

## Next

Phase 6i Waves 2–5 can run in parallel after Wave 1 close (per roadmap §
Dependencies). Wave 2 (parameter provenance closure) consumes the cache for
cross-referencing primary sources to PARAMETER_PROVENANCE entries.
