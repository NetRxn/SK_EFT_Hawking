# Bounded source modification producer review

Base: `26ac99dc`. Scope: findings 2.1 and 2.2; ADR-018 design and plan. This is not a scientific-freshness or publication acceptance report.

## Specification review

Independent reviewer accepted the relative source-tree boundary and requested preserving fractional seconds in the freshness datetime, distinguishing it from the manifest's whole-second string. ADR/spec and deterministic tests were corrected before implementation. The two readers' distinct bookkeeping exclusions are pinned. No new gate, registry, writer or resource lifecycle was introduced.

## Implementation and measurements

Both existing predicates now inspect relative source paths. Nested hidden components and `__pycache__` remain excluded; visible and hidden checkout ancestors give equal controlled timestamps. The real existing E1 source was measured read-only: both readers return a timestamp where the base returned None. No tracked source manifest or metadata was regenerated.

The corrected pre-implementation matrix reported 12 failed/20 passed, including two expected failures for the not-yet-written architecture claim; visible reader controls passed and hidden reader/writer/verdict controls failed. Post-implementation all 32 dedicated cases passed. The fractional fixture pins the original precision of each interface and covers missing, empty, fully excluded and nonpositive timestamps.

The combined dedicated/serializer run reported 87 passed, 1 skipped, 3 failed. The failures are existing canonical-serialization defects in D3 and L2 metadata, both byte-identical to HEAD: escaped Unicode in D3 and missing terminal newline in L2. They are not waived. E1 metadata and source manifest also remain byte-identical to HEAD, including stale/pending stage states. All five existing source-staleness verdict tests also passed. Independent implementation review confirmed the core repair and precision preservation. The new pytest Verify requires the project virtual environment as `python3` on PATH; the default shell Python lacks pytest. Closure writer and independent reruns use that verified environment. The default-shell attempt is not a pass. Independent implementation acceptance: dedicated matrix plus existing Lean-freshness tests independently reported 82 passed; exact finding 2.1 and 2.2 Verifies passed in the stated environment. No implementation blocker remains. Independent final closure audit accepted: every prior ledger record is preserved and exactly findings 2.1/2.2 were appended by the writer; recorded commands match declarations and rerun successfully in the stated environment. Dates and review anchors resolve. Merged-wave acceptance and unrelated failures remain pending.
