# ADR-018 — Source modification paths are relative to their source tree

Status: specification independently reviewed; implementation independently accepted for its bounded scope. Merged-wave acceptance pending.

## Context

At publication candidate `26ac99dc`, the declared reproduction for finding 2.1 in `papers/AutomatedReviews/2026-10-15-e1-roster-reconciliation/E1.md` fails: the manifest reader returns no timestamp for a real source below a hidden checkout ancestor. `_last_source_modification` in `scripts/bundle_source_manifest.py` filters absolute `p.parts`, so it treats checkout location as source content. A hidden directory inside the source must remain excluded; a hidden ancestor outside it must not suppress legitimate files.

The manifest writer already owns the artifact. No parallel writer, new validation check or routing ledger is needed. `scripts/check_bundle_source_freshness.py` has a separate reader with a similar predicate and extra bookkeeping exclusions; its exact reader is also transferred to this task. Neither reader establishes scientific freshness by itself. ADR-010's source-mtime limitations and ADR-012's closure requirements remain in force.

## Decisions

D1. Apply the existing hidden-component and `__pycache__` exclusions only to paths relative to `papers/<source>/`. Preserve recursive traversal, regular-file selection and the latest positive mtime with the existing UTC string (manifest, whole seconds) and timezone-aware datetime (freshness, including fractional seconds) interfaces. Missing/empty/fully excluded directories still return None.

D2. Exercise both actual production readers using controlled filesystem trees under visible and hidden checkout ancestors, with known mtimes. Include nested hidden/cache files newer than legitimate sources, nested ordinary files, empty and missing sources, and a writer integration test. A hidden ancestor must not affect the result; excluded descendants must not raise the result.

D3. Keep artifact and review authority unchanged. Do not regenerate tracked source manifests, change last_lift/freshness_stale/stage status, alter timestamp semantics, add a registry/check, or touch Lean/runner resources. Correct the owning architecture claim in the same implementation commit and close only the finding actually verified, through the existing closure writer after independent review.

## Plan and consequences

The design and task map are in `docs/superpowers/specs/2026-10-15-source-modification-boundary-design.md` and `docs/superpowers/plans/2026-10-15-source-modification-boundary.md`. This repairs false absence due to checkout naming; it does not cure the limitations of mtime as a content signal, infer source completeness or certify publication readiness.

Rejected alternatives: removing hidden/cache exclusions; special-casing a checkout folder name; refreshing freshness flags; adding another source walker beside the existing reader.
