# Existing acquisition producer — minimal design for independent review


Status: specification and intent independently accepted; implementation remains open. See `papers/AutomatedReviews/2026-11-05-source-register-fidelity/SOURCE_REGISTER_SPECIFICATION_REVIEW.md`. ROOT is the sole document/source writer and integrator. The existing finding is `review:2026-11-05-source-register-fidelity:source_register_fidelity:1.1` (major infra, open, indirect CitationIntegrity surface). This design follows the original objective: truthful held-fidelity and actual internal identity in the existing acquisition register. It does not acquire or certify source contents.

## Existing authority and actual residue

ADR014 D1 already owns content-based fidelity, D2 the sole derived acquisition writer, D3 curated bearing/route judgments, D4 advisory acquisition debt, D7 explicit absence exemptions. Pipeline Invariant11 and READINESS CitationIntegrity already own citation/cache correctness. No replacement architecture, classifier, resolver, check, gate, index, ledger or artifact is required.

`src/core/workspace.py::find_workspace` owns workspace discovery. `scripts/validation/checks/citations.py::_cache_fidelity` owns full/abstract/metadata classification. The existence half of `check_citation_primary_sources_present` already evaluates every accepted pdf/tex/abstract.txt/json candidate in the bibkey's canonical phase and keeps the strongest tier. `_discover_cache_for` is separately header-oriented: first-hit cross-phase/case fallback can deliberately return a parseable abstract even when a PDF exists. Its default behavior must remain unchanged or existing header comparisons could silently disappear.

The producer currently guesses the workspace as PROJECT_ROOT.parent, classifies an existing declared non-abstract filename as full, and assigns internal route by key prefix. The only needed hookup is this existing producer to those actual source properties.

At postfreeze candidate4a0d736866adb4cdc006d6835f2895254bc942cb on2026-11-05, the source-bound read-only remeasurement enumerated317 bundle-cited keys against677 registry identities. Current174 rows differ from the content/strongest-discovery projection:79 holding transitions, comprising22 full→metadata,22 none→full,23 none→metadata,10 abstract→full,2 none→abstract. The projected164 gap rows comprise45metadata,43abstract and76none, including23actual inprep companions; seven are currently misrouted. No declared-missing case and no false-internal-prefix external case currently occur in this bundle slice; those legs require explicit controlled tests rather than vacuous corpus claims. Exact every-row evidence is the postfreeze r3 population JSON. Projection is not an acquisition or regenerated production artifact.

## Stable decisions

D1. Reuse the canonical `_cache_fidelity` exactly; do not copy its body or infer JSON tiers from extension. The acquisition holding result remains full / abstract / metadata / none / missing. Only a nonempty regular cache file contributes a held tier. A declared nonexistent/zero-byte/non-file path with no usable discovery yields missing; no declaration and no discovered file yields none. Unknown-shape or unreadable JSON cannot become full. An unrecognized cache_kind with valid body evidence retains the canonical classifier result; this repair adds no stricter competing classifier.

D2. Use `find_workspace()` for shared cache paths. Keep the producer's PROJECT_ROOT, overlay and output anchored to its own script's active checkout. Ensure direct invocation by absolute script path from an unrelated cwd uses the active checkout and canonical workspace; never import editable-install primary modules in place of candidate modules. The producer's existing WORKSPACE name can remain, assigned from the canonical resolver, preserving the original finding Verify contract.

D3. Promote the existing strongest-tier enumeration in the canonical existence check into a small shared helper in the same existing citations module. The proposed name `_best_cache_for(bibkey, entry)` denotes that factoring, not a second discovery algorithm. It returns the selected path and canonical tier, or `(None, None)` when no accepted nonempty canonical candidate exists; keep stable existing extension order for equal-tier ties. Its canonical-phase lookup, accepted extension set, positive-size condition, ranking full>abstract>metadata and ties must remain behavior-identical. Have the existing check call it instead of retaining a second copy of its old loop. Keep `_discover_cache_for` and header-agreement behavior unchanged. This factoring is justified by measured first-header/strongest disagreements; merely calling the first-hit header helper is insufficient.

The producer evaluates both its declared existing artifact (to preserve real alias paths) and the canonical shared strongest-discovery result using the same classifier/ranking. It retains the strongest held tier; a null or stale declaration cannot hide a stronger canonical file. Declared-path aliases remain supported, while a stale declaration never upgrades nonexistent bytes. A declared file from a distinct edition remains only the held edition: this repair does not settle oldBarcelo filename fallback, header identity ambiguity or scientific applicability. No new cross-phase broadening of the existence check is implied. Preserve its complete before/after result details, not just pass status.

D4. Internal identity is `CITATION_REGISTRY[key].get('inprep') is True`, not spelling, absent identifiers, notes or lack of a cache. Actual inprep routes internal and priority emdash; an external key with Roehm2026 prefix receives no such identity. Keep all legitimate overlay bearing/reason/route_note/cost fields and external route decisions untouched. Inconsistent explicit overlay internal/external identity must raise a clear producer error rather than publish a silent false route; actual pilot found no such conflicts. No curated overlay edits are needed. Existing internal rows remain visible and nonpurchasable; source absence is not reclassified as a new external exemption.

D5. Keep the existing bundle usage surface, deterministic ordering, bearing-floor logic, sole writer, render/main CLI and --check content comparison. Reuse the actual registry flag within existing `_rows`; compute holding once per row if useful to avoid repeated disk reads, without an independent index or memo. Source/cache artifacts and state rows are read-only. No fetch, promotion, ledger write, source-content conclusion or assertion that a held body was read is part of this repair.

D6. Amendment of existing ADR014 D2 plus its existing QA writer-map surface is sufficient; do not allocate an ADR number. Proposed replacement wording is in the doc-amendments draft. No gate roster/topology change is warranted: this is an indirect acquisition consumer, and the canonical cache check's advisory/full-body semantics remain unchanged. Independent adversarial review must accept this specification and implementation plan before code.

## Input/behavior matrix

| Case | Required result | Actual or controlled evidence |
|---|---|---|
| Verlinde1988 Crossref record | metadata, external gap included | actual canonical metadata vs producer full, original Verify RED |
| ADW2019 declared JSON record | metadata gap, not full | actual; projection exposes previously omitted source |
| Barcelo2011 PDF | full, outside gap rows | actual known-present positive; held preprint edition remains qualified |
| IrwinHilton2005 abstract + PDF + JSON | strongest full; header checking remains independently active | actual old abstract vs strongest full; no claim this reviewer read body |
| Eddington1919 null declaration + actual abstract | abstract, gap remains | actual; discovery must not depend on declared path |
| ADM1962 null declaration + actual PDF | full, no acquisition gap | actual; acquisition-list removal is discovery correction, not download |
| ABP1967 no declaration and no cache | none, gap remains | actual known-absent external; no blanket exemption |
| All eight added actual companions | internal emdash, null external identities unchanged | actual; seven prefix-mismatches must move P2→internal |
| Declared absent/zero-byte/non-file + no alternative | missing | no actual bundle case; controlled temp-tree test required |
| Declared missing + actual stronger fallback | strongest held tier; retain separate canonical dangling-path diagnostics | controlled test; do not turn missing bytes into held |
| Metadata and full-body JSON with same extension | metadata vs full | reuse existing canonical opposite-direction cases through producer |
| Abstract cache beside full JSON and reverse extension order | strongest full | controlled tests; not first-match by spelling |
| InprepTrue with arbitrary nonprefix key | internal | controlled production-bound registry case |
| InprepFalse key named Roehm2026ExternalProbe | external; no internal route | no actual corpus case; controlled test mandatory |
| Consistent curated bearing/routes | exact overlay choices conserved | actual overlay read and controlled both-direction bearing overrides |
| Conflicting overlay identity | explicit producer refusal | controlled error test; no current conflict |
| Script invoked by absolute path from unrelated cwd | candidate registry/overlay/output; canonical workspace | separate subprocess test, no shell cwd assumptions |

## Review and completion boundaries

A real-input pilot, independent adversarial specification review, and intent review against ROOT's original objective are distinct instruments. This author supplies orientation/pilot/specification only; no independent acceptance is implied. The eventual repair must pass the original finding Verify unchanged, its meaningful producer/control suite, the existing writer followed by --check, canonical citation checks with exact population/flag conservation, post-seed residue/restoration, documentary freshness and required scope/full integration gates. Existing close_finding alone owns closure against an actual reviewed source commit. Main merge, native/security/full-tree qualification, scientific SOURCE137/B3, human review and publication remain separate.


## Independent intake clarifications

Preserve canonical full classification for an unrecognized cache_kind with a valid body. Controlled tests must separately pin wrong-phase-only discovery refusal and a valid declared alias path; the shared strongest helper does not inherit the header helper's broader search. The original r3 specification and complete pilot remain in the source-linked evidence archive.
