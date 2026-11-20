# L1 protected integration prerequisites — read-only R2

**Finding:** no minimal already-accepted dependency integration set is established by the inspected artifacts. This is a missing current owned integration/acceptance artifact, not a claim that integration is impossible. The source histories and existing process provide a concrete bounded next step; they do not authorize transporting the entire custody/frontier history.

## Exact source and continuity

Initial continuity check was fresh. Read initial publication HEAD `ddc3a0d1932e4a24f2b0305f08679547348b68b3`; canonical primary/custody `4fca5970f4f4cb0b408ea33243076c72058f6e56`; local cached `origin/main` `ce194cdc4bf939b108c17edc9530a7f0a14565f9`; cumulative publication checkpoint `14d4e3ccb56aaf7e5c02bc1ca5626b45cf259c6b`; frontier `55ec38977c378e15545156e1eda16c78fb91606b`.

During the review ROOT deliberately checkpointed the expected GW/F/catalog/SCOPE changes as `9505b60afd8c63a4b2161ddded516bf461740e70`, a direct child of ddc3. Its exact 22-path delta is recorded in the JSON. This review inspects that commit only for ancestry and changed-path population, and does not transfer source acceptance to it. Canonical primary remains 4fca. The final continuity result is **fresh=false, changed=[owned-files, source]**; referenced roadmap/notebook/authorities remained unchanged at that check. ROOT must deliberately reconcile/reissue the packet for any subsequent current composition/integration acceptance. An intermediate status read showed untracked `papers/L1/prose_state.json.lock`; the final Git status is clean. This reviewer performed no cleanup.

The JSON binds full SHAs, reference SHA256s, complete changed-path lists and grouped populations. No fetch/network occurred; origin/main and remote-tracking branches are local observations, not a fresh GitHub claim.

## Measured ancestry

| Comparison | Merge base | Unique commits left/right | Different paths |
|---|---|---:|---:|
| origin/main → initial ddc3 | ce194cdc | 0 / 19 | 115 |
| origin/main → current 9505 | ce194cdc | 0 / 20 | 129 |
| origin/main → canonical primary | ce194cdc | 0 / 399 | 485 |
| initial ddc3 ↔ primary | ce194cdc | 19 / 399 | 557 |
| current 9505 ↔ primary | ce194cdc | 20 / 399 | 571 |
| cumulative 14d4 ↔ primary | ce194cdc | 667 / 399 | 1750 |
| cumulative 14d4 ↔ initial ddc3 | ce194cdc | 667 / 19 | 1473 |
| frontier 55ec → primary | 55ec3897 | 0 / 142 | 241 |
| frontier 55ec ↔ cumulative 14d4 | ce194cdc | 257 / 667 | 1720 |

Thus origin/main is ancestor of both delivery lines, but neither publication delivery nor custody is ancestor of the other. Cumulative research acceptance is a separate lineage, not a missing publication parent one can merge implicitly. `996c84324` is a real earlier merge of publication corrections into frontier (parents 96602d704 and 0b984829c), but it precedes and does not contain the current ddc3/9505 publication branch. It supplies history, not current composed acceptance.

The initial publication difference from main consists of bounded manuscript/figure/claims/evidence, GW source, citation/provenance, G4/inventory and dependency-classification changes; it changes no `scripts/lean_slots/*` path. Primary's 485 main-relative paths include 67 NavierStokes module paths, 111 SKEFTHawking subtree paths, 27 roadmap paths, 56 audit paths and lifecycle/source readers. These are materially unrelated peer populations, not one transport prerequisite. Cumulative's much larger audit/manual scientific population must likewise retain its owner/acceptance boundary.

## Exact existing prerequisite/source packages

The primary lifecycle source/contract/test population absent from this publication branch is exactly:

- `docs/adrs/ADR-008-shared-lean-slot-control-plane.md`
- `docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md`
- `scripts/lean_slots/{cli,controller,proxy,state,supervisor}.py`
- `tests/test_lean_lifecycle_observation.py`
- `tests/test_lean_runtime_fingerprint.py`
- `tests/test_lean_slots.py`

Its existing history is:

| Commit | Existing owned package |
|---|---|
| 39f8e544b2b8f6eabe1ad488b4c152ddf7141a30 | lifecycle observations and native capacity |
| 33be8dbe04d3477788b2696633970c76fc72365f | imported-source/runtime fingerprint |
| 86af1cf6648b33c5d6366d288a45d676ed740dc1 | shutdown and authorized orphan recovery |
| 6db2cde4036587627f07077a67868809aa856f34 | bounded transient-exit shutdown completion |
| 63ae97a6f1f5c7b7084787c85345fc09b642f4e2 | reviewed recovery/native admission evidence |
| 0d5a99be1efda5f1edb537d20b56747940493b30 | selected-client session-value specification |
| 12c54e6ac2833905eca6ee6180ebd609dd0a8c3b | selected-client session validation source/tests |
| 38f5396223019b1e77de684551e8ef259c6dc521 | creation diagnostics and startup admission |

These are provenance/prerequisite package anchors, **not an accepted cherry-pick list or automatically minimal dependency closure**. Their parents interleave unrelated research. Existing native-startup branch at 38f539 has 394 main-exclusive commits; merging that branch to obtain seven source files would import much more than the lifecycle package. Current primary additionally contains five commits after that startup tip, including research preservation and GW/extraction updates.

The union of those eight commits touches 30 paths, including their existing five design/plan pairs, original findings, recovery re-review/native receipts, counts and append-only closure ledger. The JSON enumerates all 30. A source delivery must reconcile those actual source contracts and evidence, not copy only Python bodies and discard their declared acceptance conditions, or transplant old counts/closure state wholesale. The 10-path population is the current lifecycle comparison surface, not certification that its isolated transplantation would be dependency-complete.

Important **non-missing** prerequisite: `lean/SKEFTHawking/GravitationalWaves.lean` is already byte-identical between ddc3 and primary 4fca. Primary's two owning source-doc commits are 1028b0474 and bfeaadd2d; they do not need to be transported again. Primary's 4fca source-hash artifact belongs to its whole canonical extraction; it cannot certify a different commit. The later 9505 delta touches no Lean or lifecycle file.

## Why whole source postimages would be wrong

There are 38 paths changed independently from main by both initial publication and custody. Five are already identical: GravitationalWaves.lean, D8 bibliography, D9 manuscript, L1 prose_state and test_d5_citations.py. The remaining 33 divergent paths are explicitly listed in the JSON. They include `src/core/{constants,formulas,citations,provenance,visualizations}.py`, G4/readiness readers/tests, derived architecture inventory, append-only ledgers and manuscript/catalog state.

Selective actual content inspection demonstrates a real preservation requirement: primary constants retain newer peer registry additions (eventReadout_count, extendPull_identity, qutrit no-go registry), while the publication side has the accepted scalar-only H_VestigialModeIsGraviton disclosure and adopted GW range/frequency/placeholder qualifications. Primary still contains older stronger L1 interpretation and natural-range wording there. Replacing either full file would discard one accepted lineage's substance. `formulas.py` alone differs by 854 lines of diff population (+/- aggregate); no claim that every hunk is reviewed follows from reading its header/selected hunks. `scripts/build_graph.py` and `scripts/readiness_gates.py` also have substantial independent changes; current G4 acceptance cannot be silently undone by taking primary's full postimage.

Consequently the prerequisite is a fresh owned composition decision for these affected shared consumers and source records. It is not a requirement to merge every peer science commit or to redo already-identical GW Lean work.

## Accepted evidence and still-open acceptance

Primary operator guide at 4fca, “Guarded source delivery before shared native admission” lines 481–530, explicitly owns the ordered route: fresh independent whole source/doc/control review, configured broader fast and change-appropriate checks; normal protected exact checkpoint with complete ancestry/prerequisite/path audit and clean target; then distinct canonical-primary/native admission. It specifically forbids unrelated wholesale merge, cherry-pick, reset/hook bypass and primary movement for transport.

The same guide records bounded historical source acceptance for the runtime-fingerprint implementation while explicitly keeping current project gates/native admission pending. Recovery R4 at `papers/AutomatedReviews/2026-10-12-lean-runner-recovery/review-r4.md` accepts exact 6db recovery source and recorded PUBLIC normal-cycle evidence, while excluding full project, private, merged-wave and publication acceptance. Its 390 PASS/1 SKIP and mutation evidence are attributed historical results, not executions of this review. Startup and session-header packages retain their own source/control contracts; no current aggregate success is inferred.

Current publication SCOPE and immutable ddc3 history record independent bounded source/control acceptances and exact canonical D7 closure; they retain numerical literal debt, dependency/extraction freshness, full native graph, broader/main/publication/human and original physical BUILD gates. ROOT's new 9505 SCOPE describes SCALARS/catalog/F acceptance, but this lineage reviewer does not certify its complete source/evidence composition. Cumulative 14d4 independently accepted manual test-operator/duality work does not supply the physical state, metric/tensor/matter/transport BUILD or native/main acceptance.

## Concrete existing next step for ROOT

1. Reconcile expected 9505/22-path change and deliberately issue a current continuity packet. Preserve this R2's stale result and initial-bound conclusions.
2. Advance the **existing owned lifecycle/native-startup prerequisite package** through its already-documented guarded source-delivery review. Use the exact eight provenance anchors, 10 current source/contract/test paths and 30 support-path inventory as the prerequisite comparison, then require the owning reviewer to identify/accept the actual minimal integration composition and its dependency closure. ROOT owns canonical primary/native/protected Git and L1 integration; peer science owners retain their source. Existing source-reuse comparisons used for G4/citations/D7 supply the established bounded review process; this report does not design a new mechanism or authorize implementation.
3. Obtain fresh whole composition/prerequisite acceptance and required broader/change-appropriate verification before protected delivery. Preserve primary's entire materially newer lifecycle behavior and peer science; reconcile the 33 overlapping source/artifact paths without old whole-file or ledger replacement. Any deferred package needs its actual owner/acceptance disposition recorded in the existing SCOPE/notebook/planner, not a fictional completed prerequisite.

There is currently no inspected artifact that supplies step 2's minimal accepted current composition, and no current full native/project/main evidence that supplies step 3. That is the precise unresolved dependency. ROOT can make progress now by the existing owner/prerequisite review and source-reuse process; it need not invent a controller/workflow, move primary, waive gates or abandon L1 publication ownership. Native admission remains subsequent and separately governed, as already resolved in `/tmp/l1-native-validation-route-r1.md`.

Only `/tmp/l1-primary-integration-prerequisites-r2.md` and `.json` were written. Read-only Git, text/JSON/hash inspection and the existing continuity checker were used; no imports of native/project implementation, tests, builds, controller/slot/lifecycle operations, source/notebook/index/ref mutations or network calls occurred.
