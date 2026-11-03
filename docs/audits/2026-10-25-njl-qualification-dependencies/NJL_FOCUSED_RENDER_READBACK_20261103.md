# Focused NJL render and regression readback

The focused line starts from main at ce194cdc. The reviewed solver, generated Lean artifacts, and finding record end at b92e8db5. Commit db471628 carries the regenerated Paper 5 PNGs, five-page PDF, and layout adjustment.

The configured Python environment ran the same three modules, tests/test_tetrad_gap.py, tests/test_tetrad_gap_solver.py, and tests/test_adw.py. The main baseline passed 121 tests. The focused solver candidate and the render commit each passed 200. Full fast-suite qualification remains pending.

Both figure producers executed. The gap curve reaches Δ/Λ = 1.1675353693282826 at G/Gc = 4. Independent visual review accepted the revised footer and marker placement and both captions on page 3. The reviewer extracted the PDF images and confirmed exact RGB and alpha agreement with the regenerated PNGs. The compile emitted a nonfatal float-placement warning. The adjacent figures were visible on the reviewed page. The affected notebook cells had empty saved outputs at b92e8db5. Whole-notebook execution and qualified integration into main remain open.

The two Phase 5d notebook sources were corrected and independently reviewed. They separate the scalar result from physical tetrad and phase claims, label the represented critical root and near-critical refusal correctly, and distinguish an uncomputed width from a width unresolved at working precision. Independent review confirmed schema validity and sequential execution of all 13 code cells. The positive sample residuals remained at or below 1.6e−13, and the gap curve reaches the above-cutoff value reported above. The review covers the source and direct cell execution. Saved notebook output, kernel execution and HTML review remain outside this receipt.

## Completed fast-suite differential

The configured `python -m pytest -q` suite ran in the same repository Python environment on isolated checkouts of ce194cdc and b92e8db5. The baseline finished with 6,940 passed, 45 failed, nine skipped and 92 deselected. The focused solver revision finished with 7,021 passed, 44 failed, eight skipped and 92 deselected. Exact terminal failed test IDs show 44 shared failures, one baseline-only external-cache path failure, and zero candidate-only failures. This comparison establishes no added failing test IDs on the measured solver revision. The baseline failures, canonical validator and exact render/notebook head qualification still require disposition.

The render-and-notebook revision fc9555ac finished with 7,020 passed, 45 failed, eight skipped and 92 deselected. The sole added failed ID relative to b92e8db5 was the module-census freshness test. Regenerating the census at 5f9dc015 changed only the Technical notebook summary row and the exact failed test then passed. Five shared slot tests also passed with scoped loopback/process access, and the shared Python census test passed with the existing environment and UV_NO_SYNC=1. Full qualification still requires disposition of the remaining inherited failures.

The focused citation composition adds 13 historically reviewed registry entries, five acquisition records and the corresponding active bibliography updates. Independent review matched the held artifact hashes and accepted active-corpus source fidelity. The canonical primary-source check passed with 516 cited keys, zero missing registry keys and zero required cache artifacts. The measured undeclared count and ceiling both equal 76. Citation and Wave 1 tests passed 78 with one deselected. D4 bundle files and the finding ledger are excluded from this composition. The unused historical 2005 Barceló key has no declared full-text path. Filename discovery can still find its held 2024 v4 artifact, so edition-aware discovery remains owed if that key returns to a manuscript.

## Exact focused head fast suite

The configured fast suite at `f28cc370` ran with the existing repository
Python environment and `UV_NO_SYNC=1`. It finished with 7,069 passed,
34 failed, eight skipped and 92 deselected. Comparing the two terminal summaries with
the recorded `ce194cdc` baseline gives 34 shared failing node IDs, 11
baseline-only IDs and zero candidate-only IDs. This comparison does
not establish equal failure magnitudes. The open unattributed blocker
count rose from 57 to 58 against a ceiling of 44. The numerical literal
population is 149 against 117 on both measured heads. Five shared
slot failures are sandbox-sensitive. Earlier scoped passes do not
establish the current exact-head slot result. The runs used different
checkout paths and report different skip counts. The focused candidate
remains unqualified for merge pending investigation of the attribution
increase and disposition of the remaining failures.

The exact finding-set comparison traced the increase to managed-worktree
findings 1.1 and 1.2 entering open while the NJL substrate finding
closed. Both path repairs were already independently reviewed. On
`cd018f44`, the combined declared suites passed 80 with one deselected,
and the canonical closure writer reran each declared verifier before
recording both closures. The unattributed test now measures 56 against
44. The remaining over-ceiling findings still require disposition.

The architecture inventory writer now asks Git for the active hook
directory. Before the repair the linked-worktree regression missed the
configured hook and the generated inventory could falsely pass with
six hooks. The repaired writer retains seven and records the citation
registry population of 677. Independent review checked default,
relative, and absolute hook path resolution, then passed all 26
architecture inventory tests. This qualifies the scoped inventory
repair. The full focused suite needs a new exact-head receipt.

At `e965a552`, the combined scoped inventory, workspace, citation, and
solver suites passed 306 with one deselected. Two independent corpus
measurements reproduced 91 hardcoded count literals and 67 spelled-out
census figures. Lowering their ceilings from 95 and 71 restores zero
headroom. Both exact failed node IDs and the related spelled-out census
controls now pass with the existing predicates. Other ratchets remain
open.

At `da343f91`, the five previously sandbox-sensitive Lean-slot fixture
tests passed with local loopback and process inspection available.
No production slot was used. A separate prose-reference diagnostic
compared the empty candidate dependency checkout against the exact
PhysLib revision from its Lake manifest,
`c48433678e8fb6306ebcd48453300c8e16058a62`. The existing resolver
classifies `MatrixMap.of_kraus_CP` as `PHYSLIB` when supplied that
source. It then reports zero unresolved active-bundle references and
90 legacy references against ceiling 90, compared with one and 94
without PhysLib. This was a diagnostic override of the dependency
path. Qualification still needs the canonical check with its pinned
dependency provisioned on the candidate.

The unmodified canonical `prose_theorem_reference_coverage` check
also passed on `da343f91` with the exact pinned PhysLib source
temporarily linked at its expected candidate-local Lake path. It
scanned all 21 bundles and reported zero unresolved failures, two
drift advisories, and one documented waiver. The legacy leg measured
90 against ceiling 90. The temporary link was removed. This run
establishes dependency-aware prose reference coverage on the measured
head. Full merge qualification remains open.

### Terminal fast-suite differential

Candidate `4f029ab8e2afd8a42ff8acebb68d6883c1331ae8` completed with
7,080 passed, 24 failed, 8 skipped and 92 deselected in 984.67 seconds.
The run used the exact pinned PhysLib source at the candidate-local
Lake path. Comparing sorted pytest failure node IDs shows zero
additions against both `f28cc370` (34 failures) and `ce194cdc`
(45 failures). The ten IDs removed relative to `f28cc370` cover the
architecture inventory, five slot fixtures, two prose-reference
checks and two count checks.

The 24 remaining failures are 16 bundle-readiness tests, four review
verification tests, two bundle-table checks and two numerical-literal
checks. The last four span the corresponding prose, ratchet and
public-surface test modules. The failure comparison measures node
identity. The required merge checks remain open.

The table and numerical-literal failures were traced beyond node IDs.
For all 21 bundles, the ordered comment-stripped tabular blocks are
identical to `ce194cdc`. The existing table check counts 15 across
D1 (2), D2 (2), D4 (1), D6 (2), D8 (4), D9 (3) and D10 (1)
against ceiling 1. The canonical numerical scanner also returns the
same per-draft multisets of matched strings across the full candidate
draft inventory as on the baseline, totaling 149 against ceiling 117.
Both checks remain red. These comparisons isolate inherited corpus
debt for the existing table generation and numerical provenance
workflows. The other readiness and review failure groups still
require their own source-level comparisons.

The review checks also reproduced the same failing details. The
candidate scanned 275 verification lines versus 272 on the baseline,
with the same 56 malformed lines reported. The severity and lane
failure details matched, and both scans reported zero unresolved
blocked-by links. To compare beyond the backing-link display limit,
the replay used the existing graph index, link iterator and resolver
and compared sorted unresolved tuples of paper, claim ID, link kind
and target. All 111 tuples matched the baseline with multiplicity.
This is inherited review-corpus debt. The gate remains red against
ceiling 109, and the bundle-readiness failure group remains open.

The readiness replay compared all emitted details from
`bundle_lean_module_coverage`, `bundle_stage13_claim_consistent`,
`bundle_sentence_length`, `apex_theorem_claims_grounded` and
`apex_claims_not_vacuous` on the candidate and `ce194cdc`.
The only emitted difference was the unattributed open required
population, which fell from 57 to 56 against ceiling 44. The
undeclared subset fell from 22 to 21. The declared but unmapped
subset stayed at 35 and 74 findings still reached bundle aggregation.
The differential measures emitted details. Three supersession
records were added across the candidate history, including the
critical NJL finding. This replay does not isolate their individual
contributions to the net population change. Merge qualification
and publication readiness remain open.
