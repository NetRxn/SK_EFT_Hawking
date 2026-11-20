# Independent L1 generated-artifact and affine-composition review R2

Reviewer: l1_integration_review_r2. Acceptance reviewer and notebook writer: ROOT.

## Separate verdicts

A: **ACCEPT_GENERATED_ARTIFACTS_ONLY** for the six actual canonical derivatives at main candidate `d4e4494b88e15892785adac7d687459c71eb04ae`. No artifact consistency defect found within the checked derivations.

B: **ACCEPT_SOURCE_COMPOSITION_ONLY** for the two UNAPPLIED proposals: main's new module plus one leading aggregate import, and primary/wt1's aggregate-only import. No new native build or extraction of the affine composition was run or accepted. ROOT must accept before committing derivatives or applying/absorbing the next proof.

The full main profile remains **FAILED: 7172 PASS / 28 FAIL / 14 SKIP**. Focused successful checks after regeneration are not a replacement full-profile pass. Full Eq6–11 auxiliary formalization, complex/Grassmann/link constructions, physical B3, protected-main/publication and final human acceptance remain OPEN.

## Contract and observations

Original packet: primary `.codex/continuity/publication-l1-generated-and-affine-composition-review-r2.json`. Initial and FINAL checks of that SAME packet both returned `fresh=true, changed=[]`, without refresh. Exact packet hash and final command/result are in the companion JSON. Live heads remained main d4e4494b88e15892785adac7d687459c71eb04ae, primary 2fbbfd95a396cadfd89961dea226d84c4f281675 and wt1 ae0076b43813cd4c486b51dee1d5dd2466adda2c.

Read current CLAUDE.md, WAVE_EXECUTION_PIPELINE (especially native/build/scientific and independent-review requirements), Codex continuity, ADR-008/017, owning roadmap L1 obligations and latest primary notebook continuation, actual lean-worker/adversarial-reviewer guidance, installed lean4 skill and its read-only review guidance. This is a specifically authorized integration/artifact review, not the Stage13 manuscript gate; no Stage13 corpus clearance is claimed. No notebook, controller, cache, source, registration, metadata, gate, Git index/ref or closure write occurred. Only the two assigned /tmp reports were written. No native requests were repeated: the prior independent source/kernel review's complete42 request/results were parsed and inspected.

## A. Complete raw-catalog conservation

Parsed the old catalog directly from `git show HEAD:lean/lean_deps.json` and the actual new file. Old41037/new41054, zero duplicate names in either, zero removed records, zero changed prior records, exactly17 additions. Every prior row is conserved as a complete parsed record, including type, dependencies, classification and axiom closure. All2048 prior origin modules have actual source files and `git diff HEAD --name-only -- '*.lean'` is empty: regeneration did not change prior source. The new module is the already committed complete135-line GaussianPolynomialHermite, not a reduced carrying statement.

The additions are15 authored theorems, one actual definition `realHermite`, and generated theorem `realHermite.eq_1`. All17 complete records are retained in the JSON for exhaustive review. Every record belongs to GaussianPolynomialHermite; each has standard3 core axioms, no project axioms, extracted name dependencies and no timeout. Actual `autogen_index` marks only `.eq_1` generated among these additions. The definition remains a definition despite source spelling `noncomputable abbrev`; it is not counted as an authored theorem.

I compared all17 raw types/dependency surfaces to the complete source: actual polynomial Gaussian integrability; real scalar extension of Mathlib probabilists' Hermite; evaluation bridge and recurrence; whole-insertion successor transfer; unrestricted all-order derivative identity; direct Hermite evaluation identity and integrability; arbitrary monomial descending-factorial reduction; lower-degree vanishing and bounded-degree factorial coefficient extraction; monomial diagonal normalization; exact Hermite degree; off-diagonal orthogonality and squared norm n!. Quantifiers, degree premises and factorial factors agree. Source uses genuine Gaussian integrability and IBP, not an assumed desired identity. `.eq_1` states the actual scalar-extension equation and is properly excluded from authored counts. Private generated proof-helper references in dependency lists follow extractor policy; their omission as public rows is not a missing public theorem or new axiom.

## A. Exact derived data

Recomputed `compute_lean_hash()` without extraction: actual stamp and computed value both `eb3e36883f353c92`, including aggregate source. Recomputed every returned `count_lean` field against the current parsed catalog: full dictionary equality with counts.json, including complete module/axiom name lists, all vacuity/debt categories, native-decide clusters, sorry/placeholder/structure/instance/inductive counts. Changes from prior counts are exactly:

| Field | Old | New |
|---|---:|---:|
| total declarations |41037|41054|
| authored theorems |22854|22869|
| substantive theorems |22828|22843|
| kernel substantive |22761|22776|
| modules |2048|2049|
| definitions |12900|12901|

All other Lean fields are unchanged, including placeholder26, tracked debt67 and sorry0. The only module-list addition is GaussianPolynomialHermite. Full prior/new dictionaries are in JSON. Independently recomputed all cheap Python fields and Aristotle fields: modules138, test files205, notebooks91, papers42, figures170, Aristotle313/run-set40. The actual count source path resolves to this candidate. `pytest_cases=7019` is conserved; its collection belongs to the inspected actual canonical producer receipt and was not rerun by this read-only reviewer.

Called the actual `generate_tex(counts, ..., deps=new)` formatter while intercepting its final Path writer in memory. Its entire result equals actual counts.tex bytes, thereby checking all107 macros, not a selected headline subset. No temporary formatter file was written.

Called actual pure `atlas_view.build_atlas(new)` with actual registries and compared complete canonical `json.dumps(..., indent=2)` bytes to atlas_view.json. Exact match. Called actual `atlas_heatmap.render` and compared every heatmap byte. Exact match. Old atlas theorem nodes22851/new22869; all prior nodes are identical, no removals; all72 edges and complete unknowns/frontier/obstructions/tracks are unchanged. The18 added TRUE/PROVED nodes consist of15 current authored Hermite results plus the THREE already catalogued IBP theorems `integrable_polynomial_mul_gaussian`, `integral_mul_polynomial_gaussian_weight`, `integral_mul_polynomial_gaussianReal`. The old atlas lagged those IBP results. It is incorrect to describe all18 as new Hermite novelty. `realHermite` and `.eq_1` produce no authored atlas result nodes.

Loaded every actual paper tables.py via the canonical spec discovery/loader. Rendered each table/scalar through actual render_table/_render_scalar in memory. All90 outputs across15 papers match actual disk bytes and committed HEAD bytes; JSON records every path/hash/result. No manual table or census correction is requested.

## A. Actual qualification retained

Inspected original full-profile result/stdout: terminal returncode1, native build `Build completed successfully (10836 jobs)`, pytest7172/28/14. Profile also reports failures in validation, the CI_SKIP checks and tree unchanged gate; native build passing is not full-profile success. Inspected exact cached-ID differential: prior/current failure totals both28, but L2 serializer terminal-LF failure resolved, live theorem census newly failed,27 IDs persisted. That differential explicitly is not an executed exact-main-base causal assessment.

Actual post-build extraction, counts and tables steps all returned0. Actual existing sync.py --fast returned0 and produced the six dirty derivatives. Actual focused census pytest returned1PASS; four canonical census/count/table/claim-cluster checks all passed after regeneration. These receipts qualify artifact freshness only. No new full-profile pass, changed threshold, waiver or gate state is inferred.

## B. Independent unapplied-patch reconstruction

Parsed both unified diffs and applied hunks to the respective actual preimage strings entirely in memory, checking every context/deletion line. Main postimages contain only `lean/SKEFTHawking/ADW/GaussianPolynomialAffine.lean` and `lean/SKEFTHawking.lean`; primary/wt1 only the latter. Full independently reconstructed postimages are in JSON, equal to supplied proposal postimages. This does not copy an aggregate from one history into the other: their preimages differ.

The new module is exactly218 lines,11293 bytes, SHA256 `3e6a5a5671a518595571395a2584f3d8794f157aadd3b0d552677dec69b47676`, byte-equal to author's committed source ae0076b. Each proposed aggregate is exactly one leading `import SKEFTHawking.ADW.GaussianPolynomialAffine` plus ALL its own old aggregate bytes. Primary and wt1 preimages match each other. All10 proposed public exports have no compiled-main catalog collision. A recursive actual project-import traversal from the proposed module reaches35 modules, with no missing module or cycle and no aggregate import.

Actual Detector/GaussianThreshold, full Hermite, full IBP, lean-toolchain and lake-manifest hashes match across main/primary/wt1. **Entire lakefile hashes do differ:** primary/wt1 have one existing unrelated `[[lean_lib]] name="NavierStokes", leanOptions={autoImplicit=true}` stanza absent on main. Parsed TOML becomes completely equal after removing only that stanza; all selected SKEFTHawking configuration and dependency requirements agree. This is not a reason to transplant the primary lakefile or any unrelated frontier/metadata history. The patch does neither.

Read the complete affine source including private helper and all examples, full Hermite/IBP sources, actual affine-map theorem and original98-line ADW_EXACT_AUXILIARY_IDENTITY acceptance boundary. The all-order chain rule has arbitrary real scale. Carrying integral identity requires positive sigma and actual variance v=sigma², yields sigma^n, and transfers to the complete polynomial. Private integral_affine_map is only change of measure; separate integrable-map proofs establish actual absolute polynomial/Hermite integrability. Products use actual independent Measure.pi and Integrable.fintype_prod; arbitrary Fintype includes empty dimension. Monomial alpha/beta remain unrestricted, with descFactorial zero above degree; finite support and signed real coefficients are preserved, with term integrability before integral_finsetSum. These are substantive mathematical bodies, with no assumed moment identity, supplied integrability or new project axiom.

Inspected the independent kernel review's complete42 actual requests:2 clean diagnostics,10 verifies (standard3/warnings[]),24 goals including separately queried closing endpoints and seven normalization examples,6 actual types. These are pre-existing independent native receipts at the exact author source, not new requests or a main native-build claim by this reviewer. Seven examples cover n0, n1=sigma, n2=2sigma², standard specialization, two-coordinate sigma², original sigma^-2 cancellation and empty product1.

## Remaining acceptance

After ROOT acceptance, ordinary source absorption/import/native main build/ExtractDeps and canonical derivative qualification are still required for affine. Do not reuse Hermite10836 as evidence that affine aggregate composition built.

Original Eq6–11 still require exponential/formal coefficient factorial normalization and Gaussian compensation; constructed complex link coefficients and genuine complex integrability; actual even Grassmann/coframe nilpotence and evaluation; complete four-block signed source matrix, Berezin orientation/determinant; compact-link coefficient bounds/exchanges; and whole W-times-exponential Eq11 with derivative-of-W term, without division at W zeros. Physical source/Legendre state/domain, actual ordered background and full modes/matter coupling, physical susceptibility normalization and derived [0.1,10] window, transport/frequency/units/error control, independent magnitude and continuum/Lorentzian/simulation duties remain OPEN BUILD. No registration, closure, human or publication acceptance follows from this report.
