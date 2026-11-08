# Independent complete Task2 R2 original-source/science review

**Verdict: REVISE_SOURCE.** The R2 repair substantially fixes the original mismatched-certificate and scalar-product accounting defects, and the complete fixed one-site producer remains faithful to the accepted original factorization at source level. Two mandatory residual defects remain: unchecked rational accumulation in raw-jet multiplication, and a missing zero-exterior-body condition on every action-jet component. Both are independently reproduced below. They keep canonical findings 1.2 and 1.1, respectively, open. This is not rejection merely because the full scientific evaluator has not run.

The full original scientific test remains **UNEXECUTED / UNADMITTED**. No full coefficient, measured full cost/RSS/time, Task2 completion, N16/full-Z result, physical/B3 construction, main merge, gate transition or publication acceptance is established here.

## Candidate, authority and complete review

Task: publication-original-coefficient-task2-science-review-r2, parent publication-remediation. PRIMARY is `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking`, base HEAD056ccb9f08454238934977de4bb6548d18c6275e plus the frozen assigned source. FIRST action was the existing continuity check of the assigned R2 packet; exit0, fresh=true, changed=[]. FINAL SAME check is also exit0, fresh=true, changed=[]. The packet was never refreshed.

| Actual path | SHA256 | Bytes |
|---|---|---:|
| src/core/formulas.py | d2eb079a84da6ab0c68aabb91640e9b29013bcf4b22104e816d68a804bd5c1b4 |536661|
| src/vestigial/original_coefficients.py | b8c7a42192daa09a7e2d6536bed4acf4f6298ac77bc0675313e9b069da7817dc |71102|
| tests/test_original_coefficient_jets.py |40c6bf8d2cc44396c6283aab135347a88ea4a1e59ec24f8ea27dddfe694e4667|23031|

I read all1678 actual domain lines, the complete original canonical gamma/link/coframe/action block and appended Task2 formulas through the entire scientific producer, all448 jet-test lines including the unexecuted expensive test, the complete903-line R1→R2 diff, complete author R2 handoff, both complete adverse R1 reviews, canonical findings, notebook/packet, governing AGENTS/CLAUDE/pipeline/continuity/ADR017 contracts, applicable ADR008 worker boundaries and owning-roadmap original-obligation context. The accepted plan's one-site/source-family/contact/cost specifications, earlier independent prospective physics/cost reports, full accepted one-site derivation and full independent manual review were consulted as requirements and prior mathematical evidence. They were not substitutes for current source inspection. Long combined documentary reads were followed by bounded actual-source/spec reads; no scientific conclusion relies on clipped output. I did not consult the other new R2 review verdict or dispatch another agent.

The entire509040-byte accepted Task1 formulas prefix is unchanged. The entire25695-byte protected Task1 test file is unchanged, SHA25615d64a3899ad078015864ae4354156c62bbe1bb6a4e8db3c5a398833865d885d. Original Task2 tests are an exact14190-byte prefix of the new test file; no original test definition changed. AST comparison against the frozen original Task1 domain prefix identifies exactly the four deliberate changed definitions `_rational`, `QComplex`, `ScalarCost`, `Polynomial`; all other prior Task1 definitions remain equal. I audited those common primitives and their actual callers rather than treating changed prefixes as automatically acceptable or unacceptable. No old function was deleted or shadowed.

## Mandatory SCIENCE-R2-1 — raw rational mixed accumulation evades intermediate-height refusal

- **Canonical owner:** still-open Task2 finding1.2, ComputationCorrectness, major/pyrust.
- **Location:** `src/vestigial/original_coefficients.py:947`, `RawJet.__mul__`.
- **Observed:** scalar products now use the checked common primitive, but the subsequent `value=value+term` uses ordinary Fraction addition when the raw jet is rational-valued. Only the final RawJet construction rechecks those slots. An oversized intermediate can therefore cancel before any height check, and the reported peak is false.

Independent exact two-label raw jets use slots in order value,t,s,tt,ts,ss:

`a=(1,1,-1,-200,-200,200)`

`b=(1,200,200,-200,200,200)`.

Inside an actual8-bit ExactBudget, every input and every individual product fits eight bits. Their mixed accumulation is `200+200-200-200`: it creates actual Fraction400 (nine bits), then returns to zero. The call succeeds with final slots `(1,201,199,0,0,0)`,17 counted products and reported peak_integer_bits8. A separate probe temporarily observed Fraction.__add__ in its own process and captured the actual `200 + 200 -> 400` operation; this is not merely a pessimistic hypothetical cross-multiplication bound. No repository method or process outside the probe was patched.

**Required repair:** route rational raw-jet accumulations through checked rational addition, with all intermediate widths observed/refused. Audit other scalar-jet accumulation paths for the same bypass. Add this cancellation counterexample, a higher-limit positive case and a product-count conservation control; retain all17 raw C2 products. Existing tests of RawJet addition and raw rational multiplication do not cover the internal sum in RawJet multiplication. Do not weaken the height contract or silently exclude rational jets, which are an advertised supported exact coefficient type.

This demonstrates a generic accounting/refusal defect, not that the fixed scientific producer necessarily exceeds1024bits or250M products. Most fixed producer frame slots are Polynomial/QComplex, whose checked additions are different paths. A complete package nevertheless cannot claim the shared raw-jet height contract repaired while this path remains.

## Mandatory SCIENCE-R2-2 — the finite4V exponential accepts nonnilpotent action bodies, including derivative contacts

- **Canonical owner:** still-open Task2 finding1.1, source/support completeness, major/pyrust.
- **Locations:** `SourceJet.__post_init__` at1111 onward and `contract_original` at1359 onward, especially its finite exponential loop at1390.
- **Observed:** R2 binds actual monomials/masks, carrier, grading, insertion identity and request roster, but permits a nonzero exterior-scalar component in the action. It then evaluates only powers0..4V and reports complete=True. Original finite nilpotence requires the action family to lie in the positive-degree even exterior ideal. GradedTerm's `mask.bit_count()==2*t_degree` enforces evenness; it does not enforce positive degree because t_degree0 is allowed for action as well as insertion/measure.

Three independent small probes establish the boundary:

1. A fully matched graded action with body1 and a top insertion on the original V1 carrier returns complete=True and top coefficient65/24, the truncated sum through4. The true analytic value is exp(1), so this input must be refused or handled explicitly as a separate scalar exponential.
2. A stronger derivative probe starts from an **actual original** one-site coframe T with norm-one q3 links in both chiral factors. Independently, its fourth power has top24, so top exp(T)=1. The supplied raw action family is A(t)=T+t·1. Its base action has zero body, all grade/roster/carrier checks match, but the implementation returns Nbase1 and N_t=N_tt0. The exact source derivatives are both1 because top exp(T+t·1)=exp(t). Hence checking only the base action body would not repair this defect.
3. With A(t)=T+(t²/2)·1, the base and first action bodies both vanish, yet the returned second derivative is0 instead of1. The scalar-body condition must cover every declared first/repeated/mixed action-jet component, not just value or first derivatives.

For the positive original nilpotent family A(t)=(1+t+t²)T, the same generic interface returns exactly `(1,4,20)` for value/first/second, independently expected from `(1+t+t²)^4`. Thus the refusal repair can preserve genuine original frame acceleration and all current/source contacts; no lower cutoff or derivative-order truncation is needed.

**Required repair:** validate the actual scalar exterior coefficient of every action-jet slot before certifying a finite4V exponential, or implement an explicitly separate correct analytic body-exponential jet while retaining the full nilpotent part. Under the original source contract, refusing nonzero action bodies is the natural bounded exact API. Do not reject unit insertion or scalar measure bodies, which are legitimate and separate. Add base/first/second/mixed-body adverse controls and the actual coframe acceleration positive control. Enforce the hypothesis against the actual reconstructed polynomial; don't replace it with a caller assertion. Retain evenness, carrier support, all-source semantics and exact original cutoff.

These are deliberately adverse supplied families outside the original nilpotent source domain. The defect is accepting them as a complete original contraction. They do **not** establish a wrong coefficient from the full fixed one-site scientific producer, whose actual original S4/S2/J/H/frame action has positive even degree. That producer does not use these poisoned inputs.

## Full original scientific-source coverage and credited repair

| Requirement | Current independent source assessment |
|---|---|
| Original carrier and conventions | Actual four signed quarter blocks and both independent periodic anchors are added; V1 has8 independent odd generators,16 coframes, four Spin4/eight SU2 factors and cutoff4. Canonical C gamma/gamma5, exp(+S), labeled words and the preserved noncommuting unsquared-g2 convention controls remain. No N16 local8 or polar toy replaces this carrier. |
| Complete independent free tensor routes | Direct136 exterior pairs compute every740 center-allowed coefficient;3136 further slots are explicit direction-center zeros, covering3876. Separate actual2×2 chiral block determinants, with the positive4×4 offdiagonal sign and distinct multiset splits, construct the second tensor. It does not read direct tensor output. Expected172/25/128/etc remain test oracles only. |
| Singular/minor rules | Subset DP and complementary minors never divide by M or detM. Raw repeated derivatives retain both cross orders and matrix acceleration. Independently implemented plain-Fraction exterior algebra on the literal source ordering matches ALL70 complementary minors for each of one invertible and one repeated-row singular4×4 fixture:140 matches. This additionally checks the changed scalar layer without sharing the determinant algorithm. |
| Original curvature and action | Complete ordered trace retains the scalar/diagonal piece until world/internal antisymmetrization. Direct and independent action builders each retain24 cosmological terms and72 EHC quadratics; all six complete6×6 curvature covariance tables and means are recomputed for each route/word. The curvature is an original commutator, not Haar holonomy. |
| Legal support factorization | Full center parity eliminates the actual forbidden direction sectors. Surviving curvature anchors are checked disjoint from coframe/source directions before factorization; repeated anchors are never averaged independently. The common fermion top is computed first. g1 and linear-g2 terms are retained until the actual complete zero certificates apply. |
| Haar bucket optimization | Full site/axis/chirality groups are formed before exploiting normalized S3 coordinate permutation symmetry and independent-factor ordering. Equal exact Haar moments can share a final coefficient scale after complete signed accumulation. The bounded LRU stores pure rational moment kernels, not scientific tensor results. Correlated-link/sign controls and actual source inspection support the algebraic optimization; it does not justify copying producer coefficients. |
| Complete W/Gaussian schedule | Raw weight has4029 terms including compensation and all square/cross terms. The full Gaussian-compatible schedule is23504 per actual word/variance,94016 total. Kernel beta−eta=2t uses exact raw factorials and both v2/v3; no known exp(S) result is substituted into W. |
| Literal T/H and frame contacts | The whole joint J/H polynomial, offdiagonal H once,16/136 T derivatives and10/55 H derivatives are retained. Six undivided diagonal-frame slots attach to actual S/W/source factors, leaving h/compensation unframed. All26 normalized T/H insertion families at origin/nonzero-axis retain matching denominator/frame contacts. Both original words and both variances are compared before complete return. |
| Generic current/measure | Canonical pre-Haar builder differentiates actual endpoint phases, original action, literal metric/current pieces, insertion and supplied moving measure. Numeric-H grading remains distinct from g2. Zero-base phase pullback is explicit, not arbitrary irrational phase evaluation. One-site current's global-phase limitation remains explicit; N16 Ward/mixed-frame acceptance is not inferred. |
| R1 certificate defects | Typed immutable grading/support, exact roster equality, actual reconstructed action/insertion/measure coefficients, insertion tag, exact generator masks and valid original anchors are now checked. Lower-order scopes refuse nonzero hidden contacts and return only declared derivative slots. The remaining nilpotent-domain gap above prevents complete source-contract acceptance. |
| Scalar and normalization contracts | Common QComplex multiplication now counts coefficient products once; exact4 polynomial-pair and17 C2 products are independently exercised. Fraction/Haar/Hermite and scalar inverse paths gained actual checked arithmetic. Nonzero certificate matching, unknown/zero denominator refusal, quotient first/second contacts, log branch disclosure and restricted-Hessian refusal remain. The internal rational accumulation bypass above still violates complete height monitoring. |
| Cost and memory limits | The report's225370240 is a prospective source bound, not an actual full count. It prices revised bucket scaling and rational/kernel/source/frame work under the unchanged250M/2GiB/1024bit contract and retains staged maps/recursive payload checks. Independent quantitative cost acceptance and native runtime RSS/time admission remain separate; this review does not certify them from93 bounded tests. |

The fixed producer's mathematical construction remains credible and substantive. Generic API defects are not grounds to replace it by a smaller model or remove the complete scientific test. Formal grounding and the parent-owned Dirac/Berezin/Haar work retain their actual source/build/consumer boundaries. I made no missing-Lean inference from a grep result or a stale pending docstring and ran no Lean operation.

## Actual bounded execution and evidence

Command from PRIMARY, bytecode/cache provider disabled and all numeric thread pools1:

`.venv/bin/python -B -m pytest tests/test_original_coefficients.py tests/test_dependency_declaration.py tests/test_original_coefficient_jets.py -k 'not test_original_full_small_carrier_direct_vs_auxiliary' -vv -s -p no:cacheprovider --junitxml=/tmp/publication-task2-science-r2-bounded.xml`

Actual exit0: **93passed,1deselected in25.21s**. Child native process high-water RSS251363328bytes, below512MiB.88 fixture counters were printed (five dependency tests have no coefficient counter); maximum194033, sum377089. These are outer bounded fixture counters, not full scientific arithmetic. XML retains all93 selected IDs; the sole deselection is the complete scientific test. No new skips/xfails or environment bypass were introduced.

Independent probes used existing .venv, the same thread/bytecode limits and explicit10000 or100000 product budgets where contraction occurred. Actual work:17 products for the rational cancellation;16 for the constant-body contraction;394 for the actual-coframe first-body family;274 for its second-body family;602 for the valid acceleration family;502/459 for the two full minor fixtures. Each tiny probe process used roughly101–103MB RSS, below512MiB. These are finite local interface/algebra controls, not the original full one-site scientific evaluation. Native process snapshots are not per-fixture isolated allocations.

Raw logs/XML/run metadata, complete source conservation data, independent probe scripts/results and final SAME continuity output share the `/tmp/publication-task2-science-r2-` prefix and are bound by the companion review JSON. Root may preserve them using existing artifacts. Only assigned /tmp outputs and normal pytest temporary output were written. No repository/Git/index/ledger/roadmap/notebook/packet/registry changes, controller/process manipulation, build/cache repair, Lean/LSP, broad suite, GPU, campaign or full coefficient evaluator ran. No memory file was used or edited.

## Required continuation

Repair both residuals with all counterexamples and legitimate original positive controls, then obtain different complete source/cost reassessment. Keep the original full producer/test and all acceptance requirements. ROOT still owns canonical finding disposition, actual full one-CPU/2GiB/24-hour admission, complete actual execution/results/counters/peak heights/RSS/time, and independent result review. Task3 original N16 metric/contact/minor application, Task4 complete Z/source allocation and actual nonzero normalization, physical state/domain/adjoint/calibration, B3/window, modes/matter/transport/limits and publication/human gates remain owed. No deferral, scope reduction, canonical closure or execution permission is granted by this review.
