# Independent L1 affine/product source and kernel review R1

Verdict: **ACCEPT_SOURCE_AND_KERNEL_COEFFICIENT_FOUNDATION**. No blocking correctness or scope defect found in the assigned module. This accepts the all-order affine Gaussian and finite-real-coefficient product foundation at exact wt1 commit ae0076b43813cd4c486b51dee1d5dd2466adda2c. ROOT still owns acceptance, authoritative builds, absorption, main qualification, and the complete original scientific objective.

## Assignment and exact custody

Task publication-l1-affine-product-kernel-review-r1; parent publication-remediation; reviewer /root/l1_affine_kernel_review. Only /tmp/publication-l1-affine-product-kernel-review-r1.md and .json are reviewer-owned outputs. The source path listed as owned_files in the packet is an input for this review, not an editing grant. I performed no repository edit, temporary source mutation, commit, build, raw Lean invocation, controller/process operation, dependency/cache repair, notebook write, or packet refresh.

Assigned checkout: /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/worktrees/wt1.
Primary notebook: /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/publication-remediation-notebook.md; designated writer ROOT.
Roadmap: primary docs/audits/2026-10-17-publication-substance-construction/REPAIR_DISPOSITION_MAP.md.
Acceptance reviewer ROOT; required artifacts are this Markdown and companion full-request/result JSON.

The SAME original packet .codex/continuity/publication-l1-affine-product-kernel-review-r1.json checked fresh=true, changed=[] initially and finally. Packet SHA256 d05d97ed7699826ea600e1d1cf9922aa154c431f749e090f1396861c7e398689. No stale context was refreshed away. Ordinary read-only Git log/diff/status independently confirms HEAD ae0076b43813cd4c486b51dee1d5dd2466adda2c, parent 2fbbfd95a396cadfd89961dea226d84c4f281675, exactly one new 218-line module, clean worktree. Source SHA256 3e6a5a5671a518595571395a2584f3d8794f157aadd3b0d552677dec69b47676; 11293 bytes.

Mandatory primary slotctl status --json records wt1 ACTIVE, repo_role public, client codex, matching absolute checkout, endpoint skeft_wt1, prepared epoch21fbc864b245b181a22bd14a95c78c8d41b6509e95aa3962957e59c1e6396e9e; latest observed heartbeat16:38:23UTC. Sandbox observer errors are preserved as limitations: "[Errno 1] Operation not permitted: 'ps'", endpoint observations unavailable, capacity_complete=false. ROOT had already explicitly reconciled these observer limits with escalated ACTIVE/running/complete/noerrors evidence in the assignment and notebook, and was informed of my reproduction. The matching endpoint actually worked for every independent call below. The stale deferred noactivelease descriptor is not used as current lease evidence. No endpoint or controller workaround was used.

## Scope read and proof assessment

I read the entire new 218-line source including its private helper, entire GaussianPolynomialHermite and GaussianPolynomialIBP dependencies, complete original 98-line ADW_EXACT_AUXILIARY_IDENTITY, complete variance-design and independent-design-review Markdown, and both author R1/R2 reports. I read the continuity contract, actual primary notebook's relevant current L1/variance/product continuations, governing project guidance, roadmap L1 priority/ownership/auxiliary boundaries, actual lean-worker and adversarial-reviewer contracts, and installed Lean4 skill/review guidance. This is a scoped proof review, not a Stage13 manuscript/whole-corpus audit. A broad initial notebook print was truncated; I subsequently read the relevant current primary notebook continuation directly. One attempted notebook read from wt1 reported No such file or directory; the primary notebook was already located, hash-matched and read, and no authority was inferred from that absent worktree-local path.

Actual direct source checks included Detection/GaussianThreshold.lean:237-244, Mathlib Integral/Pi.lean:1-122 including empty-dimensional proofs, and Hermite/Basic.lean:1-75. Exact input hashes are in the JSON. Author evidence is corroboration; the acceptance below rests on my own source analysis and 42 matching native requests.

The formal affine chain helper retains arbitrary real scale and mean and arbitrary natural order. Its induction correctly differentiates p.comp(C sigma*X+C mu), multiplies by C(sigma^n), applies the polynomial chain rule and joins sigma^n*sigma. No analytic differentiation under an integral or degree ceiling is inserted.

The carrying theorem at lines64-88 quantifies every n and every real polynomial p; only sigma>0 and v=sigma² relate the actual Gaussian law and standardization. Gaussian v is variance, not standard deviation. Mathlib's hermite is explicitly the probabilists' polynomial over integers, recursively He0=1 and He(n+1)=X*Hen-D Hen. Its real evaluation is the accepted aeval bridge, not a newly defined or physicists' Hermite.

For Z standard normal and Y=sigma Z+mu, q=p.comp(C sigma*X+C mu). The proof uses existing Detection.gaussianReal_map_affine, cancellation ((sigma Z+mu)-mu)/sigma=Z, existing arbitrary-order standard integral_hermite_mul, and D^n q=sigma^n (D^n p).comp affine. It obtains E[He_n((Y-mu)/sigma)p(Y)]=sigma^n E[D^n p(Y)] with correct scale and complete polynomial insertion.

Private integral_affine_map lines55-61 calls actual integral_map with continuous integrand and measurable affine map. Its totalized identity alone would not prove absolute integrability. The module separately proves polynomial integrability (lines31-39) and whole Hermite insertion integrability (42-53) by integrable_map_measure .2, using continuity for strong measurability and standard polynomial/Hermite integrability. Instantiate polynomial integrability with D^n p for the right side. No assumed moment/Stein identity, desired conclusion as a premise, True placeholder, custom expectation/measure, supplied integrability assumption, or project axiom appears.

Product theorems at91-113 quantify arbitrary Fintype, coordinate means/scales/variances, alpha and polynomial family. Independence is the explicit actual Measure.pi of Gaussian laws. Integrable.fintype_prod proves genuine absolute integrability, separately from integral_fintype_prod_eq_prod. There is no Nonempty or positive-cardinality requirement; Mathlib's finite product proofs explicitly include dimension zero.

The centered monomial formula116-126 retains every alpha,beta. Its descending factorial and natural subtraction are correct: beta<alpha makes descFactorial zero rather than a negative-exponent problem. No cap of16 coordinates, four degrees, or alpha<=beta is assumed. Specialization to X^beta and exact iterated-derivative API produces product_i [sigma^(alpha_i)*descFactorial(beta_i,alpha_i)*E[Y^(beta_i-alpha_i)]].

The finite-sum integrability139-148 and integral identity151-165 allow arbitrary Finset support and arbitrary signed real coefficients. They prove term integrability before invoking actual integral_finsetSum and constant linearity. This is a genuine arbitrary finite real monomial-combination foundation, beyond a lone separable polynomial. It does not instantiate an MvPolynomial API or prove complex-coefficient casting/integrability, and no such claim is made.

## Independent native evidence

All calls used only mcp__skeft_wt1__*, SEQUENTIALLY, with actual full requests and responses preserved in JSON. No call returned isError=true.

- 2 full-file diagnostic requests: success=true, timed_out=false, items=[], failed_dependencies=[].
- 10 lean_verify calls, one for each public export: each returns exactly propext, Classical.choice, Quot.sound; warnings=[].
- 24 lean_goal calls inspect proof states and normalization examples. Successful intermediate-state observations at85,112,125,147 were not falsely recorded as closure: the actual closing endpoints88,113,126,148 were then queried separately and returned goals_after=[].
- 6 actual hover requests confirm carrying theorem/product/monomial/finite-sum and product/sum integrability types. Each actual type retains the claimed unrestricted quantifiers and hypotheses, diagnostics=[].

All ten verified public exports are:
iterate_derivative_comp_affine;
integrable_polynomial_gaussianReal_affine;
integrable_hermite_mul_affine;
integral_hermite_mul_affine;
integrable_prod_hermite_mul_affine;
integral_prod_hermite_mul_affine;
integral_prod_hermite_mul_pow_affine;
integrable_prod_hermite_mul_pow_affine;
integrable_sum_prod_hermite_mul_pow_affine;
integral_sum_prod_hermite_mul_pow_affine.
The private map helper's proof was inspected and its transitive axioms are covered by the carrying exports.

Direct closing-state observations include chain28, polynomial integrability39, insertion integrability53, private helper61, carrying identity88, product integrability98, product identity113, all-index monomial126, monomial integrability135, finite-sum integrability148, and finite-sum identity165. A term-style declaration has no tactic goals; clean diagnostics and its kernel axiom check complement that observation.

## Required normalization checks

All seven are actual examples in the unchanged source, with independent closing-goal receipts. They are consequences of the unrestricted theorem, not substitutes for it.

| Check | Actual result | Closing line |
|---|---|---|
| n=0, arbitrary p | E[p] |173|
| n=1, p=X-mu | sigma |179|
| n=2, p=(X-mu)^2 | 2sigma² |186|
| sigma=1, mu=0 | original arbitrary-n standard identity |191|
| two coordinates, alpha=beta=(1,1) | sigma² |197|
| original W multiplier sigma^(-2) | 1 |210|
| arbitrary empty finite coordinate type | 1 |217|

Every listed line returns goals_after=[]. The two-coordinate factor is sigma*sigma, so original W's sigma^(-2) cancels exactly; no extra Hermite factorial is inserted. For the n2 check the actual native state explicitly expands He2(u)=u²-1 and yields sigma²*2.

## Original full acceptance retained

This verdict accepts supporting coefficient foundation only. Original Eq6-11 is still owed in full:

1. Actual all-order Gaussian/exponential coefficients, beta! normalization, sigma^(-|alpha|) cancellation and formal Gaussian compensation/convolution.
2. Constructed complex link-dependent Eq4 coefficients for arbitrary finite couplings; genuine complex integrability and finite linearity.
3. Actual commuting even Grassmann coframes, finite nilpotence/truncation and evaluation/cancellation yielding Eq7, including extra relations.
4. Actual source-oriented Eq9 matrix with all four signed h/4 blocks and correct Dirac/barred/Spin(4) data; Berezin orientation/determinant.
5. Actual constructed compact-link coefficient continuity/boundedness, Gaussian integrability and all coefficientwise exchanges yielding Eq10, retaining W and detM; normalized correlators require Z nonzero.
6. Eq11 for the entire insertion W times exponential coefficients, including both derivative-of-W and W*T terms. The source is centered; noncentered Stein has the extra mu E[F] term. No division by W at zeros or identification h/sigma² with a physical tetrad is justified.
7. Physical source/response/Legendre state/domain, order/background, stationarity/constraints/full tensor modes/positive norm/matter and EM coupling, calibrated susceptibility normalization and derived [0.1,10] window, transport/frequency/units/errors, independent vacuum magnitude, thermodynamic/continuum/Lorentzian control and actual simulation remain OPEN BUILD.

ROOT authoritative build/ExtractDeps, aggregate import, canonical index/count/table producers, actual main qualification, independent artifact acceptance and publication/physical closure remain separate. No main/full-tree/physical-B3 acceptance is inferred from these scoped native checks.

## Disposition

No source revision required before ROOT considers absorption and authoritative qualification. No independent lifecycle or capacity-completeness claim is made from sandbox observations. Author R1 transport failures remain historical immutable evidence; all my own42calls worked, and I did not reuse the author's retry receipts as my independent gate.
