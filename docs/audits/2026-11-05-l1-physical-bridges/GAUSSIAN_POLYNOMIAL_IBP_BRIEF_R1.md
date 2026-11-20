# L1 accepted auxiliary identity: first Lean proof package

Parent: publication-remediation. Lead and acceptance reviewer: ROOT.
L1 remains the portfolio lead. This is one first proof increment of the already
accepted exact signed auxiliary/source construction, not its replacement target.

## Exact requirement

In new module `lean/SKEFTHawking/ADW/GaussianPolynomialIBP.lean`, prove for EVERY
real polynomial p, with actual standard Gaussian probability measure:

```lean
(p : Polynomial ℝ) :
  (∫ z : ℝ, z * p.eval z ∂ProbabilityTheory.gaussianReal 0 1) =
    ∫ z : ℝ, p.derivative.eval z ∂ProbabilityTheory.gaussianReal 0 1
```

Choose a descriptive theorem name in namespace SKEFTHawking.ADW. Do not assume
integrability, a Stein identity, the desired moment values or an abstract
averaging axiom: prove the necessary polynomial/Gaussian integrability and
apply the actual Mathlib integration-by-parts theorem. No bounded-degree
restriction, fitted Gaussian, mean shift, variance convention change or
redefinition of integral is permitted. Helpers must serve this actual theorem.

ROOT's statement check: no redundant conjuncts or hypotheses; p=X gives the
actual second moment1, and p=X^3 gives the fourth-moment relation3. These are
normalization controls, not substitutes for the all-polynomial theorem.
The equality follows from the true standard density derivative -z times the
density and actual integrability of every polynomial times that density.
This is the non-tautological undivided Gaussian IBP brick used coefficientwise
in accepted ADW auxiliary equation11. Finite nilpotent exponential coefficients
are polynomials, so its derivative-of-W term cannot be discarded. Do not divide
by W or add positivity of W.

## Existing assets and search evidence

Read `/tmp/l1-hermite-source-discovery-wt1-r1.md` and JSON. Actual wt1 LSP
outline/hover/search confirm generic whole-line
`MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`, Gaussian density
conversion, all-power integrability, all-degree half-line moments/recurrence
and arbitrary-coordinate `gaussInt_monomial`. Reuse these; do not rederive
GaussianSphere moments or factorization. The bounded discovery found no direct
target, and makes no global absence claim. Reconcile exact types/imports with
LSP before writing. Prefer minimal direct imports, not Mathlib through a
physical module. Toolchain and manifest stay pinned.

Accepted full construction: ADW_EXACT_AUXILIARY_IDENTITY.md, SHA256
e74fc4b792d59d19f88917f8f0365a2336583ca0abc5cac1403917b98ebd3cd8.
Read it directly. The full package STILL owes all-degree Hermite lowering and
factorial/parity identity, sigma scaling, actual constructed finite signed W,
original128-generator coframe grading/nilpotence, C2 source/test preservation
and the undivided observable correction. A first Stein theorem alone closes
none of those later obligations, physical B3, state/metric/dynamics or papers.

## Ownership and execution

Only the new module is worker-owned in prepared public wt1, base
4fca5970f4f4cb0b408ea33243076c72058f6e56, successful epoch
323eaae82597f49d8ab6fcec488d3dea03e0bab67cf57ec6a0c3a3fed81dbbb2.
ROOT owns heartbeat/controller/build/absorption, aggregate imports, shared
registries, primary notebook, roadmap and publication gates. Others work in
parallel: never revert their changes or touch wt2/wt3.

Use the Lean4 autonomous prove workflow and matching skeft_wt1 LSP only:
outline/search/type/goal/multi-attempt/diagnostics/lean_verify. Project rules
override generic skill: no lake build/clean/env lean/lean_build, cache repair,
new axiom/native_decide/maxHeartbeats, statement weakening or final sorry.
No scientific computation outside this proof, no controller/integration.
If a new import requires an olean, report it; ROOT handles the build.

Commit only a complete kernel-pure coherent module via ordinary Git, report
exact commit, statement, diagnostics, axiom evidence and all remaining work.
Do not certify project/full-wave/main/publication acceptance. ROOT arranges
fresh independent mathematical/source review and authoritative qualification
before integration. A source-consistent handoff packet is not a lease or proof.
