# L1 Hermite source discovery wt1 r1

Task: `l1-hermite-source-discovery-wt1-r1`; parent: `publication-remediation`; owner: `l1-hermite-source-discovery-wt1`. Owned outputs ONLY: `/tmp/l1-hermite-source-discovery-wt1-r1.md` and `/tmp/l1-hermite-source-discovery-wt1-r1.json`. No source ownership exercised, implementation or commit.

Primary: `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking`. Assigned slot: `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/worktrees/wt1`, project `lean`. Notebook: `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/publication-remediation-notebook.md`, sole writer ROOT. Roadmap: `docs/roadmaps/Phase6a_Roadmap.md`. Candidate state: read-only discovery against base `4fca5970f4f4cb0b408ea33243076c72058f6e56`. ROOT is acceptance reviewer. This supports the accepted signed auxiliary source identity, not physical CAR/B3/state/dynamics, main, publication or human acceptance.

## Authority, chronology and source conservation

First action: assigned continuity check returned fresh=true, changed=[]; repeated after discovery with the same result. Final `git status --short` in SLOT returned empty.

Initial primary `python3 scripts/slotctl.py status --json` exited 0 but reported capacity_complete=false and conflicts [1,2,3]. Errors included `[Errno 1] Operation not permitted: 'ps'`, `public wt1 endpoint observation unavailable`, `public wt1 identity unavailable`; observation 2026-11-06T12:18:14Z. The exposed wt1 catalog descriptions also said no active lease. I provisionally stopped and wrote these two reports with that observation, informing ROOT; this history remains preserved here and in JSON.

ROOT reconciled this: its authorized controller observation was complete, no conflicts/reservations, and acquire/prepare had returned ACTIVE at 12:16:47Z, client codex, base4fca, epoch323eaae82597f49d8ab6fcec488d3dea03e0bab67cf57ec6a0c3a3fed81dbbb2. The worker's sandbox observation was unavailable, not authoritative lease loss; catalog wording predated acquisition. ROOT explicitly directed ONE real matching MCP call without bypass, repair or permission changes.

Actual first LSP call: `mcp__skeft_wt1__lean_file_outline({file_path:"/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/worktrees/wt1/lean/SKEFTHawking/QuantumNetwork/GaussianMoments.lean",max_declarations:80})`. It succeeded, isError=false, and returned actual imports and declarations, including `∫ x : ℝ, x^2 ∂gaussianReal 0 1 = 1` and fourth moment=3. Full result is preserved in the JSON. ROOT then confirmed continuing discovery. All Lean calls used only skeft_wt1; none failed.

Read the assigned continuity contract, notebook current entries, roadmap current L1 section, project authority/worker instructions, local Lean4 skill, accepted intake/source pins and the exact ADW auxiliary source. An initial oversized combined read truncated output; targeted rereads recovered the load-bearing source and current notebook/roadmap portions. No notebook or packet refresh.

## Accepted target and conventions

Accepted ADW source SHA256 `e74fc4b792d59d19f88917f8f0365a2336583ca0abc5cac1403917b98ebd3cd8`, especially equations4–7 and11: finite signed/complex polynomial W, compensating exp(-σ² ΣX²/2), Gaussian probability with variance σ², and undivided derivative-of-weight observable correction. Intake requires all degrees for M64, source jets/insertions and the original coframe specialization later; no kinetic result is imported as a hypothesis.

For standard normal Z:
`E[He_a(Z) Z^k]/k! = [x^k](x^a exp(x²/2))`.
Precisely, for k=a+2n the value is `1/(2^n n!)`; for k<a or odd k-a it is zero. A Nat subtraction formulation must retain k≥a explicitly. These explicit values are mathematical normalization guidance, not a newly kernel-checked theorem.

Actual Mathlib `Polynomial.hermite : ℕ → ℤ[X]` is explicitly probabilists' Hermite, recurrence He_(n+1)=X He_n-He'_n, He_0=1, He_1=X. Its Gaussian derivative formula uses exp(-x²/2), exactly matching the accepted source. Do not switch to physicists' Hermite for exp(-x²). Actual hover confirms `gaussianPDFReal (μ:ℝ) (v:ℝ≥0)` uses variance v, so σ corresponds to v=σ², not v=σ. GaussianMoments/GaussianWick use unnormalized Lebesgue weight exp(-x²/2); divide by √(2π), or (√(2π))^card ι, to obtain standard Gaussian probability expectations.

## Existing assets: actual LSP types, not name-based assumptions

1. `SKEFTHawking.QuantumNetwork.gaussInt_monomial`, GaussianWick.lean:33:
```lean
{ι : Type*} [Fintype ι] (m : ι → ℕ) :
  (∫ x : EuclideanSpace ℝ ι,
    (∏ i, (x i) ^ (m i)) * Real.exp (-‖x‖ ^ 2 / 2)) =
  ∏ i, ∫ t : ℝ, t ^ (m i) * Real.exp (-t ^ 2 / 2)
```
Already arbitrary finite index type and arbitrary degrees. This is the coordinate factorization needed after finite polynomial expansion; do not re-prove it. It is not itself a signed Hermite/source theorem.

2. `halfline_moment (m:ℕ)`, GaussianSphere.lean:29:
```lean
(∫ a in Ioi (0:ℝ), a^m * Real.exp (-a^2/2)) =
  (1/2:ℝ)^(-((m:ℝ)+1)/2) * (1/2) * Real.Gamma (((m:ℝ)+1)/2)
```
`halfline_rec (m:ℕ)`, line45:
```lean
(∫ a in Ioi (0:ℝ), a^(m+2) * Real.exp (-a^2/2)) =
  ((m:ℝ)+1) * ∫ a in Ioi (0:ℝ), a^m * Real.exp (-a^2/2)
```
Both all degrees, found through built index then actual outline/source. This materially strengthens the intake's base-moment inventory: no need to derive all half-line moments afresh. Even full-line moments can reuse symmetry and this recurrence; odd full-line weighted moments already vanish for ALL k by GaussianMoments `integral_odd_mul_gaussian (k:ℕ)`.

3. `moment_eq_wval (m:ℕ) (hm:m≤4)` proves only
`∫ t, t^m exp(-t²/2)=√(2π)*wval m`.
Actual source defines wval values 1,0,1,0,3 then default0. The default is not an all-degree Gaussian moment result. Fourth-tensor Wick results remain degree4-specific.

4. `Polynomial.coeff_hermite_explicit (n k:ℕ)`:
`(hermite (2*n+k)).coeff k = (-1)^n * ↑(2*n-1).doubleFactorial * ↑((2*n+k).choose k)`.
`coeff_hermite` covers all n,k by parity. `coeff_hermite_of_lt` handles the degree cutoff. These are coefficients of He, not the desired Gaussian integral coefficients.

5. Actual outline and hover for `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`:
```lean
(n:ℕ) (x:ℝ) :
  deriv^[n] (fun y => Real.exp (-(y^2/2))) x =
  (-1)^n * Polynomial.aeval x (Polynomial.hermite n) *
    Real.exp (-(x^2/2))
```
The two `hermite_eq_deriv_gaussian` variants exist as well. These give Rodrigues/derivative identities, without the integrated moment conclusion.

6. Actual `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`, IntegralEqImproper.lean:1314, for functions into a real normed algebra:
```lean
(∀ x ∈ tsupport v, HasDerivAt u (u' x) x) →
(∀ x ∈ tsupport u, HasDerivAt v (v' x) x) →
Integrable (u * v') → Integrable (u' * v) → Integrable (u * v) →
(∫ x:ℝ, u x * v' x) = -(∫ x:ℝ, u' x * v x)
```
This version avoids separately supplying endpoint limits, provided all three products are genuinely proved integrable. The neighboring theorem alternatively requires explicit atBot/atTop limits.

7. ProbabilityTheory `integral_gaussianReal_eq_integral_smul`, Gaussian.Real.lean:275:
for normed real-vector-valued f and v≠0,
`∫ x,f x ∂gaussianReal μ v = ∫ x,gaussianPDFReal μ v x • f x`.
`memLp_id_gaussianReal` supplies finite all-order Lp membership. IntegrableExpMul contains all-natural-power integrability, and GaussianIntegral has `integrable_rpow_mul_exp_neg_mul_sq` for b>0,s>-1. These support finite polynomial integrability rather than assuming desired moment values.

8. GoltermanShamir outline confirms `FermionicFockSpace`, finite-module instance, exterior `creation_anticommute` and `pauli_exclusion`. This is substrate, not the instantiated original128-generator coframe nilpotence/source theorem or physical CAR/state. No physical identification inferred.

## Imports, built index and history

GaussianMoments imports Gaussian.Real, Moments.Variance, Integral.Gamma, Lebesgue.Integral, Group.Integral, GaussianIntegral. GaussianWick imports GaussianMoments plus Integral.Pi, Haar.InnerProductSpace, EuclideanDist. GaussianSphere imports GaussianPolar plus Integral.Gamma. GoltermanShamir imports Mathlib and LatticeHamiltonian.

A first source-graph scan mistakenly counted imports in block comments (including Mathlib documentation examples); that provisional overreach was corrected. Final nested-comment/line-comment-stripped traversal shows: GaussianMoments and GaussianWick do NOT reach Hermite.Basic/Gaussian, GaussianSphere, ExteriorAlgebra.Basis/Grading. They DO reach IntegralEqImproper and IntegrableExpMul. One exact IBP path is GaussianMoments → Integral.Gamma → Gamma.Basic → ImproperIntegrals → IntegralEqImproper. GaussianSphere does not reach Hermite; GoltermanShamir reaches Hermite and exterior modules via its actual Mathlib import. Thus Hermite availability in a separately opened source file is not evidence of availability from GaussianWick's imports. A future minimal module should explicitly import the Hermite module and chosen project moment asset; do not import GoltermanShamir solely to obtain Mathlib.

Built `lean/lean_deps.json` was parsed BEFORE any negative conclusion: 53530 records, SHA256 `30b39767ba8f495116be9c25b56f4816718582fa938408fc9032ada42220246c`. It records actual all-degree gaussInt_monomial, halfline_moment and m≤4 moment_eq_wval; zero records contain Hermite in declaration name/type. This index covers extracted project declarations, not all Mathlib availability, so it is not a global absence proof. Recorded project axioms for the inspected Gaussian assets are empty; core dependencies are the standard three. No new proof was implemented or purity-certified.

Read-only history: GaussianMoments owning commit `99ba1a11414cf424f66e5478285b64b2275c2bd0`; Wick construction `68e774ebc05bd6d397d02869b7cfd63e6f0f7c03`; finite-index generalization `52218731d06c84e18559192f6eac95def617ce6c`. GS later changes `1bb6284226051c4ada8e7382a4da7355d76589fc`, `da906d933ebc52eea083526a0a99db754dea9415` preserve its conditional/substrate distinction. No Git plumbing or integration used.

Toolchain is leanprover/lean4:v4.32.0. Slot SHA256: toolchain `2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e`; manifest `6620cd482acd9c924acd5715c07cb59f8cb840d605ad211c31c1666839516464`; lakefile `7008b3d79ac294f4e822e8c867a326c316e94ff9047c4fd110e66b9cab84e5fe`. No dependency or cache changes.

## Bounded conclusion and first proof obligation

Searches included actual file outlines/hover, lean_local_search for hermite and IBP/integrability, semantic LeanSearch and LeanFinder by the Hermite–Gaussian moment statement, and Loogle `Polynomial.hermite, MeasureTheory.integral` plus Gaussian/power terms. No returned declaration directly established the full target. This is a bounded search result, not a proof of absence. Old pending comments or a name miss were not used as evidence.

Recommended first precise proof obligation is the actual polynomial Gaussian Stein identity, all p:ℝ[X], with no assumed integration-by-parts hypothesis:
```lean
∀ p : Polynomial ℝ,
  (∫ z : ℝ, z * p.eval z ∂ProbabilityTheory.gaussianReal 0 1) =
  ∫ z : ℝ, p.derivative.eval z ∂ProbabilityTheory.gaussianReal 0 1
```
Prove it by the existing generic whole-line IBP theorem, Gaussian density conversion and proved polynomial-times-Gaussian integrability. This is a suggested statement, not an elaborated candidate. It supplies both the Hermite lowering route and the eventual derivative-of-W correction; it must not be replaced by assuming that correction.

Then use the existing Hermite recurrence and polynomial product derivative to lower Hermite order against monomials, with k=0 treated explicitly. Base a=0 full-line moments reuse all-degree halfline_rec plus symmetry and existing all-odd vanishing. Derive the guarded factorial/parity values and finite-series coefficient statement; tensorize using existing gaussInt_monomial and finite linearity. No need to re-prove arbitrary coordinate factorization, all half-line Gamma moments, or Rodrigues' formula.

Full accepted package still owes σ scaling, constructed finite W/source jets/insertion preservation, original coframe grading/nilpotence and undivided observable identity. This report does not implement or discharge them. No build, cache repair, proof edit, new axiom/sorry/native_decide/maxHeartbeats, commit, release or notebook write occurred.
