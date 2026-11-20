# Provisional complete complex auxiliary coefficient block

Task `publication-complex-auxiliary-design-r1`, parent `publication-remediation`. READ-ONLY mathematical/source design, awaiting independent prospective review and ROOT acceptance. Candidate primary `2c201cd00cd1d17e7665ea0a6711344abc1c1524`. Packet: `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/publication-complex-auxiliary-design-r1.json`. ROOT alone writes the primary notebook. No implementation, slot, proof, kernel, native, publication or physical acceptance is claimed.

## Original contract and source custody

I directly read the entire 98-line original authority `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/.publication-l1-checkpoint-20261103/docs/audits/2026-10-17-publication-substance-construction/ADW_EXACT_AUXILIARY_IDENTITY.md`, including all equations and limitations. Eq4 supplies an arbitrary finite complex polynomial after truncation; Eq5 defines its actual signed/complex Hermite weight; Eq6 is a formal identity before Grassmann evaluation. The next coherent acceptance block must establish all of Eq5–6's complex polynomial transform, without silently restricting to four moments, real coefficients, positive weights, nonempty dimension, or a defining-the-conclusion equality. Eq4's physical polynomial construction and Eqs7–11's later assembly are separate, still required work.

Mandatory project guidance/continuity, roadmap and current notebook were inspected. The controlling project contracts remain genuine integrability, strongest meaningful theorem statements, no new expectation axioms/sorry/native_decide/heartbeat overrides, MCP search before prove, independent review, and ROOT-owned authoritative integration/build/gates. Neither current namespace docstrings nor the derived graph establish absence.

## Mathematical specification

Let `ι` be ANY finite type (empty permitted), `σ : ℝ`, `hσ : 0 < σ`, and `v : ℝ≥0` with `(v : ℝ)=σ^2`. Keep the existing `v,hv` convention initially rather than force a new NNReal conversion API. Define the actual measure

`μσ = Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 v)`.

Represent multiindices canonically by `ι →₀ ℕ`, polynomial `P : MvPolynomial ι ℂ`; use coercion `fun i => α i` to consume existing affine theorems. Write

- `deg α = ∑ i, α i` (over all finite coordinates);
- `fac β = ∏ i, (β i).factorial` (a natural number, then cast);
- `Hσα(h) = ∏ i, Polynomial.aeval (h i / σ) (Polynomial.hermite (α i)) : ℝ`;
- `hβ = ∏ i, h i ^ β i : ℝ`;
- `Wσ(P,h) = ∑ α ∈ P.support, P.coeff α * ((σ ^ deg α)⁻¹ : ℝ) * (Hσα(h) : ℂ)`.

In the last expression the inverse real scale is explicitly cast to ℂ. This is exactly Eq5, with inverse natural power equivalent to negative integer power because σ≠0. Arbitrary complex coefficients enter without conjugation. No α! belongs in W: Hermite generating functions already carry 1/α! in the generating parameter, whereas the transform produces X^α directly.

Define independently the normalized scalar Gaussian coefficient

`gσ(n) = if Even n then ((σ^2 / 2 : ℝ) : ℂ)^(n/2) / ((n/2).factorial : ℂ) else 0`,

and `Gcoeffσ(γ)=∏ i, gσ(γ i)`. The normalizations at n=0,1,2,4 are 1,0,σ²/2,σ⁴/8. This definition is computational algebra, not an integral disguised as the desired answer.

The central theorem must assert, for EVERY `β : ι →₀ ℕ`,

`(∫ h, Wσ(P,h) * (hβ : ℂ) ∂μσ) / (fac β : ℂ)`
` = ∑ α ∈ P.support, if α ≤ β then P.coeff α * Gcoeffσ(β-α) else 0`.

Every β is included irrespective of P's degree; there is no degree-M or degree-four cutoff in this theorem. Prove separately, before its integral rewrites,

`Integrable (fun h => Wσ(P,h) * (hβ : ℂ)) μσ`.

In particular β=0 proves genuine integrability of W. Finite complex sums and products with real monomials are Bochner-integrable because each real Hermite-monomial product is integrable, its complex embedding is integrable, and complex constant multiplication and finite summation preserve integrability. Pointwise distribute W*hβ, combine products into `∏ i, Heαi(hᵢ/σ)*hᵢ^βi`, then call the actual existing affine integrability theorem. Do not claim arbitrary products of integrable functions are integrable.

## Full formal-series identity, not only a kernel equation

Use existing `MvPowerSeries ι ℂ` and its native coefficient/product algebra. Set

`Qσ = ∑ i, MvPowerSeries.C (((σ^2/2 : ℝ) : ℂ)) * MvPowerSeries.X i ^ 2`,

`GaussianSeriesσ = PowerSeries.subst Qσ (PowerSeries.exp ℂ)`.

This uses the ordinary formal exponential at a zero-constant series, not analytic `Complex.exp` on a normed completion. Prove `constantCoeff Qσ=0` and the required `PowerSeries.HasSubst Qσ` condition, rather than relying on the total default behavior of substitution outside its valid domain. The exact implicit-ring arguments and `HasSubst` constructor are pending typed inspection.

Define `AuxiliarySeriesσ(P)` independently by assigning coefficient β to the actual normalized integral in the preceding section. Then require the substantial theorem

`AuxiliarySeriesσ(P) = GaussianSeriesσ * (P : MvPowerSeries ι ℂ)`.

The proof must use the integral coefficient theorem and independently establish

`MvPowerSeries.coeff γ GaussianSeriesσ = Gcoeffσ(γ)`.

Only after those two results may coefficient extensionality finish the series equality. A wrapper theorem closed by ext/simp is acceptable as assembly only if it calls these nontrivial results. Defining `GaussianSeriesσ` as the auxiliary transform of 1, or defining `AuxiliarySeriesσ(P)` as the RHS, would not discharge Eq6.

The formal Gaussian coefficient calculation adds a real algebra obligation beyond IBP: coefficientwise substitution of exp, vanishing of unsuitable monomials in Qσ^n, and the multinomial coefficient. Explicitly, the coefficient of γ in Qσ^n vanishes unless all γᵢ are even and `∑ i γᵢ/2=n`. In the remaining case it is

`(n! / ∏ i (γᵢ/2)!) * (σ²/2)^n`.

After multiplication by 1/n!, this becomes `Gcoeffσ(γ)`. Coefficient substitution is locally finite because Q has zero constant term; here homogeneity of degree two gives the sharper unique n=|γ|/2. Empty dimension gives Q=0, GaussianSeries=1, and is handled directly or uniformly; no division by dimension occurs. Reuse Mathlib multinomial/coefficient-power/substitution facts after typed search. A useful equivalent intermediate is the finite product of coordinate factors `∏ i, (PowerSeries.exp ℂ).subst (C (σ²/2)*X i^2)`; if used, prove its equality with substitution at Q, rather than quietly replace exp(sum) by a new definition. No new formal-series infrastructure is required.

## Factorial and scale proof, including off-support indices

For real integrals, existing `integral_prod_hermite_mul_pow_affine` yields

`∫ ∏ i Heαi(hᵢ/σ) hᵢ^βi = ∏ i [σ^αi * (βi.descFactorial αi : ℝ) * mσ(βi-αi)]`,

where `mσ(n)=∫ y, y^n ∂gaussianReal 0 v`. Lift this equality to complex integrals using `integral_complex_ofReal`, then multiply by pα and inverse scale, not vice versa.

1. From σ>0 derive σ≠0, hence `(σ^deg α)≠0`. Use `Finset.prod_pow_eq_pow_sum` or its actual typed equivalent to identify `∏σ^αi=σ^deg α`; cancel the inverse. This cancellation is essential and testable at σ=2.
2. Split `α≤β` before manipulating natural subtraction. If false, pick i with βi<αi. Its descending factorial is zero; the entire term vanishes. Do not turn β-α into a zero index and accidentally retain a lower-degree term.
3. If α≤β, apply source-confirmed `Nat.factorial_mul_descFactorial` pointwise: `(βi-αi)! * βi.descFactorial αi = βi!`. Cast to ℂ, prove factorials nonzero, and cancel to obtain `(βi.descFactorial αi : ℂ)/(βi! : ℂ)=1/((βi-αi)! : ℂ)`.
4. Products of these identities give the normalized shift kernel `∏ mσ(βi-αi)/(βi-αi)!`.
5. Independently show normalized moments equal gσ. Preferred reuse is any current all-order Gaussian moment theorem found by typed search. A small direct fallback is available from existing polynomial Stein/affine IBP: `mσ(0)=1`, `mσ(1)=0`, `mσ(n+2)=(n+1)σ² mσ(n)`. It implies `mσ(2k)=(2k)! σ^(2k)/(2^k k!)` and odd moments zero. Prove the recurrence with `n=1` affine insertion and p=X^(n+1), then simplify He1 and divide by σ; base m1 follows `integral_id_gaussianReal`. This reuses established genuine Gaussian integrability and avoids Gamma algebra. An alternate already inspected route uses all-order half-line moments/recurrence plus odd symmetry, then normalizes the density; it is valid but adds unnecessary sphere imports if no direct moment API is found.
6. Sum over P.support using integrability for each summand, `integral_finsetSum`, and complex `integral_const_mul`. GaussianSeries*P coefficients follow from expansion P into monomials and `MvPowerSeries.coeff_mul_monomial`, or native antidiagonal convolution. Finiteness of P.support and native formal coefficient multiplication make all sums finite.

A useful intermediate theorem, before evaluating moments, is the normalized real-Hermite shift against every β, with result zero for α≰β and `(∏ mσ(βi-αi))/(fac(β-α))` otherwise. It sharply separates analytic integrability/IBP from combinatorics; its later complex-linear finite sum is short.

## Minimal coherent dependency packages

A. Complex weight and genuine integrability: definitions above, real-to-complex Hermite insertion lemma, arbitrary-support W, every monomial insertion integrable. Import existing `GaussianPolynomialAffine` plus the exact Mathlib Bochner scalar-extension module if not already available. No need to reprove complex polynomial IBP from scratch or import complex sphere moments.

B. All-order normalized shift: raw-moment coefficient identity, α≰β vanishing, factorial/σ cancellation, arbitrary-complex finite coefficient sum. Reuse A integrability and affine IBP. This is already substantive but must not be reported as the complete exp-Q statement until C/D land.

C. Gaussian coefficient algebra: all-order normalized Gaussian moments if not already available, actual formal exp substitution at Qσ, and coefficient theorem Gcoeff. This package may be developed independently of W after ROOT grants an appropriate slot; the mathematical dependencies are existing IBP/moment algebra and Mathlib formal series, not B's new source. ROOT chooses actual scheduling/ownership.

D. Eq6 assembly and controls: define AuxiliarySeries from integrals and prove coefficientwise and full formal equality, all β, with no analytic exponential interchange. Integrate with aggregate import, actual independent review/kernel verification and ROOT canonical build/extraction/gates. These are acceptance work still to be commissioned; this report executed none of them.

One coherent source module may contain A–D if small after discovery; splitting formal Gaussian algebra from complex W can reduce import cost and isolate difficult homogeneous-power bookkeeping. Do not create a second expectation API, custom axioms, routing ledger or runtime mechanism.

## Existing evidence and typed searches still required

Actual source read at primary:

- `lean/SKEFTHawking/ADW/GaussianPolynomialAffine.lean`: all 218 lines, all real finite-index affine insertion/integrability and finite real sums. Existing finite-sum theorem fixes Hermite α while varying monomial β, so W's varying α is better handled with per-α theorem plus finite summation. All finite dimensions already supported.
- `lean/SKEFTHawking/ADW/GaussianPolynomialHermite.lean`: all-order standard Gaussian polynomial IBP, Hermite recurrence, derivative reduction, orthogonality and diagonal factorial. `GaussianPolynomialIBP.lean` supplies actual Gaussian polynomial integrability/Stein identity.
- `lean/SKEFTHawking/QuantumNetwork/GaussianMoments.lean`: actual low even moments and arbitrary odd vanishing; `GaussianSphere.lean` has arbitrary half-line moment and recurrence. Its degree-four title is not an all-order absence argument.
- `GaussianComplexMoment.lean` and `GaussianComplexTensor.lean`: inspected complete actual source. They concern complex sphere degree-(2,2) tensors with nonzero dimension, not arbitrary-complex Hermite polynomial weights. Their use of `integral_re_add_im` illustrates actual complex Bochner assembly, but importing their sphere machinery is not necessary for the present scalar extension.
- Mathlib `Probability/Distributions/Gaussian/Real.lean`: actual complex Gaussian MGF `complexMGF_id_gaussianReal (z : ℂ)` and all-moment finiteness `memLp_id_gaussianReal`, plus affine map, density and first moment. The complex MGF may support a later analytic proof but does not itself discharge the polynomial-Hermite coefficient problem.
- Mathlib `MeasureTheory/Function/L1Space/Integrable.lean:1107` has `Integrable.ofReal`; `MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:158–162` has `integral_ofReal` and `integral_complex_ofReal` (latter no integrability binder; still separately prove integrability here). These are sufficient scalar-extension substrate for A/B.
- Mathlib `RingTheory/MvPowerSeries/Basic.lean`: native `coeff_mul`, `coeff_monomial_mul`, `coeff_mul_monomial`, `MvPolynomial.toMvPowerSeries`, `MvPolynomial.coeff_coe`; formal series are coefficient functions on Finsupp multiindices. `PowerSeries/Exp.lean` supplies actual `PowerSeries.exp` and `coeff_exp`; `PowerSeries/Substitution.lean` supplies `PowerSeries.subst` into multivariate series and HasSubst/AlgHom interfaces. These exact source forms were inspected, not elaborated in a live session.
- Actual aggregate `lean/SKEFTHawking.lean` imports Affine/Hermite/IBP at lines1–3; the complex sphere modules are separately imported near lines4007–4012. The local declaration graph `lean/lean_deps.json` was parsed and filtered by both module/name and statement content (`gaussianReal`, complex codomain, factorial/powers). It contains actual complex sphere declarations but did not expose the current new affine/Hermite modules in that query. That graph/source mismatch is only a freshness/reachability question for ROOT to reconcile, not evidence that source or proofs are missing. No graph refresh/build was run.

No live LSP lease is active for this assignment. The following exact searches/typed checks remain PENDING and are required before implementation:

- `#check SKEFTHawking.ADW.integrable_prod_hermite_mul_pow_affine`, `#check ...integral_prod_hermite_mul_pow_affine`; inspect α as ordinary function versus Finsupp coercion, all implicit universes.
- Typed search for `Integrable (fun h => (f h : ℂ)) μ` from real Integrable; actual `Integrable.ofReal`, `integral_complex_ofReal`, `integral_const_mul`, `integral_finsetSum` application types.
- Search by type for arbitrary `∫ x, x^n ∂gaussianReal 0 v`, parity/even-factorial or normalized-moment forms, and existing complex coefficient polynomial integrability. Search project, current Mathlib and reachable imports. No absence verdict before this.
- `#check Nat.factorial_mul_descFactorial`, typed descending-factorial-zero for n<k, product-power/sum lemma, Finsupp pointwise order and difference coercions.
- `#check PowerSeries.exp`, `#check PowerSeries.coeff_exp`, `#check PowerSeries.subst`, `#check PowerSeries.hasSubst_iff`; inspect actual `MvPowerSeries.coeff_subst` and applicable coefficient-power/multinomial lemmas by type.
- `#check MvPowerSeries.coeff_mul_monomial`, `#check MvPolynomial.coeff_coe`, polynomial support monomial-sum expansion, and extensionality. Confirm subst Q exp constant-zero side conditions; never infer from similarly named one-variable lemmas.
- Outline/diagnostics/goal checks and independent `lean_verify` on the implemented exports, then ROOT authoritative build/extraction/native composition. None is supplied by this report.

## Required nonvacuous controls and falsification

Use actual theorem instantiations involving the real integral, not tests of two new definitions alone. Proposed expected values below are mathematically derived, not Lean-checked in this read-only assignment.

1. Empty ι: there is one multiindex; P is constant, W=P(0), μσ has total mass1, AuxiliarySeries=P, Q=0. Require the integral itself equal the possibly nonreal constant `-2+3i`; do not add Nonempty or divide by cardinality.
2. One coordinate, `P=1+iX-2X²`: `W=1+i h/σ²-2(h²/σ⁴-1/σ²)`. Normalized coefficients at β=0,1,2,3,4 are `1`, `i`, `σ²/2-2`, `iσ²/2`, `σ⁴/8-σ²`. At σ=2: `1,i,0,2i,-2`; raw β4 integral is `-48`. This simultaneously tests complex phase, signed weight, Hermite2 subtraction, Gaussian sign and exponential factorials.
3. Mixed coordinate `P=(1+i)X₁X₂`: β=(1,1) coefficient is 1+i; β=(3,1) is `(1+i)σ²/2`; β=(2,1) is0. There is no factorial of total degree: fac(1,1)=1, fac(3,1)=6. This detects confusion between |β|! and ∏βi!.
4. Off-order α=(2,0), β=(1,8): the corresponding Hermite insertion vanishes even though |α|≤|β|. Coordinatewise order is essential, not total degree. α=(5), β=(4) also vanishes; β−α=0 alone does not permit a term.
5. High degree: `P=iX^7`, β7 normalized coefficient i, β9 is `iσ²/2`; raw β7 integral is `5040i`. This prevents hidden degree-four restrictions and omission of inverse scale. Include σ=2 and another positive nonunit scale.
6. Sigma cancellation: for a pure monomial α=β the normalized coefficient equals pα for every σ>0; e.g. `(1+i)X₁X₂` gives 1+i at β=(1,1), while dropping σ^-|α| gives `(1+i)σ²`.
7. Unweighted P=1: odd coefficient0, β2=σ²/2, β4=σ⁴/8; the positive Gaussian exponent sign is forced.

Meaningful faults for a future independent control harness, with exact source restoration and no permanent mutation: remove inverse σ power (controls2/6 fail at σ=2); change inverse power to σ^-2|α| (controls5/6 fail); replace probabilists He2=z²−1 by z²+1 (constant term of P=−2X² fails); drop coefficient 1/facβ (β2/β4/raw integral controls fail); use |β|! (mixed control3 fails); conjugate p (imaginary controls fail); omit α≤β filter or replace by total-degree order (control4 fails); flip Q Gaussian sign (control7 fails); impose degree-four support truncation (control5 fails); substitute zero weight or exploit nonintegrable integral=0 (integrability plus β0 P=1 and nonzero diagonal controls fail). These are prospective controls only; no mutation/test was executed.

## Exact downstream assembly still OPEN

After Eq6, Eq4 requires constructing the actual source polynomial S_x in commuting variables and proving finite total-degree truncation/cancellation for `[exp S_x * exp(-Qσ)]≤M`. Eq7 additionally requires a concrete Grassmann algebra with the source's independent complex Dirac/bar generators; proof that the explicit coframes from Eq1 are homogeneous degree2/even and commute; the global degree cutoff M=4V; and a legitimate algebra evaluation of the formal/truncated identity at those nilpotents. General formal substitution into a noncommutative Grassmann algebra cannot be assumed: it must factor through the commuting even subalgebra or use a proved commuting-family evaluation. This is an additional result beyond Eq6.

Then multiply site identities with independent Gaussian fields; construct the precise h-linear bilinear matrix with every source link/sign; prove Berezin orientation and determinant identity; prove absolute coefficient integrability plus link-coefficient continuity/boundedness over the finite compact Spin(4) product to justify the actual Gaussian/Haar/Berezin exchanges in Eq10. Only then are the exact regulated partition/insertion identities formally assembled. Eq11 needs Gaussian IBP on the weighted insertion retaining ∂W, not dividing by W. Z≠0 is separate for normalized observables. Physical source/response, Legendre action, selected state/domain/adjoint, physical B3 scale/window/mode/transport and gravity claims remain OPEN. Signed/complex W and determinant do not imply positive RHMC measure or a scalar effective potential.

## Execution and acceptance boundary

Executed only read-only source/guidance/graph inspection (`cat`, bounded `sed`, `rg`, Python JSON parsing), `git rev-parse HEAD`, and the required continuity check. Initial continuity check returned fresh=true, changed=[]. No builds/tests/LSP/slots/process inspection or mutation, no Git write, and no repository/notebook edits. Only the two assigned /tmp outputs are authored. Final continuity result is recorded in the JSON companion. This design requires independent prospective mathematical/source review, then ROOT acceptance before it is treated as settled implementation scope.

Final same-packet continuity check: exit 0, fresh=True, changed=[].
