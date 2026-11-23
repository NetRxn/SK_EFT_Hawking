/-
# DKM positive-frequency functional cone

A compatible real functional is nonnegative on the F4 cone
`∀ Ω k, 0 ≤ Ω → 0 ≤ G Ω k`. Nonnegative scaling and addition preserve
compatibility. Point evaluations require nonnegative sampled frequencies.
These closure statements do not assert linearity for an arbitrary `F`, a weighted
microscopic upper bound, a physical correlator match, or causal analyticity.

Source: CHHK arXiv:2509.18255v2 §7.1, positivity after Eq. (24).
The pointwise projection retained below is legacy F2, not Eq. (2)/(25)'s integral.
-/
import SKEFTHawking.DKMBootstrap.SDPStructure

namespace SKEFTHawking.DKMBootstrap

/-! ## §1. The DKM-compatible-functional predicate.

A functional `F : Correlator → ℝ` is *DKM-compatible* if it produces a
nonneg output on every correlator that satisfies the F4 positivity
axiom. This is the substrate analog of the "positive linear functional
on the OPE cone" condition that powers the conformal bootstrap. -/

/-- **DKM-compatible functional.** A real-valued functional on the
correlator space is *DKM-compatible* if it is nonneg on every F4-
positive correlator. This is the bootstrap-side positivity-of-test-
functional condition specialized to the F4 input. -/
def IsDKMCompatibleFunctional (F : Correlator → ℝ) : Prop :=
  ∀ G : Correlator, IsImGRetardedNonneg G → 0 ≤ F G

/-! ## §2. Convex-cone closure theorems.

The set `{F : Correlator → ℝ | IsDKMCompatibleFunctional F}` is closed
under nonneg scaling, pointwise sum, and contains the zero functional —
i.e., it forms a *convex cone* in the function space `Correlator → ℝ`. -/

/-- **The zero functional is DKM-compatible.** -/
theorem zero_dkm_compatible :
    IsDKMCompatibleFunctional (fun _ => 0) := by
  intro _ _
  exact le_refl 0

/-- **Nonneg scaling preserves DKM-compatibility.** If `F` is DKM-
compatible and `c ≥ 0`, then `c • F` (i.e., `fun G => c * F G`) is also
DKM-compatible. -/
theorem nonneg_scaling_dkm_compatible
    {F : Correlator → ℝ} (hF : IsDKMCompatibleFunctional F)
    {c : ℝ} (hc : 0 ≤ c) :
    IsDKMCompatibleFunctional (fun G => c * F G) := by
  intro G hG
  exact mul_nonneg hc (hF G hG)

/-- **Sum closure: pointwise sum of two DKM-compatible functionals is
DKM-compatible.** -/
theorem sum_dkm_compatible
    {F₁ F₂ : Correlator → ℝ}
    (hF₁ : IsDKMCompatibleFunctional F₁)
    (hF₂ : IsDKMCompatibleFunctional F₂) :
    IsDKMCompatibleFunctional (fun G => F₁ G + F₂ G) := by
  intro G hG
  exact add_nonneg (hF₁ G hG) (hF₂ G hG)

/-! ## §3. Substantive non-vacuity — point-evaluation functional. -/

/-- **Point-evaluation functional `evalAt Ω k`.** For each `(Ω, k) ∈ ℝ × ℝ`,
at `0 ≤ Ω` the functional `G ↦ G Ω k` is DKM-compatible (directly from F4
positivity at `(Ω, k)`). This is the substantive non-vacuity witness for
the convex-cone of DKM-compatible functionals — it gives a *family* of
DKM-compatible functionals parameterized by `(Ω, k)`. -/
def evalAt (Ω k : ℝ) : Correlator → ℝ := fun G => G Ω k

/-- **`evalAt Ω k` is DKM-compatible at nonnegative frequency.** -/
theorem evalAt_dkm_compatible (Ω k : ℝ) (hΩ : 0 ≤ Ω) :
    IsDKMCompatibleFunctional (evalAt Ω k) := by
  intro G hG
  exact hG Ω k hΩ

/-- **Nonneg-weighted finite sum of point evaluations is DKM-compatible.**
The sum and scaling closures apply at nonnegative sampled frequencies. This
two-point statement supplies no convergence or quadrature-error estimate for an integral. -/
theorem two_point_weighted_dkm_compatible
    (c₁ c₂ : ℝ) (Ω₁ k₁ Ω₂ k₂ : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hΩ₁ : 0 ≤ Ω₁) (hΩ₂ : 0 ≤ Ω₂) :
    IsDKMCompatibleFunctional (fun G => c₁ * G Ω₁ k₁ + c₂ * G Ω₂ k₂) := by
  exact sum_dkm_compatible
    (nonneg_scaling_dkm_compatible (evalAt_dkm_compatible Ω₁ k₁ hΩ₁) hc₁)
    (nonneg_scaling_dkm_compatible (evalAt_dkm_compatible Ω₂ k₂ hΩ₂) hc₂)

/-! ## §4. Legacy pointwise upper-bound projection.

Positive-frequency cone closure proves nonnegativity of the displayed finite functionals.
It does not prove the source's thermally weighted frequency/momentum integral bound.
-/

/-- Projection of the legacy pointwise F2 premise at one positive-frequency sample.
This is not an integrated bound, nor a derivation of CHHK v2 Eq. (2)/(25).
In particular, cone positivity supplies no microscopic upper bound. -/
theorem integrated_form_dkm_compatible_point
    (G : Correlator) (boundData : ℝ) (h_fsum : HasFSumRule G boundData)
    (ω Λ Ω k : ℝ) (hω : 0 < ω) (hωΛ : ω ≤ Λ)
    (hωΩ : ω ≤ Ω) (hΩΛ : Ω ≤ Λ) (hΩpos : 0 < Ω) :
    G Ω k / Ω ≤ boundData :=
  h_fsum ω Λ hω hωΛ Ω k hωΩ hΩΛ hΩpos

end SKEFTHawking.DKMBootstrap
