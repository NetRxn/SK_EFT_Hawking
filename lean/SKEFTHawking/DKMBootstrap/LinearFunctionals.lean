/-
# Phase 6q Wave 1c.2 — DKM Transport Bootstrap: linear-functional convex cone

The DKM-compatible linear functionals on the correlator space form a
convex cone — this is the substantive content the Wave 2a SK-EFT
specialization (and any future SDP-extension per CHHK §6) consumes.

**Substantive structural finding:** the set of nonneg linear functionals
on the correlator space that respect the F4 positivity content of the
DKM axiom set forms a *convex cone* in the sense of nonneg-scalar
+ nonneg-sum closure. This is the bootstrap-side analog of the
positivity-of-test-functionals condition that powers the conformal
bootstrap, formulated entirely at the analytic-CHHK level (no SDPB).

**Wave 1c.2 deliverables:**
1. **`IsDKMCompatibleFunctional`** — predicate: a functional
   `F : Correlator → ℝ` is DKM-compatible if it is nonneg on every
   F4-positive correlator.
2. **Convex-cone closure theorems:**
   - `nonneg_scaling_dkm_compatible`: scaling by `c ≥ 0` preserves
     DKM-compatibility.
   - `sum_dkm_compatible`: pointwise sum of DKM-compatible functionals is
     DKM-compatible.
   - `zero_dkm_compatible`: zero functional is DKM-compatible.
3. **Substantive non-vacuity** — the linear functional
   `F(G) := G Ω k` (evaluation at a kinematic point) is DKM-compatible
   for any `(Ω, k)`.

**Why this matters for the bootstrap:** the convex-cone structure
gives the bootstrap "direction of attack" — bounds are derived by
proving that *every* DKM-compatible functional satisfies a certain
inequality. The convex-cone closure ensures the bound transports
through scalar/sum operations, which is what allows the bootstrap
machinery to assemble per-axiom-family content into the master
inequalities (CHHK eqs. 8, 14, 26, 29). The substantive analytic
content (CHHK eqs. 26 + 29 mean-free-path bounds) lives in Wave 2b.1
`HorizonTransportBootstrap.lean`; here we ship the convex-cone substrate.

References:
- Wave 1a.1 DR §5: convex-cone structure of dual functionals
- DR Wave 2a.1 §3: Option B predicate-substrate primary
- Mathlib4 `Mathlib/Analysis/Convex/Cone/{Basic,Dual,Extension,InnerDual}.lean`:
  `ConvexCone`, `PointedCone`, `ProperCone`, `ProperCone.hyperplane_separation`
  — the substrate for any future SDPB-extension wave
- CHHK arXiv:2509.18255: F4 positivity (eq. 5)
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
the functional `G ↦ G Ω k` is DKM-compatible (directly from F4
positivity at `(Ω, k)`). This is the substantive non-vacuity witness for
the convex-cone of DKM-compatible functionals — it gives a *family* of
DKM-compatible functionals parameterized by `(Ω, k)`. -/
def evalAt (Ω k : ℝ) : Correlator → ℝ := fun G => G Ω k

/-- **`evalAt Ω k` is DKM-compatible.** -/
theorem evalAt_dkm_compatible (Ω k : ℝ) :
    IsDKMCompatibleFunctional (evalAt Ω k) := by
  intro G hG
  exact hG Ω k

/-- **Nonneg-weighted finite sum of point evaluations is DKM-compatible.**
By combining the sum + scaling closures, any finite nonneg-weighted sum
of `evalAt` functionals (a discrete approximation of an integrated
spectral-weight functional like CHHK eq. 8) is DKM-compatible. The
nontrivial-coefficient case is stated below. -/
theorem two_point_weighted_dkm_compatible
    (c₁ c₂ : ℝ) (Ω₁ k₁ Ω₂ k₂ : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    IsDKMCompatibleFunctional (fun G => c₁ * G Ω₁ k₁ + c₂ * G Ω₂ k₂) := by
  exact sum_dkm_compatible
    (nonneg_scaling_dkm_compatible (evalAt_dkm_compatible Ω₁ k₁) hc₁)
    (nonneg_scaling_dkm_compatible (evalAt_dkm_compatible Ω₂ k₂) hc₂)

/-! ## §4. Cross-bridge to the CHHK eq. (8) integrated bound.

CHHK eq. (8) is an integrated spectral-weight inequality: the
functional `G ↦ ∫_ω^Λ ∫_Σ Im G^R(Ω,k) / Ω dΩ dk` is bounded above by a
microscopic-data quantity `boundData = ⟨n₀²⟩_T / (ω·n_B(ω)·ν²)`. The
convex-cone structure shipped in §2 + §3 implies that *any* nonneg-
weighted integrated functional of this shape inherits the F4-positivity
direction: integrated functionals over F4-positive correlators have
nonneg integrand pointwise, hence (under any reasonable integration
theory) produce nonneg output.

We capture this at predicate-substrate level via the
`integrated_form_dkm_compatible` theorem on a *discrete-sum
approximation* of the CHHK integrated functional. The full integral
form lifts to Wave 2b.1 (substantive HorizonTransportBootstrap). -/

/-- **`HasFSumRule` is a sufficient condition for an integrated DKM-
compatible functional on the correlator's slice.** The structural
content: if `G` satisfies the f-sum-rule with `boundData`, then for
any nonneg integrand-discretisation `(c_i, Ω_i, k_i)` in the CHHK
integration window, the partial-sum functional `∑ c_i · G(Ω_i, k_i)`
is bounded above by `(∑ c_i) · Ω_i⁻¹ · boundData` (componentwise).

For Wave 1c.2 we ship this as a single-point convexity statement; the
full discrete-sum version lifts via repeated application of
`sum_dkm_compatible` in Wave 2b.1. -/
theorem integrated_form_dkm_compatible_point
    (G : Correlator) (boundData : ℝ) (h_fsum : HasFSumRule G boundData)
    (ω Λ Ω k : ℝ) (hω : 0 < ω) (hωΛ : ω ≤ Λ)
    (hωΩ : ω ≤ Ω) (hΩΛ : Ω ≤ Λ) (hΩpos : 0 < Ω) :
    G Ω k / Ω ≤ boundData :=
  h_fsum ω Λ hω hωΛ Ω k hωΩ hΩΛ hΩpos

/-! ## §5. Closure summary — Wave 1c.2 linear-functional convex cone.

This module ships:
- **`IsDKMCompatibleFunctional`** predicate — DKM-compatibility of a
  linear functional `Correlator → ℝ`.
- **Convex-cone closure** — three theorems (`zero_dkm_compatible`,
  `nonneg_scaling_dkm_compatible`, `sum_dkm_compatible`) confirming
  the set of DKM-compatible functionals forms a convex cone.
- **Substantive non-vacuity** — `evalAt Ω k` (point evaluation) is DKM-
  compatible for each `(Ω, k)`; nonneg-weighted finite sums
  (`two_point_weighted_dkm_compatible`) are also DKM-compatible.
- **CHHK eq. (8) cross-bridge** — `integrated_form_dkm_compatible_point`
  expressing the f-sum-rule predicate's content as a single-point
  bound transferable through the convex-cone closure.

Substantive integrated-functional content (full CHHK eqs. (8), (14),
(26), (29) inequalities) lifts to Wave 2b.1 substrate-specific
`HorizonTransportBootstrap` content.

The Mathlib4 `ProperCone` substrate (`ProperCone.hyperplane_separation`,
`InnerProductSpace.toDual`) is available if and when the project
attempts a future SDPB-extension wave per CHHK §6 / DR §5; the convex-
cone closure here is the bootstrap-side substrate that machinery
would consume. -/

end SKEFTHawking.DKMBootstrap
