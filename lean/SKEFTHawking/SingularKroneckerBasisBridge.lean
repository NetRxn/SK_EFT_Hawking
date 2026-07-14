/-
# Phase 5q.H (W-A arm 4, R2 enabler) — the mod-2 UCT BASIS BRIDGE: a cohomology basis
# `Hᵏ(X) ≃ₗ (Fin n → ℤ/2)` induces the dual homology basis `Hₖ(X) ≃ₗ (Fin n → ℤ/2)`.

**Why this exists (the seam-rebuild gap, named by the basis-tie worker).** The strengthened
carrier (`CharPairStrBundled`) carries its enhancement basis on the COHOMOLOGY side
(`basis : H¹(Σ;ℤ/2) ≃ₗ (Fin n → ℤ/2)`, matching `intersectionForm`/`rp2H1Equiv`), but the
membrane realization seam (`GeoRealizationData` / `transportedBInc`) consumes HOMOLOGY-side
identifications (`H₁(∂Q) → H₁(Q)`). Per the round-5 gate spec the seam's homology bases must be
DERIVED from the carried cohomology basis, never free fields (no-go
`realization-seam-basis-gauge-launders-e8`). This module supplies the derivation: the Kronecker
pairing is perfect over the field `ℤ/2` (`kroneckerHEquiv`, finite-dim-free), so a coordinate
system on `Hᵏ` dualizes to a coordinate system on `Hₖ`, canonically and gauge-covariantly — the
coordinates of `x ∈ Hₖ` are its pairings against the pulled-back standard covectors.

**The load-bearing compatibility** (`kroneckerH_eq_dotProduct`): in the induced coordinates the
Kronecker pairing IS the standard dot product — `⟨ω, x⟩ = ∑ i (e ω)ᵢ · (e⁎ x)ᵢ`. This is what
makes gauge-covariance mechanical downstream: transporting the homology coordinates by a gauge `g`
forces the cohomology coordinates by `(gᵀ)⁻¹`, so a kernel gauge can no longer move independently
of the form (the F2 exploit shape).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularKroneckerEquiv

namespace SKEFTHawking.SingularKroneckerBasisBridge

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularKroneckerEquiv

variable {X : TopCat}

/-! ## §1. The induced coordinate map on homology -/

/-- **The induced homology coordinates**: `x ↦ (i ↦ ⟨e⁻¹(δᵢ), x⟩)` — the pairings of `x` against
the pulled-back standard covectors of the cohomology basis `e`. -/
noncomputable def homologyCoords {n N : ℕ}
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Homology X (N + 1) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  LinearMap.pi fun i => kroneckerH (N + 1) (e.symm (Pi.single i 1))

@[simp] theorem homologyCoords_apply {n N : ℕ}
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (x : Homology X (N + 1)) (i : Fin n) :
    homologyCoords e x i = kroneckerH (N + 1) (e.symm (Pi.single i 1)) x :=
  rfl

/-- Any covector's pairing decomposes through the coordinates: for `ω = e.symm v`,
`⟨ω, x⟩ = ∑ i, vᵢ · (coords x)ᵢ`. The single-covector Fourier expansion of the pairing. -/
theorem kroneckerH_symm_eq_sum {n N : ℕ}
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (v : Fin n → ZMod 2)
    (x : Homology X (N + 1)) :
    kroneckerH (N + 1) (e.symm v) x = ∑ i, v i * homologyCoords e x i := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc kroneckerH (N + 1) (e.symm v) x
      = kroneckerH (N + 1) (e.symm (∑ i, v i • Pi.single i (1 : ZMod 2))) x := by rw [← hv]
    _ = ∑ i, v i * homologyCoords e x i := by
        rw [map_sum, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, homologyCoords_apply]

/-- **THE COMPATIBILITY**: in the induced coordinates the Kronecker pairing is the standard dot
product — `⟨ω, x⟩ = ∑ i, (e ω)ᵢ · (coords x)ᵢ`. -/
theorem kroneckerH_eq_dotProduct {n N : ℕ}
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (ω : Cohomology X (N + 1))
    (x : Homology X (N + 1)) :
    kroneckerH (N + 1) ω x = ∑ i, e ω i * homologyCoords e x i := by
  conv_lhs => rw [show ω = e.symm (e ω) from (e.symm_apply_apply ω).symm]
  exact kroneckerH_symm_eq_sum e (e ω) x

/-! ## §2. Bijectivity — perfection of the pairing + the dimension count -/

/-- Injectivity: a homology class with vanishing coordinates pairs to zero against EVERY covector
(the expansion above), and the pairing separates points because `kroneckerHEquiv` is SURJECTIVE
onto the dual — every functional is a pairing. -/
theorem homologyCoords_injective {n N : ℕ}
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Function.Injective (homologyCoords e) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod 2)]
  intro φ
  obtain ⟨ω, hω⟩ := (kroneckerHEquiv (X := X) N).surjective φ
  have := kroneckerH_eq_dotProduct e ω x
  rw [show kroneckerH (N + 1) ω = φ from by rw [← hω]; rfl] at this
  rw [this]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show homologyCoords e x i = 0 from by rw [hx]; rfl, mul_zero]

/-- The homology is finite-dimensional as soon as the cohomology carries a finite basis: `Hₖ`
embeds into its double dual (evaluation is injective over a field), and the double dual is
finite-dimensional because `Dual Hₖ ≃ Hᵏ ≃ (Fin n → ℤ/2)`. -/
theorem finiteDimensional_homology_of_cohomologyBasis {n N : ℕ}
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    FiniteDimensional (ZMod 2) (Homology X (N + 1)) := by
  have hdual : FiniteDimensional (ZMod 2)
      (Module.Dual (ZMod 2) (Homology X (N + 1))) :=
    LinearEquiv.finiteDimensional ((kroneckerHEquiv (X := X) N).symm.trans e).symm
  have heval : Function.Injective
      (Module.Dual.eval (ZMod 2) (Homology X (N + 1))) := by
    intro x y hxy
    have h : ∀ φ : Module.Dual (ZMod 2) (Homology X (N + 1)), φ (x - y) = 0 := by
      intro φ
      have := congrArg (fun f => f φ) hxy
      simpa [Module.Dual.eval, sub_eq_zero] using
        (by simpa [map_sub] using sub_eq_zero.mpr this :
          φ x - φ y = 0)
    have := (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp h
    exact sub_eq_zero.mp this
  exact FiniteDimensional.of_injective
    (Module.Dual.eval (ZMod 2) (Homology X (N + 1))) heval

/-- Surjectivity via the dimension count: injective into an `n`-dimensional target from a space
whose dual — hence itself — has dimension `n`. -/
theorem homologyCoords_surjective {n N : ℕ}
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Function.Surjective (homologyCoords e) := by
  haveI := finiteDimensional_homology_of_cohomologyBasis e
  have hrank : Module.finrank (ZMod 2) (Homology X (N + 1))
      = Module.finrank (ZMod 2) (Fin n → ZMod 2) := by
    have h1 : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Homology X (N + 1)))
        = Module.finrank (ZMod 2) (Fin n → ZMod 2) :=
      ((kroneckerHEquiv (X := X) N).symm.trans e).finrank_eq
    rwa [Subspace.dual_finrank_eq] at h1
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp
    (homologyCoords_injective e)

/-! ## §3. THE BRIDGE — the derived homology basis -/

/-- **THE BRIDGE**: the homology basis induced by a cohomology basis — the seam-rebuild's
required derivation (`eσ := homologyBasisOfCohomologyBasis (carried basis)`, never a free field). -/
noncomputable def homologyBasisOfCohomologyBasis {n N : ℕ}
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    Homology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
  LinearEquiv.ofBijective (homologyCoords e)
    ⟨homologyCoords_injective e, homologyCoords_surjective e⟩

@[simp] theorem homologyBasisOfCohomologyBasis_apply {n N : ℕ}
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (x : Homology X (N + 1)) :
    homologyBasisOfCohomologyBasis e x = homologyCoords e x :=
  rfl

/-- **Dual-basis normalization**: the derived basis is exactly dual to `e` — the `i`-th pulled-back
covector evaluates to `δᵢⱼ` on the `j`-th derived basis vector. -/
@[simp] theorem kroneckerH_basis_dual {n N : ℕ}
    (e : Cohomology X (N + 1) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (i j : Fin n) :
    kroneckerH (N + 1) (e.symm (Pi.single i 1))
      ((homologyBasisOfCohomologyBasis e).symm (Pi.single j 1))
      = (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) i := by
  exact congrFun ((homologyBasisOfCohomologyBasis e).apply_symm_apply (Pi.single j 1)) i

end SKEFTHawking.SingularKroneckerBasisBridge
