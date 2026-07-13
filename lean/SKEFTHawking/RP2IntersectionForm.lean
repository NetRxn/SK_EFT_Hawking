import Mathlib
import SKEFTHawking.RP2CupLadder
import SKEFTHawking.RP2Manifold
import SKEFTHawking.SingularSurfaceIntersectionForm
import SKEFTHawking.SingularUniversalCoeff

/-!
# W-A (n = 2 witness) — the rank-1 odd intersection form on `ℝP²`

The final substrate piece the `ℝP⁴` faithful-carrier witness consumes: the concrete
computation of the mod-2 intersection form of `Σ = ℝP²` on the merged
`RP2PointSet`/`RP2Manifold` carrier.

Building on the `n = 2` Smith cohomology tower (`RP2CohomologyLadder`, `RP2CupLadder`):

* **`H¹(ℝP²;ℤ/2) ≅ ℤ/2`** with explicit generator `xRP2 := xpow 1` (`rp2H1EquivFun`, the
  `ℤ/2`-linear equivalence `H¹ ≃ₗ (Fin 1 → ℤ/2)` — the basis datum of the enhancement `enh`).
* **`intersectionForm xRP2 xRP2 = 1`** (`intersectionForm_xRP2_self`) — the rank-1 **odd**
  self-intersection `x·x = 1`, the `n = 2` shadow of the in-tree `μ(x⁴) = 1` (`RP4WuAssembly`).
  Via `intersectionForm_self_eq_cupSquare` this is `μ(x ⌣ x) = 1`, the top cup-square paired
  against `[ℝP²]`. The load is the top-homology computation `H₂(ℝP²;ℤ/2) ≅ ℤ/2`
  (`homologyTopEquivZMod2` at `m = 0`) plus universal coefficients — **no P₂-window needed**.
* **The form is non-degenerate** (`intersectionForm_nondeg`) — immediate for the concrete rank-1
  form from `x·x = 1` and the one-dimensionality of `H¹`, with no appeal to the (unbuilt)
  middle-dimension `openDuality` window.

This is exactly the datum the witness's `hpolar` anchor equates with a `Brown.Z4Quadratic`'s
polar form, and whose non-degeneracy `Z4Quadratic.nondeg` consumes.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.SingularSurfaceIntersectionForm
open SKEFTHawking.RP2PointSet

namespace SKEFTHawking.RP2IntersectionForm

/-- Re-key `ℝP²`'s charted structure at the `Fin (0 + 2)` spelling the closed-surface
Poincaré-duality machinery uses (defeq to the `Fin 2` atlas; instance search is syntactic). -/
noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin (0 + 2))) RP2 :=
  inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 2)) RP2)

/-! ## §1. `H¹(ℝP²;ℤ/2) ≅ ℤ/2` with explicit generator -/

/-- **The generator of `H¹(ℝP²;ℤ/2)`** — the degree-1 Smith ladder class `δS(1)`. -/
noncomputable def xRP2 : Cohomology (TopCat.of RP2) 1 := RP2CohomologyLadder.xpow 1

/-- **`xRP2 ≠ 0`** — the ladder class is nonzero through degree 2. -/
theorem xRP2_ne_zero : xRP2 ≠ 0 := RP2CohomologyLadder.xpow_ne_zero (by norm_num)

/-- **`H¹(ℝP²;ℤ/2)` is spanned by `xRP2`** — the `n = 2` Smith ladder at degree 1. -/
theorem h1_eq_smul_xRP2 (w : Cohomology (TopCat.of RP2) 1) : ∃ c : ZMod 2, w = c • xRP2 :=
  RP2CohomologyLadder.cohomology_eq_smul_xpow (by norm_num) w

/-- `{xRP2}` is linearly independent (a single nonzero vector over the field `ℤ/2`). -/
theorem rp2H1_linearIndependent :
    LinearIndependent (ZMod 2) (fun _ : Fin 1 => xRP2) := by
  rw [linearIndependent_unique_iff]
  exact xRP2_ne_zero

/-- `{xRP2}` spans `H¹(ℝP²;ℤ/2)`. -/
theorem rp2H1_span :
    ⊤ ≤ Submodule.span (ZMod 2) (Set.range (fun _ : Fin 1 => xRP2)) := by
  intro w _
  obtain ⟨c, rfl⟩ := h1_eq_smul_xRP2 w
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

/-- **The basis `{xRP2}` of `H¹(ℝP²;ℤ/2)`** (indexed by `Fin 1`). -/
noncomputable def rp2H1Basis : Module.Basis (Fin 1) (ZMod 2) (Cohomology (TopCat.of RP2) 1) :=
  Module.Basis.mk rp2H1_linearIndependent rp2H1_span

@[simp] theorem rp2H1Basis_apply (i : Fin 1) : rp2H1Basis i = xRP2 := by
  rw [rp2H1Basis, Module.Basis.mk_apply]

/-- **`H¹(ℝP²;ℤ/2) ≃ₗ (Fin 1 → ℤ/2)`** — the `ℤ/2`-linear equivalence pinning `n = 1`, the
enhancement basis datum (design v4 §2 ▲A-5). Sends `xRP2 ↦ (fun _ => 1)`. -/
noncomputable def rp2H1EquivFun : Cohomology (TopCat.of RP2) 1 ≃ₗ[ZMod 2] (Fin 1 → ZMod 2) :=
  rp2H1Basis.equivFun

/-! ## §2. The top-homology computation and `μ(x ⌣ x) = 1` -/

/-- **`H₂(ℝP²;ℤ/2) = span{[ℝP²]}`** — every degree-2 homology class is a `ℤ/2`-multiple of the
fundamental class, from the closed-surface top-homology isomorphism `homologyTopEquivZMod2`
(`m = 0`), whose local-degree map `Φ_{x₀}` is bijective with `Φ_{x₀}([ℝP²]) = 1`. -/
theorem h2_eq_smul_fundClass (β : Homology (TopCat.of RP2) (0 + 2)) :
    ∃ c : ZMod 2, β = c • surfaceFundamentalClass (M := RP2) := by
  refine ⟨localDegree (m := 0) (Classical.arbitrary RP2) β, ?_⟩
  refine (localDegree_bijective (m := 0) (Classical.arbitrary RP2)).injective ?_
  rw [map_smul, smul_eq_mul,
    show surfaceFundamentalClass (M := RP2) = fundamentalClass (m := 0) from rfl,
    localDegree_fundamentalClass, mul_one]

/-- **`μ(x ⌣ x) = 1`** — the fundamental functional of the top cup-square is `1`. Since
`xpow 2 ≠ 0`, universal coefficients (`cohomology_eq_zero_of_kroneckerH`) forces a homology class
pairing nontrivially with it; every such class is a multiple of `[ℝP²]` (§2 top-homology), so the
pairing against `[ℝP²]` — which is `μ(x ⌣ x)` — is itself nonzero, hence `1`. -/
theorem mu_xpow2_eq_one :
    surfaceFundamentalFunctional (M := RP2) (RP2CohomologyLadder.xpow 2) = 1 := by
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1)
      (surfaceFundamentalFunctional (M := RP2) (RP2CohomologyLadder.xpow 2)) with h | h
  · exfalso
    refine RP2CohomologyLadder.xpow_ne_zero (k := 2) (by norm_num) ?_
    refine SingularUniversalCoeff.cohomology_eq_zero_of_kroneckerH 1
      (RP2CohomologyLadder.xpow 2) (fun β => ?_)
    obtain ⟨c, rfl⟩ := h2_eq_smul_fundClass β
    rw [map_smul, smul_eq_mul,
      show kroneckerH (X := TopCat.of RP2) (1 + 1) (RP2CohomologyLadder.xpow 2)
            (surfaceFundamentalClass (M := RP2))
          = surfaceFundamentalFunctional (M := RP2) (RP2CohomologyLadder.xpow 2) from
        (surfaceFundamentalFunctional_apply (M := RP2) (RP2CohomologyLadder.xpow 2)).symm,
      h, mul_zero]
  · exact h

/-! ## §3. The rank-1 odd intersection form -/

/-- **`cupSquare xRP2 = xpow 2`** — the cup square of the generator is the degree-2 ladder class
(`RP2CupLadder.xpow_two_eq_cupH`). -/
theorem cupSquare_xRP2 : cupSquare xRP2 = RP2CohomologyLadder.xpow 2 := by
  rw [cupSquare, xRP2, ← RP2CupLadder.xpow_two_eq_cupH]

/-- **`intersectionForm xRP2 xRP2 = 1`** — the rank-1 **odd** self-intersection `x · x = 1` of
`ℝP²`, the `n = 2` shadow of the in-tree `μ(x⁴) = 1`. Via `intersectionForm_self_eq_cupSquare`
this is `μ(cupSquare xRP2) = μ(x ⌣ x) = 1`. -/
theorem intersectionForm_xRP2_self :
    intersectionForm (M := RP2) xRP2 xRP2 = 1 := by
  rw [intersectionForm_self_eq_cupSquare, cupSquare_xRP2, mu_xpow2_eq_one]

/-- **The intersection form is non-degenerate** — for the concrete rank-1 form this is immediate
from `x · x = 1` and `H¹ = span{xRP2}`: a class `a = c • xRP2` with `⟨a, b⟩ = 0` for all `b`
gives, at `b = xRP2`, `c · (x·x) = c = 0`, so `a = 0`. No `openDuality` (`P₂`) window is needed. -/
theorem intersectionForm_nondeg :
    Function.Injective ⇑(intersectionForm (M := RP2)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨c, rfl⟩ := h1_eq_smul_xRP2 a
  have hax : intersectionForm (M := RP2) (c • xRP2) xRP2 = 0 :=
    LinearMap.congr_fun ha xRP2
  rw [map_smul, LinearMap.smul_apply, intersectionForm_xRP2_self, smul_eq_mul, mul_one] at hax
  rw [hax, zero_smul]

end SKEFTHawking.RP2IntersectionForm
