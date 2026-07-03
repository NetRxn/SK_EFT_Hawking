import Mathlib
import SKEFTHawking.RP4SmithCochain
import SKEFTHawking.SphereHomology
import SKEFTHawking.SingularUCFinite
import SKEFTHawking.SingularH0PathConnected

/-!
# Phase 5q.G (B-arc, M3-e,f) — the degree-0 layer and the sphere cohomology vanishing

The two boundary inputs of the cohomological Smith ladder (M3-g): `Hᵏ(S⁴;ℤ/2) = 0` for
`k = 1,2,3` (UC-duality against the M1 homological vanishing), and the degree-0 layer — on a
path-connected space the `0`-cocycles are exactly the constants (`pathSimplex` bridges any two
points), so `H⁰ = span{1}`; on `S⁴` this makes the cochain transfer vanish on `0`-cocycles
(`τ^#(const c) = 2c = 0`), which will start the ladder `δS : H⁰(ℝP⁴) ≅ H¹(ℝP⁴)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.RP4PointSet SKEFTHawking.RP4Transfer SKEFTHawking.RP4SmithCochain
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularH0PathConnected SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularUCFinite

namespace SKEFTHawking.RP4CohomologyLadder

/-! ## §1. The degree-0 layer of a path-connected space -/

section ZeroLayer

variable {X : TopCat}

/-- The constant-`1` `0`-cochain is a cocycle: `δ(1)(σ¹) = 1 + 1 = 0`. -/
theorem const_one_mem_ker :
    (fun _ => (1 : ZMod 2)) ∈ LinearMap.ker (coboundaryₗ X 0) := by
  rw [LinearMap.mem_ker]
  funext σ
  show ∑ _i : Fin 2, (1 : ZMod 2) = (0 : SingularCochain X 1) σ
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Pi.zero_apply]
  decide

/-- **The unit class** `1 ∈ H⁰(X; ℤ/2)` — the class of the constant-`1` cocycle. -/
noncomputable def unitClass (X : TopCat) : Cohomology X 0 :=
  Cohomology.mk X 0 ⟨fun _ => 1, const_one_mem_ker⟩

/-- **`0`-cocycles are constant on a path-connected space**: evaluating `δf = 0` on the
`1`-simplex of a path between the two points equates the values. -/
theorem cocycle_zero_apply_eq [PathConnectedSpace ↑X]
    (f : SingularCochain X 0) (hf : coboundaryₗ X 0 f = 0)
    (σ ρ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) : f σ = f ρ := by
  have hpath := PathConnectedSpace.joined (simplexPoint ρ) (simplexPoint σ)
  have h0 := congrFun hf (pathSimplex hpath.somePath)
  have h1 : f (face 0 (pathSimplex hpath.somePath)) + f (face 1 (pathSimplex hpath.somePath))
      = 0 := by
    have h2 : ∑ i : Fin 2, f (face i (pathSimplex hpath.somePath)) = 0 := h0
    rwa [Fin.sum_univ_two] at h2
  rw [face_zero_pathSimplex, face_one_pathSimplex] at h1
  have heq : f (constSimplex (simplexPoint σ) 0) = f (constSimplex (simplexPoint ρ) 0) := by
    revert h1
    generalize f (constSimplex (simplexPoint σ) 0) = p
    generalize f (constSimplex (simplexPoint ρ) 0) = q
    revert p q
    decide
  rw [eq_constSimplex σ, eq_constSimplex ρ]
  exact heq

/-- **`H⁰` of a path-connected space is spanned by the unit**: any `0`-class is `f(σ₀) • 1` —
on the nose at the cocycle level, by constancy. -/
theorem cohomologyZero_eq_smul_unit [PathConnectedSpace ↑X]
    (w : Cohomology X 0) :
    ∃ c : ZMod 2, w = c • unitClass X := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hσ₀ : Nonempty ↑X := PathConnectedSpace.nonempty
  set σ₀ := constSimplex (X := X) hσ₀.some 0 with hσ₀def
  refine ⟨f.1 σ₀, ?_⟩
  show Cohomology.mk X 0 f = f.1 σ₀ • unitClass X
  rw [unitClass, show (f.1 σ₀ • Cohomology.mk X 0 ⟨fun _ => 1, const_one_mem_ker⟩ :
      Cohomology X 0) = Cohomology.mk X 0 (f.1 σ₀ • ⟨fun _ => 1, const_one_mem_ker⟩) from rfl]
  refine congrArg (Cohomology.mk X 0) (Subtype.ext ?_)
  funext ρ
  show f.1 ρ = (f.1 σ₀ • fun _ => (1 : ZMod 2)) ρ
  rw [Pi.smul_apply, smul_eq_mul, mul_one]
  exact cocycle_zero_apply_eq f.1 (LinearMap.mem_ker.mp f.2) ρ σ₀

/-- **The unit class is nonzero** (degree-0 coboundaries are `⊥`; the constant-`1` cochain is
not the zero function — witnessed at the constant simplex of any point). -/
theorem unitClass_ne_zero [Nonempty ↑X] : unitClass X ≠ 0 := by
  intro h
  have h2 := (Submodule.Quotient.mk_eq_zero _).mp h
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at h2
  rw [show coboundaryRange X 0 = (⊥ : Submodule (ZMod 2) _) from rfl, Submodule.mem_bot] at h2
  have h3 := congrFun h2 (constSimplex (X := X) (Nonempty.some inferInstance) 0)
  exact one_ne_zero h3

end ZeroLayer

/-! ## §2. The sphere cohomology vanishing (M3-e) -/

/-- **`Hᵏ(S⁴; ℤ/2) = 0` for `1 ≤ k ≤ 3`** — UC-duality against M1's homological vanishing. -/
theorem sphere_cohomology_eq_zero {k : ℕ} (h1 : 1 ≤ k) (h3 : k ≤ 3)
    (ω : Cohomology (TopCat.of S4) k) : ω = 0 := by
  obtain ⟨N, rfl⟩ : ∃ N, k = N + 1 := ⟨k - 1, by omega⟩
  apply (ucDualEquiv (TopCat.of S4) N).injective
  rw [map_zero]
  apply LinearMap.ext
  intro x
  rw [SKEFTHawking.SphereHomology.sphere_homology_eq_zero (N + 1) h1 h3 x, map_zero,
    LinearMap.zero_apply]

/-! ## §3. The ladder start: `τ^* = 0` on `H⁰` (M3-f) -/

/-- Path-connectedness of `S4` (the sphere in `ℝ⁵`, dimension `≥ 1`). -/
noncomputable instance : PathConnectedSpace S4 := by
  have h : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :=
    isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      norm_num) 0 zero_le_one
  exact (isPathConnected_iff_pathConnectedSpace.mp h)

/-- **The cochain transfer kills `0`-cocycles**: on path-connected `S⁴` a `0`-cocycle is
constant, and `τ^#(const) = c + c = 0`. -/
theorem cochainTransfer_zero_of_cocycle
    (y : SingularCochain (TopCat.of S4) 0)
    (hy : coboundaryₗ (TopCat.of S4) 0 y = 0) :
    cochainTransfer 0 y = 0 := by
  funext σ
  show y (liftPlus σ) + y (liftMinus σ) = (0 : SingularCochain (TopCat.of RP4) 0) σ
  rw [cocycle_zero_apply_eq y hy (liftPlus σ) (liftMinus σ), ← two_smul (ZMod 2),
    show (2 : ZMod 2) = 0 by decide, zero_smul]
  rfl

/-- **`τ^* = 0` on `H⁰(S⁴)`** — the ladder-start input: `im τ^* = 0` in degree `0`, so the
Smith connecting `δS : H⁰(ℝP⁴) → H¹(ℝP⁴)` is injective. -/
theorem cohomologyTransfer_zero_eq_zero (y : Cohomology (TopCat.of S4) 0) :
    cohomologyTransfer 0 y = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show cohomologyTransfer 0 (Cohomology.mk (TopCat.of S4) 0 y) = 0
  rw [cohomologyTransfer_mk]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
  rw [cochainTransfer_zero_of_cocycle y.1 (LinearMap.mem_ker.mp y.2)]
  exact Submodule.zero_mem _

/-! ## §4. The ladder (M3-g): `δSᵏ(1) ≠ 0` and `Hᵏ(ℝP⁴) = span{δSᵏ(1)}` for `k ≤ 4` resp. `≤ 3` -/

/-- `ℝP⁴` is path-connected — the continuous image of the path-connected `S⁴`. -/
noncomputable instance : PathConnectedSpace RP4 := by
  rw [pathConnectedSpace_iff_univ]
  have h2 : ⇑mkC '' Set.univ = (Set.univ : Set RP4) := by
    rw [Set.image_univ, Set.range_eq_univ]
    intro q
    obtain ⟨a, ha⟩ := Quotient.exists_rep q
    exact ⟨a, ha⟩
  rw [← h2]
  exact (pathConnectedSpace_iff_univ.mp inferInstance).image mkC.continuous

/-- **`δS` is injective in degrees `k ≤ 3`**: `ker δS = im τ^*`, and `τ^*` vanishes — at `k = 0`
by constancy (M3-f), at `k = 1,2,3` because its domain `Hᵏ(S⁴)` is zero (M3-e). -/
theorem smithCoConnecting_injective {k : ℕ} (hk : k ≤ 3) :
    Function.Injective (smithCoConnecting k) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨y, hy⟩ := (exact_cohomologyTransfer_smithCoConnecting k w).mp hw
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    rw [← hy, cohomologyTransfer_zero_eq_zero]
  · rw [← hy, sphere_cohomology_eq_zero hpos hk y, map_zero]

/-- **`δS` is surjective onto degrees `k + 1 ≤ 3`**: `im δS = ker π^*`, and `π^*` lands in the
vanishing `Hᵏ⁺¹(S⁴)`. -/
theorem smithCoConnecting_surjective {k : ℕ} (h1 : k + 1 ≤ 3) :
    Function.Surjective (smithCoConnecting k) := by
  intro x
  exact (exact_smithCoConnecting_cohomologyPullback k x).mp
    (sphere_cohomology_eq_zero (Nat.succ_le_succ (Nat.zero_le k)) h1 _)

/-- **The ladder classes** `xpow k := δSᵏ(1) ∈ Hᵏ(ℝP⁴; ℤ/2)` — identified with the cup powers
of the generator in M3-i. -/
noncomputable def xpow : (k : ℕ) → Cohomology (TopCat.of RP4) k
  | 0 => unitClass (TopCat.of RP4)
  | k + 1 => smithCoConnecting k (xpow k)

@[simp] theorem xpow_succ (k : ℕ) : xpow (k + 1) = smithCoConnecting k (xpow k) := rfl

/-- **The ladder classes are nonzero through degree 4** — `δS`-injectivity walks the
nonvanishing up from the unit. -/
theorem xpow_ne_zero {k : ℕ} (hk : k ≤ 4) : xpow k ≠ 0 := by
  induction k with
  | zero => exact unitClass_ne_zero
  | succ m ih =>
      intro h
      refine ih (by omega) (smithCoConnecting_injective (by omega) ?_)
      rw [map_zero]
      exact h

/-- **`Hᵏ(ℝP⁴; ℤ/2) = span{δSᵏ(1)}` for `k ≤ 3`** — surjectivity transports the degree-0 span
up the ladder. With `xpow_ne_zero`, every `Hᵏ` (`k ≤ 3`) is one-dimensional with basis the
ladder class. -/
theorem cohomology_eq_smul_xpow : ∀ {k : ℕ}, k ≤ 3 → ∀ (w : Cohomology (TopCat.of RP4) k),
    ∃ c : ZMod 2, w = c • xpow k := by
  intro k
  induction k with
  | zero => exact fun _ w => cohomologyZero_eq_smul_unit w
  | succ m ih =>
      intro hm w
      obtain ⟨v, hv⟩ := smithCoConnecting_surjective hm w
      obtain ⟨c, hc⟩ := ih (by omega) v
      exact ⟨c, by rw [← hv, hc, map_smul, xpow_succ]⟩

end SKEFTHawking.RP4CohomologyLadder
