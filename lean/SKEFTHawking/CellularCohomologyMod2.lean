/-
# Phase 5q.F W4-cohomology — genuine graded ℤ/2 cohomology via cellular cochain complexes

The H¹(M;ℤ/2)-vector-space layer that the faithful Pin⁺ `TangentialData` instance
(`TangentialDataBordism.lean`) needs. The lab-notebook load-bearing finding is that
`Ω₄^{Pin⁺} ≅ ℤ/16` is the bordism group of **chosen** Pin⁺ structures — an `H¹(M;ℤ/2)`-torsor
per manifold — so the tangential structure must be carried as DATA over a genuine `H¹(M;ℤ/2)`
that is an actual ℤ/2-vector space (the factor-of-2 multiplicity is what produces the 16). The
project's prior substrate `SymTFT/StiefelWhitney.lean` carries a single `ZMod 2` rank per degree,
which is too coarse to be a genuine vector space / torsor base.

This module ships the genuine object the **lightest honest way**: a finite **cellular ℤ/2 cochain
complex** (finitely many cells per dimension + mod-2 incidence numbers + the chain condition
`∂² = 0`). The cochains `Cⁿ = (cells n → ZMod 2)` are genuine finite-dimensional ℤ/2-vector
spaces; the coboundary `δⁿ` is a genuine `ℤ/2`-linear map; and the cohomology
`Hⁿ = ker δⁿ / im δⁿ⁻¹` is a genuine quotient ℤ/2-vector space (NOT a rank placeholder). For the
specific manifolds in play (`RP^n` and the Pin⁺ bordism generators) the CW structure is small and
explicit, so the computation `Hᵏ(RP^n; ℤ/2) = ℤ/2` is a genuine, reviewer-checkable fact (next
shard), not a placeholder encoding.

## Honest scope

This is cellular cohomology of an explicitly-given finite CW complex over the field `ℤ/2` — genuine
homological algebra, kernel-pure, no axioms. It is NOT the full singular-cohomology-of-topological-
spaces theory (simplicial sets, Alexander–Whitney cup product, Steenrod squares) — that heavier
substrate is not needed for the H¹-torsor layer, and the cellular route is the faithful,
computable object that the chosen-Pin⁺-structure count actually lives on (cellular ≅ singular for
CW complexes, by the standard comparison; we build the cellular side because it is the finite,
decidable one).

Per Invariant #15: no new axioms — this is a definitional construction over Mathlib's linear algebra
(`LinearMap.ker`, `LinearMap.range`, `Submodule` quotients).
-/
import Mathlib

namespace SKEFTHawking.CellularCohomologyMod2

open scoped BigOperators

/-! ## §1. Finite cellular complexes over ℤ/2 -/

/-- A finite **cellular complex over ℤ/2**: finitely many cells in each dimension, the mod-2
incidence numbers `⟨σ : τ⟩` of an `(n+1)`-cell `σ` on an `n`-cell `τ`, and the chain condition
`∂² = 0` (`incidence_sq`). This is the genuine combinatorial datum underlying a CW complex's
cellular chain/cochain complex with `ℤ/2` coefficients. -/
structure CellComplex where
  /-- The set of `n`-cells. -/
  cells : ℕ → Type
  [fin : ∀ n, Fintype (cells n)]
  [dec : ∀ n, DecidableEq (cells n)]
  /-- The mod-2 incidence number of an `(n+1)`-cell on an `n`-cell. -/
  incidence : (n : ℕ) → cells (n + 1) → cells n → ZMod 2
  /-- The chain condition `∂² = 0`: for any `(n+2)`-cell `σ` and `n`-cell `τ`, the sum over
  intermediate `(n+1)`-cells of the composed incidence numbers vanishes mod 2. -/
  incidence_sq : ∀ (n : ℕ) (σ : cells (n + 2)) (τ : cells n),
    (∑ μ : cells (n + 1), incidence (n + 1) σ μ * incidence n μ τ) = 0

attribute [instance] CellComplex.fin CellComplex.dec

variable (C : CellComplex)

/-! ## §2. Cochains and the coboundary -/

/-- The **`n`-cochains** `Cⁿ(C; ℤ/2)`: `ℤ/2`-valued functions on the `n`-cells. A genuine
finite-dimensional `ℤ/2`-vector space (Pi type over the field `ZMod 2`). -/
abbrev Cochain (n : ℕ) : Type := C.cells n → ZMod 2

/-- The **coboundary** `δⁿ : Cⁿ → Cⁿ⁺¹`, `(δ f)(σ) = ∑_τ ⟨σ : τ⟩ · f(τ)`, a genuine `ℤ/2`-linear
map (the transpose of the cellular boundary). -/
def coboundary (n : ℕ) : Cochain C n →ₗ[ZMod 2] Cochain C (n + 1) where
  toFun f := fun σ => ∑ τ : C.cells n, C.incidence n σ τ * f τ
  map_add' f g := by
    funext σ; simp only [Pi.add_apply, mul_add]; rw [Finset.sum_add_distrib]
  map_smul' a f := by
    funext σ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_); ring

@[simp] theorem coboundary_apply (n : ℕ) (f : Cochain C n) (σ : C.cells (n + 1)) :
    coboundary C n f σ = ∑ τ : C.cells n, C.incidence n σ τ * f τ := rfl

/-! ## §3. `δ² = 0` -/

/-- The defining cochain identity: `δⁿ⁺¹ ∘ δⁿ = 0`, the cohomological form of `∂² = 0`. -/
theorem coboundary_comp_coboundary (n : ℕ) :
    (coboundary C (n + 1)).comp (coboundary C n) = 0 := by
  refine LinearMap.ext fun f => ?_
  funext σ
  simp only [LinearMap.comp_apply, coboundary_apply, LinearMap.zero_apply, Pi.zero_apply]
  -- (δ(δ f))(σ) = ∑_μ ⟨σ:μ⟩ ∑_τ ⟨μ:τ⟩ f(τ) = ∑_τ (∑_μ ⟨σ:μ⟩⟨μ:τ⟩) f(τ) = ∑_τ 0 · f(τ) = 0
  have : ∀ μ : C.cells (n + 1),
      C.incidence (n + 1) σ μ * ∑ τ : C.cells n, C.incidence n μ τ * f τ
        = ∑ τ : C.cells n, C.incidence (n + 1) σ μ * C.incidence n μ τ * f τ := by
    intro μ; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun τ _ => by ring)
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun τ _ => ?_)
  have hfac : ∑ μ : C.cells (n + 1), C.incidence (n + 1) σ μ * C.incidence n μ τ * f τ
      = (∑ μ : C.cells (n + 1), C.incidence (n + 1) σ μ * C.incidence n μ τ) * f τ := by
    rw [Finset.sum_mul]
  rw [hfac, C.incidence_sq n σ τ, zero_mul]

/-! ## §4. Genuine cohomology `Hⁿ = ker δⁿ / im δⁿ⁻¹` -/

/-- The submodule of `Cⁿ` of **coboundaries** (the image of the incoming `δⁿ⁻¹`), `⊥` in degree 0
(there is no `δ⁻¹`). -/
def coboundaryRange (n : ℕ) : Submodule (ZMod 2) (Cochain C n) :=
  match n with
  | 0 => ⊥
  | m + 1 => LinearMap.range (coboundary C m)

/-- Coboundaries are cocycles: `im δⁿ⁻¹ ≤ ker δⁿ`, the well-definedness of cohomology. -/
theorem coboundaryRange_le_ker (n : ℕ) :
    coboundaryRange C n ≤ LinearMap.ker (coboundary C n) := by
  cases n with
  | zero => exact bot_le
  | succ m =>
    show LinearMap.range (coboundary C m) ≤ LinearMap.ker (coboundary C (m + 1))
    rw [LinearMap.range_le_ker_iff]
    exact coboundary_comp_coboundary C m

/-- **Genuine ℤ/2 cohomology** `Hⁿ(C; ℤ/2) = ker δⁿ / im δⁿ⁻¹`, an actual quotient `ℤ/2`-vector
space (not a rank placeholder). The coboundary submodule is viewed inside the cocycle submodule
`ker δⁿ` via `Submodule.submoduleOf` (legitimate by `coboundaryRange_le_ker`). -/
def Cohomology (n : ℕ) : Type :=
  (LinearMap.ker (coboundary C n)) ⧸
    (coboundaryRange C n).submoduleOf (LinearMap.ker (coboundary C n))

noncomputable instance (n : ℕ) : AddCommGroup (Cohomology C n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (n : ℕ) : Module (ZMod 2) (Cohomology C n) :=
  inferInstanceAs (Module (ZMod 2) (_ ⧸ _))

/-- The class of a cocycle in cohomology. -/
def Cohomology.mk (n : ℕ) (z : LinearMap.ker (coboundary C n)) : Cohomology C n :=
  Submodule.Quotient.mk z

end SKEFTHawking.CellularCohomologyMod2
