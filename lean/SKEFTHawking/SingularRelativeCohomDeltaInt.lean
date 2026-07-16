/-
# Phase 5q.H close-out (#187) — the INTEGRAL cohomology pair-LES connecting map `δ` and the
# `im ι* = ker δ` middle exactness, on the annihilator model over `ℤ`

The integral mirror of `SingularRelativeCohomDelta.deltaRelH`. On this substrate's annihilator model
(`relCochainsInt S` = integral cochains killing the subspace chains `= im C_•(S;ℤ)`) the pair
connecting map has a light description as a **δ-image class**: the connecting map
`δ : Hⁿ(∂W;ℤ) → Hⁿ⁺¹(W,∂W;ℤ)` sends the class of a boundary cocycle — presented by any absolute lift
`z ∈ Cⁿ(W;ℤ)` whose coboundary `δz` annihilates the subcomplex (`δz ∈ relCochainsInt S (n+1)`) — to
`[δz] ∈ Hⁿ⁺¹(W,∂W;ℤ)`. (The lift exists because the restriction `Cⁿ(W) ↠ Cⁿ(∂W)` is surjective, the
annihilator-model dual of the subcomplex injection.)

This module banks, for a generic pair `(X, S)`, over `ℤ`:

* **§1 `deltaRelHInt`** (piece 1) — the δ-image class `[δz] ∈ Hⁿ⁺¹(X,S;ℤ)`, degree-general (`δⁿ`), with
  its additivity/`ℤ`-linearity in the lift and its `deltaRelCocycleInt` cocycle-packaging.
* **§2 the pair-LES middle exactness** `im ι* = ker δ` (piece 2). On lifts:
  `deltaRelHInt z h = 0 ↔ z` differs from an absolute cocycle by a relative cochain
  (`deltaRelHInt_eq_zero_iff`), i.e. the boundary class `[z|∂W]` is `δ`-killed **iff** it is the
  restriction of an absolute class (`= im ι*`). The two containment halves:
  `im ι* ⊆ ker δ` is `deltaRelHInt_of_cocycle_eq_zero` (an absolute cocycle has `δz = 0`, so `[δz] = 0`);
  `ker δ ⊆ im ι*` is the substantive snake-chase inside `deltaRelHInt_eq_zero_iff`.

This is the shared Int pair-LES substrate for the σ-descent, dA's hcob, and the trace's Wu functional
vanishings — the `#185`-inventoried architectural gap's core `δ`+exactness over `ℤ`. It is built on the
genuine integral relative cochain complex (`RelativeCohomologyInt`, `SingularEuclideanCapIsoInt`), NOT on
the `Fin n → ℝ` lattice model of the downstream consumers (that identification is the separate `⊗ℝ`
wiring layer).

Dimension discipline (for the consumers): `W` 5-dim, `∂W` 4-dim; `δ` in degrees `2 → 3`
(`n = 2` here); the mixed pairing against `[W,∂W]` lives in the Kronecker layer, not this module.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularEuclideanCapIsoInt

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt

namespace SKEFTHawking.SingularRelativeCohomDeltaInt

noncomputable section

variable {X : TopCat} {S : Set X}

/-! ## §1. The integral δ-image class -/

/-- The integral coboundary `δz` of an absolute cochain, packaged as a **relative cocycle** when it
annihilates the subcomplex (the cocycle condition is `δ² = 0`). Integral mirror of
`SingularRelativeCohomDelta.deltaRelCocycle`. -/
def deltaRelCocycleInt {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    LinearMap.ker (relCoboundaryIntₗ S (n + 1)) :=
  ⟨⟨coboundaryₗ X n z, h⟩, LinearMap.mem_ker.mpr (Subtype.ext (by
    rw [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero]
    exact coboundary_comp_coboundary X n z))⟩

@[simp] theorem deltaRelCocycleInt_coe {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    ((deltaRelCocycleInt z h : LinearMap.ker (relCoboundaryIntₗ S (n + 1))) :
      SingularCochainInt X (n + 1)) = coboundaryₗ X n z := rfl

/-- **The integral δ-image class** `[δz] ∈ Hⁿ⁺¹(X,S;ℤ)` — the cohomology pair connecting-map image on
the annihilator model over `ℤ`. -/
def deltaRelHInt {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) : RelativeCohomologyInt S (n + 1) :=
  RelativeCohomologyInt.mk S (n + 1) (deltaRelCocycleInt z h)

/-! ## §2. Middle exactness `im ι* = ker δ` on the lift model -/

/-- **`im ι* ⊆ ker δ`** — an absolute cocycle's boundary class is `δ`-killed. If `z` is an absolute
cocycle (`δz = 0`, so trivially relative), its δ-image class vanishes. -/
theorem deltaRelHInt_of_cocycle_eq_zero {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) (hz : coboundaryₗ X n z = 0) :
    deltaRelHInt z h = 0 := by
  rw [deltaRelHInt, RelativeCohomologyInt.mk_eq_zero_iff,
    show (↑(deltaRelCocycleInt z h) : relCochainsInt S (n + 1)) = 0 from
      Subtype.ext (by rw [deltaRelCocycleInt_coe]; exact hz)]
  exact Submodule.zero_mem _

/-- **The pair-LES middle exactness `im ι* = ker δ`, on lifts.** The δ-image class `[δz]` vanishes
**iff** the lift `z` differs from an absolute cocycle by a relative cochain — i.e. iff the boundary
class `[z|∂W] ∈ Hⁿ(∂W;ℤ)` is the restriction `ι*` of an absolute class in `Hⁿ(W;ℤ)`. The `←`
direction is `im ι* ⊆ ker δ`; the `→` direction is the substantive `ker δ ⊆ im ι*` snake-chase. -/
theorem deltaRelHInt_eq_zero_iff {n : ℕ} (z : SingularCochainInt X n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    deltaRelHInt z h = 0 ↔
      ∃ z' : SingularCochainInt X n, coboundaryₗ X n z' = 0 ∧ z - z' ∈ relCochainsInt S n := by
  rw [deltaRelHInt, RelativeCohomologyInt.mk_eq_zero_iff]
  show (↑(deltaRelCocycleInt z h) : relCochainsInt S (n + 1)) ∈
      relCoboundaryRangeInt S (n + 1) ↔ _
  rw [show relCoboundaryRangeInt S (n + 1) = LinearMap.range (relCoboundaryIntₗ S n) from rfl,
    LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨z - (w : SingularCochainInt X n), ?_, ?_⟩
    · have hw' : coboundaryₗ X n (w : SingularCochainInt X n) = coboundaryₗ X n z := by
        have := Subtype.ext_iff.mp hw
        rwa [relCoboundaryIntₗ_coe, deltaRelCocycleInt_coe] at this
      rw [map_sub, hw', sub_self]
    · rw [sub_sub_cancel]
      exact w.2
  · rintro ⟨z', hz', hmem⟩
    refine ⟨⟨z - z', hmem⟩, ?_⟩
    apply Subtype.ext
    rw [relCoboundaryIntₗ_coe, deltaRelCocycleInt_coe]
    show coboundaryₗ X n (z - z') = coboundaryₗ X n z
    rw [map_sub, hz', sub_zero]

/-- A **relative** lift has vanishing δ-image class: if `z ∈ relCochainsInt S n`, then `[δz] = 0`
(take the absolute cocycle `0`; `z - 0 = z` is relative). The well-definedness engine — `δ` factors
through the restriction `z ↦ z|∂W`. -/
theorem deltaRelHInt_relCochain_eq_zero {n : ℕ} (z : SingularCochainInt X n)
    (hz : z ∈ relCochainsInt S n)
    (h : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    deltaRelHInt z h = 0 :=
  (deltaRelHInt_eq_zero_iff z h).mpr ⟨0, map_zero _, by rwa [sub_zero]⟩

end

end SKEFTHawking.SingularRelativeCohomDeltaInt
