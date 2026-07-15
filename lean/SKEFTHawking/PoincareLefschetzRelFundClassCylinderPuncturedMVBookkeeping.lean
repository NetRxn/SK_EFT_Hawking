/-
# Phase 5q.H (W-A arm 4) — the relative-MV target DIMENSION bookkeeping (assembly prep)

Assembly prep for the terminal interior local-Künneth nonvanishing. With the two computable MV cover
pieces in hand — `puncU` (`…PuncturedPieceU`, `dim H_{k+2}(M×I, puncU) = dim H_{k+1}(M)`) and `puncV`
(`…PuncturedPieceIso`, `H_{m'+2}(M×I, puncV) ≅ ℤ/2`) — this module lays out the **dimension
bookkeeping** of the relative-MV LES around the target local homology `H_{k+1}(M×I, {x}ᶜ)`, WITHOUT
attempting the δ-image/subdivision computation itself (that, plus the top-degree vanishing
`H_{m'+3}(M, M∖σ) = 0`, is the residual left to the δ-closer).

The LES segment (`…PuncturedCover.puncMv_exact_sum`) is exact at the target
`T = H_{k+1}(M×I, puncU ∪ puncV) = H_{k+1}(M×I, {x}ᶜ)`:

  `H_{k+1}(M×I,U) ⊕ H_{k+1}(M×I,V) —[j = relMvHomSum]→ T —[δ = puncMvDelta]→ H_k(M×I, U∩V)`,

so, over the field `ℤ/2` (rank–nullity + exactness `range j = ker δ`),

  `dim T = dim(range j) + dim(range δ)`.

This decomposes the target's dimension into the **flank contribution** `range j` (fed by the two
piece dimensions `dim H_{k+1}(M×I,U)` = puncU, `dim H_{k+1}(M×I,V)` = puncV) and the **δ-image**
`range δ` into the overlap `H_k(M×I, (M∖σ)×(I∖t))` — pinning exactly where the prism class must live
to survive (in `range δ`, since the flank `j`-image is spanned by the piece classes). The closer's
sole remaining job is the δ-image: that the prism of a chart-local generator lands nonzero in the
overlap homology.

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the general exact-segment rank engine** `finrank_of_exact_segment`: for `Function.Exact f g`
  over a field with the middle finite-dimensional, `dim B = dim(range f) + dim(range g)`. Reusable.
* **§2 — the MV target decomposition** `puncMv_target_finrank_decomp` and the flank bound
  `puncMv_target_finrank_le`: `dim H_{k+1}(M×I,{x}ᶜ) ≤ dim H_{k+1}(M×I,U) + dim H_{k+1}(M×I,V)
  + dim(range δ)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedMVBookkeeping

noncomputable section

/-! ## §1. The general exact-segment rank engine -/

/-- **Exact-segment rank decomposition.** For a segment `A —f→ B —g→ C` of a long exact sequence
(`Function.Exact f g`, i.e. `range f = ker g`) over the field `ℤ/2`, with the middle term `B`
finite-dimensional, rank–nullity on `g` plus exactness gives `dim B = dim(range f) + dim(range g)`.
The reusable engine for LES dimension bookkeeping. -/
theorem finrank_of_exact_segment {A B C : Type*}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup B] [Module (ZMod 2) B]
    [AddCommGroup C] [Module (ZMod 2) C] [FiniteDimensional (ZMod 2) B]
    {f : A →ₗ[ZMod 2] B} {g : B →ₗ[ZMod 2] C} (h : Function.Exact f g) :
    Module.finrank (ZMod 2) B
      = Module.finrank (ZMod 2) (LinearMap.range f) + Module.finrank (ZMod 2) (LinearMap.range g) := by
  have hF := LinearMap.finrank_range_add_finrank_ker g
  have hk : Module.finrank (ZMod 2) (LinearMap.ker g)
      = Module.finrank (ZMod 2) (LinearMap.range f) := by rw [h.linearMap_ker_eq]
  omega

/-! ## §2. The relative-MV target dimension decomposition -/

variable {N : TopCat}

/-- **The MV target dimension decomposition** at the punctured-product cover. The relative-MV LES is
exact at the target `T = H_{k+1}(M×I, puncU ∪ puncV) = H_{k+1}(M×I, {x}ᶜ)`
(`puncMv_exact_sum`), so `dim T = dim(range relMvHomSum) + dim(range puncMvDelta)` — the flank image
(from the two pieces) plus the δ-image (into the overlap). This is the LES dimension bookkeeping the
δ-closer plugs the piece dimensions and δ-image into. -/
theorem puncMv_target_finrank_decomp [T1Space ↑N] (x : ↑(cyl N)) (k : ℕ)
    [FiniteDimensional (ZMod 2) (RelativeHomology (puncU x ∪ puncV x) (k + 1))] :
    Module.finrank (ZMod 2) (RelativeHomology (puncU x ∪ puncV x) (k + 1))
      = Module.finrank (ZMod 2) (LinearMap.range (relMvHomSum (puncU x) (puncV x) (k + 1)))
        + Module.finrank (ZMod 2) (LinearMap.range (puncMvDelta x k)) :=
  finrank_of_exact_segment (puncMv_exact_sum x k)

/-- **The MV target flank bound.** Bounding the flank image `range relMvHomSum` by its domain
`H_{k+1}(M×I,U) ⊕ H_{k+1}(M×I,V)` gives
`dim H_{k+1}(M×I,{x}ᶜ) ≤ dim H_{k+1}(M×I,puncU) + dim H_{k+1}(M×I,puncV) + dim(range δ)`. The target's
dimension is controlled by the two computed pieces (`…PuncturedPieceU`/`…PuncturedPieceIso`) plus the
δ-image into the overlap — the sole residual. -/
theorem puncMv_target_finrank_le [T1Space ↑N] (x : ↑(cyl N)) (k : ℕ)
    [FiniteDimensional (ZMod 2) (RelativeHomology (puncU x ∪ puncV x) (k + 1))]
    [FiniteDimensional (ZMod 2) (RelativeHomology (puncU x) (k + 1))]
    [FiniteDimensional (ZMod 2) (RelativeHomology (puncV x) (k + 1))] :
    Module.finrank (ZMod 2) (RelativeHomology (puncU x ∪ puncV x) (k + 1))
      ≤ Module.finrank (ZMod 2) (RelativeHomology (puncU x) (k + 1))
        + Module.finrank (ZMod 2) (RelativeHomology (puncV x) (k + 1))
        + Module.finrank (ZMod 2) (LinearMap.range (puncMvDelta x k)) := by
  rw [puncMv_target_finrank_decomp x k]
  have hle : Module.finrank (ZMod 2) (LinearMap.range (relMvHomSum (puncU x) (puncV x) (k + 1)))
      ≤ Module.finrank (ZMod 2)
        (RelativeHomology (puncU x) (k + 1) × RelativeHomology (puncV x) (k + 1)) :=
    LinearMap.finrank_range_le _
  rw [Module.finrank_prod] at hle
  omega

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedMVBookkeeping
