/-
# Phase 5q.H (E1 CSC-PD tower) — the integral `H₀` Mayer–Vietoris end exactness

Integral (`ZMod 2 → ℤ`) mirror of `SingularSubHomSumEnd`. The degree-`0` end of the homology MV ladder:
`subHomSumInt U V 0 : H₀(sub U;ℤ) × H₀(sub V;ℤ) → H₀(sub (U∪V);ℤ)` is **surjective**. Every `0`-chain is a
cycle (`cycles _ 0 = ⊤`); a `0`-simplex is the constant simplex at its point, which lies in `U` or `V`, so
each generator lifts along `homOfSubsetInt`. This is the `H₀` end (`hg₂`) the integral PD D⁰ five-lemma needs.

**The one ℤ-vs-mod-2 divergence:** `subHomSumInt` is the honest DIFFERENCE `homOfSubsetInt(fst) −
homOfSubsetInt(snd)`, so the V-case witness carries a real sign — `(0, −class)` (via `map_neg`/`neg_neg`),
NOT the mod-2 `-1 = 1` collapse.

The simplex-level lemmas (`simplexPoint`, `eq_constSimplex`, `constSimplex`, `mapSimplex_constSimplex`) are
coefficient-agnostic and reused from the mod-2 modules.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityMVSquareInt
import SKEFTHawking.SingularSubHomSumEnd

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularSubsetHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)
open SKEFTHawking.SingularH0PathConnected
open SKEFTHawking.SingularSubHomSumEnd (mapSimplex_constSimplex)
open SKEFTHawking.SingularOpenDualityMVSquareInt

namespace SKEFTHawking.SingularSubHomSumEndInt

variable {X : TopCat}

/-! ## §1. Degree-`0` integral homology classes of arbitrary `0`-chains -/

/-- The degree-`0` integral homology class of an arbitrary `0`-chain (`cycles _ 0 = ⊤`). -/
noncomputable def h0ClassInt (Y : TopCat) (c : SingularChainInt Y 0) : Homology Y 0 :=
  Homology.mk Y 0 ⟨c, Submodule.mem_top⟩

theorem h0ClassInt_zero (Y : TopCat) : h0ClassInt Y 0 = 0 := by
  rw [h0ClassInt, show (⟨0, Submodule.mem_top⟩ : cycles Y 0) = 0 from Subtype.ext rfl]
  exact Submodule.Quotient.mk_zero _

theorem h0ClassInt_add (Y : TopCat) (c d : SingularChainInt Y 0) :
    h0ClassInt Y (c + d) = h0ClassInt Y c + h0ClassInt Y d := by
  rw [h0ClassInt, h0ClassInt, h0ClassInt, show (⟨c + d, Submodule.mem_top⟩ : cycles Y 0)
    = ⟨c, Submodule.mem_top⟩ + ⟨d, Submodule.mem_top⟩ from Subtype.ext rfl]
  exact Submodule.Quotient.mk_add _

theorem h0ClassInt_surjective (Y : TopCat) (y : Homology Y 0) : ∃ c, h0ClassInt Y c = y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨z.1, congrArg (Homology.mk Y 0) (Subtype.ext rfl)⟩

/-- **`homOfSubsetInt` computes on `h0ClassInt` by the chain-level pushforward**. -/
theorem homOfSubsetInt_h0ClassInt {K K' : Set ↑X} (h : K ⊆ K') (c : SingularChainInt (sub K) 0) :
    homOfSubsetInt h 0 (h0ClassInt (sub K) c) = h0ClassInt (sub K') (mapChainInt (subInclCM h) 0 c) := by
  rw [h0ClassInt, h0ClassInt, homOfSubsetInt, Homology.mapInt_mk]
  exact congrArg (Homology.mk (sub K') 0) (Subtype.ext rfl)

/-! ## §2. Lifting `0`-simplices across the cover -/

/-- **Every degree-`0` generator of `H₀(sub (U∪V);ℤ)` lifts across the cover**. The V-case carries the
honest ℤ sign (`(0, −class)`). -/
theorem h0ClassInt_single_mem_range (U V : Set ↑X)
    (σ : (TopCat.toSSet.obj (sub (U ∪ V))).obj (op (SimplexCategory.mk 0))) (a : ℤ) :
    h0ClassInt (sub (U ∪ V)) (Finsupp.single σ a) ∈ LinearMap.range (subHomSumInt U V 0) := by
  rcases (simplexPoint σ).2 with hpU | hpV
  · refine ⟨(h0ClassInt (sub U)
      (Finsupp.single (constSimplex (⟨(simplexPoint σ).1, hpU⟩ : ↥U) 0) a), 0), ?_⟩
    rw [subHomSumInt, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, map_zero, sub_zero, homOfSubsetInt_h0ClassInt,
      mapChainInt_single, mapSimplex_constSimplex]
    exact congrArg (fun τ => h0ClassInt (sub (U ∪ V)) (Finsupp.single τ a)) (eq_constSimplex σ).symm
  · refine ⟨(0, -(h0ClassInt (sub V)
      (Finsupp.single (constSimplex (⟨(simplexPoint σ).1, hpV⟩ : ↥V) 0) a))), ?_⟩
    rw [subHomSumInt, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, map_zero, zero_sub, map_neg, neg_neg,
      homOfSubsetInt_h0ClassInt, mapChainInt_single, mapSimplex_constSimplex]
    exact congrArg (fun τ => h0ClassInt (sub (U ∪ V)) (Finsupp.single τ a)) (eq_constSimplex σ).symm

/-! ## §3. The `H₀` MV end exactness -/

/-- **The integral `H₀` Mayer–Vietoris end exactness**: `subHomSumInt U V 0` is surjective. -/
theorem subHomSumInt_zero_surjective (U V : Set ↑X) :
    Function.Surjective (subHomSumInt U V 0) := by
  intro y
  obtain ⟨c, rfl⟩ := h0ClassInt_surjective (sub (U ∪ V)) y
  suffices hmem : h0ClassInt (sub (U ∪ V)) c ∈ LinearMap.range (subHomSumInt U V 0) from hmem
  induction c using Finsupp.induction_linear with
  | zero => rw [h0ClassInt_zero]; exact zero_mem _
  | add c d hc hd => rw [h0ClassInt_add]; exact add_mem hc hd
  | single σ a => exact h0ClassInt_single_mem_range U V σ a

end SKEFTHawking.SingularSubHomSumEndInt
