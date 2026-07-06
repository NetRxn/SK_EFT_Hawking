/-
# Phase 5q.H (E1 CSC-PD tower) — integral `legW₀`/`openDuality₀` (bottom `H₀`-valued duality), §1–§2

Integral (`ZMod 2 → ℤ`) mirror of `SingularOpenDualityBot`. The bottom (`H₀`-valued) analogue of
`legW`/`openDuality`, built on the on-main integral d=0 local duality `SingularLocalDualityKBotInt`
(`relativeDualityK₀Int`). Needed for the binary-cover five-lemma of the integral PD cover-induction
(the connecting square's `U∩V` side lands in `openDuality₀`).

This module: §1 the `castChainInt`-headed transport helpers (`subst`-liners) + §2 the bottom-presented
fundamental cycle `fundCycleW₀Int` (the `(k,0)`-instance of `fundCycleW`, recast to the `(k+1)`-spelling).
§3 (the bottom `relativeDualityK₀Int` restrict/cycle-compat — TORSION-SAFE, ℤ-difference form, NOT the
mod-2 `add_self`/`neg_eq_self` route) + §4 (`legW₀Int`/`openDuality₀Int`) follow.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityCycleInt
import SKEFTHawking.SingularOpenDualityMVConnSquareInt
import SKEFTHawking.SingularLocalDualityKBotInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularOpenDualityCycleInt
open SKEFTHawking.SingularOpenDualityMVConnSquareInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularOpenDualityBotInt

variable {X : TopCat}

/-! ## §1. `castChainInt`-headed transport helpers (generic `subst`-liners) -/

private theorem castChainInt_mem_subspaceChainsInt {a b : ℕ} (e : a = b) {S : Set ↑X}
    {c : SingularChainInt X a} (hc : c ∈ subspaceChainsInt S a) :
    castChainInt e c ∈ subspaceChainsInt S b := by
  subst e; rw [castChainInt_eq]; exact hc

private theorem chainBoundary_castChainInt {a b : ℕ} (e : a + 1 = b + 1) (e' : a = b)
    (c : SingularChainInt X (a + 1)) :
    chainBoundary X b (castChainInt e c) = castChainInt e' (chainBoundary X a c) := by
  subst e'; rw [castChainInt_eq, castChainInt_eq]

/-- The ℤ-difference form of the `relB` transport (the general integral family uses the honest
`RelativeChainInt.mk`-difference, not the mod-2 `coprod`-sum). -/
private theorem relB_pair_castChainInt {a b : ℕ} (e : a = b) {S : Set ↑X}
    (x y : SingularChainInt X a)
    (h : RelativeChainInt.mk S a x - RelativeChainInt.mk S a y ∈ relBoundariesInt S a) :
    RelativeChainInt.mk S b (castChainInt e x) - RelativeChainInt.mk S b (castChainInt e y)
      ∈ relBoundariesInt S b := by
  subst e; rw [castChainInt_eq, castChainInt_eq]; exact h

/-! ## §2. The bottom-presented fundamental cycle (single-choice: the `(k, 0)`-instance recast) -/

/-- The `(k, 0)`-instance of the integral `fundCycleW` (the SAME `.choose`), presented at the clean
`(k+1)`-spelling through `castChainInt`. -/
noncomputable def fundCycleW₀Int [T2Space ↑X] {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    SingularChainInt X (k + 1) :=
  castChainInt rfl (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)

theorem fundCycleW₀Int_mem_W [T2Space ↑X] {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    fundCycleW₀Int hW z₀ hz₀ K ∈ subspaceChainsInt W (k + 1) :=
  castChainInt_mem_subspaceChainsInt (a := k + 0 + 1) (b := k + 1) rfl
    (fundCycleW_mem_W (k := k) (m := 0) hW z₀ hz₀ K)

theorem fundCycleW₀Int_boundary [T2Space ↑X] {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    chainBoundary X k (fundCycleW₀Int hW z₀ hz₀ K) ∈ subspaceChainsInt ((↑K.1 : Set ↑X)ᶜ) k := by
  rw [fundCycleW₀Int, chainBoundary_castChainInt (a := k + 0) (b := k) rfl rfl]
  exact castChainInt_mem_subspaceChainsInt (a := k + 0) (b := k) rfl
    (fundCycleW_boundary (k := k) (m := 0) hW z₀ hz₀ K)

end SKEFTHawking.SingularOpenDualityBotInt
