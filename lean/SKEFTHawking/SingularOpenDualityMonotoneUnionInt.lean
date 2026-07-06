/-
# Phase 5q.H (E1 CSC-PD tower) — integral monotone-union stability of the open duality maps (§1–§2)

Integral (`ZMod 2 → ℤ`) mirror of `SingularOpenDualityMonotoneUnion` — the A3 block of the Bott–Tu-style
open-cover induction (Hatcher 3.36 (iii)): for an ℕ-indexed monotone family of opens `W 0 ⊆ W 1 ⊆ ⋯`, the
open PD map `D_{⋃W}` is bijective if every `D_{W n}` is. This module builds the compact-absorption (§1,
coefficient-free) and the compactly-supported cohomology exhaustion (§2). The homology exhaustion (§3) and
the generic payoff (§4) follow, then instantiate at `SingularOpenDualityInt.openDuality`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCSCOpenMonotoneInt

open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCSCOpenMonotoneInt

namespace SKEFTHawking.SingularOpenDualityMonotoneUnionInt

variable {X : TopCat} {W : ℕ → Set ↑X}

/-! ## §1. Compact absorption into a stage of the monotone tower (coefficient-free) -/

/-- Monotone-tower transport: `W a ⊆ W b` for `a ≤ b`. -/
theorem monotone_subset (hmono : ∀ n, W n ⊆ W (n + 1)) {a b : ℕ} (hab : a ≤ b) : W a ⊆ W b :=
  monotone_nat_of_le_succ hmono hab

/-- **Compact absorption**: a compact subset of the monotone union `⋃ i, W i` of opens lies in a single
stage `W n` (`IsCompact.elim_directed_cover`). -/
theorem exists_compact_subset_stage (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    {K : Set ↑X} (hK : IsCompact K) (hKW : K ⊆ ⋃ i, W i) : ∃ n, K ⊆ W n :=
  hK.elim_directed_cover W hopen hKW (monotone_nat_of_le_succ hmono).directed_le

/-- **Compact absorption, packaged for the `Hᵏ_c` index poset**. -/
theorem compactsIn_iUnion_absorb (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (K : CompactsIn (⋃ i, W i)) : ∃ n, (↑K.1 : Set ↑X) ⊆ W n :=
  exists_compact_subset_stage hmono hopen K.1.isCompact' K.2

/-! ## §2. Exhaustion of the integral compactly-supported cohomology `Hᵏ_c(Wu;ℤ)` -/

/-- **CSC exhaustion (surjectivity)**: every class of `Hᵏ_c(⋃ i, W i;ℤ)` is the `cscOpenMonotoneInt`
extension of a stage class — its `K`-stage compact is absorbed into a stage. -/
theorem cscOpen_iUnion_exhaustInt (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (k : ℕ) (ξ : CompactlySupportedCohomologyOpenInt (⋃ i, W i) k) :
    ∃ (n : ℕ) (β : CompactlySupportedCohomologyOpenInt (W n) k),
      cscOpenMonotoneInt (Set.subset_iUnion W n) k β = ξ := by
  refine Module.DirectLimit.induction_on ξ (fun K a => ?_)
  obtain ⟨n, hKn⟩ := compactsIn_iUnion_absorb hmono hopen K
  refine ⟨n, Module.DirectLimit.of ℤ (CompactsIn (W n)) (cohomGWInt (W n) k)
    (cohomFWInt (W n) k) ⟨K.1, hKn⟩ a, ?_⟩
  rw [cscOpenMonotoneInt_of]
  rfl

/-- **CSC vanishing stage (injectivity side)**: a stage class dying in `Hᵏ_c(⋃ i, W i;ℤ)` already dies at
a later stage `W m ⊇ W n` (`Module.DirectLimit.of.zero_exact` + compact absorption). -/
theorem cscOpen_iUnion_vanish_stageInt (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (k n : ℕ) (α : CompactlySupportedCohomologyOpenInt (W n) k)
    (h0 : cscOpenMonotoneInt (Set.subset_iUnion W n) k α = 0) :
    ∃ m, ∃ hnm : n ≤ m, cscOpenMonotoneInt (monotone_subset hmono hnm) k α = 0 := by
  induction α using Module.DirectLimit.induction_on with
  | _ K a =>
    rw [cscOpenMonotoneInt_of] at h0
    obtain ⟨K', hKK', hf0⟩ := Module.DirectLimit.of.zero_exact h0
    obtain ⟨m₀, hK'm⟩ := compactsIn_iUnion_absorb hmono hopen K'
    refine ⟨max n m₀, le_max_left n m₀, ?_⟩
    rw [cscOpenMonotoneInt_of]
    set Km : CompactsIn (W (max n m₀)) :=
      compactsInIncl (monotone_subset hmono (le_max_left n m₀)) K with hKm
    set Km' : CompactsIn (W (max n m₀)) :=
      ⟨K'.1, hK'm.trans (monotone_subset hmono (le_max_right n m₀))⟩ with hKm'
    have hle : Km ≤ Km' := hKK'
    have harg : cohomFWInt (W (max n m₀)) k Km Km' hle a = 0 := hf0
    have h1 : Module.DirectLimit.of ℤ (CompactsIn (W (max n m₀)))
        (cohomGWInt (W (max n m₀)) k) (cohomFWInt (W (max n m₀)) k) Km'
          (cohomFWInt (W (max n m₀)) k Km Km' hle a) = 0 := by
      rw [harg, map_zero]
    exact (Module.DirectLimit.of_f).symm.trans h1

end SKEFTHawking.SingularOpenDualityMonotoneUnionInt
