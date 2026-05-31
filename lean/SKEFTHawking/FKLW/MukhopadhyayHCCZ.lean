/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x′ Phase 2 (D) — `hCCZ`: one CCZ raises the channel-rep `sde₂` by at most one

The `hCCZ` bridge of the parametric Toffoli bound, for `μ = channelSde2 = matrixSde2 ∘ channelRep`. By
Theorem 3.8 (`channelRep_CCZ_isHalfInt`) every entry of `Ĉ_CCZ` is `(integer)/2`, so each entry of
`Ĉ_CCZ · X` is `(1/2)·(integer combination of X's entries)` — and an integer combination of dyadic
rationals does not raise `sde₂`, while the `÷2` adds at most one. Hence
`matrixSde2(Ĉ_CCZ · channelRep M) ≤ matrixSde2(channelRep M) + 1`.

The bound is **conditional on `channelRep M` having rational entries** (`IsRatℂ`): a universal ℂ bound is
false (cancellation of irrational parts can leave a high-exponent dyadic residue). Lemma 3.10 (next
increment) supplies this rationality for the Clifford+CCZ words where `hCCZ` is actually applied, keeping
the final headline unconditional.

This file ships the `sde₂` arithmetic layer (`sde2`/`sde2ℂ` under integer-scaling, addition, `÷2`, and
finite sums) and the dyadic-conditional `channelSde2_ccz_le` (`hCCZ`).

PUBLIC math layer only.

## Pipeline invariants
- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected. Kernel-pure.

-/

import SKEFTHawking.FKLW.MukhopadhyayMatrixSde2
import SKEFTHawking.FKLW.MukhopadhyayCCZChannelRep
import SKEFTHawking.FKLW.MukhopadhyayToffoliBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SKEFTHawking.FKLW.MukhopadhyayCCZ

open scoped Matrix
open SKEFTHawking.FKLW.CliffordCCZ (CCZ_mat)

/-! ## D.1 — `sde₂` arithmetic on ℚ -/

/-- `sde₂` is sub-additive in the max sense: `sde₂(p+q) ≤ max (sde₂ p) (sde₂ q)` (non-archimedean). -/
theorem sde2_add_le (p q : ℚ) : sde2 (p + q) ≤ max (sde2 p) (sde2 q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases eq_or_ne (p + q) 0 with h | h
  · simp [h]
  · rw [sde2_le_iff]
    have hp : -(sde2 p : ℤ) ≤ padicValRat 2 p := sde2_le_iff.mp le_rfl
    have hq : -(sde2 q : ℤ) ≤ padicValRat 2 q := sde2_le_iff.mp le_rfl
    have hmin : min (padicValRat 2 p) (padicValRat 2 q) ≤ padicValRat 2 (p + q) :=
      padicValRat.min_le_padicValRat_add h
    have hcast : -((max (sde2 p) (sde2 q) : ℕ) : ℤ) = min (-(sde2 p : ℤ)) (-(sde2 q : ℤ)) := by
      push_cast; omega
    rw [hcast]
    exact le_trans (min_le_min hp hq) hmin

/-- Integer scaling does not raise `sde₂`: `sde₂((a:ℚ)·q) ≤ sde₂ q`. -/
theorem sde2_int_mul_le (a : ℤ) (q : ℚ) : sde2 ((a : ℚ) * q) ≤ sde2 q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases eq_or_ne ((a : ℚ) * q) 0 with h | h
  · simp [h]
  · have ha : (a : ℚ) ≠ 0 := left_ne_zero_of_mul h
    have hq : q ≠ 0 := right_ne_zero_of_mul h
    rw [sde2_le_iff, padicValRat.mul ha hq, padicValRat.of_int]
    have hq' : -(sde2 q : ℤ) ≤ padicValRat 2 q := sde2_le_iff.mp le_rfl
    have hnn : (0 : ℤ) ≤ (padicValInt 2 a : ℤ) := Int.natCast_nonneg _
    omega

/-- Halving raises `sde₂` by at most one: `sde₂(q/2) ≤ sde₂ q + 1`. -/
theorem sde2_div_two_le (q : ℚ) : sde2 (q / 2) ≤ sde2 q + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases eq_or_ne q 0 with h | h
  · simp [h]
  · have h2 : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
    rw [sde2_le_iff, padicValRat.div h (by norm_num), h2]
    have hq' : -(sde2 q : ℤ) ≤ padicValRat 2 q := sde2_le_iff.mp le_rfl
    push_cast
    omega

/-! ## D.2 — rational scalars (`IsRatℂ`) and `sde₂` on ℂ -/

/-- `z` is the image of a rational. -/
def IsRatℂ (z : ℂ) : Prop := ∃ q : ℚ, (q : ℂ) = z

theorem isRatℂ_zero : IsRatℂ 0 := ⟨0, by simp⟩

theorem isRatℂ_add {z w : ℂ} (hz : IsRatℂ z) (hw : IsRatℂ w) : IsRatℂ (z + w) := by
  obtain ⟨p, rfl⟩ := hz; obtain ⟨q, rfl⟩ := hw
  exact ⟨p + q, by push_cast; ring⟩

theorem isRatℂ_intCast_mul (a : ℤ) {z : ℂ} (hz : IsRatℂ z) : IsRatℂ ((a : ℂ) * z) := by
  obtain ⟨q, rfl⟩ := hz
  exact ⟨a * q, by push_cast; ring⟩

theorem isRatℂ_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, IsRatℂ (f i)) :
    IsRatℂ (∑ i ∈ s, f i) :=
  Finset.sum_induction f IsRatℂ (fun _ _ h1 h2 => isRatℂ_add h1 h2) isRatℂ_zero hf

theorem sde2ℂ_add_le {z w : ℂ} (hz : IsRatℂ z) (hw : IsRatℂ w) :
    sde2ℂ (z + w) ≤ max (sde2ℂ z) (sde2ℂ w) := by
  obtain ⟨p, rfl⟩ := hz; obtain ⟨q, rfl⟩ := hw
  rw [show (p : ℂ) + (q : ℂ) = ((p + q : ℚ) : ℂ) from by push_cast; ring, sde2ℂ_ratCast,
    sde2ℂ_ratCast, sde2ℂ_ratCast]
  exact sde2_add_le p q

theorem sde2ℂ_intCast_mul_le (a : ℤ) {z : ℂ} (hz : IsRatℂ z) : sde2ℂ ((a : ℂ) * z) ≤ sde2ℂ z := by
  obtain ⟨q, rfl⟩ := hz
  rw [show (a : ℂ) * (q : ℂ) = (((a : ℚ) * q : ℚ) : ℂ) from by push_cast; ring, sde2ℂ_ratCast,
    sde2ℂ_ratCast]
  exact sde2_int_mul_le a q

theorem sde2ℂ_div_two_le {z : ℂ} (hz : IsRatℂ z) : sde2ℂ (z / 2) ≤ sde2ℂ z + 1 := by
  obtain ⟨q, rfl⟩ := hz
  rw [show (q : ℂ) / 2 = ((q / 2 : ℚ) : ℂ) from by push_cast; ring, sde2ℂ_ratCast, sde2ℂ_ratCast]
  exact sde2_div_two_le q

theorem sde2ℂ_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, IsRatℂ (f i)) :
    sde2ℂ (∑ i ∈ s, f i) ≤ s.sup (fun i => sde2ℂ (f i)) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    have hfa := hf a (Finset.mem_insert_self a t)
    have hft : ∀ i ∈ t, IsRatℂ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact le_trans (sde2ℂ_add_le hfa (isRatℂ_sum t f hft)) (max_le_max le_rfl (ih hft))

/-! ## D.3 — `hCCZ` (dyadic-conditional) -/

/-- **`hCCZ`**: for `M` whose channel rep has rational entries (supplied by Lemma 3.10 for Clifford+CCZ
words), one `CCZ` raises the channel-rep `sde₂` measure by at most one. -/
theorem channelSde2_ccz_le (M : Matrix (Fin 8) (Fin 8) ℂ)
    (hM : ∀ t s, IsRatℂ (channelRep M t s)) :
    channelSde2 (CCZ_mat * M) ≤ channelSde2 M + 1 := by
  rw [channelSde2, channelSde2, channelRep_mul]
  obtain ⟨a, ha⟩ : ∃ a : (Fin 4 × Fin 4 × Fin 4) → (Fin 4 × Fin 4 × Fin 4) → ℤ,
      ∀ r t, channelRep CCZ_mat r t = (a r t : ℂ) / 2 := by
    choose a ha using channelRep_CCZ_isHalfInt
    exact ⟨a, ha⟩
  refine Finset.sup_le fun r _ => Finset.sup_le fun s _ => ?_
  have hentry : (channelRep CCZ_mat * channelRep M) r s
      = (∑ t, (a r t : ℂ) * channelRep M t s) / 2 := by
    rw [Matrix.mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ha r t]; ring
  rw [hentry]
  have hrat : ∀ t ∈ (Finset.univ : Finset (Fin 4 × Fin 4 × Fin 4)),
      IsRatℂ ((a r t : ℂ) * channelRep M t s) :=
    fun t _ => isRatℂ_intCast_mul (a r t) (hM t s)
  calc sde2ℂ ((∑ t, (a r t : ℂ) * channelRep M t s) / 2)
      ≤ sde2ℂ (∑ t, (a r t : ℂ) * channelRep M t s) + 1 :=
        sde2ℂ_div_two_le (isRatℂ_sum _ _ hrat)
    _ ≤ (Finset.univ.sup fun t => sde2ℂ ((a r t : ℂ) * channelRep M t s)) + 1 :=
        Nat.add_le_add_right (sde2ℂ_sum_le _ _ hrat) 1
    _ ≤ matrixSde2 (channelRep M) + 1 := by
        refine Nat.add_le_add_right (Finset.sup_le fun t _ => ?_) 1
        exact le_trans (sde2ℂ_intCast_mul_le (a r t) (hM t s))
          (sde2ℂ_le_matrixSde2 (channelRep M) t s)

end SKEFTHawking.FKLW.MukhopadhyayCCZ
