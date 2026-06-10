/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increments 32–33) — `ReductionStep` discharged + the unconditional dim-4 column lemma

The capstone of the circuit-`C` synthesis program (inc 10–31). The single remaining brick of the
dim-4 Giles–Selinger column lemma was the reduction step (`ReductionStep C`, inc 15): every unit
column with positive `colDenExp` factors through a realizable gate with strictly smaller
`colDenExp`. This file discharges it and assembles the column lemma, quantitatively.

## Mechanism (Giles–Selinger 1212.0506, Lemma 5 + Lemma 4)

At the top level `t+1`, an entry is *active* iff its numerator is not `√2`-divisible
(`denExp_mk_succ_eq_iff`). The unit condition forces the numerator `normSq`-sum to be `2^(t+1)`
(`numerator_sum_of_unit`), whose `c`/`d` coordinates are even — so any active entry has a
matched-active partner (`exists_matching_residue_pair`, inc 21 = Lemma 5), and the matched pair
drops one level under a realizable gadget (`exists_pair_drop`, inc 31 = Lemma 4). Each application
strictly shrinks the active set (spectators keep their `denExp`; the pair leaves the top level), so
at most 4 rounds clear the level: `ReductionStep 280` holds **unconditionally**.

## Headline theorems

  * `reductionStep_holds : ReductionStep 280` — the inc-15 brick, discharged.
  * `column_lemma_bounded` — **the quantitative dim-4 column lemma**: every unit column `v` is
    column-realizable within `280 · colDenExp v + 9` `Gate2` gates — the `O(denominator exponent)`
    = `O(log 1/ε)` gate count the KMM headline consumes.
  * `column_lemma_unconditional` — the existential form (every unit column is the first column of
    an exact two-qubit Clifford+T word).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.GilesSelingerPairDrop
import SKEFTHawking.FKLW.RossSelinger.GilesSelingerResidue
import SKEFTHawking.FKLW.RossSelinger.ColumnBaseRealizable

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-! ### The numerator-sum bridge -/

namespace ZOmega

/-- Coordinates of integer powers of two in `ℤ[ω]`: `(2^n).c = 0` and `(2^n).d = 2^n`. -/
theorem two_pow_coords (n : ℕ) : ((2 : ZOmega) ^ n).c = 0 ∧ ((2 : ZOmega) ^ n).d = 2 ^ n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [pow_succ, mul_two]
    refine ⟨?_, ?_⟩
    · rw [add_c, ih.1, add_zero]
    · rw [add_d, ih.2, pow_succ]
      ring

end ZOmega

namespace ZOmegaSqrt2

/-- Finite `mk`-sums over the 4 column indices collapse to a single `mk`. -/
theorem mk_sum_col (f : Fin 2 × Fin 2 → ZOmega) (K : ℕ) :
    ∑ i, mk (f i) K = mk (∑ i, f i) K := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [mk_add_same, mk_add_same, mk_add_same]

/-- **The numerator-sum bridge**: a unit column presented at level `t+1` has numerator
`normSq`-sum exactly `2^(t+1)` — the integer identity the Lemma-5 parity argument consumes. -/
theorem numerator_sum_of_unit {t : ℕ} {v : Fin 2 × Fin 2 → ZOmegaSqrt2}
    {w : Fin 2 × Fin 2 → ZOmega} (hv : ∀ i, v i = mk (w i) (t + 1))
    (hunit : ∑ i, normSq (v i) = 1) :
    ∑ i, ZOmega.normSq (w i) = 2 ^ (t + 1) := by
  have h1 : mk (∑ i, ZOmega.normSq (w i)) (2 * (t + 1)) = 1 := by
    rw [← mk_sum_col]
    rw [show (∑ i, mk (ZOmega.normSq (w i)) (2 * (t + 1))) = ∑ i, normSq (v i) from
      Finset.sum_congr rfl fun i _ => by rw [hv i, normSq_mk]]
    exact hunit
  have h2 : (∑ i, ZOmega.normSq (w i)) * ZOmega.sqrt2 ^ 0 =
      1 * ZOmega.sqrt2 ^ (2 * (t + 1)) := by
    rw [← mk_eq_mk_iff]
    exact h1.trans of_one.symm
  rw [pow_zero, mul_one, one_mul, pow_mul, show ZOmega.sqrt2 ^ 2 = 2 from by
    rw [pow_two]; exact ZOmega.sqrt2_sq] at h2
  exact h2

end ZOmegaSqrt2

/-! ### The reduction step, discharged -/

namespace Gate2

open ZOmegaSqrt2

/-- **Active-set descent**: a unit column presented at level `t+1` with at most `n` active entries
factors as `g · v'` with `g` realizable within `70·n` and `v'` a unit column entirely at
`denExp ≤ t`. Induction: each `exists_pair_drop` round removes a matched-active pair (spectators
keep their `denExp`), so the active count strictly decreases. -/
theorem drop_all_actives {t : ℕ} :
    ∀ (n : ℕ) (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (w : Fin 2 × Fin 2 → ZOmega),
      (∀ i, v i = mk (w i) (t + 1)) → (∑ i, normSq (v i) = 1) →
      (Finset.univ.filter fun i => denExp (v i) = t + 1).card ≤ n →
      ∃ (g : Mat4) (v' : Fin 2 × Fin 2 → ZOmegaSqrt2),
        IsRealizableWithin g (70 * n) ∧ v = g.mulVec v' ∧ (∑ i, normSq (v' i) = 1) ∧
        ∀ i, denExp (v' i) ≤ t := by
  intro n
  induction n with
  | zero =>
    intro v w hv hunit hcard
    refine ⟨1, v, ⟨[], interp2_nil, by simp⟩, (Matrix.one_mulVec v).symm, hunit, fun i => ?_⟩
    have hle : denExp (v i) ≤ t + 1 := by
      rw [hv i, denExp_mk]
      exact ZOmega.lowestDenExp_le _ _
    have hne : denExp (v i) ≠ t + 1 := by
      intro h
      have hmem : i ∈ Finset.univ.filter fun j => denExp (v j) = t + 1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have := Finset.card_pos.mpr ⟨i, hmem⟩
      omega
    omega
  | succ n ih =>
    intro v w hv hunit hcard
    by_cases hzero : (Finset.univ.filter fun i => denExp (v i) = t + 1).card = 0
    · obtain ⟨g, v', hg, hfac, hu, hd⟩ := ih v w hv hunit (by omega)
      exact ⟨g, v', hg.mono (by omega), hfac, hu, hd⟩
    · -- an active entry exists
      obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
      have hi₀' : denExp (v i₀) = t + 1 := (Finset.mem_filter.mp hi₀).2
      have hwact : ¬ ZOmega.dividesSqrt2 (w i₀) := by
        rw [hv i₀] at hi₀'
        exact denExp_mk_succ_eq_iff.mp hi₀'
      -- the matched partner (Lemma 5)
      have hnum : ∑ i, ZOmega.normSq (w i) = 2 ^ (t + 1) := numerator_sum_of_unit hv hunit
      have hc0 : (∑ i, ZOmega.normSq (w i)).c % 2 = 0 := by
        rw [hnum, (ZOmega.two_pow_coords (t + 1)).1]
        decide
      have hd0 : (∑ i, ZOmega.normSq (w i)).d % 2 = 0 := by
        rw [hnum, (ZOmega.two_pow_coords (t + 1)).2]
        have h2 : (2 : ℤ) ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; ring
        omega
      obtain ⟨pi, pj, hij, hcm, hdm, hpact⟩ :=
        ZOmega.exists_matching_residue_pair hc0 hd0 hwact
      have hqact : ¬ ZOmega.dividesSqrt2 (w pj) := fun hdvd => by
        rw [ZOmega.dividesSqrt2_iff_normSq_cd_even (w pj)] at hdvd
        exact hpact ((ZOmega.dividesSqrt2_iff_normSq_cd_even (w pi)).mpr ⟨by omega, by omega⟩)
      -- the pair drop (Lemma 4)
      obtain ⟨G, Ginv, hG, hGinv, hGG, hdp, hdq, hspec, hsum⟩ :=
        exists_pair_drop v w hv hij hpact hqact hcm hdm
      -- the new column stays at level ≤ t+1, is unit, and has strictly fewer actives
      have hvle : ∀ i, denExp (v i) ≤ t + 1 := fun i => by
        rw [hv i, denExp_mk]
        exact ZOmega.lowestDenExp_le _ _
      have hle'' : ∀ i, denExp (G.mulVec v i) ≤ t + 1 := by
        intro i
        by_cases hip : i = pi
        · subst hip; omega
        by_cases hiq : i = pj
        · subst hiq; omega
        rw [hspec i hip hiq]
        exact hvle i
      choose w'' hw'' using fun i => eq_mk_of_denExp_le (hle'' i)
      have hunit'' : ∑ i, normSq (G.mulVec v i) = 1 := hsum.trans hunit
      have hpimem : pi ∈ Finset.univ.filter fun i => denExp (v i) = t + 1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [hv pi]
          exact denExp_mk_succ_eq_iff.mpr hpact⟩
      have hsub : (Finset.univ.filter fun i => denExp (G.mulVec v i) = t + 1)
          ⊆ (Finset.univ.filter fun i => denExp (v i) = t + 1).erase pi := by
        intro x hx
        have hx' : denExp (G.mulVec v x) = t + 1 := (Finset.mem_filter.mp hx).2
        have hxp : x ≠ pi := fun h => by subst h; omega
        have hxq : x ≠ pj := fun h => by subst h; omega
        refine Finset.mem_erase.mpr ⟨hxp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        rw [← hspec x hxp hxq]
        exact hx'
      have hcard'' : (Finset.univ.filter fun i => denExp (G.mulVec v i) = t + 1).card ≤ n := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hpimem] at h1
        omega
      -- recurse and reassemble
      obtain ⟨g', v', hg', hfac', hu', hd'⟩ := ih (G.mulVec v) w'' hw'' hunit'' hcard''
      refine ⟨Ginv * g', v', (hGinv.mul hg').mono (by omega), ?_, hu', hd'⟩
      have h1 : Ginv.mulVec (G.mulVec v) = v := by
        rw [Matrix.mulVec_mulVec v Ginv G]
        exact (congrArg (fun M : Mat4 => M.mulVec v) hGG).trans (Matrix.one_mulVec v)
      rw [hfac'] at h1
      exact h1.symm.trans (Matrix.mulVec_mulVec v' Ginv g')

/-- **`ReductionStep 280` holds unconditionally** — the single brick `colLemma_of_reductionStep`
(inc 15) was waiting for: every unit column with positive `colDenExp` factors through a realizable
gate (within 280) with strictly smaller `colDenExp`. -/
theorem reductionStep_holds : ReductionStep 280 := by
  intro v hunit hpos
  obtain ⟨t, ht⟩ : ∃ t, colDenExp v = t + 1 := ⟨colDenExp v - 1, by omega⟩
  have hle : ∀ i, denExp (v i) ≤ t + 1 := fun i => ht ▸ denExp_le_colDenExp v i
  choose w hw using fun i => eq_mk_of_denExp_le (hle i)
  have hcard : (Finset.univ.filter fun i => denExp (v i) = t + 1).card ≤ 4 := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin 2 × Fin 2))
      (fun i => denExp (v i) = t + 1)
    have h4 : (Finset.univ : Finset (Fin 2 × Fin 2)).card = 4 := rfl
    omega
  obtain ⟨g, v', hg, hfac, hu', hd'⟩ := drop_all_actives 4 v w hw hunit hcard
  refine ⟨g, v', hg.mono (by omega), hfac, hu', ?_⟩
  rw [ht]
  have hsup : colDenExp v' ≤ t := Finset.sup_le fun i _ => hd' i
  omega

/-! ### The dim-4 column lemma, unconditional + quantitative -/

/-- The base case with an explicit budget: a denExp-0 unit column is column-realizable within 9
(the `ωᵏ·e_i` form has `k < 8`). Bounded variant of `base_case` for the quantitative lemma. -/
theorem base_case_bounded (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (hden : ∀ i, denExp (v i) = 0)
    (hunit : ∑ i, normSq (v i) = 1) : IsColRealizableWithin v 9 := by
  have hinj : Function.Injective (of : ZOmega → ZOmegaSqrt2) := by
    intro a b hab
    rw [of_def, of_def, mk_eq_mk_iff] at hab
    simpa using hab
  have hof : ∀ i, ∃ z, v i = of z := fun i => by
    obtain ⟨u, hu⟩ := (denExp_le_iff (x := v i) (k := 0)).mp (le_of_eq (hden i))
    refine ⟨u, ?_⟩
    rw [← one_mul (v i), ← pow_zero (sqrt2 : ZOmegaSqrt2)]
    exact hu
  choose z hz using hof
  have hzsum : ∑ i, ZOmega.normSq (z i) = 1 := by
    have hof1 : of (∑ i, ZOmega.normSq (z i)) = (1 : ZOmegaSqrt2) := by
      rw [show of (∑ i, ZOmega.normSq (z i)) = ∑ i, of (ZOmega.normSq (z i)) from
        map_sum ofRingHom _ _, ← hunit]
      exact Finset.sum_congr rfl fun i _ => by rw [hz i, normSq_of]
    exact hinj (hof1.trans of_one.symm)
  obtain ⟨i₀, hone, hzero⟩ := ZOmega.unit_col_zero_denExp_structure z hzsum
  obtain ⟨k, hk8, hzk⟩ := ZOmega.normSq_eq_one_iff_omega_pow.mp hone
  have hv_eq : v = (fun i => if i = i₀ then CliffordTGate.ωS ^ k else 0) := by
    funext i
    rw [hz i]
    by_cases hi : i = i₀
    · subst hi
      rw [hzk, if_pos rfl]
      have hcast : of (ZOmega.ω ^ k) = (of ZOmega.ω) ^ k := map_pow ofRingHom ZOmega.ω k
      rw [hcast]
      rfl
    · rw [hzero i hi, if_neg hi]
      rfl
  rw [hv_eq]
  exact (isColRealizableWithin_omega_pow_basis k i₀.1 i₀.2).mono (by omega)

/-- **The quantitative dim-4 column lemma (UNCONDITIONAL)**: every unit column over `ℤ[ω][1/√2]`
is the first column of an exact two-qubit Clifford+T word of length `≤ 280·colDenExp v + 9` —
gate count **linear in the denominator exponent**, the `O(log 1/ε)` count the KMM ≤2-ancilla
headline consumes. -/
theorem column_lemma_bounded (v : Fin 2 × Fin 2 → ZOmegaSqrt2)
    (hunit : ∑ i, normSq (v i) = 1) :
    IsColRealizableWithin v (280 * colDenExp v + 9) := by
  suffices H : ∀ (n : ℕ) (v : Fin 2 × Fin 2 → ZOmegaSqrt2), colDenExp v = n →
      (∑ i, normSq (v i) = 1) → IsColRealizableWithin v (280 * n + 9) from H _ v rfl hunit
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro v hn hv
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hden : ∀ i, denExp (v i) = 0 := fun i =>
        Nat.le_zero.mp (hn ▸ denExp_le_colDenExp v i)
      exact (base_case_bounded v hden hv).mono (by omega)
    · obtain ⟨g, v', hg, hfac, hu', hlt⟩ := reductionStep_holds v hv (hn ▸ hpos)
      have hc : colDenExp v' < n := hn ▸ hlt
      have hrec := IH (colDenExp v') hc v' rfl hu'
      rw [hfac]
      exact (IsColRealizableWithin.smul_left hg hrec).mono (by omega)

/-- **The dim-4 column lemma, existential form**: every unit column is column-realizable — the
Giles–Selinger column lemma at dim 4, fully unconditional and kernel-pure. This is the exact
synthesis of circuit `C` (the KMM `|v⟩`-preparation) modulo the length bookkeeping above. -/
theorem column_lemma_unconditional (v : Fin 2 × Fin 2 → ZOmegaSqrt2)
    (hunit : ∑ i, normSq (v i) = 1) :
    ∃ L, IsColRealizableWithin v L :=
  ⟨280 * colDenExp v + 9, column_lemma_bounded v hunit⟩

end Gate2
end SKEFTHawking.RossSelinger
