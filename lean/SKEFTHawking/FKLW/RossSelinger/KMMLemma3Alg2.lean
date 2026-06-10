/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 3, site 4/4 — KMM Lemma 3 (Algorithm 2), re-proved structurally

The statement is IDENTICAL to the former `native_decide` original in `KMMLemma3.lean`
(zero consumer changes — `KMMLemma3Column.lean` consumes it verbatim): the T-pairing
calculus (`KMMLemma3Structural.lean`) reduces it to the `(P, Q, T₀..T₃)`-data, the
norm-multiplicativity identities supply the reachability constraints, and the two
262k-tuple kernel master sweeps (split on `P(x)+P(y) ∈ {0,4}`) discharge the core.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (branch lemmas carry their own budgets).
- **#15**: no new axioms. No `native_decide`. Kernel-pure.
-/

import SKEFTHawking.FKLW.RossSelinger.KMMLemma3Structural

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger.KMM

open Coord4

/-- A `ZMod 8` element doubling to zero is `0` or `4`. -/
theorem zmod8_two_mul_eq_zero {u : ZMod 8} (h : 2 * u = 0) : u = 0 ∨ u = 4 := by
  revert h; revert u; decide

/-- Alignment: a `gdePQ` fact about the translated `(P, Q)`-data transports to `gde` of
the translate. -/
theorem gde_add_eq_of {x y : Coord4} {k : Fin 4} {n : ℕ}
    (h : gdePQ (Pform x + Pform y + 2 * Bform x (mulOmegaPow (k.val) y))
          (Qform x + Qform y + (Bform x (mulOmegaPow (1 + k.val) y)
            - Bform x (mulOmegaPow (3 + k.val) y))) = n) :
    gde (add x (mulOmegaPow k.val y)) = n := by
  rw [gde_eq_gdePQ, Pform_add, Qform_add, Pform_mulOmegaPow, Qform_mulOmegaPow,
    mulOmegaPow_add, mulOmegaPow_add]
  exact h

/-- Index fold: `B(x, ω⁵z) = −B(x, ωz)`. -/
theorem Bform_fold5 (x z : Coord4) :
    Bform x (mulOmegaPow 5 z) = -Bform x (mulOmegaPow 1 z) := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, ← mulOmegaPow_add, Bform_mulOmega_four]

/-- Index fold: `B(x, ω⁶z) = −B(x, ω²z)`. -/
theorem Bform_fold6 (x z : Coord4) :
    Bform x (mulOmegaPow 6 z) = -Bform x (mulOmegaPow 2 z) := by
  rw [show (6 : ℕ) = 4 + 2 from rfl, ← mulOmegaPow_add, Bform_mulOmega_four]

/-- `ω⁰` is the identity rotation. -/
theorem mulOmegaPow_zero (z : Coord4) : mulOmegaPow 0 z = z := rfl

/-- Branch `P(x) + P(y) = 0`: the master sweep `kmm_master_a` transports to the goal. -/
theorem kmm_lemma3_branch_a {x y : Coord4} {j : Fin 2}
    (hgx : gde x = j.val) (hgy : gde y = j.val)
    (hP0 : Pform x + Pform y = 0) (hQQ : Qform x + Qform y = 0) (s : Fin 3) :
    ∃ k : Fin 4, gde (add x (mulOmegaPow k.val y)) = (s.val + 1) + j.val := by
  have hqy : Qform y = -Qform x := by linear_combination hQQ
  have hpy : Pform y = -Pform x := by linear_combination hP0
  have hpx : gdePQ (Pform x) (Qform x) = j.val := by rw [← gde_eq_gdePQ]; exact hgx
  have hgy' : gdePQ (-Pform x) (-Qform x) = j.val := by
    rw [← hpy, ← hqy, ← gde_eq_gdePQ]; exact hgy
  have hr1 := reach_P x y
  have hr2 := reach_Q x y
  rw [hpy, hqy] at hr1 hr2
  obtain ⟨k, hk⟩ := kmm_master_a (Pform x) (Qform x) (Bform x y)
    (Bform x (mulOmegaPow 1 y)) (Bform x (mulOmegaPow 2 y)) (Bform x (mulOmegaPow 3 y))
    j hpx hgy' hr1 hr2 s
  refine ⟨k, gde_add_eq_of ?_⟩
  fin_cases k
  · refine (congrArg₂ gdePQ ?_ ?_).trans hk <;>
      simp only [pUpd, qUpd, Nat.reduceAdd, mulOmegaPow_zero]
    · linear_combination hP0
    · linear_combination hQQ
  · refine (congrArg₂ gdePQ ?_ ?_).trans hk <;>
      simp only [pUpd, qUpd, Nat.reduceAdd]
    · linear_combination hP0
    · rw [Bform_mulOmega_four]; linear_combination hQQ
  · refine (congrArg₂ gdePQ ?_ ?_).trans hk <;>
      simp only [pUpd, qUpd, Nat.reduceAdd]
    · linear_combination hP0
    · rw [Bform_fold5]; linear_combination hQQ
  · refine (congrArg₂ gdePQ ?_ ?_).trans hk <;>
      simp only [pUpd, qUpd, Nat.reduceAdd]
    · linear_combination hP0
    · rw [Bform_mulOmega_four, Bform_fold6]; linear_combination hQQ

/-- Branch `P(x) + P(y) = 4`: the master sweep `kmm_master_b` transports to the goal. -/
theorem kmm_lemma3_branch_b {x y : Coord4} {j : Fin 2}
    (hgx : gde x = j.val) (hgy : gde y = j.val)
    (hP4 : Pform x + Pform y = 4) (hQQ : Qform x + Qform y = 0) (s : Fin 3) :
    ∃ k : Fin 4, gde (add x (mulOmegaPow k.val y)) = (s.val + 1) + j.val := by
  have hqy : Qform y = -Qform x := by linear_combination hQQ
  have hpy : Pform y = 4 - Pform x := by linear_combination hP4
  have hpx : gdePQ (Pform x) (Qform x) = j.val := by rw [← gde_eq_gdePQ]; exact hgx
  have hgy' : gdePQ (4 - Pform x) (-Qform x) = j.val := by
    rw [← hpy, ← hqy, ← gde_eq_gdePQ]; exact hgy
  have hr1 := reach_P x y
  have hr2 := reach_Q x y
  rw [hpy, hqy] at hr1 hr2
  obtain ⟨k, hk⟩ := kmm_master_b (Pform x) (Qform x) (Bform x y)
    (Bform x (mulOmegaPow 1 y)) (Bform x (mulOmegaPow 2 y)) (Bform x (mulOmegaPow 3 y))
    j hpx hgy' hr1 hr2 s
  refine ⟨k, gde_add_eq_of ?_⟩
  fin_cases k
  · refine (congrArg₂ gdePQ ?_ ?_).trans hk <;>
      simp only [pUpd, qUpd, Nat.reduceAdd, mulOmegaPow_zero]
    · linear_combination hP4
    · linear_combination hQQ
  · refine (congrArg₂ gdePQ ?_ ?_).trans hk <;>
      simp only [pUpd, qUpd, Nat.reduceAdd]
    · linear_combination hP4
    · rw [Bform_mulOmega_four]; linear_combination hQQ
  · refine (congrArg₂ gdePQ ?_ ?_).trans hk <;>
      simp only [pUpd, qUpd, Nat.reduceAdd]
    · linear_combination hP4
    · rw [Bform_fold5]; linear_combination hQQ
  · refine (congrArg₂ gdePQ ?_ ?_).trans hk <;>
      simp only [pUpd, qUpd, Nat.reduceAdd]
    · linear_combination hP4
    · rw [Bform_mulOmega_four, Bform_fold6]; linear_combination hQQ

/-- **KMM Lemma 3 (Algorithm 2), STRUCTURAL.** For each base level `j ∈ {0,1}`, each
residue pair `(x,y)` with `gde x = gde y = j` satisfying the necessary congruences
`2·(P(x)+P(y)) = 0` (i.e. `P(x)+P(y) ∈ {0, 4}`) and `Q(x)+Q(y) = 0` in `ℤ[ω]/(2³)`,
and each target `d = s+1 ∈ {1,2,3}`, there is `k ∈ {0,1,2,3}` with
`gde(x + ωᵏ·y) = d + j`. This is KMM Algorithm 2 verbatim; the maximiser at `d = 3`
(resp. `d+j = 4` when `j=1`) is the sde-reducing `k`. Formerly a ~16.7M-pair
`native_decide`; now structural via the T-pairing calculus + the two kernel master
sweeps. Kernel-pure `{propext, Classical.choice, Quot.sound}`. -/
theorem kmm_lemma3_alg2 :
    ∀ (x y : Coord4) (j : Fin 2),
      gde x = j.val → gde y = j.val →
      2 * (Pform x + Pform y) = 0 → Qform x + Qform y = 0 →
      ∀ s : Fin 3, ∃ k : Fin 4, gde (add x (mulOmegaPow k.val y)) = (s.val + 1) + j.val := by
  intro x y j hgx hgy hPP hQQ s
  rcases zmod8_two_mul_eq_zero hPP with hP0 | hP4
  · exact kmm_lemma3_branch_a hgx hgy hP0 hQQ s
  · exact kmm_lemma3_branch_b hgx hgy hP4 hQQ s

end SKEFTHawking.RossSelinger.KMM
