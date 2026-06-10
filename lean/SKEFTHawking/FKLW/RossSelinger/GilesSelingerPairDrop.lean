/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 31) — the single-pair column drop

This file connects the three shipped layers into the per-pair reduction move of the dim-4
Giles–Selinger column lemma:

  * the **pair-level number theory** (inc 22–27: `matched_active_dichotomy`, `core_step`,
    `cross_orbit_drop`) — a matched-active numerator pair drops one `denExp` level under
    `(x ± ωᵐ·y)/√2`,
  * the **det-balanced row-op gadget** (inc 29: `rowOpGadget m = ctrl Tᵐ (H·Tᵐ)`) — whose column
    action at the canonical `fst = 1` pair is exactly those combinations, and
  * the **alignment table** (inc 30: `exists_pair_alignment`) — permutation words pulling any
    ordered index pair into the canonical slots.

## Headline theorem

  * `exists_pair_drop` — for a column `v` at level `t+1` (numerators `w`) with a matched-active
    pair `p ≠ q`, there is a realizable `G` (with realizable inverse, `Ginv * G = 1`, both within
    70 gates) such that `G·v` **drops both pair entries to `denExp ≤ t`**, changes no other entry's
    `denExp` (spectators pick up unit phases only), and **preserves the unit-column sum**. This is
    the entire content of one row-operation move; the active-count induction (next increment)
    iterates it into `ReductionStep`.

## Helper layer (ZOmega / ZOmegaSqrt2)

`ω⁸ = 1` and exponent capping (`ω^m = ω^(m % 8)`, keeping gadget budgets bounded), unit-phase
invariance of `denExp`/`normSq`, the `√2`-parallelogram law (unit-sum preservation), `mk`-numerator
extraction from a `denExp` bound, and the top-level-active characterization
`denExp (mk z (k+1)) = k+1 ↔ ¬dividesSqrt2 z` (consumed by the induction).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.Gate2Perm
import SKEFTHawking.FKLW.RossSelinger.GilesSelingerRowOp
import SKEFTHawking.FKLW.RossSelinger.GridSynth
import SKEFTHawking.FKLW.RossSelinger.DenExpValuation
import SKEFTHawking.FKLW.RossSelinger.ClearingConnection

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-! ### ω has order 8 — exponent capping -/

namespace ZOmega

/-- `ω⁸ = 1` (from the shipped `ω⁴ = -1`). -/
theorem omega_pow_eight : (ω : ZOmega) ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, ω_pow_four]
  ring

/-- **Exponent capping**: `ω^m = ω^(m % 8)` — phases reduce mod 8, keeping gadget budgets
bounded. -/
theorem omega_pow_mod_eight (m : ℕ) : (ω : ZOmega) ^ m = ω ^ (m % 8) := by
  conv_lhs => rw [← Nat.div_add_mod m 8]
  rw [pow_add, pow_mul, omega_pow_eight, one_pow, one_mul]

end ZOmega

namespace ZOmegaSqrt2

/-- `ωS⁸ = 1` over `ℤ[ω][1/√2]`. -/
theorem ωS_pow_eight : CliffordTGate.ωS ^ 8 = 1 := by
  show (of ZOmega.ω) ^ 8 = 1
  rw [show (of ZOmega.ω) ^ 8 = of (ZOmega.ω ^ 8) from (map_pow ofRingHom ZOmega.ω 8).symm,
    ZOmega.omega_pow_eight]
  exact of_one

/-- Exponent capping for `ωS`. -/
theorem ωS_pow_mod_eight (m : ℕ) : CliffordTGate.ωS ^ m = CliffordTGate.ωS ^ (m % 8) := by
  conv_lhs => rw [← Nat.div_add_mod m 8]
  rw [pow_add, pow_mul, ωS_pow_eight, one_pow, one_mul]

/-! ### Unit-phase invariance of `normSq` and `denExp` -/

/-- `normSq` is invariant under the unit phase `ωSᵐ`. -/
theorem normSq_omega_pow_mul (m : ℕ) (x : ZOmegaSqrt2) :
    normSq (CliffordTGate.ωS ^ m * x) = normSq x := by
  rw [normSq_mul]
  show normSq ((of ZOmega.ω) ^ m) * normSq x = normSq x
  rw [normSq_omega_pow, one_mul]

/-- `denExp` is invariant under the unit phase `ωS`. -/
theorem denExp_omega_mul (x : ZOmegaSqrt2) : denExp (CliffordTGate.ωS * x) = denExp x := by
  have hωS : denExp CliffordTGate.ωS = 0 := by
    show denExp (mk ZOmega.ω 0) = 0
    rw [denExp_mk]
    rfl
  refine le_antisymm ?_ ?_
  · have h := denExp_mul_le CliffordTGate.ωS x
    rwa [hωS, zero_add] at h
  · have h7 : denExp (CliffordTGate.ωS ^ 7) = 0 := by
      show denExp ((of ZOmega.ω) ^ 7) = 0
      rw [show (of ZOmega.ω) ^ 7 = of (ZOmega.ω ^ 7) from (map_pow ofRingHom ZOmega.ω 7).symm]
      show denExp (mk (ZOmega.ω ^ 7) 0) = 0
      rw [denExp_mk]
      rfl
    have hx : x = CliffordTGate.ωS ^ 7 * (CliffordTGate.ωS * x) := by
      rw [← mul_assoc, ← pow_succ, ωS_pow_eight, one_mul]
    conv_lhs => rw [hx]
    have h := denExp_mul_le (CliffordTGate.ωS ^ 7) (CliffordTGate.ωS * x)
    rwa [h7, zero_add] at h

/-- `denExp` is invariant under unit phases `ωSᵐ`. -/
theorem denExp_omega_pow_mul (m : ℕ) (x : ZOmegaSqrt2) :
    denExp (CliffordTGate.ωS ^ m * x) = denExp x := by
  induction m with
  | zero => rw [pow_zero, one_mul]
  | succ n ih => rw [pow_succ, mul_comm (CliffordTGate.ωS ^ n), mul_assoc, denExp_omega_mul, ih]

/-! ### The `√2`-parallelogram law -/

/-- **Parallelogram law**: the Hadamard combination `((x+u)/√2, (x-u)/√2)` preserves the
`normSq`-sum — the algebraic heart of unit-column preservation under the row operation. -/
theorem normSq_parallelogram (x u : ZOmegaSqrt2) :
    normSq (invSqrt2 * (x + u)) + normSq (invSqrt2 * (x - u)) = normSq x + normSq u := by
  have h2 : normSq invSqrt2 * 2 = 1 := by
    rw [normSq_invSqrt2]
    decide
  have hneg : conj (-u) = - conj u := by
    have h := conj_add u (-u)
    rw [add_neg_cancel, conj_zero] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hsum : normSq (x + u) + normSq (x - u) = 2 * (normSq x + normSq u) := by
    show (x + u) * conj (x + u) + (x - u) * conj (x - u) =
      2 * (x * conj x + u * conj u)
    rw [sub_eq_add_neg, conj_add, conj_add, hneg]
    ring
  calc normSq (invSqrt2 * (x + u)) + normSq (invSqrt2 * (x - u))
      = normSq invSqrt2 * (normSq (x + u) + normSq (x - u)) := by
        rw [normSq_mul, normSq_mul]; ring
    _ = normSq invSqrt2 * 2 * (normSq x + normSq u) := by rw [hsum]; ring
    _ = normSq x + normSq u := by rw [h2, one_mul]

/-! ### Numerator extraction + the top-level-active characterization -/

/-- A `denExp ≤ k` element is `mk w k` for some numerator `w`. -/
theorem eq_mk_of_denExp_le {x : ZOmegaSqrt2} {k : ℕ} (h : denExp x ≤ k) : ∃ w, x = mk w k := by
  obtain ⟨w, hw⟩ := denExp_le_iff.mp h
  refine ⟨w, ?_⟩
  have h1 : invSqrt2 ^ k * ((sqrt2 : ZOmegaSqrt2) ^ k * x) = invSqrt2 ^ k * of w :=
    congrArg (invSqrt2 ^ k * ·) hw
  rw [← mul_assoc, ← mul_pow, invSqrt2_mul_sqrt2, one_pow, one_mul] at h1
  rw [h1, invSqrt2_pow_eq]
  show mk 1 k * mk w 0 = mk w k
  rw [mk_mul, one_mul, Nat.add_zero]

/-- **Top-level-active characterization**: an entry presented at level `k+1` sits exactly at
`denExp = k+1` iff its numerator is not `√2`-divisible (= the Giles–Selinger "active" notion). -/
theorem denExp_mk_succ_eq_iff {z : ZOmega} {k : ℕ} :
    denExp (mk z (k + 1)) = k + 1 ↔ ¬ ZOmega.dividesSqrt2 z := by
  rw [denExp_mk, ZOmega.lowestDenExp_succ]
  constructor
  · intro h hdvd
    rw [if_pos hdvd] at h
    have := ZOmega.lowestDenExp_le (ZOmega.divSqrt2 z) k
    omega
  · intro h
    rw [if_neg h]

end ZOmegaSqrt2

/-! ### The single-pair column drop -/

namespace Gate2

open ZOmegaSqrt2

/-- The row-op gadget **preserves the `normSq`-sum** of a column: spectators take unit phases,
the active pair transforms by the `√2`-parallelogram. -/
theorem rowOpGadget_sum_normSq (m : ℕ) (u : Fin 2 × Fin 2 → ZOmegaSqrt2) :
    ∑ i, normSq ((rowOpGadget m).mulVec u i) = ∑ i, normSq (u i) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [rowOpGadget_mulVec_zero_zero, rowOpGadget_mulVec_zero_one, rowOpGadget_mulVec_one_zero,
    rowOpGadget_mulVec_one_one, normSq_omega_pow_mul,
    normSq_parallelogram (u (1, 0)) (CliffordTGate.ωS ^ m * u (1, 1)), normSq_omega_pow_mul]

/-- Conjugated action: `(permMat e.symm * (X * permMat e))·v` at index `i` is `X` applied to the
aligned column `v ∘ e`, read at the aligned slot `e.symm i`. -/
theorem conj_mulVec_apply (X : Mat4) (e : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (v : Fin 2 × Fin 2 → ZOmegaSqrt2) (i : Fin 2 × Fin 2) :
    (permMat ⇑e.symm * (X * permMat ⇑e)).mulVec v i = X.mulVec (v ∘ ⇑e) (e.symm i) := by
  have h1 : (permMat ⇑e.symm * (X * permMat ⇑e)).mulVec v
      = (permMat ⇑e.symm).mulVec ((X * permMat ⇑e).mulVec v) :=
    (Matrix.mulVec_mulVec v _ _).symm
  have h2 : (X * permMat ⇑e).mulVec v = X.mulVec ((permMat ⇑e).mulVec v) :=
    (Matrix.mulVec_mulVec v _ _).symm
  rw [h1, h2, permMat_mulVec, permMat_mulVec]
  rfl

/-- Sandwich inverse: conjugating an invertible pair by mutually-inverse permutations. -/
theorem sandwich_inv {PA Pi X Xinv : Mat4}
    (hPAPi : PA * Pi = 1) (hPiPA : Pi * PA = 1) (hX : Xinv * X = 1) :
    (Pi * (Xinv * PA)) * (Pi * (X * PA)) = 1 := by
  calc (Pi * (Xinv * PA)) * (Pi * (X * PA))
      = Pi * ((Xinv * PA) * (Pi * (X * PA))) := Matrix.mul_assoc _ _ _
    _ = Pi * (Xinv * (PA * (Pi * (X * PA)))) := congrArg (Pi * ·) (Matrix.mul_assoc _ _ _)
    _ = Pi * (Xinv * ((PA * Pi) * (X * PA))) :=
        congrArg (Pi * ·) (congrArg (Xinv * ·) (Matrix.mul_assoc _ _ _).symm)
    _ = Pi * (Xinv * ((1 : Mat4) * (X * PA))) := by rw [hPAPi]
    _ = Pi * (Xinv * (X * PA)) := congrArg (Pi * ·) (congrArg (Xinv * ·) (one_mul _))
    _ = Pi * ((Xinv * X) * PA) := congrArg (Pi * ·) (Matrix.mul_assoc _ _ _).symm
    _ = Pi * ((1 : Mat4) * PA) := by rw [hX]
    _ = Pi * PA := congrArg (Pi * ·) (one_mul _)
    _ = 1 := hPiPA

/-- Inverse of a product from inverses of the factors. -/
theorem mul_inv_pair {A B Ainv Binv : Mat4} (hA : Ainv * A = 1) (hB : Binv * B = 1) :
    (Ainv * Binv) * (B * A) = 1 := by
  calc (Ainv * Binv) * (B * A) = Ainv * (Binv * (B * A)) := Matrix.mul_assoc _ _ _
    _ = Ainv * ((Binv * B) * A) := congrArg (Ainv * ·) (Matrix.mul_assoc _ _ _).symm
    _ = Ainv * ((1 : Mat4) * A) := by rw [hB]
    _ = Ainv * A := congrArg (Ainv * ·) (one_mul _)
    _ = 1 := hA

/-- The mutually-inverse permutation matrices of an alignment equivalence. -/
theorem permMat_symm_mul (e : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2)) :
    permMat ⇑e * permMat ⇑e.symm = 1 := by
  rw [permMat_mul, show (⇑e.symm ∘ ⇑e) = id from funext fun x => e.symm_apply_apply x, permMat_id]

theorem permMat_mul_symm (e : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2)) :
    permMat ⇑e.symm * permMat ⇑e = 1 := by
  rw [permMat_mul, show (⇑e ∘ ⇑e.symm) = id from funext fun x => e.apply_symm_apply x, permMat_id]

/-- **The single-pair column drop.** For a column `v` presented at level `t+1` with numerators `w`,
and a matched-active pair `p ≠ q` (both numerators non-`√2`-divisible with matching residue-norm
parities), there is a realizable `G` — alignment-conjugated row-op gadget(s) — with realizable
inverse (`Ginv * G = 1`, both within 70 gates) such that `G·v` has

  * `denExp ≤ t` at **both** pair entries (the Lemma-4 drop),
  * unchanged `denExp` at every spectator (unit phases only), and
  * the same `normSq`-sum (unit column preserved).

The aligned (`core_step`) and cross-orbit (`cross_orbit_drop`) branches of
`matched_active_dichotomy` give a one- and a two-gadget word respectively. -/
theorem exists_pair_drop {t : ℕ} (v : Fin 2 × Fin 2 → ZOmegaSqrt2)
    (w : Fin 2 × Fin 2 → ZOmega) (hv : ∀ i, v i = mk (w i) (t + 1))
    {p q : Fin 2 × Fin 2} (hpq : p ≠ q)
    (hwp : ¬ ZOmega.dividesSqrt2 (w p)) (hwq : ¬ ZOmega.dividesSqrt2 (w q))
    (hc : (ZOmega.normSq (w p)).c % 2 = (ZOmega.normSq (w q)).c % 2)
    (hd : (ZOmega.normSq (w p)).d % 2 = (ZOmega.normSq (w q)).d % 2) :
    ∃ G Ginv : Mat4,
      IsRealizableWithin G 70 ∧ IsRealizableWithin Ginv 70 ∧ Ginv * G = 1 ∧
      denExp (G.mulVec v p) ≤ t ∧ denExp (G.mulVec v q) ≤ t ∧
      (∀ i, i ≠ p → i ≠ q → denExp (G.mulVec v i) = denExp (v i)) ∧
      (∑ i, normSq (G.mulVec v i)) = ∑ i, normSq (v i) := by
  obtain ⟨wa, wai, e, hwa, hwai, he10, he11, hlen, hleni⟩ := exists_pair_alignment p q hpq
  have hPA : IsRealizableWithin (permMat ⇑e) 5 := ⟨wa, hwa, hlen⟩
  have hPi : IsRealizableWithin (permMat ⇑e.symm) 5 := ⟨wai, hwai, hleni⟩
  have hu10 : (v ∘ ⇑e) (1, 0) = mk (w p) (t + 1) := by
    show v (e (1, 0)) = _
    rw [he10, hv]
  have hu11 : (v ∘ ⇑e) (1, 1) = mk (w q) (t + 1) := by
    show v (e (1, 1)) = _
    rw [he11, hv]
  have hesymm_p : e.symm p = (1, 0) := by rw [← he10, Equiv.symm_apply_apply]
  have hesymm_q : e.symm q = (1, 1) := by rw [← he11, Equiv.symm_apply_apply]
  -- spectator slot machinery, shared by both branches
  have hslot : ∀ i, i ≠ p → i ≠ q → e.symm i ≠ (1, 0) ∧ e.symm i ≠ (1, 1) := by
    intro i hip hiq
    constructor
    · intro h
      exact hip (by rw [← he10, ← h, Equiv.apply_symm_apply])
    · intro h
      exact hiq (by rw [← he11, ← h, Equiv.apply_symm_apply])
  have hui : ∀ i, (v ∘ ⇑e) (e.symm i) = v i := fun i => by
    show v (e (e.symm i)) = v i
    rw [Equiv.apply_symm_apply]
  rcases ZOmega.matched_active_dichotomy hwp hwq hc hd with ⟨m, hdvd⟩ | ⟨m, ha, hb, hcc, hdd⟩
  · -- ALIGNED branch: one gadget `rowOpGadget (m % 8)`
    rw [ZOmega.omega_pow_mod_eight] at hdvd
    set m₀ := m % 8 with hm₀def
    have hm₀ : m₀ ≤ 8 := le_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
    refine ⟨permMat ⇑e.symm * (rowOpGadget m₀ * permMat ⇑e),
      permMat ⇑e.symm * (rowOpGadgetInv m₀ * permMat ⇑e), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hPi.mul ((rowOpGadget_realizableWithin m₀).mul hPA)).mono (by omega)
    · exact (hPi.mul ((rowOpGadgetInv_realizableWithin m₀).mul hPA)).mono (by omega)
    · exact sandwich_inv (permMat_symm_mul e) (permMat_mul_symm e)
        (rowOpGadgetInv_mul_rowOpGadget m₀ hm₀)
    · rw [conj_mulVec_apply, hesymm_p, rowOpGadget_mulVec_one_zero, hu10, hu11]
      exact (ZOmegaSqrt2.core_step hdvd).1
    · rw [conj_mulVec_apply, hesymm_q, rowOpGadget_mulVec_one_one, hu10, hu11]
      exact (ZOmegaSqrt2.core_step hdvd).2
    · intro i hip hiq
      obtain ⟨hs0, hs1⟩ := hslot i hip hiq
      rw [conj_mulVec_apply]
      have huii := hui i
      have hcases : e.symm i = (0, 0) ∨ e.symm i = (0, 1) :=
        (by decide : ∀ s : Fin 2 × Fin 2, s ≠ (1, 0) → s ≠ (1, 1) → s = (0, 0) ∨ s = (0, 1))
          _ hs0 hs1
      rcases hcases with hsi | hsi <;> rw [hsi] at huii ⊢
      · rw [rowOpGadget_mulVec_zero_zero, huii]
      · rw [rowOpGadget_mulVec_zero_one, denExp_omega_pow_mul, huii]
    · calc ∑ i, normSq ((permMat ⇑e.symm * (rowOpGadget m₀ * permMat ⇑e)).mulVec v i)
          = ∑ i, normSq ((rowOpGadget m₀).mulVec (v ∘ ⇑e) (e.symm i)) :=
            Finset.sum_congr rfl fun i _ => by rw [conj_mulVec_apply]
        _ = ∑ j, normSq ((rowOpGadget m₀).mulVec (v ∘ ⇑e) j) :=
            e.symm.sum_comp fun j => normSq ((rowOpGadget m₀).mulVec (v ∘ ⇑e) j)
        _ = ∑ j, normSq ((v ∘ ⇑e) j) := rowOpGadget_sum_normSq m₀ (v ∘ ⇑e)
        _ = ∑ i, normSq (v i) := e.sum_comp fun i => normSq (v i)
  · -- CROSS-ORBIT branch: two gadgets `rowOpGadget (m' % 8) * rowOpGadget (m % 8)`
    rw [ZOmega.omega_pow_mod_eight] at ha hb hcc hdd
    set m₀ := m % 8 with hm₀def
    obtain ⟨m', hdrop⟩ := ZOmegaSqrt2.cross_orbit_drop (t := t) ha hb hcc hdd
    rw [ωS_pow_mod_eight m'] at hdrop
    set m₁ := m' % 8 with hm₁def
    have hm₀ : m₀ ≤ 8 := le_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
    have hm₁ : m₁ ≤ 8 := le_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
    -- entry formulas for the two-gadget composite at the canonical slots
    have hcomp : ∀ j, (rowOpGadget m₁ * rowOpGadget m₀).mulVec (v ∘ ⇑e) j
        = (rowOpGadget m₁).mulVec ((rowOpGadget m₀).mulVec (v ∘ ⇑e)) j := fun j =>
      congrFun (Matrix.mulVec_mulVec (v ∘ ⇑e) (rowOpGadget m₁) (rowOpGadget m₀)).symm j
    refine ⟨permMat ⇑e.symm * ((rowOpGadget m₁ * rowOpGadget m₀) * permMat ⇑e),
      permMat ⇑e.symm * ((rowOpGadgetInv m₀ * rowOpGadgetInv m₁) * permMat ⇑e),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hPi.mul (((rowOpGadget_realizableWithin m₁).mul
        (rowOpGadget_realizableWithin m₀)).mul hPA)).mono (by omega)
    · exact (hPi.mul (((rowOpGadgetInv_realizableWithin m₀).mul
        (rowOpGadgetInv_realizableWithin m₁)).mul hPA)).mono (by omega)
    · exact sandwich_inv (permMat_symm_mul e) (permMat_mul_symm e)
        (mul_inv_pair (rowOpGadgetInv_mul_rowOpGadget m₀ hm₀)
          (rowOpGadgetInv_mul_rowOpGadget m₁ hm₁))
    · rw [conj_mulVec_apply, hesymm_p, hcomp, rowOpGadget_mulVec_one_zero,
        rowOpGadget_mulVec_one_zero, rowOpGadget_mulVec_one_one, hu10, hu11]
      exact hdrop.1
    · rw [conj_mulVec_apply, hesymm_q, hcomp, rowOpGadget_mulVec_one_one,
        rowOpGadget_mulVec_one_zero, rowOpGadget_mulVec_one_one, hu10, hu11]
      exact hdrop.2
    · intro i hip hiq
      obtain ⟨hs0, hs1⟩ := hslot i hip hiq
      rw [conj_mulVec_apply]
      have huii := hui i
      have hcases : e.symm i = (0, 0) ∨ e.symm i = (0, 1) :=
        (by decide : ∀ s : Fin 2 × Fin 2, s ≠ (1, 0) → s ≠ (1, 1) → s = (0, 0) ∨ s = (0, 1))
          _ hs0 hs1
      rcases hcases with hsi | hsi <;> rw [hsi] at huii ⊢
      · rw [hcomp, rowOpGadget_mulVec_zero_zero, rowOpGadget_mulVec_zero_zero, huii]
      · rw [hcomp, rowOpGadget_mulVec_zero_one, denExp_omega_pow_mul,
          rowOpGadget_mulVec_zero_one, denExp_omega_pow_mul, huii]
    · calc ∑ i, normSq
            ((permMat ⇑e.symm * ((rowOpGadget m₁ * rowOpGadget m₀) * permMat ⇑e)).mulVec v i)
          = ∑ i, normSq ((rowOpGadget m₁ * rowOpGadget m₀).mulVec (v ∘ ⇑e) (e.symm i)) :=
            Finset.sum_congr rfl fun i _ => by rw [conj_mulVec_apply]
        _ = ∑ j, normSq ((rowOpGadget m₁ * rowOpGadget m₀).mulVec (v ∘ ⇑e) j) :=
            e.symm.sum_comp fun j => normSq ((rowOpGadget m₁ * rowOpGadget m₀).mulVec (v ∘ ⇑e) j)
        _ = ∑ j, normSq ((rowOpGadget m₁).mulVec ((rowOpGadget m₀).mulVec (v ∘ ⇑e)) j) :=
            Finset.sum_congr rfl fun j _ => by rw [hcomp]
        _ = ∑ j, normSq ((rowOpGadget m₀).mulVec (v ∘ ⇑e) j) :=
            rowOpGadget_sum_normSq m₁ ((rowOpGadget m₀).mulVec (v ∘ ⇑e))
        _ = ∑ j, normSq ((v ∘ ⇑e) j) := rowOpGadget_sum_normSq m₀ (v ∘ ⇑e)
        _ = ∑ i, normSq (v i) := e.sum_comp fun i => normSq (v i)

end Gate2
end SKEFTHawking.RossSelinger
