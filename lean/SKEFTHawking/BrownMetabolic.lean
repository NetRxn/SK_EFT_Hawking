/-
# Phase 5q.H (E2 · EASY layer) — metabolic forms have Brown invariant 0

The algebra half of the Taylor/Klug bounding argument (`Lit-Search/Phase-5qH/
Rokhlin_16_sigma_elementary_blueprint_20260703.md` route A; Klug `2011.12418` Thm 2): if a
nondegenerate `ZMod 4`-quadratic form `Q` vanishes on a **Lagrangian** submodule `L` (self-orthogonal
and maximal — a *metabolizer*), its Gauss sum equals `|L|` (positive real), so `brown Q = 0` and
`arf Q = 0`. The geometric layer later supplies `L = ker(H₁(F;ℤ/2) → H₁(M³;ℤ/2))` for a surface `F`
bounding inside a 3-manifold, with `q|_L = 0` from Taylor `0802.0111` Lemma 1.3 (bounds a disk ⟹
`q = 0`); this single theorem then replaces the surgery-induction on the algebra side wholesale.

The computation: `|L| · G = Σ_{l∈L} Σ_v ζ₄(q(v+l)) = Σ_v ζ₄(q v)·Σ_{l∈L} χ₂(B v l)`; the character
sum is `|L|` for `v ∈ L` (pairwise `B`-orthogonality of `L`, forced by `q|_L = 0`) and `0` for
`v ∉ L` (maximality gives a pairing witness; shift-involution kills the sum), so `G = |L|`. Then
`|L|² = norm G = 2^{dim}` forces `dim = 2·dim L`, and `(1+i)² = 2i` pins the Brown unit to `−dim L`,
giving `brown Q = 2·(−dim L) + 2·dim L = 0` in `ZMod 8`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.BrownInvariant
import SKEFTHawking.GMArfVanishing

namespace SKEFTHawking.Brown.Z4Quadratic

open SKEFTHawking.Brown

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)

/-- `q` vanishing on a submodule forces pairwise `B`-orthogonality on it (polarization: over the
vanishing locus, `0 = q(l+l') = q l + q l' + embed2 (B l l')` and `embed2` is injective). -/
lemma B_eq_zero_of_q_eq_zero {L : Submodule (ZMod 2) (ι → ZMod 2)}
    (hq : ∀ l ∈ L, Q.q l = 0) {l l' : ι → ZMod 2} (hl : l ∈ L) (hl' : l' ∈ L) :
    Q.B l l' = 0 := by
  have h := Q.refine' l l'
  rw [hq _ hl, hq _ hl', hq _ (L.add_mem hl hl'), zero_add, zero_add] at h
  have hemb : embed2 (Q.B l l') = 0 := h.symm
  revert hemb; generalize Q.B l l' = b; revert b; decide

/-- **The character sum over `L` vanishes off `L`** when `L` is maximal (`L^⊥ ⊆ L`): a witness
`l₀ ∈ L` with `B v l₀ = 1` exists, and the shift involution `l ↦ l + l₀` negates the sum. -/
lemma sum_chi2_eq_zero_of_notMem {L : Submodule (ZMod 2) (ι → ZMod 2)} [Fintype L]
    (hmax : ∀ v, (∀ l ∈ L, Q.B v l = 0) → v ∈ L) {v : ι → ZMod 2} (hv : v ∉ L) :
    ∑ l : L, chi2 (Q.B v l) = 0 := by
  obtain ⟨l₀, hl₀L, hl₀⟩ : ∃ l₀ ∈ L, Q.B v l₀ = 1 := by
    by_contra h
    push Not at h
    refine hv (hmax v (fun l hl => ?_))
    have := h l hl
    revert this; generalize Q.B v l = b; revert b; decide
  set S := ∑ l : L, chi2 (Q.B v l) with hS
  have key : S = -S := by
    calc S = ∑ l : L, chi2 (Q.B v ((l + (⟨l₀, hl₀L⟩ : L) : L) : ι → ZMod 2)) :=
          (Equiv.sum_comp (Equiv.addRight (⟨l₀, hl₀L⟩ : L)) fun l => chi2 (Q.B v l)).symm
      _ = ∑ l : L, chi2 (Q.B v l + Q.B v l₀) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [Submodule.coe_add, Q.B_add_right]
      _ = ∑ l : L, -chi2 (Q.B v l) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hl₀]
          generalize Q.B v (l : ι → ZMod 2) = b
          revert b; decide
      _ = -S := by rw [hS, Finset.sum_neg_distrib]
  have h2 : (2 : GaussianInt) * S = 0 := by linear_combination key
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h (by decide)
  · exact h

/-- **The Gauss sum of a metabolic form is `|L|`** — positive real, no phase. -/
theorem gaussSum4_eq_card_of_metabolic (L : Submodule (ZMod 2) (ι → ZMod 2)) [Fintype L]
    (hq : ∀ l ∈ L, Q.q l = 0)
    (hmax : ∀ v, (∀ l ∈ L, Q.B v l = 0) → v ∈ L) :
    gaussSum4 Q.q = (Fintype.card L : GaussianInt) := by
  classical
  have hcard0 : (Fintype.card L : GaussianInt) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- |L| · G = Σ_{l∈L} Σ_v ζ₄(q(v+l))  (each inner shift reindexes to G)
  have hLG : (Fintype.card L : GaussianInt) * gaussSum4 Q.q
      = ∑ l : L, ∑ v : ι → ZMod 2, zeta4 (Q.q (v + l)) := by
    have hshift : ∀ l : L, ∑ v : ι → ZMod 2, zeta4 (Q.q (v + l)) = gaussSum4 Q.q := fun l =>
      Equiv.sum_comp (Equiv.addRight (l : ι → ZMod 2)) fun v => zeta4 (Q.q v)
    rw [Finset.sum_congr rfl fun l _ => hshift l, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  -- expand q(v+l) and factor: Σ_v ζ₄(q v) · Σ_{l∈L} χ₂(B v l)
  have hexpand : ∑ l : L, ∑ v : ι → ZMod 2, zeta4 (Q.q (v + l))
      = ∑ v : ι → ZMod 2, zeta4 (Q.q v) * ∑ l : L, chi2 (Q.B v l) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Q.refine' v l, hq _ l.2, add_zero, zeta4_add, zeta4_embed2]
  -- the inner sum is |L| on L (pairwise orthogonality) and 0 off L (character vanishing)
  have hinner : ∀ v : ι → ZMod 2,
      zeta4 (Q.q v) * ∑ l : L, chi2 (Q.B v l)
        = if v ∈ L then (Fintype.card L : GaussianInt) else 0 := by
    intro v
    by_cases hv : v ∈ L
    · have hall : ∀ l : L, chi2 (Q.B v l) = 1 := fun l => by
        rw [Q.B_eq_zero_of_q_eq_zero hq hv l.2]; rfl
      rw [Finset.sum_congr rfl (fun l _ => hall l), Finset.sum_const, hq _ hv,
        if_pos hv]
      simp [zeta4]
    · rw [Q.sum_chi2_eq_zero_of_notMem hmax hv, mul_zero, if_neg hv]
  -- assemble: |L|·G = Σ_{v∈L} |L| = |L|²  ⟹  G = |L|
  have hfinal : (Fintype.card L : GaussianInt) * gaussSum4 Q.q
      = (Fintype.card L : GaussianInt) * (Fintype.card L : GaussianInt) := by
    rw [hLG, hexpand, Finset.sum_congr rfl (fun v _ => hinner v), Finset.sum_ite,
      Finset.sum_const, Finset.sum_const_zero, add_zero]
    have hc : (Finset.univ.filter (fun v => v ∈ L)).card = Fintype.card L :=
      (Fintype.card_subtype (fun v => v ∈ L)).symm
    rw [hc, nsmul_eq_mul]
  exact mul_left_cancel₀ hcard0 hfinal

/-- `zeta4` at a natural cast is the plain power `I^n` (period 4). -/
lemma zeta4_natCast (n : ℕ) : zeta4 (n : ZMod 4) = I ^ n := by
  rw [zeta4, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, I_pow_four, one_pow, one_mul]

/-- `ZMod 8` arithmetic of the Brown phase: `2·(−n mod 4).val + 2n ≡ 0 (mod 8)`. -/
lemma two_mul_val_neg_natCast_add (n : ℕ) :
    2 * (((-(n : ZMod 4)).val : ZMod 8)) + 2 * (n : ZMod 8) = 0 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have h40 : (4 : ZMod 4) = 0 := by decide
  have h80 : (8 : ZMod 8) = 0 := by decide
  have h4 : ((4 * q + r : ℕ) : ZMod 4) = (r : ZMod 4) := by
    push_cast
    linear_combination (q : ZMod 4) * h40
  have h8 : (2 : ZMod 8) * ((4 * q + r : ℕ) : ZMod 8) = 2 * (r : ZMod 8) := by
    push_cast
    linear_combination (q : ZMod 8) * h80
  rw [h4, h8]
  interval_cases r <;> decide

/-- **Metabolic ⟹ Brown invariant `0`.** If the nondegenerate `ZMod 4`-quadratic form `Q` vanishes on
a Lagrangian submodule `L` (self-orthogonality is forced by the vanishing; maximality `L^⊥ ⊆ L` is the
hypothesis), then `brown Q = 0`. The algebra half of the Taylor/Klug bounding argument: the geometric
layer supplies `L = ker(H₁(F;ℤ/2) → H₁(M³;ℤ/2))` for a bounding surface with `q|_L = 0` (Taylor
`0802.0111` Lem 1.3), and this theorem concludes `β(F) = 0` — no surgery induction needed. Falsifiable:
the `ℝP²` form (`brown = ±1`) admits no such `L`. -/
theorem brown_eq_zero_of_metabolic (L : Submodule (ZMod 2) (ι → ZMod 2)) [Fintype L]
    (hq : ∀ l ∈ L, Q.q l = 0)
    (hmax : ∀ v, (∀ l ∈ L, Q.B v l = 0) → v ∈ L) :
    Q.brown = 0 := by
  classical
  have hG := Q.gaussSum4_eq_card_of_metabolic L hq hmax
  obtain ⟨m, hι, hL⟩ : ∃ m, Fintype.card ι = 2 * m ∧ Fintype.card L = 2 ^ m := by
    have hnorm := Q.norm_gaussSum4
    rw [hG] at hnorm
    have hnat : (Fintype.card L) * (Fintype.card L) = 2 ^ Fintype.card ι := by
      have hz : ((Fintype.card L : ℤ)) * (Fintype.card L : ℤ) = (2 : ℤ) ^ Fintype.card ι := by
        rw [← hnorm]
        simp [Zsqrtd.norm]
      exact_mod_cast hz
    have hdvd : (Fintype.card L) ∣ 2 ^ Fintype.card ι := ⟨Fintype.card L, hnat.symm⟩
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    refine ⟨k, ?_, hk⟩
    have hp : (2 : ℕ) ^ (2 * k) = 2 ^ Fintype.card ι := by
      rw [two_mul, pow_add, ← hk]; exact hnat
    exact (Nat.pow_right_injective (le_refl 2) hp).symm
  have hBU := Q.gaussSum4_eq_brownUnit
  rw [hG, hL, hι] at hBU
  have hpow : ((1 : GaussianInt) + I) ^ (2 * m) = (2 : GaussianInt) ^ m * I ^ m := by
    rw [pow_mul, one_add_I_pow_two, mul_pow]
  have h2m : ((2 ^ m : ℕ) : GaussianInt) = (2 : GaussianInt) ^ m := by push_cast; ring
  rw [hpow, h2m] at hBU
  have hone : zeta4 Q.brownUnit * I ^ m = 1 :=
    mul_right_cancel₀ (pow_ne_zero m (by decide : (2 : GaussianInt) ≠ 0))
      (by linear_combination -hBU :
        zeta4 Q.brownUnit * I ^ m * (2 : GaussianInt) ^ m = 1 * (2 : GaussianInt) ^ m)
  have hbu : Q.brownUnit = -(m : ZMod 4) := by
    have hz : zeta4 (Q.brownUnit + (m : ZMod 4)) = zeta4 0 := by
      rw [zeta4_add, zeta4_natCast, hone]; rfl
    exact eq_neg_of_add_eq_zero_left (zeta4_injective hz)
  rw [brown, hbu, hι]
  have hcast : ((2 * m : ℕ) : ZMod 8) = 2 * (m : ZMod 8) := by push_cast; ring
  rw [hcast]
  exact two_mul_val_neg_natCast_add m

/-- **Metabolic ⟹ Arf invariant `0`** — the `ℤ/2` shadow through `arf = brown/4`. -/
theorem arf_eq_zero_of_metabolic (L : Submodule (ZMod 2) (ι → ZMod 2)) [Fintype L]
    (hq : ∀ l ∈ L, Q.q l = 0)
    (hmax : ∀ v, (∀ l ∈ L, Q.B v l = 0) → v ∈ L) :
    Q.arf = 0 := by
  rw [arf, Q.brown_eq_zero_of_metabolic L hq hmax]
  rfl

end SKEFTHawking.Brown.Z4Quadratic
