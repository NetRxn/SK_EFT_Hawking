import SKEFTHawking.QuantumNetwork.ErrorBasisDiamond

/-!
# Exact diamond distance of a qutrit Weyl–Heisenberg leakage channel (Phase 6AK, Wave FU-1)

The single-qubit (`n = 2`) and two-qubit (`n = 4`) Pauli channels are the unitary-error-basis
instances already shipped in `ErrorBasisDiamond`. The **qutrit** (`n = 3`) case is the natural
next instance: the nine **Weyl–Heisenberg operators** `W_{a,b} = X^a Z^b` on `ℂ³`, where `Z` is the
diagonal clock operator `diag(1, ω, ω²)` and `X` is the cyclic shift, form a (non-Hermitian) nice
unitary error basis. Their Choi-block orthogonality is governed by `ω = e^{2πi/3}`, a primitive cube
root of unity, through the geometric identity `∑_{x<3} ω^{e·x} = 3·⟦3 ∣ e⟧`.

Instantiating the dimension-general `diamondDist_errorBasisKraus_eq` at `n = 3` gives, for any
qutrit Weyl (generalised-Pauli) channel `Φ_p(ρ) = ∑_{a,b} p_{a,b} W_{a,b} ρ W_{a,b}ᴴ` with
nonnegative weights summing to `1`,

`diamondDist (weylKraus p) (id) = 1 − p₀₀`  (the total error / leakage probability).

For a single shift channel — `W_{1,0} = X` cyclically permuting the qutrit levels `0 → 1 → 2 → 0`
with probability `1 − p₀₀` — this `1 − p₀₀` is exactly the population that leaks out of any fixed
computational level, so the diamond distance equals the total leakage probability.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

/-! ## The primitive cube root of unity `ω = e^{2πi/3}` -/

/-- The primitive cube root of unity `ω = e^{2πi/3}`. -/
noncomputable def omega3 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- `ω` is a primitive cube root of unity. -/
theorem omega3_isPrimitiveRoot : IsPrimitiveRoot omega3 3 := by
  simpa [omega3] using Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- `ω³ = 1`. -/
theorem omega3_pow_three : omega3 ^ 3 = 1 := omega3_isPrimitiveRoot.pow_eq_one

/-- `1 + ω + ω² = 0` (the cube-root geometric identity). -/
theorem omega3_geom_zero : 1 + omega3 + omega3 ^ 2 = 0 := by
  have h := omega3_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ] using h

/-- For any cube root of unity `ζ ≠ 1`, `1 + ζ + ζ² = 0`. -/
theorem cube_geom_zero {ζ : ℂ} (h3 : ζ ^ 3 = 1) (hne : ζ ≠ 1) : 1 + ζ + ζ ^ 2 = 0 := by
  have h : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) hne
  · linear_combination h2

/-- `ω ≠ 0`. -/
theorem omega3_ne_zero : omega3 ≠ 0 := by
  simp [omega3, Complex.exp_ne_zero]

/-- `‖ω‖ = 1` (root of unity). -/
theorem omega3_norm_one : ‖omega3‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one omega3_pow_three (by norm_num)

/-- `conj ω = ω²` (for a primitive cube root, `ω̄ = ω⁻¹ = ω²`). -/
theorem omega3_conj : (starRingEnd ℂ) omega3 = omega3 ^ 2 := by
  have hmc : omega3 * (starRingEnd ℂ) omega3 = omega3 * omega3 ^ 2 := by
    rw [RCLike.mul_conj, omega3_norm_one,
      show omega3 * omega3 ^ 2 = omega3 ^ 3 by ring, omega3_pow_three]
    norm_num
  exact mul_left_cancel₀ omega3_ne_zero hmc

/-- Entrywise form of a Weyl–Heisenberg operator `W_{a,b} = X^a Z^b` on `ℂ³`:
`W_{a,b}(i,j) = ⟦i = j + a⟧ · ω^{b·j}`. -/
noncomputable def weylOp (a b : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => if i = j + a then omega3 ^ ((b : ℕ) * (j : ℕ)) else 0

/-- `W_{0,0} = 1` (zero shift, trivial phase). -/
theorem weylOp_zero_zero : weylOp 0 0 = 1 := by
  ext i j
  simp only [weylOp, Matrix.of_apply, add_zero, Fin.val_zero, Nat.zero_mul, pow_zero,
    Matrix.one_apply]

/-- **Phase-orthogonality sum:** `∑_{x<3} conj(ω^{b·x})·ω^{d·x} = 3·⟦b=d⟧`. The Hilbert–Schmidt
inner product of two qutrit Weyl operators reduces to this geometric sum. -/
theorem weyl_phase_sum (b d : Fin 3) :
    ∑ x : Fin 3, (starRingEnd ℂ) (omega3 ^ ((b : ℕ) * (x : ℕ))) * omega3 ^ ((d : ℕ) * (x : ℕ))
      = if b = d then (3 : ℂ) else 0 := by
  have hterm : ∀ x : Fin 3,
      (starRingEnd ℂ) (omega3 ^ ((b : ℕ) * (x : ℕ))) * omega3 ^ ((d : ℕ) * (x : ℕ))
        = (omega3 ^ (2 * (b : ℕ) + (d : ℕ))) ^ (x : ℕ) := by
    intro x
    rw [map_pow, omega3_conj, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1; ring
  simp_rw [hterm, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  by_cases hbd : b = d
  · subst hbd
    have hz : omega3 ^ (2 * (b : ℕ) + (b : ℕ)) = 1 := by
      rw [show 2 * (b : ℕ) + (b : ℕ) = 3 * (b : ℕ) by ring, pow_mul, omega3_pow_three, one_pow]
    rw [hz, if_pos rfl]; norm_num
  · rw [if_neg hbd]
    have h3 : (omega3 ^ (2 * (b : ℕ) + (d : ℕ))) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, omega3_pow_three, one_pow]
    have hne : omega3 ^ (2 * (b : ℕ) + (d : ℕ)) ≠ 1 := by
      rw [ne_eq, omega3_isPrimitiveRoot.pow_eq_one_iff_dvd]
      have hb : (b : ℕ) < 3 := b.isLt
      have hd : (d : ℕ) < 3 := d.isLt
      have hbd' : (b : ℕ) ≠ (d : ℕ) := fun h => hbd (Fin.ext h)
      omega
    linear_combination cube_geom_zero h3 hne

/-- **Hilbert–Schmidt orthogonality of the qutrit Weyl basis:**
`tr(W_{a,b}ᴴ W_{c,d}) = 3·⟦(a,b) = (c,d)⟧`. -/
theorem weyl_trace_orthonormal (a b c d : Fin 3) :
    ((weylOp a b)ᴴ * weylOp c d).trace = if a = c ∧ b = d then (3 : ℂ) else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, weylOp,
    Matrix.of_apply]
  by_cases hac : a = c
  · subst hac
    have hrhs : (if a = a ∧ b = d then (3 : ℂ) else 0) = if b = d then (3 : ℂ) else 0 := by
      by_cases hbd : b = d <;> simp [hbd]
    rw [hrhs, ← weyl_phase_sum b d]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single (x + a)
      (fun y _ hy => by rw [if_neg hy, star_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [if_pos rfl, if_pos rfl, starRingEnd_apply]
  · rw [if_neg (fun h => hac h.1)]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : y = x + a
    · have hyc : y ≠ x + c := by rw [hy]; intro h; exact hac (add_left_cancel h)
      rw [if_neg hyc, mul_zero]
    · rw [if_neg hy, star_zero, zero_mul]

/-- **Each Weyl operator is unitary:** `W_{a,b}ᴴ W_{a,b} = 1`. -/
theorem weylOp_unitary (a b : Fin 3) : (weylOp a b)ᴴ * weylOp a b = 1 := by
  ext j j'
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, weylOp, Matrix.of_apply, Matrix.one_apply]
  by_cases hjj : j = j'
  · subst hjj
    rw [if_pos rfl, Finset.sum_eq_single (j + a)
      (fun i _ hi => by rw [if_neg hi, star_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl,
      ← starRingEnd_apply, map_pow, omega3_conj, ← pow_mul, ← pow_add,
      show 2 * ((b : ℕ) * (j : ℕ)) + (b : ℕ) * (j : ℕ) = 3 * ((b : ℕ) * (j : ℕ)) by ring,
      pow_mul, omega3_pow_three, one_pow]
  · rw [if_neg hjj]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i = j + a
    · have hi' : i ≠ j' + a := by rw [hi]; intro h; exact hjj (add_right_cancel h)
      rw [if_neg hi', mul_zero]
    · rw [if_neg hi, star_zero, zero_mul]

/-! ## The qutrit Weyl–Heisenberg unitary error basis (`n = 3`) -/

/-- The nine qutrit Weyl–Heisenberg operators as a unitary error basis on `ℂ³`, indexed by
`Fin 9 ≃ Fin 3 × Fin 3`. -/
noncomputable def weyl3UEB : UnitaryErrorBasis 3 8 where
  op k := weylOp ((finProdFinEquiv (m := 3) (n := 3)).symm k).1
    ((finProdFinEquiv (m := 3) (n := 3)).symm k).2
  op_zero := by
    rw [show ((finProdFinEquiv (m := 3) (n := 3)).symm (0 : Fin 9)).1 = 0 from rfl,
      show ((finProdFinEquiv (m := 3) (n := 3)).symm (0 : Fin 9)).2 = 0 from rfl]
    exact weylOp_zero_zero
  op_unitary k := weylOp_unitary _ _
  op_orthonormal i j := by
    rw [weyl_trace_orthonormal]
    have hiff : ((finProdFinEquiv (m := 3) (n := 3)).symm i).1
          = ((finProdFinEquiv (m := 3) (n := 3)).symm j).1
        ∧ ((finProdFinEquiv (m := 3) (n := 3)).symm i).2
          = ((finProdFinEquiv (m := 3) (n := 3)).symm j).2 ↔ i = j := by
      rw [← Prod.ext_iff, Equiv.apply_eq_iff_eq]
    simp only [hiff, Nat.cast_ofNat]

/-- **Qutrit Weyl (generalised-Pauli) channel** Kraus operators `√(p_k)·W_k` (9 weights). -/
noncomputable def weylKraus (p : Fin 9 → ℝ) : Fin 9 → Matrix (Fin 3) (Fin 3) ℂ :=
  errorBasisKraus weyl3UEB p

/-- **Exact diamond distance of a general qutrit Weyl–Heisenberg channel:**
`diamondDist (weylKraus p) (id) = 1 − p₀` (the total error / leakage probability), for nonnegative
weights summing to `1`. The `n = 3` instance of the dimension-general error-basis theorem; the
generalised-Pauli (clock-shift) error model for a qutrit / single ternary logical level. -/
theorem diamondDist_weylKraus_eq {p : Fin 9 → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : p 0 ≤ 1)
    (hsum : ∑ i, p i = 1) :
    diamondDist (weylKraus p) (idKrausPad 8 3) = 1 - p 0 :=
  diamondDist_errorBasisKraus_eq weyl3UEB h0 h1 hsum

/-! ## Named instance: a pure cyclic-shift leakage channel -/

/-- Probability weights of a **pure cyclic-shift (X-type) leakage channel** on the qutrit: with
probability `1 − q` the identity `W_{0,0}` acts, and with probability `q` the cyclic shift
`X = W_{1,0}` (mapping each computational level to the next, `0 → 1 → 2 → 0`) acts — the population
that "leaks" out of any fixed level. -/
noncomputable def shiftLeakageWeights (q : ℝ) : Fin 9 → ℝ :=
  fun k => if k = 0 then 1 - q else if k = finProdFinEquiv (m := 3) (n := 3) (1, 0) then q else 0

theorem shiftLeakageWeights_zero (q : ℝ) : shiftLeakageWeights q 0 = 1 - q := by
  simp [shiftLeakageWeights]

theorem shiftLeakageWeights_sum (q : ℝ) : ∑ k, shiftLeakageWeights q k = 1 := by
  have hidx : (finProdFinEquiv (m := 3) (n := 3) (1, 0)) ≠ 0 := by decide
  have hsplit : ∀ k : Fin 9, shiftLeakageWeights q k
      = (if k = 0 then (1 - q) else 0)
        + (if k = finProdFinEquiv (m := 3) (n := 3) (1, 0) then q else 0) := by
    intro k
    unfold shiftLeakageWeights
    by_cases hk0 : k = 0
    · subst hk0; rw [if_pos rfl, if_pos rfl, if_neg (Ne.symm hidx), add_zero]
    · rw [if_neg hk0, if_neg hk0, zero_add]
  rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (0 : Fin 9) (fun _ => 1 - q),
    Finset.sum_ite_eq' Finset.univ (finProdFinEquiv (m := 3) (n := 3) (1, 0)) (fun _ => q)]
  simp only [Finset.mem_univ, if_true]; ring

/-- **Exact diamond distance of the cyclic-shift leakage channel equals the leakage probability:**
`diamondDist (weylKraus (shiftLeakageWeights q)) (id) = q`, for `0 ≤ q ≤ 1`. The diamond distance to
the identity is exactly the probability `q` that population leaks out of the computational level. -/
theorem diamondDist_shiftLeakage_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    diamondDist (weylKraus (shiftLeakageWeights q)) (idKrausPad 8 3) = q := by
  have h0 : ∀ i, 0 ≤ shiftLeakageWeights q i := by
    intro i
    unfold shiftLeakageWeights
    by_cases hi0 : i = 0
    · rw [if_pos hi0]; linarith
    · rw [if_neg hi0]
      by_cases hi : i = finProdFinEquiv (m := 3) (n := 3) (1, 0)
      · rw [if_pos hi]; exact hq0
      · rw [if_neg hi]
  have h1 : shiftLeakageWeights q 0 ≤ 1 := by rw [shiftLeakageWeights_zero]; linarith
  rw [diamondDist_weylKraus_eq h0 h1 (shiftLeakageWeights_sum q), shiftLeakageWeights_zero]
  ring

end SKEFTHawking.QuantumNetwork
