import SKEFTHawking.QuantumNetwork.FannesAudenaert

/-!
# Mirsky's inequality, UNCONDITIONAL (no Wielandt / no `hB3`)

`∑ₖ |λ↓ₖ(A) − λ↓ₖ(B)| ≤ ‖A − B‖₁` for Hermitian `A, B`, proved directly from **Weyl monotonicity**
(`A ≤ B ⟹ λ↓ₖ(A) ≤ λ↓ₖ(B)`) via the positive/negative-part split of `C = A − B`, with NO arbitrary-subset
Lidskii / Wielandt frame-existence. The substrate's `mirsky_of_subset_diff` reduces Mirsky to the *sharp*
arbitrary-subset Lidskii (which needs the unbuilt Wielandt achievability `hB3`); this module reaches the SAME
headline by the cruder-but-sufficient `∑ₖ(λ↓ₖA−λ↓ₖB)₊ ≤ tr(C₊)` bound (`+` = positive part), which follows
from Weyl monotonicity alone. Numerically validated (20000 random Hermitian pairs, gap ≤ 5e-15).

Key idea: with `M := B + C₊` (`C₊ = posPart (A−B)`), `A ⪯ M` and `B ⪯ M`, so for each `k`
`λ↓ₖ(A) − λ↓ₖ(B) ≤ λ↓ₖ(M) − λ↓ₖ(B) =: eₖ ≥ 0`, and `∑ₖ eₖ = tr(M) − tr(B) = tr(C₊) = eigPosSum`. Summing the
positive parts and applying the same to `B − A` closes Mirsky via `traceNorm_hermitian_eq`.

This is a **positive-part / matrix-splitting** argument: the Lidskii–Mirsky family follows from Weyl monotonicity +
trace alone (verified here by the kernel-pure proof below), with no Wielandt minimax / interlacing / frame
construction. The matrix-splitting technique for an elementary proof of the Lidskii–Mirsky–Wielandt theorem is due
to C. K. Li & R. Mathias, "The Lidskii–Mirsky–Wielandt theorem — additive and multiplicative versions," *Numer.
Math.* **81** (1999), 377–413 (DOI 10.1007/s002110050397; citation independently verified). The specific
Mirsky-trace-norm form proved here was rediscovered via numerical test-before-build and is established here by
machine-checked proof, not by appeal to the reference.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms; no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix

open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Weyl monotonicity (matrix sorted eigenvalues).** If `A ≤ B` in the Loewner order (`B − A` PSD), then
every sorted eigenvalue is monotone: `λ↓ₖ(A) ≤ λ↓ₖ(B)`. Transported from the LinearMap Courant–Fischer bound
`weyl_single_lower_of_eq` (`λ↓ₖ(S) + λ↓ₙ₋₁(R) ≤ λ↓ₖ(S+R)`) with `R = B − A` PSD (so `λ↓ₙ₋₁(R) ≥ 0`). -/
theorem eigenvalues₀_mono {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hBA : (B - A).PosSemidef) (k : Fin (Fintype.card ι)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  have hAs : (toEuclideanLin A).IsSymmetric := isHermitian_iff_isSymmetric.1 hA
  have hBs : (toEuclideanLin B).IsSymmetric := isHermitian_iff_isSymmetric.1 hB
  have hBAs : (toEuclideanLin (B - A)).IsSymmetric := isHermitian_iff_isSymmetric.1 hBA.1
  have hTeq : toEuclideanLin B = toEuclideanLin A + toEuclideanLin (B - A) := by
    rw [← map_add]; congr 1; abel
  have hk : (k : ℕ) < Fintype.card ι := k.isLt
  have hN : 0 < Fintype.card ι := lt_of_le_of_lt (Nat.zero_le _) hk
  have hweyl := weyl_single_lower_of_eq (𝕜 := ℂ) finrank_euclideanSpace hBs hAs hBAs hTeq hk
  -- the smallest eigenvalue of the PSD perturbation `B − A` is ≥ 0
  have hmin : 0 ≤ hBAs.eigenvalues finrank_euclideanSpace ⟨Fintype.card ι - 1, by omega⟩ := by
    have hbridge : hBAs.eigenvalues finrank_euclideanSpace ⟨Fintype.card ι - 1, by omega⟩
        = hBA.1.eigenvalues₀ ⟨Fintype.card ι - 1, by omega⟩ := rfl
    rw [hbridge]
    obtain ⟨i, hi⟩ : ∃ i, hBA.1.eigenvalues₀ ⟨Fintype.card ι - 1, by omega⟩ = hBA.1.eigenvalues i :=
      ⟨Fintype.equivOfCardEq (Fintype.card_fin _) ⟨Fintype.card ι - 1, by omega⟩, by
        simp only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]⟩
    rw [hi]; exact hBA.eigenvalues_nonneg i
  -- bridge matrix eigenvalues₀ to the LinearMap eigenvalues (defeq through `isHermitian_iff_isSymmetric`)
  have hAbridge : hAs.eigenvalues finrank_euclideanSpace ⟨k, hk⟩ = hA.eigenvalues₀ k := rfl
  have hBbridge : hBs.eigenvalues finrank_euclideanSpace ⟨k, hk⟩ = hB.eigenvalues₀ k := rfl
  rw [hAbridge, hBbridge] at hweyl
  linarith [hweyl, hmin]

/-- **The PSD-split core.** `∑ₖ (λ↓ₖ(A) − λ↓ₖ(B))₊ ≤ tr((A−B)₊)` (`₊` = positive part, `eigPosSum`). With
`M := B + (A−B)₊` we have `A ⪯ M` and `B ⪯ M` (PSD differences `(A−B)₋`, `(A−B)₊`), so Weyl monotonicity gives
`(λ↓ₖA − λ↓ₖB)₊ ≤ λ↓ₖM − λ↓ₖB`, and `∑ₖ(λ↓ₖM − λ↓ₖB) = tr M − tr B = tr((A−B)₊) = eigPosSum`. -/
theorem sum_max_diff_le {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : (A - B).IsHermitian) :
    ∑ k, max (hA.eigenvalues₀ k - hB.eigenvalues₀ k) 0 ≤ eigPosSum hC := by
  set M := B + posPart hC with hMdef
  have hposH : (posPart hC).IsHermitian := cfc_isHermitian hC _
  have hMh : M.IsHermitian := hB.add hposH
  -- M − B = posPart hC ⪰ 0
  have hBM : (M - B).PosSemidef := by
    have : M - B = posPart hC := by rw [hMdef]; abel
    rw [this]; exact posPart_posSemidef hC
  -- M − A = negPart hC ⪰ 0  (since A − B = posPart hC − negPart hC)
  have hAM : (M - A).PosSemidef := by
    have heq : M - A = negPart hC := by
      have h := self_eq_posPart_sub_negPart hC
      set p := posPart hC
      set q := negPart hC
      rw [hMdef]
      calc B + p - A = p - (A - B) := by abel
        _ = p - (p - q) := by rw [h]
        _ = q := by abel
    rw [heq]; exact negPart_posSemidef hC
  have hkey : ∀ k, max (hA.eigenvalues₀ k - hB.eigenvalues₀ k) 0
      ≤ hMh.eigenvalues₀ k - hB.eigenvalues₀ k := by
    intro k
    have hAle := eigenvalues₀_mono hA hMh hAM k
    have hBle := eigenvalues₀_mono hB hMh hBM k
    exact max_le (by linarith) (by linarith)
  calc ∑ k, max (hA.eigenvalues₀ k - hB.eigenvalues₀ k) 0
      ≤ ∑ k, (hMh.eigenvalues₀ k - hB.eigenvalues₀ k) := Finset.sum_le_sum (fun k _ => hkey k)
    _ = (∑ k, hMh.eigenvalues₀ k) - ∑ k, hB.eigenvalues₀ k := by rw [Finset.sum_sub_distrib]
    _ = M.trace.re - B.trace.re := by
        rw [sum_eigenvalues₀_eq_trace_re hMh, sum_eigenvalues₀_eq_trace_re hB]
    _ = (posPart hC).trace.re := by rw [hMdef, Matrix.trace_add, Complex.add_re]; ring
    _ = eigPosSum hC := (eigPosSum_eq_re_trace_posPart hC).symm

/-- **Mirsky's inequality, UNCONDITIONAL** — `∑ₖ |λ↓ₖ(A) − λ↓ₖ(B)| ≤ ‖A − B‖₁`. No Wielandt frame-existence
`hB3`, no arbitrary-subset Lidskii: the positive/negative parts of `d := λ↓(A) − λ↓(B)` are each bounded by the
positive part of `A − B` resp. `B − A` (`sum_max_diff_le`, from Weyl monotonicity), and
`eigPosSum(A−B) + eigPosSum(B−A) = ‖A−B‖₁` (`traceNorm_hermitian_eq`). Discharges the `hMirsky` hypothesis of
`quantum_fannes_audenaert_of_mirsky`. -/
theorem mirsky_unconditional {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ k, |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ traceNorm (A - B) := by
  have hC : (A - B).IsHermitian := hA.sub hB
  have hC' : (B - A).IsHermitian := hB.sub hA
  have habs : ∀ k, |hA.eigenvalues₀ k - hB.eigenvalues₀ k|
      = max (hA.eigenvalues₀ k - hB.eigenvalues₀ k) 0
        + max (hB.eigenvalues₀ k - hA.eigenvalues₀ k) 0 := by
    intro k
    rcases le_total (hA.eigenvalues₀ k) (hB.eigenvalues₀ k) with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  rw [Finset.sum_congr rfl (fun k _ => habs k), Finset.sum_add_distrib]
  have h1 := sum_max_diff_le hA hB hC
  have h2 := sum_max_diff_le hB hA hC'
  have htn : traceNorm (A - B) = eigPosSum hC + eigPosSum hC' := by
    have e1 := traceNorm_hermitian_eq hC
    have e2 := traceNorm_hermitian_eq hC'
    have e3 : traceNorm (B - A) = traceNorm (A - B) := by
      rw [show B - A = -(A - B) from by abel, traceNorm_neg]
    have e4 : (B - A).trace.re = -(A - B).trace.re := by
      rw [show B - A = -(A - B) from by abel, Matrix.trace_neg, Complex.neg_re]
    linarith [e1, e2, e3, e4]
  rw [htn]; linarith [h1, h2]

/-- **Quantum Fannes–Audenaert continuity in trace distance — `hMirsky` discharged (no `hB3`/Wielandt).**
The Mirsky hypothesis of `quantum_fannes_audenaert_of_mirsky` is now supplied unconditionally by
`mirsky_unconditional`, so the trace-distance entropy-continuity bound `|S(ρ)−S(σ)| ≤ H_d(½‖ρ−σ‖₁)` rests
*only* on the classical sharp-Audenaert envelope `hAud` (the `log(d−1)` constant, a maximization absent from
Mathlib — a residual entirely separate from, and smaller than, the eliminated Wielandt frame-existence `hB3`).
The Fannes-constant (`log d`) spectral form `quantum_fannes_bound` is already fully unconditional. -/
theorem quantum_fannes_audenaert {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hd : 2 ≤ Fintype.card ι)
    (hTV : traceNorm (ρ - σ) / 2 ≤ 1 - 1 / (Fintype.card ι : ℝ))
    (hAud : |vonNeumannEntropy hρ - vonNeumannEntropy hσ|
              ≤ Real.qaryEntropy (Fintype.card ι)
                  ((∑ k, |hρ.eigenvalues₀ k - hσ.eigenvalues₀ k|) / 2)) :
    |vonNeumannEntropy hρ - vonNeumannEntropy hσ|
      ≤ Real.qaryEntropy (Fintype.card ι) (traceNorm (ρ - σ) / 2) :=
  quantum_fannes_audenaert_of_mirsky hρ hσ hd hTV (mirsky_unconditional hρ hσ) hAud

/-- `Real.negMulLog` is monotone increasing on `[0, e⁻¹]` (its derivative `−log x − 1 ≥ 0` there). -/
theorem negMulLog_monotoneOn : MonotoneOn Real.negMulLog (Set.Icc 0 (Real.exp (-1))) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) Real.continuous_negMulLog.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (Real.differentiableAt_negMulLog (ne_of_gt hx.1)).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [Real.deriv_negMulLog (ne_of_gt hx.1)]
    have hlog : Real.log x < -1 := by
      have := Real.log_lt_log hx.1 hx.2; rwa [Real.log_exp] at this
    linarith

/-- **Quantum Fannes entropy continuity in TRACE DISTANCE — fully unconditional (no `hB3`, no `hAud`).**
For density operators `ρ, σ` with per-index spectral gap `≤ ½` and trace distance within the Fannes regime
`‖ρ−σ‖₁ ≤ d/e`, the von Neumann entropies obey `|S(ρ) − S(σ)| ≤ d · η(‖ρ−σ‖₁ / d)` (`η = negMulLog`, the
Fannes envelope `T·log d + η(T)` with `T = ‖ρ−σ‖₁`). The operationally-composable certificate: a trace-distance
bound on the state directly bounds the entropy/entanglement deviation, with NO unproven residual — only the
honest input/range hypotheses inherent to any Fannes-type estimate. Proof: the unconditional spectral form
`quantum_fannes_bound` gives the bound at the spectral ℓ¹ distance `∑ₖ|λ↓ₖρ−λ↓ₖσ|`; `mirsky_unconditional`
(Li–Mathias) shows that `≤ ‖ρ−σ‖₁`; and `negMulLog` is monotone on `[0, e⁻¹]` (`negMulLog_monotoneOn`), so the
envelope transports from the spectral distance up to the trace distance. -/
theorem quantum_fannes_trace_distance {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {ρ σ : Matrix ι ι ℂ} (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (hgap : ∀ k, |hρ.1.isHermitian.eigenvalues₀ k - hσ.1.isHermitian.eigenvalues₀ k| ≤ 1/2)
    (hrange : traceNorm (ρ - σ) / Fintype.card ι ≤ Real.exp (-1)) :
    |vonNeumannEntropy hρ.1.isHermitian - vonNeumannEntropy hσ.1.isHermitian|
      ≤ (Fintype.card ι : ℝ) * Real.negMulLog (traceNorm (ρ - σ) / Fintype.card ι) := by
  have hdpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set a := (∑ k, |hρ.1.isHermitian.eigenvalues₀ k - hσ.1.isHermitian.eigenvalues₀ k|)
    / Fintype.card ι with ha
  set b := traceNorm (ρ - σ) / Fintype.card ι with hb
  have hmirsky := mirsky_unconditional hρ.1.isHermitian hσ.1.isHermitian
  have hsum_nonneg : 0 ≤ ∑ k, |hρ.1.isHermitian.eigenvalues₀ k - hσ.1.isHermitian.eigenvalues₀ k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have hab : a ≤ b := by rw [ha, hb]; exact div_le_div_of_nonneg_right hmirsky hdpos.le
  have ha_nonneg : 0 ≤ a := div_nonneg hsum_nonneg (le_of_lt hdpos)
  have ha_mem : a ∈ Set.Icc (0 : ℝ) (Real.exp (-1)) := ⟨ha_nonneg, le_trans hab hrange⟩
  have hb_mem : b ∈ Set.Icc (0 : ℝ) (Real.exp (-1)) := ⟨le_trans ha_nonneg hab, hrange⟩
  refine (quantum_fannes_bound hρ hσ hgap).trans ?_
  exact mul_le_mul_of_nonneg_left (negMulLog_monotoneOn ha_mem hb_mem hab) (le_of_lt hdpos)

end SKEFTHawking.QuantumNetwork
