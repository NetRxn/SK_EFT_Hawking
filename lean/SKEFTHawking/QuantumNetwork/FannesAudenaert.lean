import SKEFTHawking.QuantumNetwork.SpectralMajorization
import SKEFTHawking.QuantumNetwork.MixedState
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Toward Fannes–Audenaert entropy continuity (Phase 6AL, Wave 4, items F1b/F2/F3)

This module assembles the Fannes–Audenaert entropy-continuity bound from the Ky Fan / spectral-majorization
layer (`SpectralMajorization.lean`) and the mixed-state trace-norm API (`MixedState.lean`).

Shipped here so far: the **trace-norm ↔ sorted-eigenvalue bridge** `traceNorm_eq_sum_abs_eigenvalues₀`
(`‖A‖₁ = ∑ₖ |λ↓ₖ(A)|`), which is the right-hand side of Mirsky's inequality and the spectral form used by
the entropy assembly. (The Mirsky ℓ¹ majorization step — Lidskii–Wielandt + Karamata/HLP convex-majorization,
both absent from Mathlib — and the classical Fannes–Audenaert inequality remain to be built; see the
Phase 6AL roadmap Wave-4 block for the precise decomposition.)

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Trace norm via the sorted spectrum:** `‖A‖₁ = ∑ₖ |λ↓ₖ(A)|` for Hermitian `A`. This is the
right-hand side of Mirsky's inequality and the spectral form consumed by the entropy continuity assembly. -/
theorem traceNorm_eq_sum_abs_eigenvalues₀ {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    traceNorm A = ∑ k, |hA.eigenvalues₀ k| := by
  rw [traceNorm_hermitian hA]
  exact sum_eigenvalues_eq_sum_eigenvalues₀ hA (fun x => |x|)

/-- The sum of all sorted eigenvalues equals the real part of the trace. -/
theorem sum_eigenvalues₀_eq_trace_re {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    ∑ k, hA.eigenvalues₀ k = (A.trace).re := by
  rw [← sum_eigenvalues_eq_sum_eigenvalues₀ hA (fun x => x), hA.trace_eq_sum_eigenvalues,
    Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => (Complex.ofReal_re _).symm

/-- **Mirsky's inequality, reduced to the arbitrary-subset Lidskii–Wielandt bound (`H`).** If every
subset sum of the sorted eigenvalue difference `λ↓(A)−λ↓(B)` is bounded by the corresponding largest
eigenvalues of `C = A−B` (`H` — the Lidskii–Wielandt content), then the trace-norm Mirsky bound
`∑ₖ |λ↓ₖ(A)−λ↓ₖ(B)| ≤ ‖A−B‖₁` follows. Proof: sort the difference descending (`Tuple.sort`), so each
prefix sum is a top-subset sum bounded by `H`; with equal totals (trace) feed the shipped
`abs_sum_le_of_prefix`, then `traceNorm_eq_sum_abs_eigenvalues₀`. The remaining Wielandt frame-existence
brick discharges `H`. -/
theorem mirsky_of_subset_diff {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : (A - B).IsHermitian)
    (H : ∀ S : Finset (Fin (Fintype.card ι)),
        ∑ i ∈ S, (hA.eigenvalues₀ i - hB.eigenvalues₀ i)
          ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card ι) => (j : ℕ) < S.card),
              hC.eigenvalues₀ j) :
    ∑ k, |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ traceNorm (A - B) := by
  set N := Fintype.card ι with hN
  set δ : Fin N → ℝ := fun i => hA.eigenvalues₀ i - hB.eigenvalues₀ i with hδ
  -- descending sort of δ via ascending sort of -δ
  set σ : Equiv.Perm (Fin N) := Tuple.sort (fun i => - δ i) with hσ
  set d : Fin N → ℝ := fun i => δ (σ i) with hd
  have hd_anti : Antitone d := by
    have hmono : Monotone (fun i => -(δ (σ i))) := Tuple.monotone_sort (fun i => - δ i)
    intro a b hab
    exact neg_le_neg_iff.mp (hmono hab)
  -- prefix sums of the sorted difference are top-subset sums, bounded by H
  have hpre : ∀ m : ℕ,
      ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < m), d i
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < m), hC.eigenvalues₀ j := by
    intro m
    set F : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => (i : ℕ) < m) with hF
    set S : Finset (Fin N) := F.image σ with hSdef
    have hinj : ∀ x ∈ F, ∀ y ∈ F, σ x = σ y → x = y := fun x _ y _ h => σ.injective h
    have hsum_d : ∑ i ∈ F, d i = ∑ i ∈ S, δ i := by
      rw [hSdef, Finset.sum_image hinj]
    have hcard : S.card = F.card := Finset.card_image_of_injective F σ.injective
    have hfilter : Finset.univ.filter (fun j : Fin N => (j : ℕ) < S.card)
        = Finset.univ.filter (fun j : Fin N => (j : ℕ) < m) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcard, hF, Fin.card_filter_val_lt]
      have := j.isLt
      omega
    calc ∑ i ∈ F, d i = ∑ i ∈ S, δ i := hsum_d
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < S.card), hC.eigenvalues₀ j := H S
      _ = ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < m), hC.eigenvalues₀ j := by
          rw [hfilter]
  -- equal totals: ∑ d = ∑ λ↓(C), via the trace
  have htot : ∑ i, d i = ∑ j, hC.eigenvalues₀ j := by
    have hsumd : ∑ i, d i = ∑ i, δ i := Equiv.sum_comp σ δ
    rw [hsumd, hδ, Finset.sum_sub_distrib, sum_eigenvalues₀_eq_trace_re hA,
      sum_eigenvalues₀_eq_trace_re hB, sum_eigenvalues₀_eq_trace_re hC,
      ← Complex.sub_re, ← Matrix.trace_sub]
  -- apply the shipped majorization → ℓ¹ reduction, then re-index the absolute values
  have hkey : ∑ i, |d i| ≤ ∑ j, |hC.eigenvalues₀ j| :=
    abs_sum_le_of_prefix hd_anti hpre htot
  have habs : ∑ i, |d i| = ∑ k, |hA.eigenvalues₀ k - hB.eigenvalues₀ k| := by
    have : ∑ i, |d i| = ∑ i, |δ i| := Equiv.sum_comp σ (fun i => |δ i|)
    rw [this, hδ]
  rw [traceNorm_eq_sum_abs_eigenvalues₀ hC, ← habs]
  exact hkey

end SKEFTHawking.QuantumNetwork
