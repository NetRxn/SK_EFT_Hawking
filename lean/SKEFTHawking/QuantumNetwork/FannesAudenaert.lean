import SKEFTHawking.QuantumNetwork.SpectralMajorization
import SKEFTHawking.QuantumNetwork.MixedState
import SKEFTHawking.QuantumNetwork.WielandtLidskii
import SKEFTHawking.QuantumNetwork.VonNeumannEntropy
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

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

/-- **Mirsky's inequality, reduced to single-frame existence (the Lidskii–Wielandt core).** Given that for
every subset `S` there is a rank-`|S|` orthogonal projection `P` simultaneously high for `A`
(`∑_{i∈S}λ↓ᵢ(A) ≤ tr(PA)`) and low for `B` (`tr(PB) ≤ ∑_{i∈S}λ↓ᵢ(B)`), the trace-norm Mirsky bound follows:
`∑_{i∈S}(λ↓(A)−λ↓(B)) ≤ tr(PA)−tr(PB) = tr(P(A−B)) ≤ ∑_{j<|S|}λ↓ⱼ(A−B)` (shipped Ky Fan `trace_mul_proj_le`),
which is the interface `H` consumed by `mirsky_of_subset_diff`. Numerically validated (single-frame existence
holds for all random Hermitian pairs); the explicit witness is the top-`|S|` eigenspace of `A − tB` for a
suitable `t ≥ 0`. -/
theorem mirsky_of_proj_exists {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : (A - B).IsHermitian)
    (Hproj : ∀ S : Finset (Fin (Fintype.card ι)), ∃ P : Matrix ι ι ℂ,
      P.IsHermitian ∧ P * P = P ∧ P.trace.re = (S.card : ℝ) ∧
      (∑ i ∈ S, hA.eigenvalues₀ i) ≤ (P * A).trace.re ∧
      (P * B).trace.re ≤ ∑ i ∈ S, hB.eigenvalues₀ i) :
    ∑ k, |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ traceNorm (A - B) := by
  refine mirsky_of_subset_diff hA hB hC (fun S => ?_)
  obtain ⟨P, hPh, hPP, hPk, hPA, hPB⟩ := Hproj S
  have hsplit : (P * (A - B)).trace.re = (P * A).trace.re - (P * B).trace.re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  calc ∑ i ∈ S, (hA.eigenvalues₀ i - hB.eigenvalues₀ i)
      = (∑ i ∈ S, hA.eigenvalues₀ i) - (∑ i ∈ S, hB.eigenvalues₀ i) := by rw [Finset.sum_sub_distrib]
    _ ≤ (P * A).trace.re - (P * B).trace.re := by linarith [hPA, hPB]
    _ = (P * (A - B)).trace.re := hsplit.symm
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card ι) => (j : ℕ) < S.card),
          hC.eigenvalues₀ j := trace_mul_proj_le hC hPh hPP S.card hPk

/-- **Mirsky's inequality, reduced to Wielandt frame-existence (the single remaining Lidskii–Wielandt core).**
Given that for every position tuple `s` there is an orthonormal frame `{wᵣ}` lying in `A`'s eigen-flag —
`wᵣ ∈ span` of the top-`sᵣ` eigenvectors of `toEuclideanLin A` — whose `B`-Rayleigh sum is bounded by the
corresponding sorted `B`-eigenvalues (`∑ᵣ ⟪wᵣ, B wᵣ⟫ ≤ ∑ᵣ λ↓_{sᵣ}(B)`), the trace-norm Mirsky bound
`∑ₖ |λ↓ₖ(A)−λ↓ₖ(B)| ≤ ‖A−B‖₁` follows.

This stages the **entire** Lidskii→Mirsky chain on the one research-grade hypothesis `Hframe` (the Wielandt
min–max "≤" direction). Everything downstream is discharged here: `lidskii_of_frame` supplies the per-tuple
inequality `∑ᵣ λ↓_{sᵣ}(A) ≤ ∑ᵣ λ↓_{sᵣ}(B) + ∑_{j<k} λ↓ⱼ(A−B)`; the matrix `eigenvalues₀` ↔ `LinearMap`
`IsSymmetric.eigenvalues (toEuclideanLin ·)` identification is definitional; the `A−B` operator term is
bridged by `congr` (over `toEuclideanLin (A−B) = toEuclideanLin A − toEuclideanLin B`); and the `Finset`↔tuple
positions are reindexed through the sorted order-embedding `S.orderEmbOfFin`. Composing with the shipped
`mirsky_of_subset_diff` gives the trace-norm conclusion. The remaining `Hframe` brick — numerically validated
for all random Hermitian pairs, with explicit witness the top-`|S|` eigenspace of `A − t B` — is the genuine
Wielandt frame-existence content (absent from Mathlib). -/
theorem mirsky_of_wielandt_frame {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : (A - B).IsHermitian)
    (Hframe : ∀ {k : ℕ} (s : Fin k → ℕ) (hs : ∀ r, s r < Fintype.card ι),
      ∃ w : Fin k → EuclideanSpace ℂ ι, Orthonormal ℂ w ∧
        (∀ r, w r ∈ Submodule.span ℂ
          (⇑((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis finrank_euclideanSpace) ''
            ({i : Fin (Fintype.card ι) | (i : ℕ) ≤ s r} : Set (Fin (Fintype.card ι))))) ∧
        ∑ r, RCLike.re (inner ℂ (w r) (toEuclideanLin B (w r)))
          ≤ ∑ r, hB.eigenvalues₀ ⟨s r, hs r⟩) :
    ∑ k, |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ traceNorm (A - B) := by
  refine mirsky_of_subset_diff hA hB hC (fun S => ?_)
  set s : Fin S.card → ℕ :=
    fun r => ((S.orderEmbOfFin (rfl : S.card = S.card)) r : Fin (Fintype.card ι)).val with hs_def
  have hs : ∀ r, s r < Fintype.card ι := fun r => (S.orderEmbOfFin rfl r).isLt
  obtain ⟨w, hw, hwflag, hB3⟩ := Hframe s hs
  have hLid := lidskii_of_frame (isHermitian_iff_isSymmetric.1 hA) (isHermitian_iff_isSymmetric.1 hB)
    finrank_euclideanSpace hs hw hwflag hB3
  -- positions reindex: a sum over the sorted tuple `s` = a sum over the subset `S`
  have reidx : ∀ (g : Fin (Fintype.card ι) → ℝ),
      (∑ r : Fin S.card, g ⟨s r, hs r⟩) = ∑ i ∈ S, g i := by
    intro g
    conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S (rfl : S.card = S.card)]
    rw [Finset.sum_map]
    rfl
  -- the `A − B` operator term: `eigenvalues (toEuclideanLin A − toEuclideanLin B) = λ↓(A−B)`
  have hCbridge : ((isHermitian_iff_isSymmetric.1 hA).sub (isHermitian_iff_isSymmetric.1 hB)).eigenvalues
      finrank_euclideanSpace = hC.eigenvalues₀ := by
    show ((isHermitian_iff_isSymmetric.1 hA).sub (isHermitian_iff_isSymmetric.1 hB)).eigenvalues
        finrank_euclideanSpace = (isHermitian_iff_isSymmetric.1 hC).eigenvalues finrank_euclideanSpace
    congr 1
    rw [map_sub]
  have key : ∑ i ∈ S, hA.eigenvalues₀ i
      ≤ ∑ i ∈ S, hB.eigenvalues₀ i
        + ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card ι) => (i : ℕ) < S.card), hC.eigenvalues₀ i := by
    rw [← reidx hA.eigenvalues₀, ← reidx hB.eigenvalues₀, ← hCbridge]
    exact hLid
  calc ∑ i ∈ S, (hA.eigenvalues₀ i - hB.eigenvalues₀ i)
      = (∑ i ∈ S, hA.eigenvalues₀ i) - ∑ i ∈ S, hB.eigenvalues₀ i := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (Fintype.card ι) => (i : ℕ) < S.card),
          hC.eigenvalues₀ i := by linarith [key]

/-- **Subadditivity of `negMulLog`:** `η(a+b) ≤ η(a) + η(b)` for `a, b ≥ 0`, where `η = negMulLog`.
A concave function on `[0,∞)` vanishing at `0` is subadditive (`η(a) ≥ (a/(a+b))·η(a+b)` and symmetrically,
summed). This is the easy (unconditional) direction of the per-term Fannes modulus
`|η(s)−η(t)| ≤ η(|s−t|)` and a reusable building block for the classical Fannes entropy-continuity bound
`|H(p)−H(q)| ≤ 2T·log d + η(2T)` (the reverse direction additionally needs `|s−t| ≤ 1/2`). -/
theorem negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (a + b) ≤ Real.negMulLog a + Real.negMulLog b := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h0 | hpos
  · have ha0 : a = 0 := le_antisymm (by linarith) ha
    have hb0 : b = 0 := le_antisymm (by linarith) hb
    simp [ha0, hb0, Real.negMulLog_zero]
  · have hne : a + b ≠ 0 := ne_of_gt hpos
    have hsmem : (a + b) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr (le_of_lt hpos)
    have h0mem : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr (le_refl 0)
    have hpa : 0 ≤ a / (a + b) := div_nonneg ha (le_of_lt hpos)
    have hpb : 0 ≤ b / (a + b) := div_nonneg hb (le_of_lt hpos)
    have hsum : a / (a + b) + b / (a + b) = 1 := by field_simp
    have hca := Real.concaveOn_negMulLog.2 hsmem h0mem hpa hpb hsum
    have hcb := Real.concaveOn_negMulLog.2 hsmem h0mem hpb hpa (by rw [add_comm]; exact hsum)
    simp only [Real.negMulLog_zero, mul_zero, add_zero, smul_eq_mul] at hca hcb
    rw [div_mul_cancel₀ a hne] at hca
    rw [div_mul_cancel₀ b hne] at hcb
    have hfac : a / (a + b) * Real.negMulLog (a + b) + b / (a + b) * Real.negMulLog (a + b)
        = Real.negMulLog (a + b) := by rw [← add_mul, hsum, one_mul]
    linarith [hca, hcb, hfac]

/-- **Jensen bound for `negMulLog` (the Fannes concavity step):** `∑ᵢ η(δᵢ) ≤ d · η((∑ᵢ δᵢ)/d)` for
`δᵢ ≥ 0`, `η = negMulLog`. Concavity of `negMulLog` (`ConcaveOn.le_map_sum` with uniform weights `1/d`)
caps the entropy of the difference-magnitudes by the value at their mean. With `∑ᵢ δᵢ = 2T` this gives
`∑ᵢ η(δᵢ) ≤ d·η(2T/d) = 2T·log d + η(2T)` — the right-hand side of the classical Fannes bound. -/
theorem sum_negMulLog_le_card_mul {d : ℕ} (hd : 0 < d) (δ : Fin d → ℝ) (hδ : ∀ i, 0 ≤ δ i) :
    ∑ i, Real.negMulLog (δ i) ≤ (d : ℝ) * Real.negMulLog ((∑ i, δ i) / d) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin d)), (0:ℝ) ≤ (1 / d : ℝ) := fun i _ => by positivity
  have hw1 : ∑ _i : Fin d, (1 / d : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_self (ne_of_gt hdR)]
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin d)), δ i ∈ Set.Ici (0:ℝ) :=
    fun i _ => Set.mem_Ici.mpr (hδ i)
  have hJ := Real.concaveOn_negMulLog.le_map_sum hw0 hw1 hmem
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hJ
  have harg : (1 / d : ℝ) * ∑ i, δ i = (∑ i, δ i) / d := by ring
  rw [harg] at hJ
  have h2 := mul_le_mul_of_nonneg_left hJ (le_of_lt hdR)
  rwa [← mul_assoc, mul_one_div, div_self (ne_of_gt hdR), one_mul] at h2

/-- **Classical Fannes entropy-continuity bound, reduced to the per-term modulus (the F2/P2 assembly).**
Given the per-term modulus `|η(pᵢ)−η(qᵢ)| ≤ η(|pᵢ−qᵢ|)` (which holds whenever `|pᵢ−qᵢ| ≤ 1/2`; `η = negMulLog`),
the Shannon-entropy difference is bounded by the Jensen envelope:
`|∑ᵢ η(pᵢ) − ∑ᵢ η(qᵢ)| ≤ d · η((∑ᵢ|pᵢ−qᵢ|)/d)`. With `∑ᵢ|pᵢ−qᵢ| = 2T` the right-hand side equals
`2T·log d + η(2T)` — the classical Fannes bound. Proof: linearity of the sum, the triangle inequality
(`Finset.abs_sum_le_sum_abs`), the per-term modulus hypothesis, then the shipped Jensen step
`sum_negMulLog_le_card_mul`. This stages the entire classical Fannes inequality on the single analytic
residual `hmod` (the per-term modulus of `negMulLog`), whose forward direction is `negMulLog_add_le` and whose
reverse direction is a `|pᵢ−qᵢ| ≤ 1/2` calculus lemma. -/
theorem fannes_entropy_bound_of_modulus {d : ℕ} (hd : 0 < d) (p q : Fin d → ℝ)
    (hmod : ∀ i, |Real.negMulLog (p i) - Real.negMulLog (q i)| ≤ Real.negMulLog (|p i - q i|)) :
    |∑ i, Real.negMulLog (p i) - ∑ i, Real.negMulLog (q i)|
      ≤ (d : ℝ) * Real.negMulLog ((∑ i, |p i - q i|) / d) := by
  have hstep1 : |∑ i, Real.negMulLog (p i) - ∑ i, Real.negMulLog (q i)|
      = |∑ i, (Real.negMulLog (p i) - Real.negMulLog (q i))| := by rw [Finset.sum_sub_distrib]
  rw [hstep1]
  calc |∑ i, (Real.negMulLog (p i) - Real.negMulLog (q i))|
      ≤ ∑ i, |Real.negMulLog (p i) - Real.negMulLog (q i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, Real.negMulLog (|p i - q i|) := Finset.sum_le_sum (fun i _ => hmod i)
    _ ≤ (d : ℝ) * Real.negMulLog ((∑ i, |p i - q i|) / d) :=
        sum_negMulLog_le_card_mul hd (fun i => |p i - q i|) (fun i => abs_nonneg _)

/-- **Von Neumann entropy as the Shannon entropy of the sorted spectrum:**
`S(ρ) = ∑ₖ negMulLog(λ↓ₖ(ρ))`. Since `negMulLog`-sums are permutation-invariant, the entropy (defined over
the unsorted eigenvalues) equals the sum over the descending-sorted `eigenvalues₀`. This is the bridge that
lets the classical Fannes–Audenaert bound — applied to the eigenvalue *distributions* — read directly as a
statement about `vonNeumannEntropy`. -/
theorem vonNeumannEntropy_eq_sum_negMulLog_eigenvalues₀ {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy hρ = ∑ k, Real.negMulLog (hρ.eigenvalues₀ k) := by
  rw [vonNeumannEntropy]
  exact sum_eigenvalues_eq_sum_eigenvalues₀ hρ Real.negMulLog

/-- **Quantum Fannes–Audenaert continuity, reduced to Mirsky + classical Fannes–Audenaert (F3 assembly).**
Given (i) the Mirsky trace-norm spectral bound `∑ₖ|λ↓ₖ(ρ)−λ↓ₖ(σ)| ≤ ‖ρ−σ‖₁` (the F1b content, staged on the
Wielandt frame-existence hypothesis `Hframe` via `mirsky_of_wielandt_frame`), and (ii) the classical
Fannes–Audenaert inequality applied to the two eigenvalue distributions — `|S(ρ)−S(σ)| ≤ H_d(Tλ)` where
`Tλ = ½∑ₖ|λ↓ₖ(ρ)−λ↓ₖ(σ)|` is the spectral total-variation distance and `H_d = Real.qaryEntropy d` is the
Audenaert envelope `T·log(d−1)+h(T)` (the F2 content) — the quantum continuity bound in *trace distance*
follows: `|S(ρ)−S(σ)| ≤ H_d(½‖ρ−σ‖₁)`.

The coupling is the strict monotonicity of `qaryEntropy` on `[0, 1−1/d]` (`qaryEntropy_strictMonoOn`): Mirsky
gives `Tλ ≤ ½‖ρ−σ‖₁`, and on the increasing branch the bound transports from the (smaller) spectral
total-variation to the (larger) trace distance. The hypothesis `½‖ρ−σ‖₁ ≤ 1−1/d` keeps both distances on that
branch (outside it the trivial `|S(ρ)−S(σ)| ≤ log d` ceiling already applies). This stages F3 entirely on the
two precise, decomposition-backed F-residuals (`Hframe` for Mirsky, the classical Audenaert inequality for F2),
both isolated as named hypotheses; all assembly — entropy↔spectrum bridge, Mirsky transport, monotone
envelope — is discharged here. -/
theorem quantum_fannes_audenaert_of_mirsky {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hd : 2 ≤ Fintype.card ι)
    (hTV : traceNorm (ρ - σ) / 2 ≤ 1 - 1 / (Fintype.card ι : ℝ))
    (hMirsky : ∑ k, |hρ.eigenvalues₀ k - hσ.eigenvalues₀ k| ≤ traceNorm (ρ - σ))
    (hAud : |vonNeumannEntropy hρ - vonNeumannEntropy hσ|
              ≤ Real.qaryEntropy (Fintype.card ι)
                  ((∑ k, |hρ.eigenvalues₀ k - hσ.eigenvalues₀ k|) / 2)) :
    |vonNeumannEntropy hρ - vonNeumannEntropy hσ|
      ≤ Real.qaryEntropy (Fintype.card ι) (traceNorm (ρ - σ) / 2) := by
  refine hAud.trans ?_
  set TL := (∑ k, |hρ.eigenvalues₀ k - hσ.eigenvalues₀ k|) / 2 with hTL
  set Ts := traceNorm (ρ - σ) / 2 with hTs
  have hTL_nonneg : 0 ≤ TL := by rw [hTL]; positivity
  have hle : TL ≤ Ts := by rw [hTL, hTs]; linarith [hMirsky]
  have hTs_mem : Ts ∈ Set.Icc (0 : ℝ) (1 - 1 / (Fintype.card ι : ℝ)) :=
    ⟨le_trans hTL_nonneg hle, hTV⟩
  have hTL_mem : TL ∈ Set.Icc (0 : ℝ) (1 - 1 / (Fintype.card ι : ℝ)) :=
    ⟨hTL_nonneg, le_trans hle hTV⟩
  exact (Real.qaryEntropy_strictMonoOn hd).monotoneOn hTL_mem hTs_mem hle

end SKEFTHawking.QuantumNetwork
