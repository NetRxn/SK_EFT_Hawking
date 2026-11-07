import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Combinatorics.Colex
import Mathlib.Tactic

/-!
# Exact row/subset determinant recurrence

The finite subset scatter is the mathematical recurrence of
`src/vestigial/original_coefficients.py::determinant_polynomial`. Each prefix state is a
sorted-column minor. At the mask level, the shift-and test, singleton OR, and shifted
population count implement membership, insertion, and the additional inversion parity.
Absent sparse entries and absent states have coefficient zero.

This file treats coefficients as elements of an arbitrary commutative ring. It does not
formalize Python polynomial storage, RawJet arithmetic, or assembly of the original matrix.
-/

namespace SKEFTHawking.ADW.FiniteDeterminantSubsetDP

open scoped BigOperators

variable {α R : Type*} [LinearOrder α] [CommRing R]

/-- The row-prefix minor on columns listed in their increasing order. -/
def prefixMinor (M : ℕ → α → R) (k : ℕ) (s : Finset α) (hs : s.card = k) :
    Matrix (Fin k) (Fin k) R :=
  fun i j ↦ M i (s.orderEmbOfFin hs j)

/-- The inversion count added by appending column j to the prefix on s. -/
def appendInversions (s : Finset α) (j : α) : ℕ :=
  (s.filter (fun c ↦ j < c)).card

/-- The row/subset recurrence, with an absent state valued at zero. -/
def rowSubsetDP (M : ℕ → α → R) : ℕ → Finset α → R
  | 0, s => if s = ∅ then 1 else 0
  | k + 1, s =>
    ∑ j ∈ s, rowSubsetDP M k (s.erase j) * M k j * (-1) ^ appendInversions (s.erase j) j

private theorem cardErase {k : ℕ} {s : Finset α} (hs : s.card = k + 1)
    {j : α} (hj : j ∈ s) : (s.erase j).card = k := by
  rw [Finset.card_erase_of_mem hj, hs, Nat.add_sub_cancel]

private theorem orderEmbOfFin_erase {k : ℕ} {s : Finset α} (hs : s.card = k + 1)
    (t : Fin (k + 1)) :
    (fun i ↦ s.orderEmbOfFin hs (t.succAbove i)) =
      (s.erase (s.orderEmbOfFin hs t)).orderEmbOfFin
        (cardErase hs (s.orderEmbOfFin_mem hs t)) := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_erase.mpr
      ⟨fun h ↦ Fin.succAbove_ne t i ((s.orderEmbOfFin hs).injective h),
        s.orderEmbOfFin_mem hs _⟩
  · exact (s.orderEmbOfFin hs).strictMono.comp (Fin.strictMono_succAbove t)

/-- The appended inversion count is the number of sorted columns to the right
of the new column, so its parity is the last-row Laplace parity. -/
theorem appendInversions_orderEmb {k : ℕ} {s : Finset α} (hs : s.card = k + 1)
    (t : Fin (k + 1)) :
    appendInversions (s.erase (s.orderEmbOfFin hs t)) (s.orderEmbOfFin hs t) =
      k - (t : ℕ) := by
  let e := s.orderEmbOfFin hs
  have h : (Finset.Ioi t).card =
      ((s.erase (e t)).filter (fun c ↦ e t < c)).card := by
    apply Finset.card_bij (fun i _ ↦ e i)
    · intro i hi
      have hlt := e.strictMono (Finset.mem_Ioi.mp hi)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨ne_of_gt hlt, s.orderEmbOfFin_mem hs i⟩, hlt⟩
    · exact fun i _ j _ hij ↦ e.injective hij
    · intro c hc
      obtain ⟨hcs, hlt⟩ := Finset.mem_filter.mp hc
      have hmem := (Finset.mem_erase.mp hcs).2
      obtain ⟨i, hi⟩ : c ∈ Set.range e := by
        simpa only [e, Finset.range_orderEmbOfFin, Finset.mem_coe] using hmem
      exact ⟨i, Finset.mem_Ioi.mpr (e.lt_iff_lt.mp (hi ▸ hlt)), hi⟩
  rw [Fin.card_Ioi] at h
  simpa [appendInversions, e] using h.symm

private theorem laplaceSign_eq_appendSign (k : ℕ) (t : Fin (k + 1)) :
    (-1 : R) ^ (k + (t : ℕ)) = (-1 : R) ^ (k - (t : ℕ)) := by
  have ht : (t : ℕ) ≤ k := by omega
  have h : k + (t : ℕ) = (k - (t : ℕ)) + 2 * (t : ℕ) := by omega
  rw [h, pow_add, pow_mul]
  simp

/-- All states at their proper cardinalities are the increasing-column prefix minors. -/
theorem rowSubsetDP_eq_prefixMinor (M : ℕ → α → R) (k : ℕ) (s : Finset α)
    (hs : s.card = k) :
    rowSubsetDP M k s = (prefixMinor M k s hs).det := by
  induction k generalizing s with
  | zero =>
    simp [rowSubsetDP, Finset.card_eq_zero.mp hs, Matrix.det_isEmpty]
  | succ k ih =>
    rw [rowSubsetDP, Matrix.det_succ_row _ (Fin.last k)]
    symm
    apply Finset.sum_bij (fun t _ ↦ s.orderEmbOfFin hs t)
    · exact fun t _ ↦ s.orderEmbOfFin_mem hs t
    · exact fun i _ j _ hij ↦ (s.orderEmbOfFin hs).injective hij
    · intro c hc
      obtain ⟨t, ht⟩ : c ∈ Set.range (s.orderEmbOfFin hs) := by
        simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hc
      exact ⟨t, Finset.mem_univ _, ht⟩
    · intro t _
      have hsub :
          (prefixMinor M (k + 1) s hs).submatrix (Fin.last k).succAbove t.succAbove =
            prefixMinor M k (s.erase (s.orderEmbOfFin hs t))
              (cardErase hs (s.orderEmbOfFin_mem hs t)) := by
        ext i j
        simp only [prefixMinor, Matrix.submatrix_apply, Fin.succAbove_last, Fin.val_castSucc]
        rw [congrFun (orderEmbOfFin_erase hs t) j]
      rw [ih _ (cardErase hs (s.orderEmbOfFin_mem hs t)), hsub,
        appendInversions_orderEmb hs t]
      simp only [prefixMinor, Fin.val_last]
      rw [laplaceSign_eq_appendSign]
      ring

/-- A state outside the current row count has zero coefficient. -/
theorem rowSubsetDP_eq_zero_of_card_ne (M : ℕ → α → R) (k : ℕ) (s : Finset α)
    (hs : s.card ≠ k) : rowSubsetDP M k s = 0 := by
  induction k generalizing s with
  | zero =>
    have hne : s ≠ ∅ := fun h ↦ hs (h ▸ Finset.card_empty)
    simp [rowSubsetDP, hne]
  | succ k ih =>
    rw [rowSubsetDP]
    apply Finset.sum_eq_zero
    intro j hj
    have hpos := Finset.card_pos.mpr ⟨j, hj⟩
    have hne : (s.erase j).card ≠ k := by
      rw [Finset.card_erase_of_mem hj]
      omega
    simp [ih _ hne]

/-- The zero row stage starts with exactly one unit state. -/
@[simp]
theorem rowSubsetDP_zero_empty (M : ℕ → α → R) : rowSubsetDP M 0 ∅ = 1 := by
  simp [rowSubsetDP]

/-- Sparse absent entries are zeros, so skipping zero matrix entries gives the same step. -/
theorem rowSubsetDP_succ_eq_sparse [DecidableEq R] (M : ℕ → α → R) (k : ℕ) (t : Finset α) :
    rowSubsetDP M (k + 1) t =
      ∑ j ∈ t with M k j ≠ 0,
        rowSubsetDP M k (t.erase j) * M k j * (-1) ^ appendInversions (t.erase j) j := by
  rw [rowSubsetDP, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : M k j = 0 <;> simp [hj]

/-- The Python scatter step, summed by destination subset. -/
def rowSubsetPush [Fintype α] (M : ℕ → α → R) (k : ℕ) (state : Finset α → R)
    (t : Finset α) : R :=
  ∑ s ∈ (Finset.univ : Finset α).powerset, ∑ j : α,
    if j ∉ s ∧ insert j s = t
    then state s * M k j * (-1) ^ appendInversions s j
    else 0

private theorem insertionTarget_iff (j : α) (s t : Finset α) :
    j ∉ s ∧ insert j s = t ↔ j ∈ t ∧ s = t.erase j := by
  constructor
  · rintro ⟨hj, rfl⟩
    exact ⟨Finset.mem_insert_self _ _, (Finset.erase_insert hj).symm⟩
  · rintro ⟨hj, rfl⟩
    exact ⟨Finset.notMem_erase _ _, Finset.insert_erase hj⟩

/-- The Python scatter and the destination-indexed recurrence agree for every state. -/
theorem rowSubsetPush_eq_sum [Fintype α] (M : ℕ → α → R) (k : ℕ)
    (state : Finset α → R) (t : Finset α) :
    rowSubsetPush M k state t =
      ∑ j ∈ t, state (t.erase j) * M k j * (-1) ^ appendInversions (t.erase j) j := by
  unfold rowSubsetPush
  rw [Finset.sum_comm]
  have ht : t = Finset.univ.filter (fun j ↦ j ∈ t) := by ext j; simp
  conv_rhs => rw [ht]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  simp only [insertionTarget_iff]
  by_cases hj : j ∈ t
  · simp only [hj, true_and, if_true]
    rw [Finset.sum_eq_single_of_mem (t.erase j) (by simp)]
    · simp
    · intro b _ hb
      simp [hb]
  · simp [hj]

/-- Iterating the scatter from the unit state gives the exact prefix recurrence. -/
theorem rowSubsetDP_succ_eq_push [Fintype α] (M : ℕ → α → R) (k : ℕ) (t : Finset α) :
    rowSubsetDP M (k + 1) t = rowSubsetPush M k (rowSubsetDP M k) t := by
  rw [rowSubsetPush_eq_sum, rowSubsetDP]

/-- At the full subset the recurrence gives the determinant of the input square matrix. -/
theorem rowSubsetDP_eq_det {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    rowSubsetDP (fun i j ↦ if h : i < n then M ⟨i, h⟩ j else 0) n Finset.univ = M.det := by
  have h := rowSubsetDP_eq_prefixMinor
    (fun i j ↦ if h : i < n then M ⟨i, h⟩ j else 0) n Finset.univ (Finset.card_fin n)
  have he : (⇑((Finset.univ : Finset (Fin n)).orderEmbOfFin (Finset.card_fin n))) =
      (fun j ↦ j) := by
    symm
    apply Finset.orderEmbOfFin_unique
    · simp
    · exact strictMono_id
  rw [h]
  congr 1
  ext i j
  simp only [prefixMinor, dif_pos i.isLt, Fin.eta]
  rw [congrFun he j]

section Mask

variable {n : ℕ}

/-- Binary encoding of a subset of matrix columns. -/
def columnMask (s : Finset (Fin n)) : ℕ :=
  ∑ i ∈ s.map Fin.valEmbedding, 2 ^ i

private theorem testBit_columnMask_iff (s : Finset (Fin n)) (k : ℕ) :
    (columnMask s).testBit k = true ↔ ∃ i ∈ s, (i : ℕ) = k := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, columnMask, Finset.toFinset_bitIndices_sum_two_pow]
  simp [Finset.mem_map, Fin.valEmbedding]

/-- Python's bit membership is column membership. -/
theorem testBit_columnMask (s : Finset (Fin n)) (j : Fin n) :
    (columnMask s).testBit (j : ℕ) = decide (j ∈ s) := by
  apply Bool.eq_iff_iff.mpr
  rw [testBit_columnMask_iff, decide_eq_true_eq]
  exact ⟨fun ⟨i, hi, h⟩ ↦ Fin.ext h ▸ hi, fun h ↦ ⟨j, h, rfl⟩⟩

/-- Python's bitwise OR with the singleton bit inserts that column. -/
theorem columnMask_insert (s : Finset (Fin n)) (j : Fin n) :
    columnMask (insert j s) = columnMask s ||| (1 <<< (j : ℕ)) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.one_shiftLeft, Nat.testBit_or, Nat.testBit_two_pow]
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true, decide_eq_true_eq, testBit_columnMask_iff, testBit_columnMask_iff]
  simp only [Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl | hi, h⟩
    · exact Or.inr h
    · exact Or.inl ⟨i, hi, h⟩
  · rintro (⟨i, hi, h⟩ | h)
    · exact ⟨i, Or.inr hi, h⟩
    · exact ⟨j, Or.inl rfl, h⟩

/-- Python's shifted bit count gives exactly the appended inversion count. -/
theorem columnMask_highBitCount (s : Finset (Fin n)) (j : Fin n) :
    ((columnMask s) >>> ((j : ℕ) + 1)).bitIndices.length = appendInversions s j := by
  rw [← List.toFinset_card_of_nodup Nat.bitIndices_nodup, appendInversions]
  symm
  apply Finset.card_bij (s := s.filter (fun c ↦ j < c))
    (t := ((columnMask s) >>> ((j : ℕ) + 1)).bitIndices.toFinset)
    (fun c _ ↦ (c : ℕ) - ((j : ℕ) + 1))
  · intro c hc
    obtain ⟨hcs, hjc⟩ := Finset.mem_filter.mp hc
    rw [List.mem_toFinset, Nat.mem_bitIndices, Nat.testBit_shiftRight, testBit_columnMask_iff]
    refine ⟨c, hcs, ?_⟩
    have h : (j : ℕ) < (c : ℕ) := hjc
    omega
  · intro x hx y hy hxy
    have hx' : (j : ℕ) < (x : ℕ) := (Finset.mem_filter.mp hx).2
    have hy' : (j : ℕ) < (y : ℕ) := (Finset.mem_filter.mp hy).2
    exact Fin.ext (by omega)
  · intro b hb
    rw [List.mem_toFinset, Nat.mem_bitIndices, Nat.testBit_shiftRight, testBit_columnMask_iff] at hb
    obtain ⟨c, hc, hcb⟩ := hb
    refine ⟨c, Finset.mem_filter.mpr ⟨hc, ?_⟩, ?_⟩
    · change (j : ℕ) < (c : ℕ)
      omega
    · omega

/-- The initial mask of the empty subset is zero. -/
@[simp]
theorem columnMask_empty : columnMask (∅ : Finset (Fin n)) = 0 := by
  simp [columnMask]

/-- The full subset is the Python terminal mask. -/
theorem columnMask_univ (n : ℕ) :
    columnMask (Finset.univ : Finset (Fin n)) = (1 <<< n) - 1 := by
  rw [columnMask, Finset.sum_map, Nat.one_shiftLeft]
  change (∑ i : Fin n, 2 ^ (i : ℕ)) = 2 ^ n - 1
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ 2 ^ i) n, Nat.geomSum_eq (by decide : 2 ≤ 2)]
  simp

/-- Distinct column subsets have distinct masks. -/
theorem columnMask_injective : Function.Injective (columnMask (n := n)) := by
  intro s t h
  ext j
  have he := congrArg (fun m : ℕ ↦ m.testBit (j : ℕ)) h
  simpa only [testBit_columnMask, decide_eq_decide] using he

/-- The low-bit test used by the Python recurrence skips exactly the used columns. -/
theorem columnMask_shift_and_one_eq_zero (s : Finset (Fin n)) (j : Fin n) :
    ((columnMask s >>> (j : ℕ)) &&& 1) = 0 ↔ j ∉ s := by
  rw [Nat.and_one_is_mod, Nat.mod_two_eq_zero_iff_testBit_zero, Nat.testBit_shiftRight,
    Nat.add_zero, testBit_columnMask, decide_eq_false_iff_not]

/-- The scatter indexed by natural masks, summing all updates to one destination. -/
def maskScatter (M : ℕ → Fin n → R) (k : ℕ) (state : ℕ → R) (m : ℕ) : R :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset, ∑ j : Fin n,
    if ((columnMask s >>> (j : ℕ)) &&& 1) = 0 ∧
        (columnMask s ||| (1 <<< (j : ℕ))) = m
    then state (columnMask s) * M k j *
      (-1) ^ ((columnMask s) >>> ((j : ℕ) + 1)).bitIndices.length
    else 0

/-- The membership test, destination mask and shifted population count all agree
with the subset scatter. -/
theorem maskScatter_eq_subsetPush (M : ℕ → Fin n → R) (k : ℕ) (state : ℕ → R)
    (t : Finset (Fin n)) :
    maskScatter M k state (columnMask t) =
      rowSubsetPush M k (fun s ↦ state (columnMask s)) t := by
  unfold maskScatter rowSubsetPush
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro j _
  simp only [columnMask_shift_and_one_eq_zero, ← columnMask_insert, columnMask_injective.eq_iff,
    columnMask_highBitCount]

/-- The natural-mask recurrence with the initial singleton dictionary {0: 1}.
The domain of source masks is enumerated by subsets, and zero states can be omitted. -/
def maskSubsetDP (M : ℕ → Fin n → R) : ℕ → ℕ → R
  | 0, m => if m = 0 then 1 else 0
  | k + 1, m => maskScatter M k (maskSubsetDP M k) m

/-- At every encoded mask the natural-mask recurrence is the exact subset recurrence. -/
theorem maskSubsetDP_eq_rowSubsetDP (M : ℕ → Fin n → R) (k : ℕ) (t : Finset (Fin n)) :
    maskSubsetDP M k (columnMask t) = rowSubsetDP M k t := by
  induction k generalizing t with
  | zero =>
    have he : columnMask t = 0 ↔ t = ∅ := by
      rw [← columnMask_empty (n := n), columnMask_injective.eq_iff]
    simp only [maskSubsetDP, rowSubsetDP, he]
  | succ k ih =>
    rw [maskSubsetDP, maskScatter_eq_subsetPush, rowSubsetDP_succ_eq_push]
    simp only [ih]

/-- At the Python terminal mask the recurrence computes the determinant, without
any nonsingularity or invertibility requirement. -/
theorem maskSubsetDP_eq_det (M : Matrix (Fin n) (Fin n) R) :
    maskSubsetDP (fun i j ↦ if h : i < n then M ⟨i, h⟩ j else 0) n
      ((1 <<< n) - 1) = M.det := by
  rw [← columnMask_univ, maskSubsetDP_eq_rowSubsetDP, rowSubsetDP_eq_det]

/-- Repeated rows give a singular zero result in the exact mask recurrence. -/
theorem maskSubsetDP_eq_zero_of_row_eq (M : Matrix (Fin n) (Fin n) R)
    {i j : Fin n} (hne : i ≠ j) (heq : M i = M j) :
    maskSubsetDP (fun i j ↦ if h : i < n then M ⟨i, h⟩ j else 0) n
      ((1 <<< n) - 1) = 0 := by
  rw [maskSubsetDP_eq_det, Matrix.det_zero_of_row_eq hne heq]

/-- A mask outside the encoded subset domain never acquires a nonzero state. -/
theorem maskSubsetDP_eq_zero_of_not_encoded (M : ℕ → Fin n → R) (k m : ℕ)
    (hm : ¬ ∃ s : Finset (Fin n), columnMask s = m) :
    maskSubsetDP M k m = 0 := by
  cases k with
  | zero =>
    have hn : m ≠ 0 := fun h ↦ hm ⟨∅, by simp [h]⟩
    simp [maskSubsetDP, hn]
  | succ k =>
    rw [maskSubsetDP, maskScatter]
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro j _
    have hn : (columnMask s ||| (1 <<< (j : ℕ))) ≠ m := by
      rw [← columnMask_insert]
      exact fun h ↦ hm ⟨insert j s, h⟩
    simp [hn]

end Mask

end SKEFTHawking.ADW.FiniteDeterminantSubsetDP
