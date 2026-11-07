import SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

/-!
# Signed complementary minors of the original finite Berezin form

The row replacement is proved in the original exterior algebra. Ordered
Laplace deletion and the odd-generator shuffle give the signed minor in
the executable barred-then-unbarred convention.
-/
noncomputable section
open scoped BigOperators IsMulCommutative
open Matrix
namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
open FiniteGrassmannCoframe FiniteGrassmannEvaluation GaussianGrassmannAuxiliary
open scoped SKEFTHawking.ADW.FiniteGrassmannEvaluation


private theorem exp_sum_rows {A : Type*} [CommRing A] [Algebra ℂ A]
    (xs : List A) (hx : ∀ x ∈ xs, x ^ 2 = 0) :
    nilExp xs.length xs.sum = (xs.map (1 + ·)).prod := by
  letI : Algebra ℚ A := Algebra.restrictScalars ℚ ℂ A
  letI : IsScalarTower ℚ ℂ A := IsScalarTower.restrictScalars ℚ ℂ A
  suffices he : IsNilpotent.exp xs.sum = (xs.map (1 + ·)).prod by
    rw [nilExp_eq_exp _ _ (squareZero_list_sum_top xs hx).2, he]
  induction xs with
  | nil => simp [IsNilpotent.exp_zero]
  | cons x xs ih =>
    have hs : ∀ y ∈ xs, y ^ 2 = 0 := fun y hy ↦ hx y (List.mem_cons_of_mem _ hy)
    have h2 : x ^ 2 = 0 := hx x (by simp)
    have hex : IsNilpotent.exp x = 1 + x := by
      rw [← nilExp_eq_exp 1 x h2]
      simp [nilExp, Finset.sum_range_succ]
    simp [IsNilpotent.exp_add_of_commute (Commute.all x xs.sum) ⟨2, h2⟩
      ⟨_, (squareZero_list_sum_top xs hs).2⟩, hex, ih hs]

/-- Exact row factorization of the original finite bilinear exponential. -/
theorem nilExp_barMpsi_rows (L : Torus) (M : DiracMatrix L) :
    nilExp (4 * volume L) (barMpsi L M) =
      ((∏ p, (1 + rowFactor L p (M p)) : bilinearAlgebra L) : Grassmann L) := by
  classical
  let xs := (Finset.univ : Finset (Fermion L)).toList.map (fun p ↦ rowFactor L p (M p))
  have hx : ∀ a ∈ xs, a ^ 2 = 0 := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    exact rowFactor_square L p (M p)
  have h := exp_sum_rows xs hx
  have hn : Fintype.card (Fermion L) = 4 * volume L := by
    simp only [Fermion, Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_comm _ _
  simp only [xs, List.length_map, Finset.length_toList, Finset.card_univ,
    Finset.sum_map_toList, List.map_map, Function.comp_def, Finset.prod_map_toList, hn] at h
  have he := congrArg (bilinearAlgebra L).val h
  rw [map_nilExp] at he
  change nilExp (4 * volume L)
    ((∑ p, rowFactor L p (M p) : bilinearAlgebra L) : Grassmann L) = _ at he
  rwa [sum_rowFactor] at he

private theorem rowFactor_sameBar_zero (L : Torus) (p : Fermion L) (r s : Fermion L → ℂ) :
    rowFactor L p r * rowFactor L p s = 0 := by
  apply Subtype.ext
  change (rowFactor L p r : Grassmann L) * (rowFactor L p s : Grassmann L) = 0
  rw [rowFactor_image, rowFactor_image]
  have hs := ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (Pi.basisFun ℂ (Gen L) (p.1,Sum.inr p.2))
    (rowVector L r)
  have hz := theta_square_zero L (p.1,Sum.inr p.2)
  change theta L (p.1,Sum.inr p.2) * ExteriorAlgebra.ι ℂ (rowVector L r) +
    ExteriorAlgebra.ι ℂ (rowVector L r) * theta L (p.1,Sum.inr p.2) = 0 at hs
  change theta L (p.1,Sum.inr p.2) * theta L (p.1,Sum.inr p.2) = 0 at hz
  change (theta L (p.1,Sum.inr p.2) * ExteriorAlgebra.ι ℂ (rowVector L r)) *
    (theta L (p.1,Sum.inr p.2) * ExteriorAlgebra.ι ℂ (rowVector L s)) = 0
  calc
    _ = theta L (p.1,Sum.inr p.2) *
      (ExteriorAlgebra.ι ℂ (rowVector L r) * theta L (p.1,Sum.inr p.2)) *
      ExteriorAlgebra.ι ℂ (rowVector L s) := by noncomm_ring
    _ = -(theta L (p.1,Sum.inr p.2) * theta L (p.1,Sum.inr p.2)) *
      (ExteriorAlgebra.ι ℂ (rowVector L r) * ExteriorAlgebra.ι ℂ (rowVector L s)) := by
        rw [eq_neg_of_add_eq_zero_right hs]
        noncomm_ring
    _ = 0 := by rw [hz]; simp

/-- Replace the rows selected by a finite insertion, leaving every other row intact. -/
def insertionRows (L : Torus) (M : DiracMatrix L) (s : Finset (Fermion L))
    (c : Fermion L → Fermion L) : DiracMatrix L :=
  fun p ↦ if p ∈ s then Pi.basisFun ℂ (Fermion L) (c p) else M p

private theorem row_prod_grade (L : Torus) (s : Finset (Fermion L)) (M : DiracMatrix L) :
    ((∏ p ∈ s, rowFactor L p (M p) : bilinearAlgebra L) : Grassmann L) ∈
      grade L (2 * s.card) := by
  simpa using weighted_product_grade L s (fun p ↦ rowFactor L p (M p))
    (fun _ ↦ 1) (fun p _ ↦ rowFactor_grade L p (M p))

/-- Inserting any set of paired generators replaces exactly those determinant rows.
Repeated columns are allowed and give a repeated-row determinant. -/
theorem berezin_insert_rows (L : Torus) (M : DiracMatrix L) (s : Finset (Fermion L))
    (c : Fermion L → Fermion L) :
    berezin L
      (((∏ p ∈ s, rowFactor L p (Pi.basisFun ℂ (Fermion L) (c p)) :
          bilinearAlgebra L) : Grassmann L) * nilExp (4 * volume L) (barMpsi L M)) =
      (insertionRows L M s c).det := by
  classical
  let A := bilinearAlgebra L
  let Q : DiracMatrix L := fun p ↦ Pi.basisFun ℂ (Fermion L) (c p)
  let q : A := ∏ p ∈ s, rowFactor L p (Q p)
  let F (p : Fermion L) : A := 1 + rowFactor L p (M p)
  let ev : A →ₗ[ℂ] ℂ := (berezin L).comp (bilinearAlgebra L).val.toLinearMap
  have hq : q * ∏ p ∈ s, F p = q := by
    dsimp [q]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    change rowFactor L p (Q p) * (1 + rowFactor L p (M p)) = rowFactor L p (Q p)
    rw [mul_add, mul_one, rowFactor_sameBar_zero, add_zero]
  have hE : (∏ p ∈ sᶜ, F p) =
      ∑ t ∈ sᶜ.powerset, ∏ p ∈ t, rowFactor L p (M p) := by
    simp only [F, add_comm (1 : A)]
    rw [Finset.prod_add]
    simp
  rw [nilExp_barMpsi_rows]
  change ev (q * ∏ p, F p) = _
  rw [← Finset.prod_mul_prod_compl s F, ← mul_assoc, hq, hE, Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single sᶜ]
  · have hd : rowBerezin L (insertionRows L M s c) = (insertionRows L M s c).det := by
      rw [rowBerezin_det, rowBerezin_normalization, one_mul]
    rw [← hd]
    change ev (q * ∏ p ∈ sᶜ, rowFactor L p (M p)) =
      ev (∏ p, rowFactor L p (insertionRows L M s c p))
    congr 1
    rw [← Finset.prod_mul_prod_compl s (fun p ↦ rowFactor L p (insertionRows L M s c p))]
    unfold q
    congr 1
    · exact Finset.prod_congr rfl fun p hp ↦ by simp [insertionRows, hp, Q]
    · exact Finset.prod_congr rfl fun p hp ↦ by simp [insertionRows, Finset.mem_compl.mp hp]
  · intro t ht hne
    have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.mem_powerset.mp ht, hne⟩)
    have hfull : s.card + sᶜ.card = 4 * volume L := by
      have h := Finset.card_le_univ s
      rw [Finset.card_compl, Nat.add_sub_of_le h]
      simp only [Fermion, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]
    have hg := SetLike.mul_mem_graded (row_prod_grade L s Q) (row_prod_grade L t M)
    exact berezin_grade_zero L hg (by omega)
  · simp

/-- A unit row deletes its row and its occupied column, including the Laplace sign. -/
theorem det_of_unit_row {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (r c : Fin (n + 1))
    (h : ∀ j, M r j = if j = c then 1 else 0) :
    M.det = (-1) ^ (r.val + c.val) * (M.submatrix r.succAbove c.succAbove).det := by
  rw [Matrix.det_succ_row M r, Finset.sum_eq_single c]
  · simp [h]
  · intro j _ hj
    simp [h, hj]
  · simp

private def belowDeletion {n : ℕ} (p q : Fin (n + 1)) (h : q ≠ p) : Fin n :=
  (Fin.exists_succAbove_eq h).choose

@[simp] private theorem above_belowDeletion {n : ℕ} (p q : Fin (n + 1)) (h : q ≠ p) :
    p.succAbove (belowDeletion p q h) = q :=
  (Fin.exists_succAbove_eq h).choose_spec

private theorem belowDeletion_val_succ {n : ℕ} {p q : Fin (n + 1)} (h : p < q) :
    (belowDeletion p q (ne_of_gt h)).val + 1 = q.val := by
  let v := belowDeletion p q (ne_of_gt h)
  have hv : p.succAbove v = q := above_belowDeletion _ _ _
  have hp : p ≤ v.castSucc := (Fin.lt_succAbove_iff_le_castSucc _ _).mp (hv ▸ h)
  rw [Fin.succAbove_of_le_castSucc _ _ hp] at hv
  exact congrArg Fin.val hv

private theorem belowDeletion_strictMono {n m : ℕ} (p : Fin (n + 1))
    (f : Fin m → Fin (n + 1)) (hf : StrictMono f) (h : ∀ i, f i ≠ p) :
    StrictMono (fun i ↦ belowDeletion p (f i) (h i)) := by
  intro i j hij
  apply (Fin.strictMono_succAbove p).lt_iff_lt.mp
  simpa only [above_belowDeletion] using hf hij

private theorem fin_strictMono_self {n : ℕ} (f : Fin n → Fin n) (h : StrictMono f) :
    f = id := by
  have hf := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin n)))
    (by simp) (fun i ↦ Finset.mem_univ (f i)) h
  have hi := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin n)))
    (by simp) (fun i ↦ Finset.mem_univ (id i)) strictMono_id
  exact hf.trans hi.symm

/-- Ordered unit rows can all be deleted with the signed complementary determinant.
The chosen rows, columns, and both complementary enumerations are increasing. -/
theorem det_of_ordered_unit_rows {R : Type*} [CommRing R] {n k : ℕ}
    (M : Matrix (Fin (n + k)) (Fin (n + k)) R)
    (r c : Fin k → Fin (n + k)) (u v : Fin n → Fin (n + k))
    (hr : StrictMono r) (hc : StrictMono c) (hu : StrictMono u) (hv : StrictMono v)
    (hru : ∀ i j, u i ≠ r j) (hcv : ∀ i j, v i ≠ c j)
    (h : ∀ i j, M (r i) j = if j = c i then 1 else 0) :
    M.det = (-1) ^ (∑ i, ((r i).val + (c i).val)) * (M.submatrix u v).det := by
  induction k with
  | zero =>
    rw [fin_strictMono_self u hu, fin_strictMono_self v hv]
    simp
  | succ k ih =>
    have hr0 (i : Fin k) : r 0 < r i.succ := hr (Fin.succ_pos i)
    have hc0 (i : Fin k) : c 0 < c i.succ := hc (Fin.succ_pos i)
    let rt (i : Fin k) := belowDeletion (r 0) (r i.succ) (ne_of_gt (hr0 i))
    let ct (i : Fin k) := belowDeletion (c 0) (c i.succ) (ne_of_gt (hc0 i))
    let ut (i : Fin n) := belowDeletion (r 0) (u i) (hru i 0)
    let vt (i : Fin n) := belowDeletion (c 0) (v i) (hcv i 0)
    have hrt : StrictMono rt := belowDeletion_strictMono _ _ (hr.comp Fin.strictMono_succ) _
    have hct : StrictMono ct := belowDeletion_strictMono _ _ (hc.comp Fin.strictMono_succ) _
    have hut : StrictMono ut := belowDeletion_strictMono _ _ hu _
    have hvt : StrictMono vt := belowDeletion_strictMono _ _ hv _
    have hru' (i j) : ut i ≠ rt j := by
      intro hh
      apply hru i j.succ
      simpa [ut, rt] using congrArg (r 0).succAbove hh
    have hcv' (i j) : vt i ≠ ct j := by
      intro hh
      apply hcv i j.succ
      simpa [vt, ct] using congrArg (c 0).succAbove hh
    have hunit (i : Fin k) (j : Fin (n + k)) :
        (M.submatrix (r 0).succAbove (c 0).succAbove) (rt i) j =
          if j = ct i then 1 else 0 := by
      have he : (c 0).succAbove j = c i.succ ↔ j = ct i := by
        rw [← above_belowDeletion (c 0) (c i.succ) (ne_of_gt (hc0 i)), Fin.succAbove_inj]
      simp only [Matrix.submatrix_apply, rt, above_belowDeletion, h, he]
    have hmat : ((M.submatrix (r 0).succAbove (c 0).succAbove).submatrix ut vt) =
        M.submatrix u v := by
      ext i j
      simp [ut, vt]
    have hsum : (∑ i : Fin k, ((r i.succ).val + (c i.succ).val)) =
        (∑ i : Fin k, ((rt i).val + (ct i).val)) + 2 * k := by
      have hs (i : Fin k) : (r i.succ).val + (c i.succ).val =
          (rt i).val + (ct i).val + 2 := by
        have ha := belowDeletion_val_succ (hr0 i)
        have hb := belowDeletion_val_succ (hc0 i)
        dsimp [rt, ct]
        omega
      simp_rw [hs, Finset.sum_add_distrib]
      simp [Nat.mul_comm]
    have hsign : (-1 : R) ^ (2 * k) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
    rw [det_of_unit_row M (r 0) (c 0) (h 0), ih _ _ _ _ _ hrt hct hut hvt hru' hcv' hunit,
      hmat, Fin.sum_univ_succ, hsum]
    simp only [pow_add, hsign, mul_one, mul_assoc]

private theorem theta_mul_word (L : Torus) (p : Gen L) (xs : List (Gen L)) :
    theta L p * (xs.map (theta L)).prod =
      ((-1 : ℂ) ^ xs.length) • ((xs.map (theta L)).prod * theta L p) := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [← mul_assoc, theta_odd_swap, neg_mul, mul_assoc, ih, mul_smul_comm, ← neg_smul,
      pow_succ, mul_neg, mul_one]
    simp only [mul_assoc]

private theorem pair_word_sign (L : Torus) (xs : List (Gen L × Gen L)) :
    (xs.map (fun x ↦ pair L x.1 x.2)).prod =
      ((-1 : ℂ) ^ xs.length.choose 2) •
        ((xs.map (fun x ↦ theta L x.1)).prod * (xs.map (fun x ↦ theta L x.2)).prod) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    let B := (xs.map (fun x ↦ theta L x.1)).prod
    let P := (xs.map (fun x ↦ theta L x.2)).prod
    have hmove : theta L x.2 * B = ((-1 : ℂ) ^ xs.length) • (B * theta L x.2) := by
      simpa [B, List.map_map, Function.comp_def] using theta_mul_word L x.2 (xs.map Prod.fst)
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih]
    unfold pair
    change (theta L x.1 * theta L x.2) * (((-1 : ℂ) ^ xs.length.choose 2) • (B * P)) =
      ((-1 : ℂ) ^ (xs.length + 1).choose 2) • ((theta L x.1 * B) * (theta L x.2 * P))
    calc
      _ = ((-1 : ℂ) ^ xs.length.choose 2) • (theta L x.1 * (theta L x.2 * B) * P) := by
        rw [mul_smul_comm]
        simp only [mul_assoc]
      _ = _ := by
        rw [hmove, mul_smul_comm, smul_mul_assoc, smul_smul, ← pow_add,
          Nat.choose_succ_succ', Nat.choose_one_right, Nat.add_comm xs.length]
        simp only [mul_assoc]

private theorem rowFactor_basis_col (L : Torus) (p q : Fermion L) :
    (rowFactor L p (Pi.basisFun ℂ (Fermion L) q) : Grassmann L) =
      pair L (p.1, Sum.inr p.2) (q.1, Sum.inl q.2) := by
  classical
  simp [rowFactor, Pi.basisFun_apply, Pi.single_apply]

/-- The executable all-bars then all-psis insertion has the triangular reorder sign. -/
theorem berezin_grouped_insert_rows (L : Torus) (M : DiracMatrix L)
    (rows : List (Fermion L)) (c : Fermion L → Fermion L) (hr : rows.Nodup) :
    berezin L
      (((rows.map (fun p ↦ theta L (p.1, Sum.inr p.2))).prod *
        (rows.map (fun p ↦ theta L ((c p).1, Sum.inl (c p).2))).prod) *
        nilExp (4 * volume L) (barMpsi L M)) =
      (-1 : ℂ) ^ (rows.length.choose 2) * (insertionRows L M rows.toFinset c).det := by
  classical
  let pairs := rows.map (fun p ↦ (((p.1, Sum.inr p.2), ((c p).1, Sum.inl (c p).2)) :
    Gen L × Gen L))
  have h := pair_word_sign L pairs
  simp only [pairs, List.map_map, List.length_map, Function.comp_def] at h
  have hp :
      ((∏ p ∈ rows.toFinset, rowFactor L p (Pi.basisFun ℂ (Fermion L) (c p)) :
          bilinearAlgebra L) : Grassmann L) =
        (rows.map (fun p ↦ pair L (p.1, Sum.inr p.2) ((c p).1, Sum.inl (c p).2))).prod := by
    rw [List.prod_toFinset _ hr]
    change (bilinearAlgebra L).val (List.map _ rows).prod = _
    rw [map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun p _ ↦ rowFactor_basis_col L p (c p)
  have hb := berezin_insert_rows L M rows.toFinset c
  rw [hp, h, smul_mul_assoc, map_smul, smul_eq_mul] at hb
  rw [← hb, ← mul_assoc, ← pow_add]
  have hs : (-1 : ℂ) ^ (rows.length.choose 2 + rows.length.choose 2) = 1 := by
    rw [← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [hs, one_mul]

/-- The actual Berezin top coefficient equals the signed complementary minor.
The supplied Fermion enumeration fixes the same row/column ordering for both sorted
selections and complements. No invertibility or relation between the selected row
and column sets is assumed. -/
theorem berezin_ordered_complementary_minor (L : Torus) (M : DiracMatrix L)
    {n k : ℕ} (e : Fermion L ≃ Fin (n + k))
    (r c : Fin k → Fin (n + k)) (u v : Fin n → Fin (n + k))
    (hr : StrictMono r) (hc : StrictMono c) (hu : StrictMono u) (hv : StrictMono v)
    (hru : ∀ i j, u i ≠ r j) (hcv : ∀ i j, v i ≠ c j) :
    berezin L
      (((List.ofFn (fun i ↦ theta L ((e.symm (r i)).1, Sum.inr (e.symm (r i)).2))).prod *
        (List.ofFn (fun i ↦ theta L ((e.symm (c i)).1, Sum.inl (e.symm (c i)).2))).prod) *
        nilExp (4 * volume L) (barMpsi L M)) =
      (-1 : ℂ) ^ (k * (k - 1) / 2 + ∑ i, ((r i).val + (c i).val)) *
        (M.submatrix (e.symm ∘ u) (e.symm ∘ v)).det := by
  classical
  let rows := List.ofFn (fun i ↦ e.symm (r i))
  let q (p : Fermion L) := if h : ∃ i, e.symm (r i) = p then e.symm (c h.choose) else p
  have hq (i : Fin k) : q (e.symm (r i)) = e.symm (c i) := by
    have h : ∃ j, e.symm (r j) = e.symm (r i) := ⟨i, rfl⟩
    dsimp only [q]
    rw [dif_pos h, hr.injective (e.symm.injective h.choose_spec)]
  have hrows (p : Fermion L) : p ∈ rows.toFinset ↔ ∃ i, e.symm (r i) = p := by
    simp [rows, List.mem_ofFn]
  have hn : rows.Nodup := List.nodup_ofFn.mpr (e.symm.injective.comp hr.injective)
  have hb := berezin_grouped_insert_rows L M rows q hn
  simp only [rows, List.map_ofFn, Function.comp_def, hq, List.length_ofFn,
    Nat.choose_two_right] at hb
  rw [hb]
  let A := insertionRows L M rows.toFinset q
  let A' := A.submatrix e.symm e.symm
  have hA (i : Fin k) (j : Fin (n + k)) :
      A' (r i) j = if j = c i then 1 else 0 := by
    have hm : e.symm (r i) ∈ rows.toFinset := (hrows _).mpr ⟨i, rfl⟩
    simp [A', A, insertionRows, hm, hq, Pi.basisFun_apply, Pi.single_apply]
  have hminor : A'.submatrix u v = M.submatrix (e.symm ∘ u) (e.symm ∘ v) := by
    ext i j
    have hm : e.symm (u i) ∉ rows.toFinset := by
      intro h
      obtain ⟨l, hl⟩ := (hrows _).mp h
      exact hru i l (e.symm.injective hl).symm
    simp [A', A, insertionRows, hm]
  change _ * A.det = _
  rw [← Matrix.det_submatrix_equiv_self e.symm A]
  change _ * A'.det = _
  rw [det_of_ordered_unit_rows A' r c u v hr hc hu hv hru hcv hA, hminor, pow_add, mul_assoc]

private def siteDigits (L : Torus) : Site L ≃
    ((Fin (L.extent 0) × Fin (L.extent 1)) × Fin (L.extent 2)) × Fin (L.extent 3) where
  toFun x := ⟨⟨⟨(ZMod.finEquiv _).symm (x 0), (ZMod.finEquiv _).symm (x 1)⟩,
    (ZMod.finEquiv _).symm (x 2)⟩, (ZMod.finEquiv _).symm (x 3)⟩
  invFun x :=
    Fin.cons (α := fun i : Fin 4 ↦ ZMod (L.extent i)) (ZMod.finEquiv _ x.1.1.1)
      (Fin.cons (α := fun i : Fin 3 ↦ ZMod (L.extent i.succ)) (ZMod.finEquiv _ x.1.1.2)
        (Fin.cons (α := fun i : Fin 2 ↦ ZMod (L.extent i.succ.succ)) (ZMod.finEquiv _ x.1.2)
          (Fin.cons (α := fun i : Fin 1 ↦ ZMod (L.extent i.succ.succ.succ))
            (ZMod.finEquiv _ x.2) (fun i ↦ nomatch i))))
  left_inv x := by
    funext i
    fin_cases i <;> exact (ZMod.finEquiv _).apply_symm_apply _
  right_inv x := by
    rcases x with ⟨⟨⟨a, b⟩, c⟩, d⟩
    change ((((ZMod.finEquiv _).symm (ZMod.finEquiv _ a),
      (ZMod.finEquiv _).symm (ZMod.finEquiv _ b)),
      (ZMod.finEquiv _).symm (ZMod.finEquiv _ c)),
      (ZMod.finEquiv _).symm (ZMod.finEquiv _ d)) = _
    simp

private theorem finEquiv_symm_val (n : ℕ) [NeZero n] (x : ZMod n) :
    ((ZMod.finEquiv n).symm x).val = x.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

private def rawSiteIndex (L : Torus) : Site L ≃
    Fin (L.extent 0 * L.extent 1 * L.extent 2 * L.extent 3) :=
  (siteDigits L).trans
    ((Equiv.prodCongr (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)) (Equiv.refl _)).trans
      ((Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv))

/-- Python's mixed-radix site numbering and its four fermion components. -/
def executableFermionIndex (L : Torus) : Fermion L ≃ Fin (4 * volume L) :=
  ((Equiv.prodCongr (rawSiteIndex L) (Equiv.refl (Fin 4))).trans finProdFinEquiv).trans
    (finCongr (by
      have h := Fintype.card_congr (rawSiteIndex L)
      rw [Fintype.card_fin] at h
      rw [← h, Nat.mul_comm]))

/-- The exact left-to-right mixed radix used by Python's site_number, then its spin index. -/
theorem executableFermionIndex_val (L : Torus) (x : Site L) (i : Fin 4) :
    (executableFermionIndex L (x,i)).val =
      4 * ((((x 0).val * L.extent 1 + (x 1).val) * L.extent 2 + (x 2).val) *
        L.extent 3 + (x 3).val) + i.val := by
  simp [executableFermionIndex, rawSiteIndex, siteDigits, finProdFinEquiv, finEquiv_symm_val,
    Nat.add_comm, Nat.mul_comm]

/-- Repeated generator words have zero exterior product before any Berezin integration. -/
theorem theta_word_repeat_zero (L : Torus) (xs : List (Gen L)) (h : ¬ xs.Nodup) :
    (xs.map (theta L)).prod = 0 := by
  induction xs with
  | nil => exact (h List.nodup_nil).elim
  | cons p xs ih =>
    simp only [List.map_cons, List.prod_cons]
    by_cases hp : p ∈ xs
    · obtain ⟨a,b,rfl⟩ := List.append_of_mem hp
      simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons]
      rw [← mul_assoc, theta_mul_word L p a, smul_mul_assoc]
      have hz := theta_square_zero L p
      simp only [mul_assoc, ← mul_assoc (theta L p) (theta L p), hz, zero_mul, mul_zero,
        smul_zero]
    · rw [ih (fun hn ↦ h (List.nodup_cons.mpr ⟨hp, hn⟩)), mul_zero]

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
