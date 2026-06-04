import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Vector majorization layer (Phase 6AL, Wave 4, route (b) toward Lidskii–Wielandt / Mirsky)

Pure real-vector majorization infrastructure that Mathlib lacks (the `Mathlib/Analysis/Convex/Birkhoff.lean`
`## TODO` notes the missing majorization predicate). This is the foundation of the **Lidskii-via-Schur–Horn**
route to the trace-norm Mirsky inequality: instead of the Wielandt subspace minimax (single-frame existence is
provably false here), we prove `λ↓(A)−λ↓(B) ≺_w λ(A−B)` purely as vector majorization, fed by the already-shipped
doubly-stochastic eigenvalue relation.

Shipped here: `sortDesc` (the descending sort permutation) and `subset_sum_le_sorted_prefix` — the sum over any
subset `S` is at most the sum of the `|S|` largest entries.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Finset

/-- The descending-sort permutation of `x : Fin N → ℝ` (sorts `-x` ascending, so `x∘sortDesc x` is antitone). -/
noncomputable def sortDesc {N : ℕ} (x : Fin N → ℝ) : Equiv.Perm (Fin N) :=
  Tuple.sort (fun i => - x i)

/-- `x` precomposed with its descending sort is antitone. -/
theorem antitone_comp_sortDesc {N : ℕ} (x : Fin N → ℝ) :
    Antitone (fun i => x (sortDesc x i)) := by
  have hmono : Monotone (fun i => -(x (sortDesc x i))) := Tuple.monotone_sort (fun i => - x i)
  intro a b hab
  exact neg_le_neg_iff.mp (hmono hab)

/-- **Subset sum ≤ sum of the `|S|` largest entries.** For any `x : Fin N → ℝ` and any `S`, the sum of `x`
over `S` is at most the sum of `x` over its `|S|` largest positions (`∑_{i<|S|} x∘sortDesc x`). The maximal
`k`-subset sum equals the sum of the `k` largest entries; this is the inequality form. Absent from Mathlib. -/
theorem subset_sum_le_sorted_prefix {N : ℕ} (x : Fin N → ℝ) (S : Finset (Fin N)) :
    ∑ i ∈ S, x i
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < S.card), x (sortDesc x i) := by
  set k := S.card with hk
  set σ := sortDesc x with hσ
  have hanti : Antitone (fun i => x (σ i)) := antitone_comp_sortDesc x
  set F : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => (i : ℕ) < k) with hF
  set T : Finset (Fin N) := F.image σ with hT
  -- RHS = ∑ over T = σ '' (top-k positions)
  have hRHS : ∑ i ∈ F, x (σ i) = ∑ j ∈ T, x j := by
    rw [hT, Finset.sum_image (fun a _ b _ h => σ.injective h)]
  rw [hRHS]
  -- decomposition of a sum over `u` into the `u∩v` and `u\v` parts
  have hdecomp : ∀ u v : Finset (Fin N), ∑ i ∈ u ∩ v, x i + ∑ i ∈ u \ v, x i = ∑ i ∈ u, x i := by
    intro u v
    rw [add_comm, ← Finset.sum_union (Finset.disjoint_sdiff_inter u v), Finset.sdiff_union_inter]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have hSempty : S = ∅ := Finset.card_eq_zero.mp hk0
    have hTempty : T = ∅ := by
      rw [hT, hF]
      have hFe : Finset.univ.filter (fun i : Fin N => (i : ℕ) < k) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro i _
        omega
      rw [hFe, Finset.image_empty]
    simp [hSempty, hTempty]
  · have hkN : k ≤ N := by rw [hk]; exact (Finset.card_le_univ S).trans_eq (Fintype.card_fin N)
    -- threshold c = the k-th largest value
    have hk1 : k - 1 < N := by omega
    set c : ℝ := x (σ ⟨k - 1, hk1⟩) with hc
    have hFcard : F.card = k := by rw [hF, Fin.card_filter_val_lt]; exact min_eq_right hkN
    have hTcard : T.card = k := by rw [hT, Finset.card_image_of_injective F σ.injective, hFcard]
    -- every element of T is ≥ c; every element outside T is ≤ c
    have hge : ∀ j ∈ T, c ≤ x j := by
      intro j hj
      rw [hT, Finset.mem_image] at hj
      obtain ⟨i, hiF, rfl⟩ := hj
      rw [hF, Finset.mem_filter] at hiF
      obtain ⟨-, hilt⟩ := hiF
      have hile : i ≤ (⟨k - 1, hk1⟩ : Fin N) := by
        rw [Fin.le_def]; show (i : ℕ) ≤ k - 1; omega
      exact hanti hile
    have hle : ∀ j ∈ Tᶜ, x j ≤ c := by
      intro j hj
      rw [Finset.mem_compl] at hj
      have hji : j = σ (σ.symm j) := (σ.apply_symm_apply j).symm
      have hnF : σ.symm j ∉ F := by
        intro hmem
        exact hj (by rw [hT, Finset.mem_image]; exact ⟨σ.symm j, hmem, (σ.apply_symm_apply j)⟩)
      rw [hF, Finset.mem_filter, not_and] at hnF
      have hge' : k ≤ (σ.symm j : ℕ) := by
        have := hnF (Finset.mem_univ _); omega
      have hle' : (⟨k - 1, hk1⟩ : Fin N) ≤ σ.symm j := by
        rw [Fin.le_def]; show k - 1 ≤ (σ.symm j : ℕ); omega
      rw [hji]
      exact hanti hle'
    -- card of the two symmetric-difference parts agree
    have hcard_eq : (S \ T).card = (T \ S).card := by
      have h1 : (S ∩ T).card + (S \ T).card = S.card := Finset.card_inter_add_card_sdiff S T
      have h2 : (T ∩ S).card + (T \ S).card = T.card := Finset.card_inter_add_card_sdiff T S
      rw [Finset.inter_comm T S] at h2
      omega
    -- bound each symmetric-difference part by the threshold
    have hSdiff : ∑ i ∈ S \ T, x i ≤ (S \ T).card • c :=
      Finset.sum_le_card_nsmul _ _ _ (fun j hj => hle j (by
        rw [Finset.mem_sdiff] at hj; exact Finset.mem_compl.mpr hj.2))
    have hTdiff : (T \ S).card • c ≤ ∑ i ∈ T \ S, x i :=
      Finset.card_nsmul_le_sum _ _ _ (fun j hj => hge j (by
        rw [Finset.mem_sdiff] at hj; exact hj.1))
    calc ∑ i ∈ S, x i
        = ∑ i ∈ S ∩ T, x i + ∑ i ∈ S \ T, x i := (hdecomp S T).symm
      _ ≤ ∑ i ∈ S ∩ T, x i + (S \ T).card • c := by linarith [hSdiff]
      _ = ∑ i ∈ S ∩ T, x i + (T \ S).card • c := by rw [hcard_eq]
      _ ≤ ∑ i ∈ S ∩ T, x i + ∑ i ∈ T \ S, x i := by linarith [hTdiff]
      _ = ∑ i ∈ T ∩ S, x i + ∑ i ∈ T \ S, x i := by rw [Finset.inter_comm]
      _ = ∑ i ∈ T, x i := hdecomp T S

/-- The sum of the `k` largest entries of `x` (`= ∑_{i<k}` of `x` sorted descending). -/
noncomputable def topkSum {N : ℕ} (x : Fin N → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), x (sortDesc x i)

/-- `topkSum x k` is the sum of `x` over its top-`k` index set `T = (top-k positions) ∘ sortDesc`. -/
theorem topkSum_eq_image_sum {N : ℕ} (x : Fin N → ℝ) (k : ℕ) :
    topkSum x k
      = ∑ j ∈ (Finset.univ.filter (fun i : Fin N => (i : ℕ) < k)).image (sortDesc x), x j := by
  rw [topkSum, Finset.sum_image (fun a _ b _ h => (sortDesc x).injective h)]

/-- The image index set realizing `topkSum x k` has cardinality `min N k`. -/
theorem image_sortDesc_card {N : ℕ} (x : Fin N → ℝ) (k : ℕ) :
    ((Finset.univ.filter (fun i : Fin N => (i : ℕ) < k)).image (sortDesc x)).card = min N k := by
  rw [Finset.card_image_of_injective _ (sortDesc x).injective, Fin.card_filter_val_lt]

/-- Any subset sum is at most `topkSum`. -/
theorem subset_sum_le_topkSum {N : ℕ} (x : Fin N → ℝ) (S : Finset (Fin N)) :
    ∑ i ∈ S, x i ≤ topkSum x S.card :=
  subset_sum_le_sorted_prefix x S

/-- `topkSum` saturates at `N`: `topkSum z (min N k) = topkSum z k`. -/
theorem topkSum_min_left {N : ℕ} (z : Fin N → ℝ) (k : ℕ) : topkSum z (min N k) = topkSum z k := by
  unfold topkSum
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have := i.isLt
  omega

/-- **`topkSum` is permutation-invariant** (the `k` largest values depend only on the multiset). -/
theorem topkSum_comp_perm {N : ℕ} (x : Fin N → ℝ) (τ : Equiv.Perm (Fin N)) (k : ℕ) :
    topkSum (fun i => x (τ i)) k = topkSum x k := by
  -- top-k set of `x∘τ` maps under τ to a `min N k`-subset of `x`, and vice versa; bound both ways
  refine le_antisymm ?_ ?_
  · rw [topkSum_eq_image_sum]
    set Timg := (Finset.univ.filter (fun i : Fin N => (i : ℕ) < k)).image (sortDesc (fun i => x (τ i)))
      with hTimg
    have hcard : (Timg.image τ).card = min N k := by
      rw [Finset.card_image_of_injective _ τ.injective, hTimg, image_sortDesc_card]
    calc ∑ j ∈ Timg, x (τ j)
        = ∑ j ∈ Timg.image τ, x j := (Finset.sum_image (fun a _ b _ h => τ.injective h)).symm
      _ ≤ topkSum x (Timg.image τ).card := subset_sum_le_topkSum x _
      _ = topkSum x k := by rw [hcard]; exact topkSum_min_left _ _
  · rw [topkSum_eq_image_sum]
    set Timg := (Finset.univ.filter (fun i : Fin N => (i : ℕ) < k)).image (sortDesc x) with hTimg
    have hcard : (Timg.image τ.symm).card = min N k := by
      rw [Finset.card_image_of_injective _ τ.symm.injective, hTimg, image_sortDesc_card]
    calc ∑ j ∈ Timg, x j
        = ∑ j ∈ Timg.image τ.symm, x (τ j) := by
          rw [Finset.sum_image (fun a _ b _ h => τ.symm.injective h)]
          exact Finset.sum_congr rfl (fun j _ => by rw [Equiv.apply_symm_apply])
      _ ≤ topkSum (fun i => x (τ i)) (Timg.image τ.symm).card := subset_sum_le_topkSum _ _
      _ = topkSum (fun i => x (τ i)) k := by rw [hcard]; exact topkSum_min_left _ _

/-- **`topkSum` is sublinear over nonnegative combinations** (it is a max of linear functionals, hence
convex): `topkSum (∑ₐ wₐ zₐ) k ≤ ∑ₐ wₐ · topkSum zₐ k` for `wₐ ≥ 0`. -/
theorem topkSum_sum_le {N : ℕ} {ι : Type*} (s : Finset ι) (w : ι → ℝ) (hw : ∀ a ∈ s, 0 ≤ w a)
    (z : ι → Fin N → ℝ) (k : ℕ) :
    topkSum (fun i => ∑ a ∈ s, w a * z a i) k ≤ ∑ a ∈ s, w a * topkSum (z a) k := by
  rw [topkSum_eq_image_sum]
  set T := (Finset.univ.filter (fun i : Fin N => (i : ℕ) < k)).image
    (sortDesc (fun i => ∑ a ∈ s, w a * z a i)) with hT
  have hTcard : T.card = min N k := by rw [hT]; exact image_sortDesc_card _ _
  calc ∑ j ∈ T, ∑ a ∈ s, w a * z a j
      = ∑ a ∈ s, w a * ∑ j ∈ T, z a j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun a _ => (Finset.mul_sum _ _ _).symm)
    _ ≤ ∑ a ∈ s, w a * topkSum (z a) k := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (hw a ha)
        calc ∑ j ∈ T, z a j ≤ topkSum (z a) T.card := subset_sum_le_topkSum (z a) T
          _ = topkSum (z a) k := by rw [hTcard]; exact topkSum_min_left _ _

end SKEFTHawking.QuantumNetwork
