/-
# Phase 5q.F (w₂-foundation, brick 6c-c8.3): the barycentric-subdivision diameter estimate

The analytic heart of excision: barycentric subdivision shrinks simplices geometrically. The key
metric fact is the **barycenter-to-vertex bound** — in a normed `ℝ`-space, the barycenter of a simplex
is within `(n/(n+1))·d` of each of its vertices (`d` = the diameter), because the `i=j` term of
`barycenter v − vⱼ = (n+1)⁻¹ ∑ᵢ(vᵢ−vⱼ)` vanishes. The factor `n/(n+1) < 1` is what drives
`diam(Sdᵐ pieces) → 0`. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularExcisionMod2
import SKEFTHawking.SingularSubdivisionConvex

namespace SKEFTHawking.SingularSubdivisionDiameter

open SKEFTHawking.SingularExcisionMod2 SKEFTHawking.SingularSubdivisionConvex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `barycenter v − vⱼ = (n+1)⁻¹ ∑ᵢ (vᵢ − vⱼ)` (the centered form; the `i=j` term is `0`). -/
theorem barycenter_sub_vertex {n : ℕ} (v : Fin (n + 1) → V) (j : Fin (n + 1)) :
    barycenter v - v j = ((n : ℝ) + 1)⁻¹ • ∑ i, (v i - v j) := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [barycenter, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_sub, sub_right_inj, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add, Nat.cast_one, smul_smul,
    inv_mul_cancel₀ hne, one_smul]

/-- **Barycenter-to-vertex bound**: `‖barycenter v − vⱼ‖ ≤ (n/(n+1))·d` when `‖vᵢ − vⱼ‖ ≤ d` for all `i`.
The `(n/(n+1)) < 1` factor that makes barycentric subdivision contract. -/
theorem norm_barycenter_sub_vertex_le {n : ℕ} (v : Fin (n + 1) → V) (j : Fin (n + 1)) {d : ℝ}
    (hd : ∀ i, ‖v i - v j‖ ≤ d) :
    ‖barycenter v - v j‖ ≤ ((n : ℝ) / ((n : ℝ) + 1)) * d := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsum : ‖∑ i, (v i - v j)‖ ≤ (n : ℝ) * d := by
    calc ‖∑ i, (v i - v j)‖ ≤ ∑ i, ‖v i - v j‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.univ.erase j, ‖v i - v j‖ := by
          rw [Finset.sum_erase _ (by rw [sub_self, norm_zero])]
      _ ≤ (Finset.univ.erase j).card • d :=
          Finset.sum_le_card_nsmul _ _ _ (fun i _ => hd i)
      _ = (n : ℝ) * d := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
            Nat.add_sub_cancel, nsmul_eq_mul]
  rw [barycenter_sub_vertex, norm_smul, norm_inv, Real.norm_of_nonneg hpos.le]
  calc ((n : ℝ) + 1)⁻¹ * ‖∑ i, (v i - v j)‖
      ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) * d) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((n : ℝ) / ((n : ℝ) + 1)) * d := by field_simp

/-- **Convexity distance bound**: a fixed point `b` is within `δ` of *any* point of the affine simplex
on `w` whenever it is within `δ` of every vertex `wₖ` (`b − ∑ tₖwₖ = ∑ tₖ(b − wₖ)`, `∑ tₖ = 1`). Used
in the sub-simplex diameter bound: the subdivision vertices lie in the parent faces. -/
theorem norm_sub_affineSimplex_le {n : ℕ} (b : V) (w : Fin (n + 1) → V)
    (t : stdSimplex ℝ (Fin (n + 1))) {δ : ℝ} (h : ∀ k, ‖b - w k‖ ≤ δ) :
    ‖b - affineSimplex w t‖ ≤ δ := by
  have hnn : ∀ k, (0 : ℝ) ≤ (t : Fin (n + 1) → ℝ) k := t.2.1
  have hs1 : ∑ k, (t : Fin (n + 1) → ℝ) k = 1 := t.2.2
  have hb : b = ∑ k, (t : Fin (n + 1) → ℝ) k • b := by
    rw [← Finset.sum_smul, hs1, one_smul]
  rw [affineSimplex_apply, hb, ← Finset.sum_sub_distrib]
  calc ‖∑ k, ((t : Fin (n + 1) → ℝ) k • b - (t : Fin (n + 1) → ℝ) k • w k)‖
      ≤ ∑ k, ‖(t : Fin (n + 1) → ℝ) k • b - (t : Fin (n + 1) → ℝ) k • w k‖ := norm_sum_le _ _
    _ = ∑ k, (t : Fin (n + 1) → ℝ) k * ‖b - w k‖ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hnn k)]
    _ ≤ ∑ k, (t : Fin (n + 1) → ℝ) k * δ :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (hnn k)
    _ = δ := by rw [← Finset.sum_mul, hs1, one_mul]

/-- **The diameter invariant**: every basis simplex of the chain `c` has all pairwise vertex distances
`≤ δ`. The carrier of the subdivision-shrinkage induction. -/
def diamLe (δ : ℝ) {n : ℕ} (c : LinChain V n) : Prop :=
  ∀ w ∈ c.support, ∀ i k, ‖w i - w k‖ ≤ δ

omit [NormedSpace ℝ V] in
theorem diamLe_zero_chain (δ : ℝ) {n : ℕ} : diamLe δ (0 : LinChain V n) := by
  intro w hw; simp at hw

omit [NormedSpace ℝ V] in
theorem diamLe.mono {δ δ' : ℝ} (hle : δ ≤ δ') {n : ℕ} {c : LinChain V n} (h : diamLe δ c) :
    diamLe δ' c := fun w hw i k => (h w hw i k).trans hle

omit [NormedSpace ℝ V] in
theorem diamLe_single {δ : ℝ} {n : ℕ} {v : Fin (n + 1) → V} {a : ZMod 2}
    (h : ∀ i k, ‖v i - v k‖ ≤ δ) : diamLe δ (Finsupp.single v a) := by
  intro w hw i k
  obtain rfl := Finset.mem_singleton.1 (Finset.mem_of_subset Finsupp.support_single_subset hw)
  exact h i k

omit [NormedSpace ℝ V] in
theorem diamLe.add {δ : ℝ} {n : ℕ} {c d : LinChain V n} (hc : diamLe δ c) (hd : diamLe δ d) :
    diamLe δ (c + d) := by
  classical
  intro w hw i k
  rcases Finset.mem_union.1 (Finsupp.support_add hw) with h | h
  · exact hc w h i k
  · exact hd w h i k

omit [NormedSpace ℝ V] in
theorem diamLe.smul {δ : ℝ} {n : ℕ} (a : ZMod 2) {c : LinChain V n} (hc : diamLe δ c) :
    diamLe δ (a • c) :=
  fun w hw => hc w (Finsupp.support_smul hw)

omit [NormedSpace ℝ V] in
theorem diamLe.sum {δ : ℝ} {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → LinChain V n)
    (hf : ∀ i ∈ s, diamLe δ (f i)) : diamLe δ (∑ i ∈ s, f i) :=
  Finset.sum_induction f (diamLe δ) (fun _ _ => diamLe.add) (diamLe_zero_chain δ) hf

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Membership in `chainsIn S` forces every vertex of every support simplex into `S`. -/
theorem chainsIn_support {S : Set V} {n : ℕ} {c : LinChain V n} (hc : c ∈ chainsIn S n) :
    ∀ w ∈ c.support, ∀ i, w i ∈ S := by
  classical
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨u, hu, rfl⟩ w hw i
    obtain rfl := Finset.mem_singleton.1 (Finset.mem_of_subset Finsupp.support_single_subset hw)
    exact hu i
  · intro w hw; simp at hw
  · intro x y _ _ hx hy w hw i
    rcases Finset.mem_union.1 (Finsupp.support_add hw) with h | h
    · exact hx w h i
    · exact hy w h i
  · intro a x _ hx w hw i; exact hx w (Finsupp.support_smul hw) i

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The cone is the relabelling `v ↦ Fin.cons b v` of the chain — its support simplices are exactly the
`b`-coned simplices of `c`. -/
theorem cone_eq_mapDomain (b : V) (n : ℕ) (c : LinChain V n) :
    cone b n c = Finsupp.mapDomain (Fin.cons b) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.mapDomain_zero]
  | add c d hc hd => rw [map_add, Finsupp.mapDomain_add, hc, hd]
  | single v a => rw [cone_single_smul, Finsupp.mapDomain_single, Finsupp.smul_single,
      smul_eq_mul, mul_one]

omit [NormedSpace ℝ V] in
/-- **Cone diameter preservation**: if the apex `b` is within `δ` of every vertex of `c` and every
basis simplex of `c` has diameter `≤ δ`, then so does `cone b c` (its simplices are `b` prepended). -/
theorem cone_diamLe {δ : ℝ} {m : ℕ} {b : V} {c : LinChain V m}
    (hb : ∀ w ∈ c.support, ∀ i, ‖b - w i‖ ≤ δ) (hc : diamLe δ c) :
    diamLe δ (cone b m c) := by
  classical
  rw [cone_eq_mapDomain]
  intro w' hw' i k
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hw')
  refine Fin.cases ?_ (fun j => ?_) i
  · refine Fin.cases ?_ (fun l => ?_) k
    · simp only [Fin.cons_zero, sub_self, norm_zero]
      exact (norm_nonneg _).trans (hb w hw 0)
    · simpa only [Fin.cons_zero, Fin.cons_succ] using hb w hw l
  · refine Fin.cases ?_ (fun l => ?_) k
    · simp only [Fin.cons_succ, Fin.cons_zero]
      rw [norm_sub_rev]
      exact hb w hw j
    · simpa only [Fin.cons_succ] using hc w hw j l

/-- **Barycenter-to-hull bound**: the barycenter of `v` is within `(k/(k+1))·d` of *any* point of the
convex hull of `v`'s vertices (the distance to a hull point is `≤` the distance to some vertex, by
`convexHull_exists_dist_ge`, then Lemma A). Used for the subdivision vertices, which live in the hull. -/
theorem norm_barycenter_sub_convexHull_le {k : ℕ} (v : Fin (k + 1) → V) {p : V}
    (hp : p ∈ convexHull ℝ (Set.range v)) {d : ℝ} (hd : ∀ i j, ‖v i - v j‖ ≤ d) :
    ‖barycenter v - p‖ ≤ ((k : ℝ) / ((k : ℝ) + 1)) * d := by
  obtain ⟨_, ⟨i, rfl⟩, hle⟩ := convexHull_exists_dist_ge hp (barycenter v)
  calc ‖barycenter v - p‖ = dist p (barycenter v) := by rw [dist_comm, dist_eq_norm]
    _ ≤ dist (v i) (barycenter v) := hle
    _ = ‖barycenter v - v i‖ := by rw [dist_eq_norm, norm_sub_rev]
    _ ≤ ((k : ℝ) / ((k : ℝ) + 1)) * d := norm_barycenter_sub_vertex_le v i (fun j => hd j i)

/-- The subdivision contraction factors increase with dimension: `m/(m+1) ≤ (m+1)/((m+1)+1)`. Stated
with the `Nat.cast (m+1)` numerator so it matches the `↑(n+1)` factor of the goal in the recursion. -/
theorem div_succ_le_div_succ_succ (m : ℕ) :
    (m : ℝ) / ((m : ℝ) + 1) ≤ ((m + 1 : ℕ) : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) := by
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith

/-- **Barycentric subdivision contracts diameter by `n/(n+1)`**: if every basis simplex of `c` has
diameter `≤ δ`, then every simplex of `Sd c` has diameter `≤ (n/(n+1))·δ`. Induction on dimension `n`:
a piece of `Sd[v]` is `barycenter v` coned onto a piece of `Sd(∂[v])`; the barycenter is within
`(n/(n+1))δ` of the whole hull (Lemma A + convexity) and the inner pieces shrink by the smaller
dimension factor (IH + monotonicity). -/
theorem linSubdiv_diamLe {δ : ℝ} : ∀ (n : ℕ) {c : LinChain V n}, diamLe δ c →
    diamLe ((n : ℝ) / ((n : ℝ) + 1) * δ) (linSubdiv n c)
  | 0, c, _ => by
    rw [linSubdiv_zero]
    intro w _ i k
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero k, sub_self, norm_zero]
    simp
  | n + 1, c, hc => by
    have hrw : linSubdiv (n + 1) c
        = c.sum (fun v a => linSubdiv (n + 1) (Finsupp.single v a)) := by
      conv_lhs => rw [← Finsupp.sum_single c]
      simp only [Finsupp.sum, map_sum]
    rw [hrw, Finsupp.sum]
    refine diamLe.sum _ _ (fun v hv => ?_)
    have hvd : ∀ i k, ‖v i - v k‖ ≤ δ := hc v hv
    rw [linSubdiv_single_smul]
    refine diamLe.smul _ (cone_diamLe (fun w hw i => ?_) ?_)
    · have hmem : w i ∈ convexHull ℝ (Set.range v) :=
        chainsIn_support (linSubdiv_mem_chainsIn (convex_convexHull ℝ _) n
          (linBoundary_mem_chainsIn (single_mem_chainsIn
            (fun j => subset_convexHull ℝ (Set.range v) (Set.mem_range_self j))))) w hw i
      exact norm_barycenter_sub_convexHull_le v hmem hvd
    · refine (linSubdiv_diamLe n ?_).mono
        (mul_le_mul_of_nonneg_right (div_succ_le_div_succ_succ n)
          ((norm_nonneg _).trans (hvd 0 0)))
      rw [linBoundary_single, linBoundaryBasis]
      exact diamLe.sum _ _ (fun i _ => diamLe_single (fun a b => hvd _ _))

/-- **Iterated subdivision contracts diameter geometrically**: the `m`-fold barycentric subdivision
shrinks every simplex's diameter by `(n/(n+1))^m`. Induction on `m` from `linSubdiv_diamLe`. -/
theorem linSubdiv_iterate_diamLe {δ : ℝ} {n : ℕ} :
    ∀ (m : ℕ) {c : LinChain V n}, diamLe δ c →
      diamLe (((n : ℝ) / ((n : ℝ) + 1)) ^ m * δ) ((linSubdiv n)^[m] c)
  | 0, c, hc => by simpa using hc
  | m + 1, c, hc => by
    rw [Function.iterate_succ_apply']
    refine (linSubdiv_diamLe n (linSubdiv_iterate_diamLe m hc)).mono (le_of_eq ?_)
    rw [pow_succ]; ring

/-- **Existence of an arbitrarily fine subdivision**: for any target `ε > 0`, enough barycentric
subdivisions make every simplex's diameter `< ε`, since the contraction factor `(n/(n+1))^m → 0`. The
smallness input that the Lebesgue-number excision step consumes. -/
theorem exists_iterate_diamLe {δ : ℝ} {n : ℕ} {c : LinChain V n} (hc : diamLe δ c)
    {ε : ℝ} (hε : 0 < ε) : ∃ m, diamLe ε ((linSubdiv n)^[m] c) := by
  have hr0 : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have hr1 : (n : ℝ) / ((n : ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have htend : Filter.Tendsto (fun m => ((n : ℝ) / ((n : ℝ) + 1)) ^ m * δ) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const δ
  obtain ⟨m, hm⟩ := (htend.eventually_lt_const hε).exists
  exact ⟨m, (linSubdiv_iterate_diamLe m hc).mono (le_of_lt hm)⟩

end SKEFTHawking.SingularSubdivisionDiameter
