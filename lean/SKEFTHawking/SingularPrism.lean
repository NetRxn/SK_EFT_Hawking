import Mathlib
import SKEFTHawking.SingularExcisionPushforward

/-!
# The prism operator and homotopy invariance of singular ℤ/2 homology

Given a homotopy `H : X × I → Y` between `f, g : X → Y`, the prism operator `P : Cₙ(X) → Cₙ₊₁(Y)`
is a chain homotopy witnessing `f_# ≃ g_#`, hence homotopic maps induce equal maps on singular
homology. The construction triangulates each prism `Δⁿ × I` into `n + 1` affine `(n+1)`-simplices

  `a_i : Δⁿ⁺¹ → Δⁿ × I`,  `ê_k ↦ (e_k, 0)` for `k ≤ i`, `(e_{k-1}, 1)` for `k > i`,

and post-composes `H ∘ (σ × id) ∘ a_i`. Because the `a_i` are **affine** (vertices map to vertices),
there is no continuity seam — the cone/division formula is avoided entirely.

This is the foundation for `Hₖ(ℝⁿ) = 0` (acyclicity of star-convex sets via the contraction
homotopy) and the homotopy equivalences `ℝⁿ ∖ 0 ≃ Sⁿ⁻¹` used in the local-homology computation.

## §1. The affine prism maps

`prismAlpha i : Δⁿ⁺¹ → Δⁿ` is the simplicial degeneracy `Fin.predAbove i` realized affinely (the
`Δⁿ`-component of `a_i`); `prismBeta i : Δⁿ⁺¹ → I` is the `[0,1]`-component (sum of the coordinates
strictly above `i`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularExcisionPushforward
open SKEFTHawking.SingularCohomologyMod2

namespace SKEFTHawking.SingularPrism

/-- The `Δⁿ`-component of the `i`-th prism map: the affine realization of the simplicial degeneracy
`Fin.predAbove i`, sending vertex `ê_k` to `e_k` for `k ≤ i` and `e_{k-1}` for `k > i`. -/
noncomputable def prismAlpha {n : ℕ} (i : Fin (n + 1)) :
    C(stdSimplex ℝ (Fin (n + 2)), stdSimplex ℝ (Fin (n + 1))) :=
  affineSimplexStd (fun k => stdSimplex.vertex (Fin.predAbove i k))

/-- The `[0,1]`-component of the `i`-th prism map: the sum of the barycentric coordinates strictly
above `i` (so vertex `ê_k ↦ 0` for `k ≤ i`, `↦ 1` for `k > i`). -/
noncomputable def prismBeta {n : ℕ} (i : Fin (n + 1)) :
    C(stdSimplex ℝ (Fin (n + 2)), unitInterval) where
  toFun t := ⟨∑ k ∈ Finset.univ.filter (i.castSucc < ·), (t : Fin (n + 2) → ℝ) k, by
    refine ⟨Finset.sum_nonneg (fun k _ => t.2.1 k), ?_⟩
    calc ∑ k ∈ Finset.univ.filter (i.castSucc < ·), (t : Fin (n + 2) → ℝ) k
        ≤ ∑ k, (t : Fin (n + 2) → ℝ) k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun k _ _ => t.2.1 k)
      _ = 1 := t.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_finset_sum _ (fun k _ => ?_)) _
    exact (continuous_apply k).comp continuous_subtype_val

/-! ## §2. The prism simplices and the prism operator -/

/-- The `i`-th prism `(n+1)`-simplex of `σ` under the homotopy `H : X × I → Y`: the affine prism
map `(prismAlpha i, prismBeta i) : Δⁿ⁺¹ → Δⁿ × I` post-composed with `σ × id` and then `H`. -/
noncomputable def prismSimplex {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (i : Fin (n + 1)) :
    (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk (n + 1))) :=
  (Y.toSSetObjEquiv (op (SimplexCategory.mk (n + 1)))).symm
    (H.comp
      (((X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ).comp (prismAlpha i)).prodMk (prismBeta i)))

/-- The prism chain assigned to a single simplex `σ`: the ℤ/2-sum of its `n + 1` prism simplices
(over ℤ/2 the alternating signs `(-1)^i` of the integral prism all collapse to `1`). -/
noncomputable def prismBasis {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) : SingularChain Y (n + 1) :=
  ∑ i : Fin (n + 1), Finsupp.single (prismSimplex H σ i) 1

/-- **The prism operator** `P : Cₙ(X) → Cₙ₊₁(Y)`, the linear extension of `prismBasis` off the basis
simplices (`Finsupp.linearCombination`). It is the chain homotopy witnessing `f_# ≃ g_#`. -/
noncomputable def prismOp {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (n : ℕ) :
    SingularChain X n →ₗ[ZMod 2] SingularChain Y (n + 1) :=
  Finsupp.linearCombination (ZMod 2) (prismBasis H n)

@[simp] theorem prismOp_single {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ZMod 2) :
    prismOp H n (Finsupp.single σ a) = a • prismBasis H n σ := by
  rw [prismOp, Finsupp.linearCombination_single]

/-! ## §3. Face computations (towards the chain-homotopy identity `∂P + P∂ = f_# + g_#`) -/

/-- The affine `Δⁿ → Δⁿ⁺¹` coface map `δ_j` realized on standard simplices. -/
noncomputable def faceMap {n : ℕ} (j : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (SimplexCategory.δ j), stdSimplex.continuous_map (SimplexCategory.δ j)⟩

/-- The `Δⁿ`-component of the prism map post-composed with a coface is again affine, with vertex
data `predAbove i ∘ j.succAbove` — the simplicial identity that drives the boundary computation. -/
theorem prismAlpha_comp_face {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (prismAlpha i).comp (faceMap j)
      = affineSimplexStd (fun k => stdSimplex.vertex (Fin.predAbove i (j.succAbove k))) :=
  affineSimplexStd_comp_face (fun k => stdSimplex.vertex (Fin.predAbove i k)) j

/-- Filtered fiberwise sum: summing the `g`-fibers of `T` over the targets satisfying `P` is the
sum of `T` over the sources whose `g`-image satisfies `P`. The reindexing that converts a
pushforward coordinate restricted to a coordinate-threshold (the β-face computation) into a
threshold on the source simplex. -/
private theorem sum_fiberwise_filter {α γ : Type*} [Fintype α] [Fintype γ] [DecidableEq γ]
    (g : α → γ) (P : γ → Prop) [DecidablePred P] (T : α → ℝ) :
    ∑ k ∈ Finset.univ.filter P, ∑ l ∈ Finset.univ.filter (fun m => g m = k), T l
      = ∑ l ∈ Finset.univ.filter (fun l => P (g l)), T l := by
  rw [Finset.sum_filter]
  conv_rhs => rw [Finset.sum_filter]
  rw [← Finset.sum_fiberwise Finset.univ g (fun l => if P (g l) then T l else 0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hk
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_filter] at hl
    rw [hl.2, if_pos hk]
  · refine (Finset.sum_eq_zero fun l hl => ?_).symm
    rw [Finset.mem_filter] at hl
    rw [hl.2, if_neg hk]

/-- **The β-face behaviour**: the `[0,1]`-component of the prism map, restricted along the coface
`δ_j`, is the coordinate-threshold `i.castSucc < j.succAbove ·` on the source simplex. This is the
threshold shift that classifies each face of a prism simplex (top/bottom/internal/side). -/
theorem prismBeta_faceMap_coe {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2))
    (t : stdSimplex ℝ (Fin (n + 1))) :
    ((prismBeta i (faceMap j t) : unitInterval) : ℝ)
      = ∑ l ∈ Finset.univ.filter (fun l => i.castSucc < j.succAbove l), (t : Fin (n + 1) → ℝ) l := by
  have hcoe : ∀ k, ((faceMap j t : stdSimplex ℝ (Fin (n + 2))) : Fin (n + 2) → ℝ) k
      = ∑ l ∈ Finset.univ.filter (fun m => j.succAbove m = k), (t : Fin (n + 1) → ℝ) l := by
    intro k
    show (stdSimplex.map _ t : Fin (n + 2) → ℝ) k = _
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    rfl
  show ∑ k ∈ Finset.univ.filter (fun k => i.castSucc < k),
      ((faceMap j t : stdSimplex ℝ (Fin (n + 2))) : Fin (n + 2) → ℝ) k = _
  simp_rw [hcoe]
  exact sum_fiberwise_filter (fun m => j.succAbove m) (fun k => i.castSucc < k) (t : Fin (n + 1) → ℝ)

/-- **Gateway face computation**: the realization of the `j`-th face of the `i`-th prism simplex of
`σ` is `H` applied to the coface-restricted prism map. The α-component is `prismAlpha i ∘ δ_j`
(simplifiable by `prismAlpha_comp_face`), the β-component is `prismBeta i ∘ δ_j` (whose value is
`prismBeta_faceMap_coe`). Each face of `prismSimplex` is then classified by these two. -/
theorem prismSimplex_face {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (Y.toSSetObjEquiv (op (SimplexCategory.mk n))) (face j (prismSimplex H σ i))
      = H.comp
          ((((X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ).comp (prismAlpha i)).comp
              (faceMap j)).prodMk ((prismBeta i).comp (faceMap j))) := by
  rw [prismSimplex, toSSetObjEquiv_symm_face]
  rfl

/-! ## §4. The homotopy endpoints `f_#` and `g_#` -/

/-- The simplex `σ` evaluated at homotopy-time `r`: realization `x ↦ H(σ(x), r)`. The boundary
identity expresses `∂P + P∂` in terms of the two endpoints `endSimplex H 0` (`f_#`) and
`endSimplex H 1` (`g_#`). -/
noncomputable def endSimplex {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (r : unitInterval) (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk n)) :=
  (Y.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
    (H.comp ((X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ).prodMk (ContinuousMap.const _ r)))

/-- The chain map `Cₙ(X) → Cₙ(Y)` of the homotopy's time-`r` slice (`f_#` at `r = 0`, `g_#` at
`r = 1`), the linear extension of `endSimplex`. -/
noncomputable def endMap {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval) (n : ℕ) :
    SingularChain X n →ₗ[ZMod 2] SingularChain Y n :=
  Finsupp.linearCombination (ZMod 2) (fun σ => Finsupp.single (endSimplex H r σ) 1)

@[simp] theorem endMap_single {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval)
    (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ZMod 2) :
    endMap H r n (Finsupp.single σ a) = Finsupp.single (endSimplex H r σ) a := by
  rw [endMap, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## §5. The bottom face is `f_#` -/

/-- The `α`-component of the last prism map restricted along the last coface is the identity
(`predAbove last ∘ succAbove last` is vertex-preserving). -/
theorem prismAlpha_last_comp_faceMap_last {n : ℕ} :
    (prismAlpha (Fin.last n)).comp (faceMap (Fin.last (n + 1))) = ContinuousMap.id _ := by
  rw [prismAlpha_comp_face]
  simp only [Fin.succAbove_last, Fin.predAbove_last_castSucc]
  exact affineSimplexStd_vertex_id

/-- The `β`-component of the last prism map restricted along the last coface is constantly `0` —
the time coordinate of `f_#` (the threshold `last.castSucc < l.castSucc` is never met). -/
theorem prismBeta_last_comp_faceMap_last {n : ℕ} :
    (prismBeta (Fin.last n)).comp (faceMap (Fin.last (n + 1)))
      = ContinuousMap.const _ (0 : unitInterval) := by
  ext t
  have hfilter : Finset.univ.filter
      (fun l => (Fin.last n).castSucc < (Fin.last (n + 1)).succAbove l) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro l _
    rw [Fin.succAbove_last, Fin.castSucc_lt_castSucc_iff]
    exact Fin.not_lt.2 (Fin.le_last l)
  show (prismBeta (Fin.last n) (faceMap (Fin.last (n + 1)) t) : ℝ) = ((0 : unitInterval) : ℝ)
  rw [prismBeta_faceMap_coe, hfilter, Finset.sum_empty]
  rfl

/-- **The bottom face of the last prism simplex is `f_#`**: `face_last (prismSimplex H σ last) =
endSimplex H 0 σ`. The α-component collapses to the identity and the β-component to constant `0`.
(Closed by defeq-aware `congrArg`/`congr_arg₂` rather than syntactic `rw`: the gateway-produced
`(prismAlpha last).comp (faceMap last)` is defeq — but not syntactically equal — to the freshly
elaborated form, so `rw` cannot match it.) -/
theorem face_last_prismSimplex_last {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    face (Fin.last (n + 1)) (prismSimplex H σ (Fin.last n)) = endSimplex H 0 σ := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
  rw [prismSimplex_face, endSimplex, Equiv.apply_symm_apply]
  refine congrArg (fun g => H.comp g) ?_
  refine congr_arg₂ ContinuousMap.prodMk ?_ prismBeta_last_comp_faceMap_last
  rw [ContinuousMap.comp_assoc]
  exact (congrArg (((X.toSSetObjEquiv (op (SimplexCategory.mk n))) σ).comp ·)
    prismAlpha_last_comp_faceMap_last).trans (ContinuousMap.comp_id _)

/-! ## §6. The top face is `g_#` -/

/-- The `α`-component of the zeroth prism map restricted along the zeroth coface is the identity. -/
theorem prismAlpha_zero_comp_faceMap_zero {n : ℕ} :
    (prismAlpha (0 : Fin (n + 1))).comp (faceMap (0 : Fin (n + 2))) = ContinuousMap.id _ := by
  rw [prismAlpha_comp_face]
  simp only [Fin.succAbove_zero, Fin.predAbove_zero_succ]
  exact affineSimplexStd_vertex_id

/-- The `β`-component of the zeroth prism map restricted along the zeroth coface is constantly `1` —
the time coordinate of `g_#` (the threshold `0 < l.succ` always holds, so the full sum `= 1`). -/
theorem prismBeta_zero_comp_faceMap_zero {n : ℕ} :
    (prismBeta (0 : Fin (n + 1))).comp (faceMap (0 : Fin (n + 2)))
      = ContinuousMap.const _ (1 : unitInterval) := by
  ext t
  have hfilter : Finset.univ.filter
      (fun l => (0 : Fin (n + 1)).castSucc < (0 : Fin (n + 2)).succAbove l) = Finset.univ := by
    rw [Finset.filter_true_of_mem]
    intro l _
    rw [Fin.succAbove_zero, Fin.castSucc_zero]
    exact Fin.succ_pos l
  show (prismBeta (0 : Fin (n + 1)) (faceMap (0 : Fin (n + 2)) t) : ℝ) = ((1 : unitInterval) : ℝ)
  rw [prismBeta_faceMap_coe, hfilter]
  exact t.2.2

/-- **The top face of the zeroth prism simplex is `g_#`**: `face_0 (prismSimplex H σ 0) =
endSimplex H 1 σ`. The α-component collapses to the identity and the β-component to constant `1`. -/
theorem face_zero_prismSimplex_zero {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    face (0 : Fin (n + 2)) (prismSimplex H σ (0 : Fin (n + 1))) = endSimplex H 1 σ := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
  rw [prismSimplex_face, endSimplex, Equiv.apply_symm_apply]
  refine congrArg (fun g => H.comp g) ?_
  refine congr_arg₂ ContinuousMap.prodMk ?_ prismBeta_zero_comp_faceMap_zero
  rw [ContinuousMap.comp_assoc]
  exact (congrArg (((X.toSSetObjEquiv (op (SimplexCategory.mk n))) σ).comp ·)
    prismAlpha_zero_comp_faceMap_zero).trans (ContinuousMap.comp_id _)

/-! ## §7. The diagonal faces (`j = i.castSucc`, `j = i.succ`) collapse the prism map -/

/-- The `α`-component of the `i`-th prism map restricted along the `i.castSucc` coface is the
identity (`Fin.predAbove_succAbove` — the adjacent codegeneracy ∘ coface law). -/
theorem prismAlpha_comp_faceMap_castSucc {n : ℕ} (i : Fin (n + 1)) :
    (prismAlpha i).comp (faceMap i.castSucc) = ContinuousMap.id _ := by
  rw [prismAlpha_comp_face]
  simp only [Fin.predAbove_succAbove]
  exact affineSimplexStd_vertex_id

/-- The `α`-component of the `i`-th prism map restricted along the `i.succ` coface is the identity
(the other adjacent codegeneracy ∘ coface law `σ_i δ_{i+1} = id`). -/
theorem prismAlpha_comp_faceMap_succ {n : ℕ} (i : Fin (n + 1)) :
    (prismAlpha i).comp (faceMap i.succ) = ContinuousMap.id _ := by
  rw [prismAlpha_comp_face]
  have h : ∀ k : Fin (n + 1), Fin.predAbove i (Fin.succAbove i.succ k) = k := by
    intro k
    unfold Fin.predAbove Fin.succAbove
    split_ifs with h1 h2 h2
    · exfalso; simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h2; omega
    · exact Fin.castPred_castSucc _
    · exact Fin.pred_succ _
    · exfalso; simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h2; omega
  simp only [h]
  exact affineSimplexStd_vertex_id

/-- The β-value of the `w`-diagonal face (`j = i.succ`) is the partial stdSimplex sum over `l > i`. -/
theorem prismBeta_faceMap_succ_eq {n : ℕ} (i : Fin (n + 1)) (t : stdSimplex ℝ (Fin (n + 1))) :
    ((prismBeta i (faceMap i.succ t) : unitInterval) : ℝ)
      = ∑ l ∈ Finset.univ.filter (fun l => i < l), (t : Fin (n + 1) → ℝ) l := by
  rw [prismBeta_faceMap_coe]
  refine Finset.sum_congr (Finset.filter_congr (fun l _ => ?_)) (fun _ _ => rfl)
  unfold Fin.succAbove
  split_ifs with hc <;> simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hc ⊢ <;> omega

/-- The β-value of the `v`-diagonal face (`j = i.castSucc`) is the partial stdSimplex sum over
`l ≥ i`. -/
theorem prismBeta_faceMap_castSucc_eq {n : ℕ} (i : Fin (n + 1)) (t : stdSimplex ℝ (Fin (n + 1))) :
    ((prismBeta i (faceMap i.castSucc t) : unitInterval) : ℝ)
      = ∑ l ∈ Finset.univ.filter (fun l => i ≤ l), (t : Fin (n + 1) → ℝ) l := by
  rw [prismBeta_faceMap_coe]
  refine Finset.sum_congr (Finset.filter_congr (fun l _ => ?_)) (fun _ _ => rfl)
  unfold Fin.succAbove
  split_ifs with hc <;>
    simp only [Fin.lt_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ] at hc ⊢ <;> omega

/-! ## §8. The mixed simplicial identity (extracted from `SimplexCategory`) -/

/-- The mixed simplicial identity `σ_j δ_i = δ_i σ_{j}` (for `i ≤ j.castSucc`), extracted at the Fin
level from `SimplexCategory.δ_comp_σ_of_le`. The categorical equation's underlying-function
component IS this identity definitionally, so `congrArg … |> exact` closes it with no coercion
lemmas. This is the α-input for the `v`-side prism faces. -/
theorem predAbove_succAbove_of_le {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (H : i ≤ j.castSucc) (m : Fin (n + 2)) :
    Fin.predAbove j.succ (Fin.succAbove i.castSucc m) = Fin.succAbove i (Fin.predAbove j m) :=
  congrArg (fun f => (ConcreteCategory.hom f) m) (SimplexCategory.δ_comp_σ_of_le H)

/-- The mixed simplicial identity `σ_j δ_i = δ_i σ_j` (for `j.castSucc < i`), extracted from
`SimplexCategory.δ_comp_σ_of_gt`. The α-input for the `w`-side prism faces. -/
theorem predAbove_succAbove_of_gt {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (H : j.castSucc < i) (m : Fin (n + 2)) :
    Fin.predAbove j.castSucc (Fin.succAbove i.succ m) = Fin.succAbove i (Fin.predAbove j m) :=
  congrArg (fun f => (ConcreteCategory.hom f) m) (SimplexCategory.δ_comp_σ_of_gt H)

/-- **The `v`-side prism-face α-identity**: `prismAlpha (j₀.succ) ∘ δ_{i₀.castSucc} = δ_{i₀} ∘
prismAlpha j₀` (for `i₀ ≤ j₀.castSucc`). The vertex data agree by `predAbove_succAbove_of_le`. -/
theorem prismAlpha_comp_faceMap_eq_v {n : ℕ} {i₀ : Fin (n + 2)} {j₀ : Fin (n + 1)}
    (H : i₀ ≤ j₀.castSucc) :
    (prismAlpha j₀.succ).comp (faceMap i₀.castSucc) = (faceMap i₀).comp (prismAlpha j₀) := by
  rw [prismAlpha_comp_face, prismAlpha, faceMap, stdSimplexMap_comp_affineSimplexStd]
  congr 1
  funext m
  exact (congrArg stdSimplex.vertex (predAbove_succAbove_of_le H m)).trans
    (stdSimplex.map_vertex _ _).symm

/-- **The `w`-side prism-face α-identity**: `prismAlpha (j₀.castSucc) ∘ δ_{i₀.succ} = δ_{i₀} ∘
prismAlpha j₀` (for `j₀.castSucc < i₀`). -/
theorem prismAlpha_comp_faceMap_eq_w {n : ℕ} {i₀ : Fin (n + 2)} {j₀ : Fin (n + 1)}
    (H : j₀.castSucc < i₀) :
    (prismAlpha j₀.castSucc).comp (faceMap i₀.succ) = (faceMap i₀).comp (prismAlpha j₀) := by
  rw [prismAlpha_comp_face, prismAlpha, faceMap, stdSimplexMap_comp_affineSimplexStd]
  congr 1
  funext m
  exact (congrArg stdSimplex.vertex (predAbove_succAbove_of_gt H m)).trans
    (stdSimplex.map_vertex _ _).symm

/-- **The `v`-side prism-face β-preservation**: `prismBeta (j₀.succ) ∘ δ_{i₀.castSucc} = prismBeta
j₀` (for `i₀ ≤ j₀.castSucc`) — the time coordinate is unchanged by the side coface. -/
theorem prismBeta_comp_faceMap_eq_v {n : ℕ} {i₀ : Fin (n + 2)} {j₀ : Fin (n + 1)}
    (H : i₀ ≤ j₀.castSucc) :
    (prismBeta j₀.succ).comp (faceMap i₀.castSucc) = prismBeta j₀ := by
  have hH : (i₀ : ℕ) ≤ (j₀ : ℕ) := by simpa [Fin.le_def, Fin.val_castSucc] using H
  ext t
  show (prismBeta j₀.succ (faceMap i₀.castSucc t) : ℝ)
    = ∑ l ∈ Finset.univ.filter (fun l => j₀.castSucc < l), (t : Fin (n + 2) → ℝ) l
  rw [prismBeta_faceMap_coe]
  refine Finset.sum_congr (Finset.filter_congr (fun l _ => ?_)) (fun _ _ => rfl)
  unfold Fin.succAbove
  split_ifs with hc <;> simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hc ⊢ <;> omega

/-- **The `w`-side prism-face β-preservation**: `prismBeta (j₀.castSucc) ∘ δ_{i₀.succ} = prismBeta
j₀` (for `j₀.castSucc < i₀`). -/
theorem prismBeta_comp_faceMap_eq_w {n : ℕ} {i₀ : Fin (n + 2)} {j₀ : Fin (n + 1)}
    (H : j₀.castSucc < i₀) :
    (prismBeta j₀.castSucc).comp (faceMap i₀.succ) = prismBeta j₀ := by
  have hH : (j₀ : ℕ) < (i₀ : ℕ) := by simpa [Fin.lt_def, Fin.val_castSucc] using H
  ext t
  show (prismBeta j₀.castSucc (faceMap i₀.succ t) : ℝ)
    = ∑ l ∈ Finset.univ.filter (fun l => j₀.castSucc < l), (t : Fin (n + 2) → ℝ) l
  rw [prismBeta_faceMap_coe]
  refine Finset.sum_congr (Finset.filter_congr (fun l _ => ?_)) (fun _ _ => rfl)
  unfold Fin.succAbove
  split_ifs with hc <;> simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hc ⊢ <;> omega

/-- **The `v`-side prism side face is a prism of a face**: `face_{i₀.castSucc}(prismSimplex H σ
(j₀.succ)) = prismSimplex H (face i₀ σ) j₀` (for `i₀ ≤ j₀.castSucc`). These are the `prismOp(∂σ)`
terms in the boundary identity. -/
theorem face_prismSimplex_side_v {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) {i₀ : Fin (n + 2)}
    {j₀ : Fin (n + 1)} (H' : i₀ ≤ j₀.castSucc) :
    face i₀.castSucc (prismSimplex H σ j₀.succ) = prismSimplex H (face i₀ σ) j₀ := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk (n + 1)))).injective
  rw [prismSimplex_face, prismSimplex, Equiv.apply_symm_apply]
  refine congrArg (fun g => H.comp g) ?_
  refine congr_arg₂ ContinuousMap.prodMk ?_ (prismBeta_comp_faceMap_eq_v H')
  refine (ContinuousMap.comp_assoc _ _ _).trans ?_
  refine (congrArg (((X.toSSetObjEquiv (op (SimplexCategory.mk (n + 1)))) σ).comp ·)
    (prismAlpha_comp_faceMap_eq_v H')).trans ?_
  refine (ContinuousMap.comp_assoc _ _ _).symm.trans ?_
  exact congrArg (·.comp (prismAlpha j₀)) (toSSetObjEquiv_face i₀ σ).symm

/-- **The `w`-side prism side face is a prism of a face**: `face_{i₀.succ}(prismSimplex H σ
(j₀.castSucc)) = prismSimplex H (face i₀ σ) j₀` (for `j₀.castSucc < i₀`). -/
theorem face_prismSimplex_side_w {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) {i₀ : Fin (n + 2)}
    {j₀ : Fin (n + 1)} (H' : j₀.castSucc < i₀) :
    face i₀.succ (prismSimplex H σ j₀.castSucc) = prismSimplex H (face i₀ σ) j₀ := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk (n + 1)))).injective
  rw [prismSimplex_face, prismSimplex, Equiv.apply_symm_apply]
  refine congrArg (fun g => H.comp g) ?_
  refine congr_arg₂ ContinuousMap.prodMk ?_ (prismBeta_comp_faceMap_eq_w H')
  refine (ContinuousMap.comp_assoc _ _ _).trans ?_
  refine (congrArg (((X.toSSetObjEquiv (op (SimplexCategory.mk (n + 1)))) σ).comp ·)
    (prismAlpha_comp_faceMap_eq_w H')).trans ?_
  refine (ContinuousMap.comp_assoc _ _ _).symm.trans ?_
  exact congrArg (·.comp (prismAlpha j₀)) (toSSetObjEquiv_face i₀ σ).symm

/-! ## §9. Internal cancellation of the diagonal faces -/

/-- **Internal cancellation**: the shared face `(i.castSucc).succ = (i.succ).castSucc` is the
`w`-diagonal of prism `i.castSucc` AND the `v`-diagonal of prism `i.succ`; both have α-component the
identity and β-component `Σ_{l>i}`, so the two prism simplices share this face. In the ℤ/2 boundary
`∑ᵢ∑ⱼ face_j(prism σ i)` the two appearances cancel. -/
theorem prism_internal_cancel {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (i : Fin n) :
    face i.castSucc.succ (prismSimplex H σ i.castSucc)
      = face i.succ.castSucc (prismSimplex H σ i.succ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
  rw [prismSimplex_face, prismSimplex_face]
  refine congrArg (fun g => H.comp g) ?_
  refine congr_arg₂ ContinuousMap.prodMk ?_ ?_
  · have hL : ((X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ).comp
        (prismAlpha i.castSucc)).comp (faceMap i.castSucc.succ)
        = X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ := by
      rw [ContinuousMap.comp_assoc]
      exact (congrArg (((X.toSSetObjEquiv (op (SimplexCategory.mk n))) σ).comp ·)
        (prismAlpha_comp_faceMap_succ i.castSucc)).trans (ContinuousMap.comp_id _)
    have hR : ((X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ).comp
        (prismAlpha i.succ)).comp (faceMap i.succ.castSucc)
        = X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ := by
      rw [ContinuousMap.comp_assoc]
      exact (congrArg (((X.toSSetObjEquiv (op (SimplexCategory.mk n))) σ).comp ·)
        (prismAlpha_comp_faceMap_castSucc i.succ)).trans (ContinuousMap.comp_id _)
    exact hL.trans hR.symm
  · ext t
    show (prismBeta i.castSucc (faceMap i.castSucc.succ t) : ℝ)
      = (prismBeta i.succ (faceMap i.succ.castSucc t) : ℝ)
    rw [prismBeta_faceMap_succ_eq, prismBeta_faceMap_castSucc_eq]
    refine Finset.sum_congr (Finset.filter_congr (fun l _ => ?_)) (fun _ _ => rfl)
    simp only [Fin.lt_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ]
    omega

/-! ## §10. The boundary-identity double sums -/

/-- `∂(prismBasis σ)` as a double sum of single faces of prism simplices. -/
theorem chainBoundary_prismBasis {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    chainBoundary Y (n + 1) (prismBasis H (n + 1) σ)
      = ∑ i : Fin (n + 2), ∑ j : Fin (n + 3), Finsupp.single (face j (prismSimplex H σ i)) 1 := by
  rw [prismBasis, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [chainBoundary_single, boundaryBasis]

/-- `prismOp(∂σ)` as a double sum of single prism simplices of faces. -/
theorem prismOp_chainBoundary {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    prismOp H n (chainBoundary X n (Finsupp.single σ 1))
      = ∑ k : Fin (n + 2), ∑ i' : Fin (n + 1),
          Finsupp.single (prismSimplex H (face k σ) i') 1 := by
  rw [chainBoundary_single, boundaryBasis, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [prismOp_single, one_smul, prismBasis]

/-- **The diagonal faces telescope to the endpoints**: `∑_p (face_{p.castSucc}(prism σ p) +
face_{p.succ}(prism σ p)) = g_# + f_#`. The w-diagonal of prism `p` equals the v-diagonal of prism
`p+1` (`prism_internal_cancel`), so the interior cancels mod 2, leaving the two endpoints. -/
theorem prism_diagonal_telescope {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    ∑ p : Fin (n + 2), (Finsupp.single (face p.castSucc (prismSimplex H σ p)) (1 : ZMod 2)
      + Finsupp.single (face p.succ (prismSimplex H σ p)) 1)
    = Finsupp.single (endSimplex H 1 σ) 1 + Finsupp.single (endSimplex H 0 σ) 1 := by
  rw [Finset.sum_add_distrib,
    Fin.sum_univ_succ
      (fun p : Fin (n + 2) => Finsupp.single (face p.castSucc (prismSimplex H σ p)) (1 : ZMod 2)),
    Fin.sum_univ_castSucc
      (fun p : Fin (n + 2) => Finsupp.single (face p.succ (prismSimplex H σ p)) (1 : ZMod 2))]
  have hcancel : (∑ p : Fin (n + 1),
        Finsupp.single (face p.castSucc.succ (prismSimplex H σ p.castSucc)) (1 : ZMod 2))
      = ∑ p : Fin (n + 1),
        Finsupp.single (face p.succ.castSucc (prismSimplex H σ p.succ)) (1 : ZMod 2) :=
    Finset.sum_congr rfl
      (fun p _ => congrArg (Finsupp.single · (1 : ZMod 2)) (prism_internal_cancel H σ p))
  rw [hcancel, Fin.castSucc_zero, face_zero_prismSimplex_zero]
  rw [show (Fin.last (n + 1)).succ = (Fin.last (n + 2) : Fin (n + 3)) from rfl]
  rw [show (Fin.last (n + 1) : Fin (n + 2)) = Fin.last (n + 1) from rfl, face_last_prismSimplex_last]
  rw [add_assoc, ← add_assoc _ _ (Finsupp.single (endSimplex H 0 σ) (1 : ZMod 2)),
    ZModModule.add_self, zero_add]

/-! ## §11. Assembling the chain-homotopy identity `∂P + P∂ = g_# + f_#` -/

/-- The `i`-th boundary face sum splits into the two **diagonal** faces (`j ∈ {i.castSucc, i.succ}`)
and the remaining **side** faces (the `prismOp(∂σ)` terms). -/
private theorem prism_face_sum_split {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) (i : Fin (n + 2)) :
    ∑ j : Fin (n + 3), Finsupp.single (face j (prismSimplex H σ i)) (1 : ZMod 2)
      = (Finsupp.single (face i.castSucc (prismSimplex H σ i)) 1
          + Finsupp.single (face i.succ (prismSimplex H σ i)) 1)
        + ∑ j ∈ Finset.univ.filter (fun j => ¬ (j = i.castSucc ∨ j = i.succ)),
            Finsupp.single (face j (prismSimplex H σ i)) (1 : ZMod 2) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin (n + 3) => j = i.castSucc ∨ j = i.succ)
    (fun j => Finsupp.single (face j (prismSimplex H σ i)) (1 : ZMod 2))]
  congr 1
  have hne : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
  have hfilter : Finset.univ.filter (fun j : Fin (n + 3) => j = i.castSucc ∨ j = i.succ)
      = {i.castSucc, i.succ} := by
    rw [Finset.filter_or, Finset.filter_eq', Finset.filter_eq', if_pos (Finset.mem_univ _),
      if_pos (Finset.mem_univ _), Finset.singleton_union]
  rw [hfilter, Finset.sum_pair hne]

/-- Splitting `∂(prismBasis σ)` into the diagonal sum (telescopes to `g_# + f_#`) and the side sum
(equals `prismOp(∂σ)`). -/
private theorem prism_boundary_diag_side {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    (∑ i : Fin (n + 2), ∑ j : Fin (n + 3),
        Finsupp.single (face j (prismSimplex H σ i)) (1 : ZMod 2))
      = (∑ p : Fin (n + 2), (Finsupp.single (face p.castSucc (prismSimplex H σ p)) 1
          + Finsupp.single (face p.succ (prismSimplex H σ p)) 1))
        + ∑ i : Fin (n + 2), ∑ j ∈ Finset.univ.filter (fun j => ¬ (j = i.castSucc ∨ j = i.succ)),
            Finsupp.single (face j (prismSimplex H σ i)) (1 : ZMod 2) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => prism_face_sum_split H σ i)

/-- **The side faces are exactly the `prismOp(∂σ)` terms**: the reindexing bijection `(k, i') ↦
(i, j)` sending each prism-of-a-face simplex to the matching side face of a prism. `v` for
`k ≤ i'.castSucc` (`(i, j) = (i'.succ, k.castSucc)`), `w` otherwise (`(i'.castSucc, k.succ)`). -/
private theorem prism_prismOp_eq_side {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    (∑ k : Fin (n + 2), ∑ i' : Fin (n + 1),
        Finsupp.single (prismSimplex H (face k σ) i') (1 : ZMod 2))
      = ∑ i : Fin (n + 2), ∑ j ∈ Finset.univ.filter (fun j => ¬ (j = i.castSucc ∨ j = i.succ)),
          Finsupp.single (face j (prismSimplex H σ i)) (1 : ZMod 2) := by
  have hconv : (∑ i : Fin (n + 2),
        ∑ j ∈ Finset.univ.filter (fun j => ¬ (j = i.castSucc ∨ j = i.succ)),
          Finsupp.single (face j (prismSimplex H σ i)) (1 : ZMod 2))
      = ∑ x ∈ (Finset.univ : Finset (Fin (n + 2) × Fin (n + 3))).filter
            (fun x => ¬ (x.2 = x.1.castSucc ∨ x.2 = x.1.succ)),
          Finsupp.single (face x.2 (prismSimplex H σ x.1)) (1 : ZMod 2) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_filter _ _)
  rw [← Finset.sum_product', Finset.univ_product_univ, hconv]
  refine Finset.sum_bij
    (fun (a : Fin (n + 2) × Fin (n + 1)) _ =>
      if a.1 ≤ a.2.castSucc then ((a.2.succ, a.1.castSucc) : Fin (n + 2) × Fin (n + 3))
      else (a.2.castSucc, a.1.succ)) ?_ ?_ ?_ ?_
  · intro a _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only
    split_ifs with h
    · simp only [Fin.le_def, Fin.val_castSucc] at h
      simp only [not_or, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      omega
    · simp only [not_le, Fin.lt_def, Fin.val_castSucc] at h
      simp only [not_or, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      omega
  · intro a₁ _ a₂ _ h
    obtain ⟨k₁, i₁⟩ := a₁
    obtain ⟨k₂, i₂⟩ := a₂
    dsimp only at h
    split_ifs at h with h1 h2 <;>
      simp only [Prod.mk.injEq, Fin.ext_iff, Fin.le_def, not_le, Fin.val_castSucc,
        Fin.val_succ] at * <;>
      omega
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨i, j⟩ := b
    obtain ⟨_, hb2⟩ := hb
    simp only [not_or, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hb2
    have hilt : (i : ℕ) < n + 2 := i.isLt
    have hjlt : (j : ℕ) < n + 3 := j.isLt
    by_cases hreg : (j : ℕ) < (i : ℕ)
    · refine ⟨(⟨(j : ℕ), by omega⟩, ⟨(i : ℕ) - 1, by omega⟩), Finset.mem_univ _, ?_⟩
      dsimp only
      have hc : (⟨(j : ℕ), by omega⟩ : Fin (n + 2))
          ≤ (⟨(i : ℕ) - 1, by omega⟩ : Fin (n + 1)).castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc]; omega
      rw [if_pos hc]
      simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, and_true]
      omega
    · refine ⟨(⟨(j : ℕ) - 1, by omega⟩, ⟨(i : ℕ), by omega⟩), Finset.mem_univ _, ?_⟩
      dsimp only
      have hc : ¬ (⟨(j : ℕ) - 1, by omega⟩ : Fin (n + 2))
          ≤ (⟨(i : ℕ), by omega⟩ : Fin (n + 1)).castSucc := by
        simp only [not_le, Fin.lt_def, Fin.val_castSucc]; omega
      rw [if_neg hc]
      simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, true_and]
      omega
  · intro a _
    dsimp only
    split_ifs with h
    · exact congrArg (Finsupp.single · (1 : ZMod 2)) (face_prismSimplex_side_v H σ h).symm
    · rw [not_le] at h
      exact congrArg (Finsupp.single · (1 : ZMod 2)) (face_prismSimplex_side_w H σ h).symm

/-- **The chain-homotopy identity on a basis simplex**: `∂P + P∂ = g_# + f_#` evaluated at
`single σ 1`. The boundary `∂(prismBasis σ)` splits into diagonal faces (telescoping to the two
endpoints `g_#`, `f_#` via `prism_diagonal_telescope`) and side faces (which double the `prismOp(∂σ)`
terms and cancel mod 2 via `prism_prismOp_eq_side`). -/
theorem prism_chainHomotopy_single {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    chainBoundary Y (n + 1) (prismOp H (n + 1) (Finsupp.single σ 1))
        + prismOp H n (chainBoundary X n (Finsupp.single σ 1))
      = endMap H 1 (n + 1) (Finsupp.single σ 1) + endMap H 0 (n + 1) (Finsupp.single σ 1) := by
  rw [prismOp_single, one_smul, endMap_single, endMap_single, chainBoundary_prismBasis,
    prismOp_chainBoundary, prism_boundary_diag_side, ← prism_prismOp_eq_side, add_assoc,
    ZModModule.add_self, add_zero]
  exact prism_diagonal_telescope H σ

/-- **The prism operator is a chain homotopy** witnessing `f_# ≃ g_#`: for any chain `c`,
`∂(Pc) + P(∂c) = g_#(c) + f_#(c)` (over ℤ/2). Extends `prism_chainHomotopy_single` off the basis by
linearity. This is the engine of homotopy invariance of singular ℤ/2 homology. -/
theorem prism_chainHomotopy {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) {n : ℕ}
    (c : SingularChain X (n + 1)) :
    chainBoundary Y (n + 1) (prismOp H (n + 1) c) + prismOp H n (chainBoundary X n c)
      = endMap H 1 (n + 1) c + endMap H 0 (n + 1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ =>
      simp only [map_add]
      rw [add_add_add_comm, add_add_add_comm (endMap H 1 (n + 1) c₁), h₁, h₂]
  | single σ a =>
      have hsa : Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod 2) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsa]
      simp only [map_smul, ← smul_add]
      exact congrArg (a • ·) (prism_chainHomotopy_single H σ)

/-- **The degree-0 chain-homotopy identity** `∂(P z) = g_#(z) + f_#(z)` on `single σ 1` (there is no
`P∂` term in degree `0`). The prism `1`-simplex of a `0`-simplex has exactly two faces — its
endpoints `g_#` and `f_#`. -/
theorem prism_chainHomotopy_zero_single {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    chainBoundary Y 0 (prismOp H 0 (Finsupp.single σ 1))
      = Finsupp.single (endSimplex H 1 σ) 1 + Finsupp.single (endSimplex H 0 σ) 1 := by
  rw [prismOp_single, one_smul, prismBasis, Fin.sum_univ_one, chainBoundary_single, boundaryBasis,
    Fin.sum_univ_two, face_zero_prismSimplex_zero,
    show face (1 : Fin 2) (prismSimplex H σ (0 : Fin 1)) = endSimplex H 0 σ from
      face_last_prismSimplex_last H σ]

/-- **The degree-0 chain homotopy** `∂ ∘ P = g_# + f_#` on all of `C₀` (no `P∂` term). -/
theorem prism_chainHomotopy_zero {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y))
    (c : SingularChain X 0) :
    chainBoundary Y 0 (prismOp H 0 c) = endMap H 1 0 c + endMap H 0 0 c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ =>
      simp only [map_add]
      rw [add_add_add_comm (endMap H 1 0 c₁), h₁, h₂]
  | single σ a =>
      rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod 2) by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      simp only [map_smul, endMap_single, ← smul_add]
      exact congrArg (a • ·) (prism_chainHomotopy_zero_single H σ)

/-! ## §12. The endpoint maps are chain maps -/

/-- **`endSimplex` face-naturality**: `face i (endSimplex H r σ) = endSimplex H r (face i σ)` — the
endpoint pushforward commutes with the simplicial face (post-composing by `H(·, r)` is natural). -/
theorem face_endSimplex {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) (i : Fin (n + 2)) :
    face i (endSimplex H r σ) = endSimplex H r (face i σ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
  simp only [endSimplex, toSSetObjEquiv_face, Equiv.apply_symm_apply]
  rfl

/-- **The endpoint map `endMap H r` is a chain map**: `∂ ∘ endMap = endMap ∘ ∂`. Hence `endMap H r`
sends cycles to cycles — the well-definedness input for homology-level homotopy invariance. -/
theorem chainBoundary_endMap {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval)
    (c : SingularChain X (n + 1)) :
    chainBoundary Y n (endMap H r (n + 1) c) = endMap H r n (chainBoundary X n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single σ a =>
      have hsa : Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod 2) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsa]
      simp only [map_smul]
      congr 1
      rw [endMap_single, chainBoundary_single, chainBoundary_single]
      simp only [boundaryBasis, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [endMap_single, face_endSimplex]

/-! ## §13. Homotopy invariance of singular ℤ/2 homology -/

/-- The endpoint map of a homotopy sends cycles to cycles (immediate from `chainBoundary_endMap`). -/
theorem endMap_mem_cycles {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y)) (r : unitInterval)
    (z : SingularChain X (n + 1)) (hz : chainBoundary X n z = 0) :
    chainBoundary Y n (endMap H r (n + 1) z) = 0 := by
  rw [chainBoundary_endMap, hz, map_zero]

/-- **Homotopy invariance, chain level**: for a cycle `z` the two endpoints `g_#(z)` and `f_#(z)` of
a homotopy `H` differ by a boundary, `g_#(z) + f_#(z) = ∂(P z) ∈ im ∂`. The two endpoints therefore
represent the same homology class — homotopic maps induce equal maps on `Hₙ(·; ℤ/2)`. -/
theorem endMap_add_mem_boundaries {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (z : SingularChain X (n + 1)) (hz : chainBoundary X n z = 0) :
    endMap H 1 (n + 1) z + endMap H 0 (n + 1) z ∈ boundaries Y (n + 1) := by
  rw [← prism_chainHomotopy H z, hz, map_zero, add_zero]
  exact ⟨prismOp H (n + 1) z, rfl⟩
