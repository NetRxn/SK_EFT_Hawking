/-
# Phase 5q.F (w₂-foundation, brick 6c) — barycentric subdivision and excision (ℤ/2)

The excision engine for singular ℤ/2 homology: the **barycentric subdivision operator** `Sd` and the
natural **chain homotopy** `T` with `∂T + T∂ = 1 − Sd`, whose iterate `Sdᵐ` shrinks simplices into any
open cover (the small-simplices theorem) ⟹ excision `Hₙ(X,A) ≅ Hₙ(X∖Z, A∖Z)`. Needed to compute the
local homology `Hₙ(ℝⁿ, ℝⁿ∖0) ≅ ℤ/2` → the ℤ/2 fundamental class → Poincaré duality. Mathlib has none of
this (verified 2026-06-15: no subdivision/excision/sphere-homology), but has the convex/affine geometry
(`stdSimplex` convexity, convex combinations) the construction runs on.

This first sub-brick (c1) builds the **affine (linear) singular simplices** `[v₀,…,vₙ] : Δⁿ → V`
(`t ↦ ∑ tᵢ vᵢ`) and the **cone operator** foundation — the geometric atoms of the subdivision (Hatcher
§2.1). Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.SingularExcisionMod2

open CategoryTheory Opposite

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V]

/-- The **affine `n`-simplex** `[v₀, …, vₙ] : Δⁿ → V` on vertices `v : Fin (n+1) → V`: the convex-affine
map `t ↦ ∑ᵢ tᵢ • vᵢ` from the topological standard simplex `stdSimplex ℝ (Fin (n+1))`. The basic atom of
the barycentric subdivision. -/
noncomputable def affineSimplex {n : ℕ} (v : Fin (n + 1) → V) :
    C(stdSimplex ℝ (Fin (n + 1)), V) where
  toFun t := ∑ i, (t : Fin (n + 1) → ℝ) i • v i
  continuous_toFun := by
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact (continuous_apply i |>.comp continuous_subtype_val).smul continuous_const

@[simp] theorem affineSimplex_apply {n : ℕ} (v : Fin (n + 1) → V) (t : stdSimplex ℝ (Fin (n + 1))) :
    affineSimplex v t = ∑ i, (t : Fin (n + 1) → ℝ) i • v i := rfl

/-- The value of an affine simplex on a vertex `e_j` of `Δⁿ` is the corresponding vertex `v_j`
(`∑ᵢ δᵢⱼ vᵢ = v_j`). -/
theorem affineSimplex_vertex {n : ℕ} (v : Fin (n + 1) → V) (j : Fin (n + 1)) :
    affineSimplex v ⟨Pi.single j 1, by
      constructor
      · intro i; rcases eq_or_ne i j with h | h
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      · simp⟩ = v j := by
  simp only [affineSimplex_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ## §2. The affine (linear) chain complex `LC(Y)` — the combinatorial subdivision layer

The barycentric subdivision algebra (recursive `Sd`, the cone, the chain homotopy `∂T+T∂=1−Sd`) is
cleanest on the **affine chain complex** `LC_n(Y)` of a set `Y`: the free `ℤ/2`-module on vertex-tuples
`Fin (n+1) → Y` (an affine `n`-simplex is its tuple of vertices). The geometric realization
`affineSimplex` (§1) and the pushforward to singular chains come later; here we set up the boundary. -/

variable {Y : Type*}

/-- **Affine `n`-chains** `LC_n(Y)`: free `ℤ/2`-module on vertex-tuples `Fin (n+1) → Y`. -/
abbrev LinChain (Y : Type*) (n : ℕ) : Type _ := (Fin (n + 1) → Y) →₀ ZMod 2

/-- The affine boundary of a *single* vertex-tuple `v` (an affine `(n+1)`-simplex): `∂[v] = ∑ᵢ [∂ᵢv]`
over `ℤ/2`, where `∂ᵢv = v ∘ Fin.succAbove i` drops the `i`-th vertex. -/
noncomputable def linBoundaryBasis (n : ℕ) (v : Fin (n + 1 + 1) → Y) : LinChain Y n :=
  ∑ i : Fin (n + 2), Finsupp.single (v ∘ i.succAbove) 1

/-- The **affine boundary** `∂ : LC_{n+1}(Y) → LC_n(Y)`, the `ℤ/2`-linear extension of `[v] ↦ ∑ᵢ [∂ᵢv]`. -/
noncomputable def linBoundary (n : ℕ) : LinChain Y (n + 1) →ₗ[ZMod 2] LinChain Y n :=
  Finsupp.linearCombination (ZMod 2) (linBoundaryBasis n)

theorem linBoundary_single (n : ℕ) (v : Fin (n + 1 + 1) → Y) :
    linBoundary n (Finsupp.single v 1) = linBoundaryBasis n v := by
  rw [linBoundary, Finsupp.linearCombination_single, one_smul]

theorem linBoundary_single_smul (n : ℕ) (v : Fin (n + 1 + 1) → Y) (a : ZMod 2) :
    linBoundary n (Finsupp.single v a) = a • linBoundaryBasis n v := by
  rw [linBoundary, Finsupp.linearCombination_single]

/-- `∂²` on a single vertex-tuple `v` (an affine `(n+2)`-simplex) is the double sum
`∑ᵢ∑ⱼ [∂ⱼ∂ᵢv]`. -/
theorem linBoundary_linBoundary_single (n : ℕ) (v : Fin (n + 1 + 1 + 1) → Y) :
    linBoundary n (linBoundary (n + 1) (Finsupp.single v 1))
      = ∑ i : Fin (n + 3), ∑ j : Fin (n + 2),
          Finsupp.single ((v ∘ i.succAbove) ∘ j.succAbove) (1 : ZMod 2) := by
  rw [linBoundary_single, linBoundaryBasis, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [linBoundary_single, linBoundaryBasis]

/-- **`∂² = 0` on a single vertex-tuple** — the cosimplicial `Fin.succAbove` involution (the affine
analog of the singular `∂²=0`): the pairing `(i,j) ↦ (j.castSucc, i.pred)` / `(j.succ, i.castPred)`
identifies the double-sum terms in pairs (via `Fin.succAbove_succAbove_succAbove_predAbove`), so the sum
vanishes over `ℤ/2`. -/
theorem linBoundary_linBoundary_single_eq_zero (n : ℕ) (v : Fin (n + 1 + 1 + 1) → Y) :
    linBoundary n (linBoundary (n + 1) (Finsupp.single v 1)) = 0 := by
  rw [linBoundary_linBoundary_single]
  rw [← Fintype.sum_prod_type (f := fun p : Fin (n + 3) × Fin (n + 2) =>
    Finsupp.single ((v ∘ p.1.succAbove) ∘ p.2.succAbove) (1 : ZMod 2))]
  refine Finset.sum_involution
    (fun p _ => if h : p.2.castSucc < p.1
      then (p.2.castSucc, p.1.pred ((Fin.zero_le _).trans_lt h).ne')
      else (p.2.succ, p.1.castPred (by
        simp only [not_lt] at h
        rw [Fin.ne_iff_vne, Fin.val_last]; have := p.2.isLt
        rw [Fin.le_def, Fin.val_castSucc] at h; omega))) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ -
    simp only
    by_cases h : j.castSucc < i
    · rw [dif_pos h]
      have hne : i ≠ 0 := ((Fin.zero_le _).trans_lt h).ne'
      have hfin : ((v ∘ i.succAbove) ∘ j.succAbove)
          = ((v ∘ (j.castSucc).succAbove) ∘ (i.pred hne).succAbove) := by
        funext k
        simp only [Function.comp_apply]
        congr 1
        rw [← Fin.succAbove_succAbove_succAbove_predAbove i j k,
          Fin.succAbove_of_castSucc_lt i j h, Fin.predAbove_of_castSucc_lt j i h]
      rw [hfin]; exact ZModModule.add_self _
    · rw [dif_neg h]
      simp only [not_lt] at h
      have hne : i ≠ Fin.last (n + 1 + 1) := by
        rw [Fin.ne_iff_vne, Fin.val_last]; have := j.isLt
        rw [Fin.le_def, Fin.val_castSucc] at h; omega
      have hfin : ((v ∘ i.succAbove) ∘ j.succAbove)
          = ((v ∘ (j.succ).succAbove) ∘ (i.castPred hne).succAbove) := by
        funext k
        simp only [Function.comp_apply]
        congr 1
        rw [← Fin.succAbove_succAbove_succAbove_predAbove i j k,
          Fin.succAbove_of_le_castSucc i j h, Fin.predAbove_of_le_castSucc j i h]
      rw [hfin]; exact ZModModule.add_self _
  · rintro ⟨i, j⟩ - _
    by_cases h : j.castSucc < i
    · simp only [dif_pos h, ne_eq, Prod.mk.injEq]
      rintro ⟨hc, -⟩
      simp only [Fin.ext_iff, Fin.val_castSucc] at hc
      simp only [Fin.lt_def, Fin.val_castSucc] at h; omega
    · simp only [dif_neg h, ne_eq, Prod.mk.injEq]
      rintro ⟨hc, -⟩
      simp only [Fin.ext_iff, Fin.val_succ] at hc
      simp only [not_lt, Fin.le_def, Fin.val_castSucc] at h; omega
  · intro a _; exact Finset.mem_univ _
  · rintro ⟨i, j⟩ -
    by_cases h : j.castSucc < i
    · have hne : i ≠ 0 := ((Fin.zero_le _).trans_lt h).ne'
      have h2 : ¬ (i.pred hne).castSucc < j.castSucc := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_pred]
        simp only [Fin.lt_def, Fin.val_castSucc] at h; omega
      simp only [dif_pos h, dif_neg h2, Fin.succ_pred, Fin.castPred_castSucc]
    · have hle : i ≤ j.castSucc := not_lt.mp h
      have hne : i ≠ Fin.last (n + 1 + 1) := by
        simp only [Fin.ne_iff_vne, Fin.val_last]; have := j.isLt
        simp only [Fin.le_def, Fin.val_castSucc] at hle; omega
      have h2 : i < j.succ := by
        simp only [Fin.lt_def, Fin.val_succ]
        simp only [Fin.le_def, Fin.val_castSucc] at hle; omega
      simp only [dif_neg h, Fin.castSucc_castPred, Fin.pred_succ, dif_pos h2]

/-- **`∂² = 0`** on the affine chain complex (reduced to the single-tuple case by linearity). -/
theorem linBoundary_comp_linBoundary (n : ℕ) :
    (linBoundary n (Y := Y)).comp (linBoundary (n + 1)) = 0 := by
  refine Finsupp.lhom_ext (fun v b => ?_)
  have hsingle : (Finsupp.single v b) = b • Finsupp.single v 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [LinearMap.comp_apply, LinearMap.zero_apply, hsingle, map_smul, map_smul,
    linBoundary_linBoundary_single_eq_zero, smul_zero]

/-! ## §3. The cone operator `b · (-)` and its boundary formula

The cone `b · [v₀,…,vₙ] = [b, v₀, …, vₙ]` (prepend the apex `b`) is the contracting homotopy of an affine
simplex. Its boundary formula `∂(b·c) = c − b·(∂c)` (= `c + b·(∂c)` over ℤ/2, for `n ≥ 1`) is the engine
that makes the subdivision a chain map. -/

/-- The cone of a single affine simplex on apex `b`: `b·[v] = [b,v]` (prepend `b`). -/
noncomputable def coneBasis (b : Y) (n : ℕ) (v : Fin (n + 1) → Y) : LinChain Y (n + 1) :=
  Finsupp.single (Fin.cons b v) 1

/-- The **cone operator** `b · (-) : LC_n(Y) → LC_{n+1}(Y)`, the `ℤ/2`-linear extension of `[v] ↦ [b,v]`. -/
noncomputable def cone (b : Y) (n : ℕ) : LinChain Y n →ₗ[ZMod 2] LinChain Y (n + 1) :=
  Finsupp.linearCombination (ZMod 2) (coneBasis b n)

theorem cone_single (b : Y) (n : ℕ) (v : Fin (n + 1) → Y) :
    cone b n (Finsupp.single v 1) = Finsupp.single (Fin.cons b v) 1 := by
  rw [cone, Finsupp.linearCombination_single, one_smul, coneBasis]

theorem cone_single_smul (b : Y) (n : ℕ) (v : Fin (n + 1) → Y) (a : ZMod 2) :
    cone b n (Finsupp.single v a) = a • Finsupp.single (Fin.cons b v) 1 := by
  rw [cone, Finsupp.linearCombination_single, coneBasis]

/-- Dropping the apex of a cone recovers the original simplex: `(cons b v) ∘ ∂₀ = v`
(`∂₀ = (0).succAbove = Fin.succ`). -/
theorem cons_comp_zero_succAbove (b : Y) {n : ℕ} (v : Fin (n + 1) → Y) :
    (Fin.cons b v : Fin (n + 2) → Y) ∘ (0 : Fin (n + 2)).succAbove = v := by
  rw [Fin.succAbove_zero]
  funext k
  simp only [Function.comp_apply, Fin.cons_succ]

/-- Dropping a later vertex of a cone is the cone of dropping that vertex of the base:
`(cons b v) ∘ (j.succ).succAbove = cons b (v ∘ j.succAbove)`. -/
theorem cons_comp_succ_succAbove (b : Y) {n : ℕ} (v : Fin (n + 1) → Y) (j : Fin (n + 1)) :
    (Fin.cons b v : Fin (n + 2) → Y) ∘ (j.succ).succAbove = Fin.cons b (v ∘ j.succAbove) := by
  funext k
  refine Fin.cases ?_ ?_ k
  · rw [Function.comp_apply, Fin.succAbove_of_castSucc_lt _ _ (by
      rw [Fin.castSucc_zero]; exact Fin.succ_pos j), Fin.castSucc_zero, Fin.cons_zero, Fin.cons_zero]
  · intro m
    rw [Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ, Fin.cons_succ,
      Function.comp_apply]

/-- **The cone boundary formula** (`n ≥ 1`): `∂(b·[v]) = [v] + b·(∂[v])` over `ℤ/2`. The `∂₀` face
drops the apex (giving `[v]`); the later faces are the cone of `∂[v]`. -/
theorem linBoundary_coneBasis (b : Y) (n : ℕ) (v : Fin (n + 1 + 1) → Y) :
    linBoundary (n + 1) (coneBasis b (n + 1) v)
      = Finsupp.single v 1 + cone b n (linBoundary n (Finsupp.single v 1)) := by
  rw [coneBasis, linBoundary_single, linBoundaryBasis,
    Fin.sum_univ_succ (f := fun i => Finsupp.single ((Fin.cons b v) ∘ i.succAbove) (1 : ZMod 2)),
    cons_comp_zero_succAbove]
  congr 1
  rw [linBoundary_single, linBoundaryBasis, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cons_comp_succ_succAbove, cone_single]

/-- **The cone boundary formula on a general chain** (`n ≥ 1`): `∂(b·c) = c + b·(∂c)` over `ℤ/2`
(the linear extension of `linBoundary_coneBasis`). -/
theorem linBoundary_cone (b : Y) (n : ℕ) (c : LinChain Y (n + 1)) :
    linBoundary (n + 1) (cone b (n + 1) c) = c + cone b n (linBoundary n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, zero_add]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]; abel
  | single v a =>
    rw [cone_single_smul, map_smul,
      show Finsupp.single (Fin.cons b v) (1 : ZMod 2) = coneBasis b (n + 1) v from rfl,
      linBoundary_coneBasis, smul_add]
    congr 1
    · rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    · rw [← map_smul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]

/-! ## §4. The barycentric subdivision `Sd` (recursive)

`Sd[v₀,…,vₙ] = b_v · Sd(∂[v₀,…,vₙ])`, coning the subdivided boundary at the barycenter `b_v`. Needs a
real vector space `V` for the barycenter (the average of the vertices). -/

section Subdivision

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The **barycenter** of an affine simplex `[v₀,…,vₙ]`: the average `(n+1)⁻¹ ∑ᵢ vᵢ`. -/
noncomputable def barycenter {n : ℕ} (v : Fin (n + 1) → V) : V :=
  ((n : ℝ) + 1)⁻¹ • ∑ i, v i

/-- The **barycentric subdivision** `Sd : LC_n(V) → LC_n(V)`, recursive: `Sd[v] = b_v · Sd(∂[v])`
(in degree 0, `Sd = id`). -/
noncomputable def linSubdiv : (n : ℕ) → LinChain V n →ₗ[ZMod 2] LinChain V n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination (ZMod 2)
      (fun v => cone (barycenter v) n (linSubdiv n (linBoundary n (Finsupp.single v 1))))

theorem linSubdiv_zero (c : LinChain V 0) : linSubdiv 0 c = c := rfl

/-- The subdivision on a single simplex: `Sd[v] = b_v · Sd(∂[v])`. -/
theorem linSubdiv_single (n : ℕ) (v : Fin (n + 1 + 1) → V) :
    linSubdiv (n + 1) (Finsupp.single v 1)
      = cone (barycenter v) n (linSubdiv n (linBoundary n (Finsupp.single v 1))) := by
  rw [linSubdiv, Finsupp.linearCombination_single, one_smul]

end Subdivision

end SKEFTHawking.SingularExcisionMod2
