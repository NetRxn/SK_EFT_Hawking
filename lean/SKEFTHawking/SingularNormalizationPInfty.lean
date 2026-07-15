import Mathlib
import SKEFTHawking.SingularPrismProjectionNull

/-!
# Phase 5q.H Track 2 — THE NORMALIZATION DISCHARGE via the Dold–Kan `PInfty` normalization

Scratch skeleton; being built brick by brick.
-/

open CategoryTheory Opposite Simplicial
open AlgebraicTopology AlgebraicTopology.DoldKan
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularPrism SKEFTHawking.SingularExcisionPushforward
open SKEFTHawking.SingularPrismProjectionNull SKEFTHawking.SingularCapCrossProjection

namespace SKEFTHawking.SingularNormalizationPInfty

variable {M : TopCat}

/-- The free `ℤ/2`-simplicial module on the singular simplicial set of `M`. -/
noncomputable def singularSMod (M : TopCat) : SimplicialObject (ModuleCat (ZMod 2)) :=
  TopCat.toSSet.obj M ⋙ ModuleCat.free (ZMod 2)

/-- Carrier check: an `n`-chain viewed in the alternating-face-map complex level. -/
example (n : ℕ) (c : SingularChain M n) :
    ((AlternatingFaceMapComplex.obj (singularSMod M)).X n : Type) := c

/-- `(singularSMod M).δ i` acts on a basis simplex as the face map. -/
theorem sδ_single {n : ℕ} (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj M).obj (op (SimplexCategory.mk (n + 1)))) :
    (singularSMod M).δ i (Finsupp.single σ (1 : ZMod 2)) = Finsupp.single (face i σ) 1 :=
  ModuleCat.free_map_apply _ σ

/-- Over a `ℤ/2`-module the `(-1)^i` signs collapse: `(-1)^i • v = v`. -/
theorem neg_one_pow_zsmul {N : Type*} [AddCommGroup N] [Module (ZMod 2) N] (i : ℕ) (v : N) :
    ((-1 : ℤ) ^ i) • v = v := by
  rcases Nat.even_or_odd i with h | h
  · rw [h.neg_one_pow, one_zsmul]
  · rw [h.neg_one_pow, neg_one_zsmul, neg_eq_iff_add_eq_zero, ZModModule.add_self]

/-- **The Dold–Kan differential matches `chainBoundary` on a basis simplex** (`ℤ/2`: the alternating
signs collapse; each `δᵢ` acts as the singular face). -/
theorem dMatch_single {n : ℕ}
    (σ : (TopCat.toSSet.obj M).obj (op (SimplexCategory.mk (n + 1)))) :
    (AlternatingFaceMapComplex.obj (singularSMod M)).d (n + 1) n (Finsupp.single σ (1 : ZMod 2))
      = chainBoundary M n (Finsupp.single σ 1) := by
  rw [AlternatingFaceMapComplex.obj_d_eq, chainBoundary_single, boundaryBasis]
  simp only [AlternatingFaceMapComplex.obj_X, Int.reduceNeg, neg_one_pow_zsmul, ModuleCat.hom_sum]
  exact (LinearMap.sum_apply Finset.univ (fun i => ModuleCat.Hom.hom ((singularSMod M).δ i))
    (Finsupp.single σ 1)).trans (Finset.sum_congr rfl (fun i _ => sδ_single i σ))

/-- **The Dold–Kan differential IS `chainBoundary`** as a linear map (`Finsupp.lhom_ext` off `single`). -/
theorem dMatch_hom {n : ℕ} :
    ModuleCat.Hom.hom ((AlternatingFaceMapComplex.obj (singularSMod M)).d (n + 1) n)
      = chainBoundary M n := by
  apply Finsupp.lhom_ext
  intro σ b
  rw [show (Finsupp.single σ b : SingularChain M (n + 1)) = b • Finsupp.single σ 1 by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, map_smul]
  exact congrArg (b • ·) (dMatch_single σ)

/-- **The Dold–Kan differential is `chainBoundary`** (applied form). -/
theorem dMatch {n : ℕ} (c : SingularChain M (n + 1)) :
    (AlternatingFaceMapComplex.obj (singularSMod M)).d (n + 1) n c = chainBoundary M n c :=
  DFunLike.congr_fun dMatch_hom c

/-! ## §2. The projection prism is a degeneracy; `PInfty` kills it -/

/-- `stdSimplex.map` of a function is the affine simplex on the image vertices. -/
theorem stdSimplex_map_eq_affineSimplexStd {a b : ℕ} (f : Fin (a + 1) → Fin (b + 1)) :
    (⟨_root_.stdSimplex.map f, _root_.stdSimplex.continuous_map f⟩ :
        C(stdSimplex ℝ (Fin (a + 1)), stdSimplex ℝ (Fin (b + 1))))
      = affineSimplexStd (fun k => _root_.stdSimplex.vertex (f k)) := by
  ext t k
  show ((_root_.stdSimplex.map f t : stdSimplex ℝ (Fin (b + 1))) : Fin (b + 1) → ℝ) k
    = ((affineSimplexStd (fun k => _root_.stdSimplex.vertex (f k)) t :
        stdSimplex ℝ (Fin (b + 1))) : Fin (b + 1) → ℝ) k
  rw [_root_.stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, affineSimplexStd_coe_apply,
    Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [_root_.stdSimplex.vertex_coe, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : f i = k
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg (fun hk : k = f i => h hk.symm), mul_zero]

/-- **`prismAlpha i` is the affine realization of the degeneracy `σ i`.** -/
theorem prismAlpha_eq_map_σ {n : ℕ} (i : Fin (n + 1)) :
    prismAlpha i
      = (⟨_root_.stdSimplex.map (SimplexCategory.σ i),
          _root_.stdSimplex.continuous_map (SimplexCategory.σ i)⟩ :
        C(stdSimplex ℝ (Fin (n + 1 + 1)), stdSimplex ℝ (Fin (n + 1)))) := by
  refine Eq.trans ?_
    (stdSimplex_map_eq_affineSimplexStd (⇑(SimplexCategory.σ i) : Fin (n + 1 + 1) → Fin (n + 1))).symm
  rfl

/-- **The projection prism simplex is exactly the `i`-th degeneracy of `σ`.** Since `projHom` collapses
the interval, `prismSimplex projHom σ i = σ ∘ (affine σ i) = (toSSet).map (σ i).op σ`. -/
theorem prismSimplex_projHom_eq_degen {n : ℕ}
    (σ : (TopCat.toSSet.obj M).obj (op (SimplexCategory.mk n))) (i : Fin (n + 1)) :
    prismSimplex (projHom M) σ i = (TopCat.toSSet.obj M).map (SimplexCategory.σ i).op σ := by
  apply (M.toSSetObjEquiv (op (SimplexCategory.mk (n + 1)))).injective
  rw [prismSimplex, Equiv.apply_symm_apply]
  have hL : (projHom M).comp
        ((((M.toSSetObjEquiv (op (SimplexCategory.mk n))) σ).comp (prismAlpha i)).prodMk
          (prismBeta i))
      = ((M.toSSetObjEquiv (op (SimplexCategory.mk n))) σ).comp (prismAlpha i) :=
    ContinuousMap.ext fun a => rfl
  refine hL.trans ?_
  rw [prismAlpha_eq_map_σ]
  rfl

/-- Mathlib's `PInfty` at level `n`, as a plain linear endomorphism of `SingularChain M n`. -/
noncomputable def pinftyChain (n : ℕ) : SingularChain M n →ₗ[ZMod 2] SingularChain M n :=
  ModuleCat.Hom.hom ((PInfty (X := singularSMod M)).f n)

/-- **`PInfty` kills each projection-prism simplex** (it is a degeneracy `σᵢ`, and
`σ_comp_PInfty`). -/
theorem pinf_single_prismSimplex {n : ℕ}
    (σ : (TopCat.toSSet.obj M).obj (op (SimplexCategory.mk (n + 1)))) (i : Fin (n + 2)) :
    pinftyChain (n + 2) (Finsupp.single (prismSimplex (projHom M) σ i) (1 : ZMod 2)) = 0 := by
  show (PInfty (X := singularSMod M)).f (n + 2)
      (Finsupp.single (prismSimplex (projHom M) σ i) 1) = 0
  rw [prismSimplex_projHom_eq_degen,
    show Finsupp.single ((TopCat.toSSet.obj M).map (SimplexCategory.σ i).op σ) (1 : ZMod 2)
      = (singularSMod M).σ i (Finsupp.single σ 1) from (ModuleCat.free_map_apply _ σ).symm]
  have hc := ModuleCat.comp_apply ((singularSMod M).σ i) ((PInfty (X := singularSMod M)).f (n + 2))
    (Finsupp.single σ (1 : ZMod 2))
  refine hc.symm.trans ?_
  rw [show (singularSMod M).σ i ≫ (PInfty (X := singularSMod M)).f (n + 2) = 0 from
    σ_comp_PInfty (singularSMod M) i]
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply]

/-- **`PInfty` kills the whole projection prism** `prismOp projHom w` (a sum of degeneracies). -/
theorem pinf_kills_prism {n : ℕ} (w : SingularChain M (n + 1)) :
    pinftyChain (n + 2) (prismOp (projHom M) (n + 1) w) = 0 := by
  induction w using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | single σ x =>
      rw [prismOp_single, prismBasis]
      simp only [map_smul, map_sum]
      rw [Finset.sum_eq_zero fun i _ => pinf_single_prismSimplex σ i, smul_zero]

/-! ## §3. THE NORMALIZATION DISCHARGE -/

variable (M) in
/-- `K.d` at level `m`, as a plain linear map `SingularChain M (m+1) → SingularChain M m`. -/
noncomputable def kdL (m : ℕ) : SingularChain M (m + 1) →ₗ[ZMod 2] SingularChain M m :=
  ModuleCat.Hom.hom ((AlternatingFaceMapComplex.obj (singularSMod M)).d (m + 1) m)

/-- `kdL` is `chainBoundary` (the differential match, packaged for the clean linear maps). -/
theorem kdL_eq {m : ℕ} (c : SingularChain M (m + 1)) : kdL M m c = chainBoundary M m c := dMatch c

variable (M) in
/-- The `homotopyPInftyToId` homotopy component `hom i j`, as a plain linear map. -/
noncomputable def htpHom (i j : ℕ) : SingularChain M i →ₗ[ZMod 2] SingularChain M j :=
  ModuleCat.Hom.hom ((homotopyPInftyToId (X := singularSMod M)).hom i j)

/-- **`PrismProjKillsHomology` holds for every space.** For a cycle `w`, `prismOp projHom w` is a
cycle (banked) made of degeneracies (killed by `PInfty`), so by Mathlib's `homotopyPInftyToId`
(`PInfty ≃ 𝟙`) it is a boundary: `w' = PInfty w' + ∂(hom w') + hom(∂w')`, and here `PInfty w' = 0`,
`∂w' = 0`, leaving `w' = ∂(hom w')`. -/
theorem prismProjKillsHomology_holds (M : TopCat) : PrismProjKillsHomology M := by
  intro n w hw
  have hcyc : chainBoundary M (n + 1) (prismOp (projHom M) (n + 1) w) = 0 :=
    chainBoundary_prismOp_projHom w hw
  -- The `PInfty ≃ 𝟙` homotopy relation at level `n+2`, packaged as clean linear maps.
  have hcomm := (homotopyPInftyToId (X := singularSMod M)).comm (n + 2)
  rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl),
      prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 3) (n + 2) from rfl)] at hcomm
  have hcomm_hom :
      pinftyChain (n + 2) = htpHom M (n + 1) (n + 2) ∘ₗ kdL M (n + 1)
        + kdL M (n + 2) ∘ₗ htpHom M (n + 2) (n + 3) + LinearMap.id := by
    rw [pinftyChain, hcomm]
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, HomologicalComplex.id_f, ModuleCat.hom_id]
    rfl
  refine ⟨htpHom M (n + 2) (n + 3) (prismOp (projHom M) (n + 1) w), ?_⟩
  -- Evaluate the clean relation at the prism.
  have hkey := DFunLike.congr_fun hcomm_hom (prismOp (projHom M) (n + 1) w)
  rw [pinf_kills_prism w] at hkey
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_coe, id_eq,
    kdL_eq, hcyc, map_zero, zero_add] at hkey
  -- `hkey : 0 = chainBoundary M (n+2) (htpHom … Pw) + Pw`, so the two are equal over `ℤ/2`.
  have hneg : -(prismOp (projHom M) (n + 1) w) = prismOp (projHom M) (n + 1) w :=
    neg_eq_of_add_eq_zero_left (ZModModule.add_self _)
  exact (eq_neg_of_add_eq_zero_left hkey.symm).trans hneg

end SKEFTHawking.SingularNormalizationPInfty
