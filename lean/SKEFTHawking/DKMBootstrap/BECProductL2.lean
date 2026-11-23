import SKEFTHawking.DKMBootstrap.BECBosonicSectors
import SKEFTHawking.DKMBootstrap.BECPhysicalWallModes
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite products in physical configuration L²

Coordinate products are constructed from actual interval L² classes in the unnormalized
`configurationMeasure`. Their representatives agree with the pointwise product almost everywhere.
The inner product and norm factor exactly, including the empty product at particle number zero.
Multilinearity and the norm identity give a continuous coordinate product. Measurable rectangle
indicators and measurable-class induction prove density of pure products. Continuity then transfers
dense one-coordinate spans to dense product spans, giving a physical wall-product Hilbert basis.
Bosonic permutation averaging and higher-sector kinetic operators are separate constructions.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

namespace SKEFTHawking.DKMBootstrap.BECProductL2

open BECBosonicSectors

variable {l r : ℝ} {N : ℕ}

/-- One coordinate uses exactly the existing physical interval measure. -/
abbrev IntervalL2 (l r : ℝ) := Lp ℂ 2 (intervalMeasure l r)

/-- Pointwise product of the chosen coercions; the construction below is an L² class. -/
def productRepresentative (f : Fin N → IntervalL2 l r) (x : Configuration N) : ℂ :=
  ∏ i, f i (x i)

/-- Square integrability follows from Fubini applied to the coordinate squared norms. -/
theorem productRepresentative_memLp (f : Fin N → IntervalL2 l r) :
    MemLp (productRepresentative f) 2 (configurationMeasure l r N) := by
  have hm : AEStronglyMeasurable (productRepresentative f) (configurationMeasure l r N) :=
    Finset.aestronglyMeasurable_fun_prod Finset.univ (fun i _ ↦
      (Lp.aestronglyMeasurable (f i)).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun _ : Fin N ↦ intervalMeasure l r) i))
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := Integrable.fintype_prod_dep (μ := fun _ : Fin N ↦ intervalMeasure l r)
    (fun i ↦ (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (f i))).mp
      (Lp.memLp (f i)))
  simpa only [productRepresentative, configurationMeasure, norm_prod, Finset.prod_pow] using hi

/-- Genuine separable product in the actual physical configuration Hilbert space. -/
def product (f : Fin N → IntervalL2 l r) : ConfigurationHilbert l r N :=
  (productRepresentative_memLp f).toLp (productRepresentative f)

/-- The product formula is asserted almost everywhere, as required for Lp classes. -/
theorem product_ae (f : Fin N → IntervalL2 l r) :
    (product f : Configuration N → ℂ) =ᵐ[configurationMeasure l r N]
      productRepresentative f :=
  (productRepresentative_memLp f).coeFn_toLp

/-- Coordinate representative changes transport simultaneously through the product measure. -/
theorem product_ae_of_coordinate_ae (f : Fin N → IntervalL2 l r)
    (g : Fin N → ℝ → ℂ) (h : ∀ i, (f i : ℝ → ℂ) =ᵐ[intervalMeasure l r] g i) :
    (product f : Configuration N → ℂ) =ᵐ[configurationMeasure l r N]
      (fun x ↦ ∏ i, g i (x i)) :=
  (product_ae f).trans ((Measure.ae_eq_pi h).mono fun _ hx ↦
    congrArg (fun v : Fin N → ℂ ↦ ∏ i, v i) hx)

/-- Exact Fubini factorization on physical volume, with no probability normalization. -/
theorem product_inner (f g : Fin N → IntervalL2 l r) :
    inner ℂ (product f) (product g) = ∏ i, inner ℂ (f i) (g i) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, ∏ i, inner ℂ (f i (x i)) (g i (x i))
        ∂(configurationMeasure l r N) := by
      apply integral_congr_ae
      filter_upwards [product_ae f, product_ae g] with x hf hg
      rw [hf, hg]
      simp only [productRepresentative, RCLike.inner_apply', map_prod,
        Finset.prod_mul_distrib]
    _ = _ := by
      change (∫ x : Fin N → ℝ, ∏ i, inner ℂ (f i (x i)) (g i (x i))
        ∂(Measure.pi (fun _ ↦ intervalMeasure l r))) = _
      exact (integral_fintype_prod_eq_prod (fun i t ↦ inner ℂ (f i t) (g i t))).trans
        (Finset.prod_congr rfl (fun i _ ↦ (L2.inner_def (f i) (g i)).symm))

/-- Exact multiplicativity of the L² norm, also at particle number zero. -/
theorem product_norm (f : Fin N → IntervalL2 l r) :
    ‖product f‖ = ∏ i, ‖f i‖ := by
  have h := product_inner f f
  simp only [inner_self_eq_norm_sq_to_K] at h
  rw [Finset.prod_pow] at h
  have hs : ‖product f‖ ^ 2 = (∏ i, ‖f i‖) ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg (fun i _ ↦ norm_nonneg (f i)))).mp hs

/-- Evaluation of an updated coordinate is an updated family of scalar values. -/
private theorem eval_update [DecidableEq (Fin N)] (f : Fin N → IntervalL2 l r) (i : Fin N)
    (v : IntervalL2 l r) (x : Configuration N) :
    (fun j ↦ Function.update f i v j (x j)) =
      Function.update (fun j ↦ f j (x j)) i (v (x i)) := by
  classical
  funext j
  by_cases h : j = i <;> simp [h]

/-- Addition in one L² coordinate gives addition of the configuration products. -/
theorem product_update_add [DecidableEq (Fin N)] (f : Fin N → IntervalL2 l r) (i : Fin N)
    (u v : IntervalL2 l r) :
    product (Function.update f i (u + v)) =
      product (Function.update f i u) + product (Function.update f i v) := by
  apply Lp.ext
  have ha := (Measure.quasiMeasurePreserving_eval (fun _ : Fin N ↦ intervalMeasure l r) i).ae_eq
    (Lp.coeFn_add u v)
  filter_upwards [product_ae (Function.update f i (u + v)),
    product_ae (Function.update f i u), product_ae (Function.update f i v),
    Lp.coeFn_add (product (Function.update f i u)) (product (Function.update f i v)),
    ha] with x hsum hu hv hadd huv
  simp only [Pi.add_apply, Function.comp_apply, Function.eval] at hadd huv
  rw [hsum, hadd, hu, hv]
  unfold productRepresentative
  change (MultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ)
    (fun j ↦ Function.update f i (u + v) j (x j)) = _
  rw [eval_update, huv]
  exact ((MultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ).map_update_add
    (fun j ↦ f j (x j)) i (u (x i)) (v (x i))).trans (by
      simp only [MultilinearMap.mkPiAlgebra_apply, ← eval_update])

/-- Complex scalar multiplication in one coordinate respects the configuration product. -/
theorem product_update_smul [DecidableEq (Fin N)] (f : Fin N → IntervalL2 l r) (i : Fin N)
    (c : ℂ) (u : IntervalL2 l r) :
    product (Function.update f i (c • u)) = c • product (Function.update f i u) := by
  apply Lp.ext
  have ha := (Measure.quasiMeasurePreserving_eval (fun _ : Fin N ↦ intervalMeasure l r) i).ae_eq
    (Lp.coeFn_smul c u)
  filter_upwards [product_ae (Function.update f i (c • u)),
    product_ae (Function.update f i u), Lp.coeFn_smul c (product (Function.update f i u)),
    ha] with x hcu hu hsmul hcu'
  simp only [Pi.smul_apply, Function.comp_apply, Function.eval] at hsmul hcu'
  rw [hcu, hsmul, hu]
  unfold productRepresentative
  change (MultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ)
    (fun j ↦ Function.update f i (c • u) j (x j)) = _
  rw [eval_update, hcu']
  exact ((MultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ).map_update_smul
    (fun j ↦ f j (x j)) i c (u (x i))).trans (by
      simp only [MultilinearMap.mkPiAlgebra_apply, ← eval_update])

/-- Algebraic multilinearity of the actual L²-class construction. -/
def productMultilinear (l r : ℝ) (N : ℕ) :
    MultilinearMap ℂ (fun _ : Fin N ↦ IntervalL2 l r) (ConfigurationHilbert l r N) where
  toFun := product
  map_update_add' f i u v := by simpa using product_update_add f i u v
  map_update_smul' f i c u := by simpa using product_update_smul f i c u

/-- Continuous coordinate product, with the exact multiplicative norm bound. -/
def productContinuousMultilinear (l r : ℝ) (N : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin N ↦ IntervalL2 l r)
      (ConfigurationHilbert l r N) :=
  (productMultilinear l r N).mkContinuous 1 (fun f ↦ by
    change ‖product f‖ ≤ 1 * ∏ i, ‖f i‖
    rw [product_norm, one_mul])

/-- Physical interval indicator vectors used to test measurable configuration rectangles. -/
def rectangleCoordinates (s : Fin N → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
    Fin N → IntervalL2 l r :=
  fun i ↦ indicatorConstLp 2 (hs i) (measure_ne_top (intervalMeasure l r) (s i)) (1 : ℂ)

/-- A pointwise product of coordinate indicators is the indicator of the actual rectangle. -/
private theorem indicator_product (s : Fin N → Set ℝ) (x : Configuration N) :
    (∏ i, (s i).indicator (fun _ ↦ (1 : ℂ)) (x i)) =
      (Set.univ.pi s).indicator (fun _ ↦ (1 : ℂ)) x := by
  classical
  by_cases hx : ∀ i, x i ∈ s i
  · have hmem : x ∈ Set.univ.pi s := fun i _ ↦ hx i
    simp only [Set.indicator_of_mem hmem]
    exact Finset.prod_eq_one (fun i _ ↦ Set.indicator_of_mem (hx i) _)
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hnot : x ∉ Set.univ.pi s := fun h ↦ hi (h i (Set.mem_univ i))
    rw [Set.indicator_of_notMem hnot]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

/-- Measurable rectangles are genuine products of coordinate L² indicators. -/
theorem product_rectangle_ae (s : Fin N → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) :
    (product (rectangleCoordinates (l := l) (r := r) s hs) : Configuration N → ℂ)
      =ᵐ[configurationMeasure l r N] (Set.univ.pi s).indicator (fun _ ↦ (1 : ℂ)) := by
  have h := product_ae_of_coordinate_ae (rectangleCoordinates (l := l) (r := r) s hs)
    (fun i ↦ (s i).indicator (fun _ ↦ (1 : ℂ)))
    (fun _ ↦ indicatorConstLp_coeFn)
  exact h.trans (Filter.Eventually.of_forall (indicator_product s))

/-- Orthogonality to a rectangle product is precisely its set-integral test. -/
theorem rectangle_inner (s : Fin N → Set ℝ) (hs : ∀ i, MeasurableSet (s i))
    (u : ConfigurationHilbert l r N) :
    inner ℂ (product (rectangleCoordinates s hs)) u =
      ∫ x in Set.univ.pi s, u x ∂(configurationMeasure l r N) := by
  rw [L2.inner_def, ← integral_indicator (MeasurableSet.univ_pi hs)]
  apply integral_congr_ae
  filter_upwards [product_rectangle_ae (l := l) (r := r) s hs] with x hx
  rw [hx]
  by_cases h : x ∈ Set.univ.pi s <;> simp [Set.indicator, h]

/-- Rectangle tests force an L² vector to vanish, using finite physical volume and
measurable-class induction. -/
theorem eq_zero_of_rectangle_integrals (u : ConfigurationHilbert l r N)
    (hrect : ∀ (s : Fin N → Set ℝ), (∀ i, MeasurableSet (s i)) →
      ∫ x in Set.univ.pi s, u x ∂(configurationMeasure l r N) = 0) : u = 0 := by
  letI : IsFiniteMeasure (configurationMeasure l r N) := by
    unfold configurationMeasure
    infer_instance
  have hu : Integrable (u : Configuration N → ℂ) (configurationMeasure l r N) :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp u)
  have htotal : ∫ x, u x ∂(configurationMeasure l r N) = 0 := by
    simpa using hrect (fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ)
  have hall : ∀ t : Set (Configuration N), MeasurableSet t →
      ∫ x in t, u x ∂(configurationMeasure l r N) = 0 := by
    apply MeasurableSpace.induction_on_inter
      (C := fun t _ ↦ ∫ x in t, u x ∂(configurationMeasure l r N) = 0)
      generateFrom_pi.symm isPiSystem_pi
    · simp
    · rintro _ ⟨s, hs, rfl⟩
      exact hrect s (fun i ↦ hs i (Set.mem_univ i))
    · intro t ht hi
      rw [setIntegral_compl ht hu, htotal, hi, sub_self]
    · intro t hd ht hi
      rw [integral_iUnion ht hd hu.integrableOn]
      simp only [hi, tsum_zero]
  apply Lp.ext
  exact (hu.ae_eq_zero_of_forall_setIntegral_eq_zero (fun t ht _ ↦ hall t ht)).trans
    (Lp.coeFn_zero ℂ 2 (configurationMeasure l r N)).symm

/-- Pure coordinate products span a dense subspace of the actual configuration L². -/
theorem product_span_dense (l r : ℝ) (N : ℕ) :
    (Submodule.span ℂ (Set.range (product (l := l) (r := r) (N := N)))).topologicalClosure
      = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  apply eq_zero_of_rectangle_integrals u
  intro s hs
  rw [← rectangle_inner s hs u]
  exact (Submodule.mem_orthogonal _ u).mp hu _
    (Submodule.subset_span (Set.mem_range_self (rectangleCoordinates s hs)))

section Families

variable {ι : Fin N → Type*} (v : (i : Fin N) → ι i → IntervalL2 l r)

/-- Products of a specified family in each physical coordinate. -/
def familyProduct (n : (i : Fin N) → ι i) : ConfigurationHilbert l r N :=
  product (fun i ↦ v i (n i))

/-- Finite coordinate linear combinations expand to finite linear combinations of products. -/
theorem product_mem_family_span (f : Fin N → IntervalL2 l r)
    (hf : ∀ i, f i ∈ Submodule.span ℂ (Set.range (v i))) :
    product f ∈ Submodule.span ℂ (Set.range (familyProduct v)) := by
  classical
  have hrep : ∀ i, ∃ c : ι i →₀ ℂ, (∑ j ∈ c.support, c j • v i j) = f i := by
    intro i
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp (hf i)
  choose c hc using hrep
  have he : f = fun i ↦ ∑ j ∈ (c i).support, c i j • v i j :=
    funext (fun i ↦ (hc i).symm)
  rw [he]
  change (productMultilinear l r N) (fun i ↦ ∑ j ∈ (c i).support, c i j • v i j) ∈ _
  rw [(productMultilinear l r N).map_sum_finset]
  apply Submodule.sum_mem
  intro n _
  rw [(productMultilinear l r N).map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self n))

/-- Dense coordinate spans imply a dense product span in actual configuration L². -/
theorem familyProduct_dense
    (hd : ∀ i, (Submodule.span ℂ (Set.range (v i))).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (familyProduct v))).topologicalClosure = ⊤ := by
  let S := Submodule.span ℂ (Set.range (familyProduct v))
  let C := S.topologicalClosure
  have hclosed : IsClosed (product (l := l) (r := r) (N := N) ⁻¹'
      (C : Set (ConfigurationHilbert l r N))) :=
    S.isClosed_topologicalClosure.preimage (productContinuousMultilinear l r N).cont
  have hsub : Set.univ.pi (fun i ↦
      (Submodule.span ℂ (Set.range (v i)) : Set (IntervalL2 l r))) ⊆
      product ⁻¹' (C : Set (ConfigurationHilbert l r N)) := by
    intro f hf
    exact S.le_topologicalClosure (product_mem_family_span v f
      (fun i ↦ hf i (Set.mem_univ i)))
  have hpi := dense_pi Set.univ (fun i _ ↦
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (hd i))
  have hall : ∀ f : Fin N → IntervalL2 l r, product f ∈ C := by
    intro f
    apply closure_minimal hsub hclosed
    rw [hpi.closure_eq]
    exact Set.mem_univ f
  have hspan : Submodule.span ℂ (Set.range (product (l := l) (r := r) (N := N))) ≤ C :=
    Submodule.span_le.mpr (by rintro _ ⟨f, rfl⟩; exact hall f)
  have hfull := Submodule.topologicalClosure_minimal _ hspan S.isClosed_topologicalClosure
  rw [product_span_dense] at hfull
  exact top_unique hfull

/-- Products of coordinate orthonormal families are orthonormal on physical product volume. -/
theorem familyProduct_orthonormal (hv : ∀ i, Orthonormal ℂ (v i)) :
    Orthonormal ℂ (familyProduct v) := by
  classical
  rw [orthonormal_iff_ite]
  intro n m
  change inner ℂ (product (fun i ↦ v i (n i))) (product (fun i ↦ v i (m i))) = _
  rw [product_inner]
  by_cases h : n = m
  · subst m
    simp only [orthonormal_iff_ite.mp (hv _), ite_true, Finset.prod_const_one]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      rw [orthonormal_iff_ite.mp (hv i), if_neg hi])

end Families

section PhysicalWallModes

open BECPhysicalWallModes

variable (T : ℝ) [Fact (0 < T)] (odd : Bool) (N : ℕ)

/-- Nonredundant physical wall products; the even zero coordinate mode is retained. -/
def wallProduct (n : Fin N → Index odd) : ConfigurationHilbert 0 (T / 2) N :=
  familyProduct (fun _ : Fin N ↦ wallMode T odd) n

/-- Physical wall products are orthonormal, including the unique vacuum product. -/
theorem wallProduct_orthonormal : Orthonormal ℂ (wallProduct T odd N) :=
  familyProduct_orthonormal _ (fun _ ↦ wallMode_orthonormal T odd)

/-- Physical wall products have dense span, derived from the actual one-coordinate wall bases. -/
theorem wallProduct_dense :
    (Submodule.span ℂ (Set.range (wallProduct T odd N))).topologicalClosure = ⊤ :=
  familyProduct_dense _ (fun _ ↦ wallMode_dense T odd)

/-- Hilbert basis of the full configuration space before bosonic averaging. -/
def wallProductBasis : HilbertBasis (Fin N → Index odd) ℂ (ConfigurationHilbert 0 (T / 2) N) :=
  HilbertBasis.mk (wallProduct_orthonormal T odd N) (wallProduct_dense T odd N).ge

/-- The concrete continuous wall representatives give the configuration product
almost everywhere. -/
theorem wallProduct_ae (n : Fin N → Index odd) :
    (wallProduct T odd N n : Configuration N → ℂ) =ᵐ[configurationMeasure 0 (T / 2) N]
      (fun x ↦ ∏ i, wallRepresentative T odd (n i) (x i)) :=
  product_ae_of_coordinate_ae _ _ (fun i ↦ wallMode_ae T odd (n i))

end PhysicalWallModes

end SKEFTHawking.DKMBootstrap.BECProductL2
