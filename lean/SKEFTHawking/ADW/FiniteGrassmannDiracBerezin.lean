import SKEFTHawking.ADW.FiniteGrassmannSourceAuxiliary
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-!
# Original finite Dirac matrix and Berezin coefficients

All matrix blocks below act on the original independent barred and unbarred
coordinates. Coincident periodic neighbours contribute additively.
-/
noncomputable section
open scoped BigOperators IsMulCommutative NNReal
open Matrix MeasureTheory
namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
open FiniteGrassmannCoframe FiniteGrassmannEvaluation GaussianGrassmannAuxiliary
open scoped SKEFTHawking.ADW.FiniteGrassmannEvaluation

abbrev Fermion (L : Torus) := Site L × Fin 4
abbrev DiracMatrix (L : Torus) := Matrix (Fermion L) (Fermion L) ℂ
abbrev Auxiliary (L : Torus) := Site L × Fin 4 × Fin 4

/-- The actual four signed quarter blocks, summed before any coincident anchors are identified. -/
def globalMatrix (L : Torus) (U : Links L) (h : Auxiliary L → ℂ) : DiracMatrix L :=
  fun p q ↦ ∑ a, h a * hopping L U a.1 a.2.1 a.2.2 p.1 q.1 p.2 q.2

/-- The barred/unbarred contraction has no conjugation of either independent generator. -/
def barMpsi (L : Torus) (M : DiracMatrix L) : Grassmann L :=
  ∑ y, ∑ z, bilinear L y z (fun i j ↦ M (y,i) (z,j))

/-- Ordinary matrix addition induces addition of the actual Grassmann bilinear. -/
def matrixBilinear (L : Torus) : DiracMatrix L →ₗ[ℂ] Grassmann L where
  toFun := barMpsi L
  map_add' A B := by
    simp only [barMpsi, bilinear, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [barMpsi, bilinear, Matrix.smul_apply, smul_eq_mul,
      mul_smul, Finset.smul_sum, RingHom.id_apply]

/-- Eq9, including all anchors and all coincident-neighbour additions. -/
theorem globalMatrix_eq9 (L : Torus) (U : Links L) (h : Auxiliary L → ℂ) :
    barMpsi L (globalMatrix L U h) =
      ∑ a, h a • coframe L U a.1 a.2.1 a.2.2 := by
  classical
  let B (y z : Site L) : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Grassmann L :=
    { toFun := bilinear L y z
      map_add' A B := by
        simp only [bilinear, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' c A := by
        simp only [bilinear, Matrix.smul_apply, smul_eq_mul, mul_smul,
          Finset.smul_sum, RingHom.id_apply] }
  have hm (y z : Site L) :
      (fun i j ↦ globalMatrix L U h (y,i) (z,j)) =
        ∑ a, h a • hopping L U a.1 a.2.1 a.2.2 y z := by
    ext i j
    simp only [globalMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  unfold barMpsi
  simp_rw [hm]
  change (∑ y, ∑ z, B y z (∑ a, h a • hopping L U a.1 a.2.1 a.2.2 y z)) = _
  simp only [map_sum, map_smul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ y, ∑ x, h a • bilinear L x y (hopping L U a.1 a.2.1 a.2.2 x y)) = _
  simp only [← Finset.smul_sum]
  rw [Finset.sum_comm, hopping_reconstructs_coframe]

/-- Literal local source word: barL1 barL2 psiL1 psiL2 barR1 barR2 psiR1 psiR2. -/
def localSourceOrder : Fin 8 ≃ (Fin 4 ⊕ Fin 4) :=
  Equiv.ofBijective ![Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inl 1,
    Sum.inr 2, Sum.inr 3, Sum.inl 2, Sum.inl 3] (by decide)

/-- Sites have a fixed finite enumeration; the eight local source generators stay consecutive. -/
def sourceIndex (L : Torus) : Gen L ≃ Fin (volume L * 8) :=
  (Equiv.prodCongr (Fintype.equivFin (Site L)) localSourceOrder.symm).trans finProdFinEquiv

def sourceBasis (L : Torus) : Module.Basis (Fin (volume L * 8)) ℂ (Coordinate L) :=
  (Pi.basisFun ℂ (Gen L)).reindex (sourceIndex L)

/-- Actual top coefficient of the exterior basis, independent of every matrix. -/
def berezin (L : Torus) : Grassmann L →ₗ[ℂ] ℂ :=
  (sourceBasis L).ExteriorAlgebra.coord Finset.univ

/-- Finite dimensionality gives continuity in C1's actual transported norm. -/
def berezinContinuous (L : Torus) : Grassmann L →L[ℂ] ℂ :=
  (berezin L).toContinuousLinearMap

theorem berezin_continuous (L : Torus) : Continuous (berezin L) :=
  (berezinContinuous L).continuous

/-- Normalization is fixed by the actual ordered exterior basis word. -/
theorem berezin_top (L : Torus) :
    berezin L ((sourceBasis L).ExteriorAlgebra Finset.univ) = 1 := by
  simp [berezin, Module.Basis.coord_apply]

/-- Berezin integration commutes with an actual Bochner integral after integrability. -/
theorem berezin_integral (L : Torus) {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → Grassmann L} (hf : Integrable f μ) :
    (∫ x, berezin L (f x) ∂μ) = berezin L (∫ x, f x ∂μ) :=
  (berezinContinuous L).integral_comp_comm hf

/-- Fixed-link C3 transport with the complete original product of site weights. -/
theorem berezin_C3 (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Site L → FiniteGrassmannSourceAuxiliary.Polynomial)
    (hS : ∀ x, (S x).constantCoeff = 0) :
    (∫ h : Auxiliary L → ℝ,
      berezin L (FiniteGrassmannSourceAuxiliary.uncurriedIntegrand L U σ S h)
      ∂gaussianMeasure (Auxiliary L) v) =
      berezin L (nilExp (4 * volume L)
        (∑ x, ((MvPolynomial.aeval (FiniteGrassmannSourceAuxiliary.localCoframe L U x)
          (S x) : bilinearAlgebra L) : Grassmann L))) := by
  rw [berezin_integral L
    (FiniteGrassmannSourceAuxiliary.uncurried_global_integrable L U σ hσ v hv S)]
  rw [FiniteGrassmannSourceAuxiliary.uncurried_global_eq7 L U σ hσ v hv S hS]

/-- The independent unbarred coordinate vector associated with an arbitrary matrix row. -/
def rowVector (L : Torus) (r : Fermion L → ℂ) : Coordinate L :=
  fun g ↦ match g.2 with
    | Sum.inl j => r (g.1,j)
    | Sum.inr _ => 0

/-- The actual even row factor, inside the same bilinear subalgebra. -/
def rowFactor (L : Torus) (p : Fermion L) :
    (Fermion L → ℂ) →ₗ[ℂ] bilinearAlgebra L where
  toFun r := ∑ q, r q • ⟨pair L (p.1,Sum.inr p.2) (q.1,Sum.inl q.2), pair_mem L _ _⟩
  map_add' r s := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c r := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem rowVector_expansion (L : Torus) (r : Fermion L → ℂ) :
    rowVector L r = ∑ q, r q • Pi.basisFun ℂ (Gen L) (q.1,Sum.inl q.2) := by
  classical
  ext ⟨x,g⟩
  rcases g with j | j <;>
    simp [rowVector, Finset.sum_apply, Fintype.sum_prod_type, Pi.basisFun_apply,
      Pi.single_apply, ite_and]

/-- A row factor is a product of two genuine odd vectors. -/
theorem rowFactor_image (L : Torus) (p : Fermion L) (r : Fermion L → ℂ) :
    (rowFactor L p r : Grassmann L) =
      barpsi L p.1 p.2 * ExteriorAlgebra.ι ℂ (rowVector L r) := by
  rw [rowVector_expansion]
  simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  simp [rowFactor, pair, theta, barpsi]

/-- Each row factor squares to zero without any invertibility condition. -/
theorem rowFactor_square (L : Torus) (p : Fermion L) (r : Fermion L → ℂ) :
    rowFactor L p r ^ 2 = 0 := by
  apply Subtype.ext
  change (rowFactor L p r : Grassmann L) ^ 2 = 0
  rw [rowFactor_image, pow_two]
  have hs := ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (Pi.basisFun ℂ (Gen L) (p.1,Sum.inr p.2))
    (rowVector L r)
  have hz := theta_square_zero L (p.1,Sum.inr p.2)
  change theta L (p.1,Sum.inr p.2) * theta L (p.1,Sum.inr p.2) = 0 at hz
  change theta L (p.1,Sum.inr p.2) * ExteriorAlgebra.ι ℂ (rowVector L r) +
    ExteriorAlgebra.ι ℂ (rowVector L r) * theta L (p.1,Sum.inr p.2) = 0 at hs
  change (theta L (p.1,Sum.inr p.2) * ExteriorAlgebra.ι ℂ (rowVector L r)) *
    (theta L (p.1,Sum.inr p.2) * ExteriorAlgebra.ι ℂ (rowVector L r)) = 0
  calc
    _ = theta L (p.1,Sum.inr p.2) *
        (ExteriorAlgebra.ι ℂ (rowVector L r) * theta L (p.1,Sum.inr p.2)) *
          ExteriorAlgebra.ι ℂ (rowVector L r) := by noncomm_ring
    _ = -(theta L (p.1,Sum.inr p.2) * theta L (p.1,Sum.inr p.2)) *
        (ExteriorAlgebra.ι ℂ (rowVector L r) * ExteriorAlgebra.ι ℂ (rowVector L r)) := by
      rw [eq_neg_of_add_eq_zero_right hs]
      noncomm_ring
    _ = 0 := by rw [hz]; simp

/-- Equal unbarred rows kill the product even when their barred anchors are distinct. -/
theorem rowFactor_repeat (L : Torus) (p q : Fermion L) (r : Fermion L → ℂ) :
    rowFactor L p r * rowFactor L q r = 0 := by
  apply Subtype.ext
  change (rowFactor L p r : Grassmann L) * (rowFactor L q r : Grassmann L) = 0
  rw [rowFactor_image, rowFactor_image]
  have hs := ExteriorAlgebra.ι_add_mul_swap (R := ℂ)
    (Pi.basisFun ℂ (Gen L) (q.1,Sum.inr q.2)) (rowVector L r)
  have hz := ExteriorAlgebra.ι_sq_zero (R := ℂ) (rowVector L r)
  change theta L (q.1,Sum.inr q.2) * ExteriorAlgebra.ι ℂ (rowVector L r) +
    ExteriorAlgebra.ι ℂ (rowVector L r) * theta L (q.1,Sum.inr q.2) = 0 at hs
  change (theta L (p.1,Sum.inr p.2) * ExteriorAlgebra.ι ℂ (rowVector L r)) *
    (theta L (q.1,Sum.inr q.2) * ExteriorAlgebra.ι ℂ (rowVector L r)) = 0
  calc
    _ = theta L (p.1,Sum.inr p.2) *
        (ExteriorAlgebra.ι ℂ (rowVector L r) * theta L (q.1,Sum.inr q.2)) *
          ExteriorAlgebra.ι ℂ (rowVector L r) := by noncomm_ring
    _ = -(theta L (p.1,Sum.inr p.2) * theta L (q.1,Sum.inr q.2)) *
        (ExteriorAlgebra.ι ℂ (rowVector L r) * ExteriorAlgebra.ι ℂ (rowVector L r)) := by
      rw [eq_neg_of_add_eq_zero_right hs]
      noncomm_ring
    _ = 0 := by rw [hz]; simp

/-- Multilinear row product, with values still in the actual even subalgebra. -/
def rowProduct (L : Torus) :
    MultilinearMap ℂ (fun _ : Fermion L ↦ Fermion L → ℂ) (bilinearAlgebra L) :=
  (MultilinearMap.mkPiAlgebra ℂ (Fermion L) (bilinearAlgebra L)).compLinearMap
    (rowFactor L)

/-- The actual row product is alternating, before taking any top coefficient. -/
def rowAlternating (L : Torus) :
    (Fermion L → ℂ) [⋀^Fermion L]→ₗ[ℂ] bilinearAlgebra L := by
  classical
  refine ⟨rowProduct L, ?_⟩
  intro M p q hpq hne
  change (∏ i, rowFactor L i (M i)) = 0
  rw [← Finset.prod_mul_prod_compl {p,q} (fun i ↦ rowFactor L i (M i))]
  have hz : (∏ i ∈ ({p,q} : Finset (Fermion L)), rowFactor L i (M i)) = 0 := by
    rw [Finset.prod_pair hne]
    rw [hpq, rowFactor_repeat]
  rw [hz, zero_mul]

/-- Taking the independently fixed top coefficient yields an alternating form. -/
def rowBerezin (L : Torus) : (Fermion L → ℂ) [⋀^Fermion L]→ₗ[ℂ] ℂ :=
  ((berezin L).comp (bilinearAlgebra L).val.toLinearMap).compAlternatingMap
    (rowAlternating L)

/-- Determinant dependence for arbitrary complex rows, with normalization still explicit. -/
theorem rowBerezin_det (L : Torus) (M : DiracMatrix L) :
    rowBerezin L M = rowBerezin L (Pi.basisFun ℂ (Fermion L)) * M.det := by
  classical
  have h := congrArg (fun f ↦ f M)
    ((rowBerezin L).eq_smul_basis_det (Pi.basisFun ℂ (Fermion L)))
  have he : Matrix.of M = M := by ext i j; rfl
  simpa only [AlternatingMap.smul_apply, smul_eq_mul, Pi.basisFun_det_apply, he] using h

/-- The top coefficient annihilates every other homogeneous degree. -/
theorem berezin_grade_zero (L : Torus) {k : ℕ} {g : Grassmann L}
    (hg : g ∈ grade L k) (hk : k ≠ volume L * 8) : berezin L g = 0 := by
  classical
  unfold berezin
  simp only [Module.Basis.coord_apply, Module.Basis.ExteriorAlgebra,
    Module.Basis.repr_reindex]
  rw [Finsupp.mapDomain_equiv_apply]
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ (by simpa using hk) hg

/-- Each row retains homogeneous exterior degree two. -/
theorem rowFactor_grade (L : Torus) (p : Fermion L) (r : Fermion L → ℂ) :
    (rowFactor L p r : Grassmann L) ∈ grade L 2 := by
  change ((bilinearAlgebra L).val (∑ q, r q •
    ⟨pair L (p.1,Sum.inr p.2) (q.1,Sum.inl q.2), pair_mem L _ _⟩)) ∈ _
  simp only [map_sum, map_smul]
  exact Submodule.sum_mem _ fun q _ ↦ Submodule.smul_mem _ _ (pair_grade L _ _)

/-- Row summation recovers the full bilinear, including arbitrary off-diagonal entries. -/
theorem sum_rowFactor (L : Torus) (M : DiracMatrix L) :
    ((∑ p, rowFactor L p (M p) : bilinearAlgebra L) : Grassmann L) = barMpsi L M := by
  classical
  change (bilinearAlgebra L).val (∑ p, rowFactor L p (M p)) = _
  simp only [map_sum, rowFactor, LinearMap.coe_mk, AddHom.coe_mk, map_smul]
  simp only [Fintype.sum_prod_type, barMpsi, bilinear]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  rfl

/-- The top power is the full row product times its actual factorial. -/
theorem barMpsi_top_power (L : Torus) (M : DiracMatrix L) :
    barMpsi L M ^ (4 * volume L) =
      ((4 * volume L).factorial : ℂ) •
        ((rowProduct L M : bilinearAlgebra L) : Grassmann L) := by
  classical
  let xs := (Finset.univ : Finset (Fermion L)).toList.map (fun p ↦ rowFactor L p (M p))
  have hx : ∀ a ∈ xs, a ^ 2 = 0 := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    exact rowFactor_square L p (M p)
  have ht := (squareZero_list_sum_top xs hx).1
  have hn : Fintype.card (Fermion L) = 4 * volume L := by
    simp only [Fermion, Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_comm _ _
  have ht' : (∑ p, rowFactor L p (M p)) ^ (4 * volume L) =
      ((4 * volume L).factorial : bilinearAlgebra L) * ∏ p, rowFactor L p (M p) := by
    simpa [xs, hn] using ht
  have he := congrArg (bilinearAlgebra L).val ht'
  simp only [map_pow, map_mul] at he
  rw [← sum_rowFactor L M, Algebra.smul_def, map_natCast]
  exact he

/-- Only the degree-4V term of the finite exponential contributes to the source top coefficient. -/
theorem berezin_nilExp_top (L : Torus) (M : DiracMatrix L) :
    berezin L (nilExp (4 * volume L) (barMpsi L M)) =
      ((4 * volume L).factorial : ℂ)⁻¹ • berezin L (barMpsi L M ^ (4 * volume L)) := by
  classical
  have hg : barMpsi L M ∈ grade L 2 := by
    exact Submodule.sum_mem _ fun y _ ↦ Submodule.sum_mem _ fun z _ ↦ bilinear_grade L y z _
  simp only [nilExp, map_sum, map_smul]
  apply Finset.sum_eq_single (4 * volume L)
  · intro k hk hkn
    have hk' := Finset.mem_range.mp hk
    rw [berezin_grade_zero L (power_grade L _ hg k) (by omega), smul_zero]
  · simp

/-- Arbitrary complex and singular matrices already have determinant dependence. -/
theorem berezin_nilExp_det_normalization (L : Torus) (M : DiracMatrix L) :
    berezin L (nilExp (4 * volume L) (barMpsi L M)) =
      rowBerezin L (Pi.basisFun ℂ (Fermion L)) * M.det := by
  rw [berezin_nilExp_top, barMpsi_top_power, map_smul, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero (4 * volume L)), one_smul]
  exact rowBerezin_det L M

/-- The standard matrix row gives the actual named diagonal barred/unbarred pair. -/
theorem rowFactor_basis (L : Torus) (p : Fermion L) :
    (rowFactor L p (Pi.basisFun ℂ (Fermion L) p) : Grassmann L) =
      pair L (p.1,Sum.inr p.2) (p.1,Sum.inl p.2) := by
  classical
  simp [rowFactor, Pi.basisFun_apply, Pi.single_apply]

/-- The full source basis top word is in its explicitly declared generator order. -/
theorem source_top_word (L : Torus) :
    (sourceBasis L).ExteriorAlgebra Finset.univ =
      (List.ofFn fun i : Fin (volume L * 8) ↦
        theta L ((sourceIndex L).symm i)).prod := by
  let s := Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin (volume L * 8))).toOrderEmbedding
  have hs : s.val = Finset.univ := by
    ext i
    simp [s, Set.powersetCard.ofFinEmbEquiv_apply]
  rw [← hs, ExteriorAlgebra.basis_apply_powersetCard]
  simp [s, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    sourceBasis, theta]

/-- The literal local source order differs from diagonal-pair order by two odd swaps. -/
theorem local_source_pairs (L : Torus) (x : Site L) :
    (List.ofFn fun i : Fin 8 ↦ theta L (x,localSourceOrder i)).prod =
      pair L (x,Sum.inr 0) (x,Sum.inl 0) * pair L (x,Sum.inr 1) (x,Sum.inl 1) *
      pair L (x,Sum.inr 2) (x,Sum.inl 2) * pair L (x,Sum.inr 3) (x,Sum.inl 3) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  change theta L (x,Sum.inr 0) * (theta L (x,Sum.inr 1) *
    (theta L (x,Sum.inl 0) * (theta L (x,Sum.inl 1) * (theta L (x,Sum.inr 2) *
    (theta L (x,Sum.inr 3) * (theta L (x,Sum.inl 2) * theta L (x,Sum.inl 3))))))) = _
  calc
    _ = theta L (x,Sum.inr 0) * (theta L (x,Sum.inr 1) * theta L (x,Sum.inl 0)) *
        theta L (x,Sum.inl 1) * theta L (x,Sum.inr 2) *
        (theta L (x,Sum.inr 3) * theta L (x,Sum.inl 2)) * theta L (x,Sum.inl 3) := by
      noncomm_ring
    _ = _ := by
      rw [theta_odd_swap L (x,Sum.inr 1) (x,Sum.inl 0),
        theta_odd_swap L (x,Sum.inr 3) (x,Sum.inl 2)]
      unfold pair
      noncomm_ring

/-- Grouping the source top word keeps each site's eight-generator word intact. -/
theorem source_top_sites (L : Torus) :
    (sourceBasis L).ExteriorAlgebra Finset.univ =
      (List.ofFn fun s : Fin (volume L) ↦
        (List.ofFn fun i : Fin 8 ↦ theta L ((Fintype.equivFin (Site L)).symm s,
          localSourceOrder i)).prod).prod := by
  rw [source_top_word, List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext s
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  congr 1
  simp [sourceIndex, Equiv.prodCongr, finProdFinEquiv]
  constructor <;> apply Fin.ext <;> simp [Fin.divNat, Fin.modNat]
  all_goals omega

/-- A complete site's four diagonal pairs have precisely the declared source orientation. -/
theorem local_diagonal_source (L : Torus) (x : Site L) :
    (List.ofFn fun i : Fin 8 ↦ theta L (x,localSourceOrder i)).prod =
      (bilinearAlgebra L).val
        (∏ i : Fin 4, rowFactor L (x,i) (Pi.basisFun ℂ (Fermion L) (x,i))) := by
  rw [local_source_pairs, ← List.prod_ofFn]
  rw [map_list_prod, List.map_ofFn]
  change _ = (List.ofFn fun i : Fin 4 ↦
    (rowFactor L (x,i) (Pi.basisFun ℂ (Fermion L) (x,i)) : Grassmann L)).prod
  simp only [rowFactor_basis, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, mul_one, mul_assoc]
  rfl

/-- The complete diagonal row product equals the actual source-oriented top word. -/
theorem diagonal_source_top (L : Torus) :
    ((rowProduct L (Pi.basisFun ℂ (Fermion L)) : bilinearAlgebra L) : Grassmann L) =
      (sourceBasis L).ExteriorAlgebra Finset.univ := by
  rw [source_top_sites]
  change (bilinearAlgebra L).val (∏ p, rowFactor L p (Pi.basisFun ℂ (Fermion L) p)) = _
  rw [Fintype.prod_prod_type]
  have he := (Fintype.equivFin (Site L)).symm.prod_comp
    (fun x ↦ ∏ i : Fin 4, rowFactor L (x,i) (Pi.basisFun ℂ (Fermion L) (x,i)))
  rw [← he, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext s
  exact (local_diagonal_source L _).symm

/-- Source orientation fixes the normalization; it is not a matrix-dependent definition. -/
theorem rowBerezin_normalization (L : Torus) :
    rowBerezin L (Pi.basisFun ℂ (Fermion L)) = 1 := by
  change berezin L ((rowProduct L (Pi.basisFun ℂ (Fermion L)) : bilinearAlgebra L) :
    Grassmann L) = 1
  rw [diagonal_source_top, berezin_top]

/-- The original 8V-generator Berezin integral of the finite bilinear exponential.
No inverse, positivity, reality, or nonsingularity premise is used. -/
theorem berezin_nilExp_det (L : Torus) (M : DiracMatrix L) :
    berezin L (nilExp (4 * volume L) (barMpsi L M)) = M.det := by
  rw [berezin_nilExp_det_normalization, rowBerezin_normalization, one_mul]

/-- Every original site weight is retained, at the same common global cutoff. -/
def fullWeight (L : Torus) (σ : ℝ)
    (S : Site L → FiniteGrassmannSourceAuxiliary.Polynomial) (h : Auxiliary L → ℝ) : ℂ :=
  ∏ x, auxiliaryWeight σ (compensationPolynomial (4 * FiniteGrassmannCoframe.volume L) σ (S x))
    (fun i ↦ h (x,i))

/-- Pointwise fermion integration of the actual C3 integrand, before Gaussian integration. -/
theorem berezin_original_integrand (L : Torus) (U : Links L) (σ : ℝ)
    (S : Site L → FiniteGrassmannSourceAuxiliary.Polynomial) (h : Auxiliary L → ℝ) :
    berezin L (FiniteGrassmannSourceAuxiliary.uncurriedIntegrand L U σ S h) =
      fullWeight L σ S h * (globalMatrix L U (fun a ↦ (h a : ℂ))).det := by
  unfold FiniteGrassmannSourceAuxiliary.uncurriedIntegrand
  rw [map_smul, ← globalMatrix_eq9, berezin_nilExp_det]
  exact smul_eq_mul _ _

/-- Absolute scalar integrability follows from actual vector integrability and continuity. -/
theorem original_determinant_integrable (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Site L → FiniteGrassmannSourceAuxiliary.Polynomial) :
    Integrable (fun h : Auxiliary L → ℝ ↦
      fullWeight L σ S h * (globalMatrix L U (fun a ↦ (h a : ℂ))).det)
        (gaussianMeasure (Auxiliary L) v) := by
  have hi := (berezinContinuous L).integrable_comp
    (FiniteGrassmannSourceAuxiliary.uncurried_global_integrable L U σ hσ v hv S)
  change Integrable (fun h ↦ berezin L
    (FiniteGrassmannSourceAuxiliary.uncurriedIntegrand L U σ S h)) _ at hi
  simpa only [berezin_original_integrand] using hi

/-- Fixed-link original Eq9–10 fermion/Gaussian identity.
Compact-link Haar integration and its Fubini hypotheses remain a separate consumer. -/
theorem original_fixed_link_determinant (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Site L → FiniteGrassmannSourceAuxiliary.Polynomial)
    (hS : ∀ x, (S x).constantCoeff = 0) :
    berezin L (nilExp (4 * volume L)
      (∑ x, ((MvPolynomial.aeval (FiniteGrassmannSourceAuxiliary.localCoframe L U x)
        (S x) : bilinearAlgebra L) : Grassmann L))) =
      ∫ h : Auxiliary L → ℝ,
        fullWeight L σ S h * (globalMatrix L U (fun a ↦ (h a : ℂ))).det
        ∂gaussianMeasure (Auxiliary L) v := by
  rw [← berezin_C3 L U σ hσ v hv S hS]
  exact integral_congr_ae (Filter.Eventually.of_forall (berezin_original_integrand L U σ S))

/-- The printed plaquette word keeps its own source and all original site weights. -/
theorem printed_fixed_link_determinant (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    berezin L (nilExp (4 * volume L)
      (∑ x, ((MvPolynomial.aeval (FiniteGrassmannSourceAuxiliary.localCoframe L U x)
        (FiniteGrassmannSourceAuxiliary.printedSource L U x g1 g2) :
          bilinearAlgebra L) : Grassmann L))) =
      ∫ h : Auxiliary L → ℝ,
        fullWeight L σ (fun x ↦ FiniteGrassmannSourceAuxiliary.printedSource L U x g1 g2) h *
          (globalMatrix L U (fun a ↦ (h a : ℂ))).det
        ∂gaussianMeasure (Auxiliary L) v :=
  original_fixed_link_determinant L U σ hσ v hv _
    (fun x ↦ FiniteGrassmannSourceAuxiliary.printedSource_constantCoeff L U x g1 g2)

/-- The separately labeled closed plaquette word keeps its own original source. -/
theorem closed_fixed_link_determinant (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    berezin L (nilExp (4 * volume L)
      (∑ x, ((MvPolynomial.aeval (FiniteGrassmannSourceAuxiliary.localCoframe L U x)
        (FiniteGrassmannSourceAuxiliary.closedSource L U x g1 g2) :
          bilinearAlgebra L) : Grassmann L))) =
      ∫ h : Auxiliary L → ℝ,
        fullWeight L σ (fun x ↦ FiniteGrassmannSourceAuxiliary.closedSource L U x g1 g2) h *
          (globalMatrix L U (fun a ↦ (h a : ℂ))).det
        ∂gaussianMeasure (Auxiliary L) v :=
  original_fixed_link_determinant L U σ hσ v hv _
    (fun x ↦ FiniteGrassmannSourceAuxiliary.closedSource_constantCoeff L U x g1 g2)

/-- Singular matrices with repeated rows are covered on the full original carrier. -/
theorem singular_repeated_row (L : Torus) (M : DiracMatrix L) (p q : Fermion L)
    (hpq : p ≠ q) (hrows : M p = M q) :
    berezin L (nilExp (4 * volume L) (barMpsi L M)) = 0 := by
  rw [berezin_nilExp_det, Matrix.det_zero_of_row_eq hpq hrows]

/-- A full-carrier off-diagonal permutation retains its negative determinant phase. -/
theorem offdiagonal_swap (L : Torus) (p q : Fermion L) (hpq : p ≠ q) :
    berezin L (nilExp (4 * volume L)
      (barMpsi L ((1 : DiracMatrix L).submatrix (Equiv.swap p q) id))) = -1 := by
  classical
  rw [berezin_nilExp_det, Matrix.det_permute]
  simp [Equiv.Perm.sign_swap hpq]

/-- A genuinely complex phase in a diagonal entry is preserved, not replaced by its magnitude. -/
theorem complex_phase (L : Torus) (p : Fermion L) :
    berezin L (nilExp (4 * volume L)
      (barMpsi L (Matrix.diagonal (fun q ↦ if q = p then Complex.I else 1)))) =
        Complex.I := by
  classical
  rw [berezin_nilExp_det, Matrix.det_diagonal]
  simp

/-- The zero matrix control on the actual smallest periodic regulator. -/
theorem one_site_zero_matrix :
    berezin oneSite (nilExp (4 * volume oneSite) (barMpsi oneSite 0)) = 0 := by
  rw [berezin_nilExp_det, Matrix.det_zero]

/-- Coincident periodic neighbours are all added on the one-site regulator. -/
theorem one_site_original_matrix (h : Auxiliary oneSite → ℂ) :
    globalMatrix oneSite (fun _ _ ↦ 1) h = 0 := by
  classical
  have hs (x y : Site oneSite) : x = y := Subsingleton.elim _ _
  ext p q
  change (∑ a, h a * hopping oneSite (fun _ _ ↦ 1) a.1 a.2.1 a.2.2
    p.1 q.1 p.2 q.2) = 0
  apply Finset.sum_eq_zero
  intro a _
  have h1 : p.1 = a.1 := hs _ _
  have h2 : q.1 = a.1 := hs _ _
  have hf : forward oneSite a.1 a.2.1 = a.1 := hs _ _
  have hb : backward oneSite a.1 a.2.1 = a.1 := hs _ _
  simp [hopping, h1, h2, hf, hb, dirac_identity]

/-- Consequently the actual one-site identity-link fermion integral vanishes. -/
theorem one_site_original_integral (h : Auxiliary oneSite → ℂ) :
    berezin oneSite (nilExp (4 * volume oneSite)
      (barMpsi oneSite (globalMatrix oneSite (fun _ _ ↦ 1) h))) = 0 := by
  rw [one_site_original_matrix]
  exact one_site_zero_matrix

/-- Independent top coefficient on the empty exterior carrier, for the empty-matrix control. -/
def emptyBerezin : ExteriorAlgebra ℂ (Fin 0 → ℂ) →ₗ[ℂ] ℂ :=
  (Pi.basisFun ℂ (Fin 0)).ExteriorAlgebra.coord ∅

/-- The empty finite exponential and empty determinant both have value one. -/
theorem empty_matrix_control (M : Matrix (Fin 0) (Fin 0) ℂ) :
    emptyBerezin (nilExp 0 (0 : ExteriorAlgebra ℂ (Fin 0 → ℂ))) = M.det := by
  rw [nilExp_zero_cutoff, Matrix.det_fin_zero]
  have he : (Pi.basisFun ℂ (Fin 0)).ExteriorAlgebra ∅ =
      (1 : ExteriorAlgebra ℂ (Fin 0 → ℂ)) := by
    rw [ExteriorAlgebra.basis_apply_ofCard _
      (show (∅ : Finset (Fin 0)).card = 0 from rfl)]
    simp only [ExteriorAlgebra.ιMulti_family]
    rw [ExteriorAlgebra.ιMulti_apply]
    rfl
  rw [← he]
  simp [emptyBerezin, Module.Basis.coord_apply]

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
open FiniteGrassmannCoframe

/-- The original compact group has bounded matrix entries, without an operator-norm convention. -/
theorem su2_entry_norm_le (U : SU2) (i j : Fin 2) : ‖U.val i j‖ ≤ 1 := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ ↦ (A i i).re)
    ((mem_specialUnitaryGroup_iff.mp U.property).1.2)
  simp only [mul_apply, star_eq_conjTranspose, conjTranspose_apply,
    Fin.sum_univ_two, Complex.add_re, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re, one_apply_eq, Complex.one_re] at h
  have hj0 : 0 ≤ Complex.normSq (U.val i 0) := Complex.normSq_nonneg _
  have hj1 : 0 ≤ Complex.normSq (U.val i 1) := Complex.normSq_nonneg _
  have hs0 := Complex.sq_norm (U.val i 0)
  have hs1 := Complex.sq_norm (U.val i 1)
  fin_cases j
  · change ‖U.val i 0‖ ≤ 1
    nlinarith [norm_nonneg (U.val i 0)]
  · change ‖U.val i 1‖ ≤ 1
    nlinarith [norm_nonneg (U.val i 1)]

/-- Compactness is proved for the actual determinant-one unitary matrices. -/
instance su2CompactSpace : CompactSpace SU2 := by
  apply isCompact_iff_compactSpace.mp
  have hc : IsCompact {A : Matrix (Fin 2) (Fin 2) ℂ | ∀ i j, ‖A i j‖ ≤ 1} := by
    simpa only [Set.matrix, Metric.mem_closedBall, dist_zero_right] using
      (isCompact_closedBall (0 : ℂ) 1).matrix (m := Fin 2) (n := Fin 2)
  apply hc.of_isClosed_subset
  · have he : (SU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) =
        (unitaryGroup (Fin 2) ℂ : Set _) ∩ {A | A.det = 1} := by
      ext A
      exact mem_specialUnitaryGroup_iff
    rw [he]
    exact isClosed_unitary.inter (isClosed_eq continuous_id.matrix_det continuous_const)
  · intro U hU
    exact su2_entry_norm_le ⟨U,hU⟩

instance su2ContinuousInv : ContinuousInv SU2 where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun U : SU2 ↦ star U.val)
    exact continuous_subtype_val.star

instance su2TopologicalGroup : IsTopologicalGroup SU2 where

instance su2SecondCountable : SecondCountableTopology SU2 := by
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  exact (Topology.IsInducing.subtypeVal
    (t := (SU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)))).secondCountableTopology

instance su2MeasurableSpace : MeasurableSpace SU2 := borel SU2
instance su2BorelSpace : BorelSpace SU2 := ⟨rfl⟩

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
open FiniteGrassmannCoframe

/-- Original SU(2) Haar measure normalized on the whole compact group. -/
def su2Haar : Measure SU2 := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)
instance su2HaarProbability : IsProbabilityMeasure su2Haar := by
  constructor
  simpa only [su2Haar, TopologicalSpace.PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts SU2)))
instance su2HaarInvariant : Measure.IsMulLeftInvariant su2Haar := inferInstanceAs
  (Measure.IsMulLeftInvariant (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)))

/-- Independent left and right chiral Haar factors, with no diagonal identification. -/
def spin4Haar : Measure Spin4 := su2Haar.prod su2Haar
instance spin4HaarProbability : IsProbabilityMeasure spin4Haar := by
  unfold spin4Haar
  infer_instance

/-- Every original anchor has its own independent Spin(4) Haar variable. -/
def linkHaar (L : Torus) : Measure (Links L) :=
  Measure.pi (fun _ : Site L ↦ Measure.pi (fun _ : Fin 4 ↦ spin4Haar))
instance linkHaarProbability (L : Torus) : IsProbabilityMeasure (linkHaar L) := by
  unfold linkHaar
  infer_instance

/-- The source Dirac representation is continuous on the actual compact group. -/
theorem dirac_continuous : Continuous (dirac : Spin4 → Matrix (Fin 4) (Fin 4) ℂ) := by
  have hb : Continuous (fun U : Spin4 ↦
      Matrix.fromBlocks U.1.val (0 : Matrix (Fin 2) (Fin 2) ℂ)
        (0 : Matrix (Fin 2) (Fin 2) ℂ) U.2.val) := by
    fun_prop
  exact hb.matrix_submatrix diracIndex.symm diracIndex.symm

/-- Actual anchor evaluation retains the full original product topology. -/
theorem link_dirac_continuous (L : Torus) (x : Site L) (μ : Fin 4) :
    Continuous (fun U : Links L ↦ dirac (U x μ)) :=
  dirac_continuous.comp ((continuous_apply μ).comp (continuous_apply x))

/-- Both original curvature words are continuous, with their orders unchanged. -/
theorem printed_plaquette_continuous (L : Torus) (x : Site L) (k l : Fin 4) :
    Continuous (fun U : Links L ↦ FiniteGrassmannSourceAuxiliary.plaquettePrinted L U x k l) := by
  unfold FiniteGrassmannSourceAuxiliary.plaquettePrinted
  exact (((link_dirac_continuous L x k).matrix_mul
    (link_dirac_continuous L (forward L x k) l)).matrix_mul
      (link_dirac_continuous L (forward L x l) k).matrix_conjTranspose).matrix_mul
        (link_dirac_continuous L x l).matrix_conjTranspose

theorem closed_plaquette_continuous (L : Torus) (x : Site L) (k l : Fin 4) :
    Continuous (fun U : Links L ↦ FiniteGrassmannSourceAuxiliary.plaquetteClosed L U x k l) := by
  unfold FiniteGrassmannSourceAuxiliary.plaquetteClosed
  exact (((link_dirac_continuous L x l).matrix_conjTranspose.matrix_mul
    (link_dirac_continuous L (forward L x l) k).matrix_conjTranspose).matrix_mul
      (link_dirac_continuous L (forward L x k) l)).matrix_mul
        (link_dirac_continuous L x k)

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
open FiniteGrassmannCoframe
open FiniteGrassmannSourceAuxiliary

/-- Finite coefficient convolution preserves parameter continuity. -/
theorem coeff_mul_continuous {K ι : Type*} [TopologicalSpace K] [DecidableEq ι]
    (P Q : K → MvPolynomial ι ℂ)
    (hP : ∀ α, Continuous (fun u ↦ (P u).coeff α))
    (hQ : ∀ α, Continuous (fun u ↦ (Q u).coeff α)) (α : ι →₀ ℕ) :
    Continuous (fun u ↦ (P u * Q u).coeff α) := by
  simp only [MvPolynomial.coeff_mul]
  exact continuous_finsetSum _ (fun d _ ↦ (hP d.1).mul (hQ d.2))

/-- Powers use finite convolution, not a topology on the infinite polynomial space. -/
theorem coeff_pow_continuous {K ι : Type*} [TopologicalSpace K] [DecidableEq ι]
    (P : K → MvPolynomial ι ℂ)
    (hP : ∀ α, Continuous (fun u ↦ (P u).coeff α)) (n : ℕ) (α : ι →₀ ℕ) :
    Continuous (fun u ↦ (P u ^ n).coeff α) := by
  induction n generalizing α with
  | zero => simp only [pow_zero]; exact continuous_const
  | succ n ih =>
    simp only [pow_succ]
    exact coeff_mul_continuous (fun u ↦ P u ^ n) P ih hP α

/-- Every retained compensation coefficient is an actual finite continuous expression. -/
theorem compensation_coeff_continuous {K ι : Type*} [TopologicalSpace K]
    [Fintype ι] [DecidableEq ι] (M : ℕ) (σ : ℝ) (S : K → MvPolynomial ι ℂ)
    (hS : ∀ u, (S u).constantCoeff = 0)
    (hC : ∀ α, Continuous (fun u ↦ (S u).coeff α)) (α : ι →₀ ℕ) :
    Continuous (fun u ↦ (compensationPolynomial M σ (S u)).coeff α) := by
  simp only [compensationPolynomial_coeff_finite M σ _ (hS _) α]
  split_ifs
  · apply continuous_finsetSum
    intro k _
    apply continuous_finsetSum
    intro l _
    exact continuous_const.mul
      (coeff_mul_continuous (fun u ↦ S u ^ k)
        (fun _ : K ↦ (-auxiliaryQuadraticPolynomial σ) ^ l)
        (coeff_pow_continuous S hC k) (fun _ ↦ continuous_const) α)
  · exact continuous_const

/-- Original ordered curvature traces have continuous coefficients. -/
theorem curvature_coeff_continuous {K : Type*} [TopologicalSpace K]
    (F : K → Curvature) (hF : ∀ k l, Continuous (fun u ↦ F u k l))
    (m n C D : Fin 4) :
    Continuous (fun u ↦ curvatureCoefficient (F u) m n C D) := by
  unfold curvatureCoefficient
  apply continuous_finsetSum
  intro k _
  apply continuous_finsetSum
  intro l _
  apply continuous_const.mul
  have h1 : Continuous (fun u ↦ F u k l * gamma C) :=
    (hF k l).matrix_mul continuous_const
  have h2 : Continuous (fun u ↦ F u k l * gamma C * gamma D) :=
    h1.matrix_mul continuous_const
  have h3 : Continuous (fun u ↦ F u k l * gamma C * gamma D * gamma5) :=
    h2.matrix_mul continuous_const
  exact h3.matrix_trace

/-- Both physical polynomial families discharge coefficient continuity at their actual matrices. -/
theorem source_coeff_continuous {K : Type*} [TopologicalSpace K]
    (F : K → Curvature) (hF : ∀ k l, Continuous (fun u ↦ F u k l))
    (g1 g2 : ℂ) (α : D →₀ ℕ) :
    Continuous (fun u ↦ (source (F u) g1 g2).coeff α) := by
  simp only [source, MvPolynomial.coeff_add]
  apply continuous_const.add
  simp only [einsteinCartan, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  apply continuous_finsetSum
  intro m _
  apply continuous_finsetSum
  intro n _
  apply continuous_finsetSum
  intro C _
  apply continuous_finsetSum
  intro D _
  exact (continuous_const.mul (curvature_coeff_continuous F hF m n C D)).mul continuous_const

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
open FiniteGrassmannCoframe

open GaussianGrassmannAuxiliary

/-- Polynomial auxiliary fields with actual continuous original-link coefficients. -/
abbrev LinkCoefficient (L : Torus) := C(Links L, ℂ)
abbrev HaarPolynomial (L : Torus) := MvPolynomial (Auxiliary L) (LinkCoefficient L)

def coefficientEvaluation (L : Torus) (U : Links L) : LinkCoefficient L →+* ℂ where
  toFun f := f U
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def haarPolynomialEvaluation (L : Torus) (U : Links L) (h : Auxiliary L → ℝ) :
    HaarPolynomial L →+* ℂ :=
  MvPolynomial.eval₂Hom (coefficientEvaluation L U) (fun a ↦ (h a : ℂ))

/-- Every real monomial has an actual absolute Gaussian moment. -/
theorem gaussian_monomial_integrable (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (d : Auxiliary L →₀ ℕ) :
    Integrable (fun h : Auxiliary L → ℝ ↦ (auxiliaryMonomial d h : ℂ))
      (gaussianMeasure (Auxiliary L) v) := by
  have hi := (integrable_auxiliaryHermite_mul_monomial σ hσ v hv
    (0 : Auxiliary L →₀ ℕ) d).ofReal (𝕜 := ℂ)
  simpa [auxiliaryHermite] using hi

/-- Compactness controls every continuous coefficient before any product integral is exchanged. -/
theorem link_coefficient_integrable (L : Torus) (a : LinkCoefficient L) :
    Integrable a (linkHaar L) :=
  a.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace a)

/-- Finite polynomial separation proves genuine joint Haar–Gaussian integrability. -/
theorem haarPolynomial_integrable (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (P : HaarPolynomial L) :
    Integrable (fun z : Links L × (Auxiliary L → ℝ) ↦
      haarPolynomialEvaluation L z.1 z.2 P)
      ((linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) := by
  classical
  change Integrable (fun z : Links L × (Auxiliary L → ℝ) ↦
    MvPolynomial.eval₂ (coefficientEvaluation L z.1) (fun a ↦ (z.2 a : ℂ)) P) _
  simp only [MvPolynomial.eval₂_eq]
  apply integrable_finsetSum
  intro d _
  have hi : Integrable (fun h : Auxiliary L → ℝ ↦
      ∏ i ∈ d.support, (h i : ℂ) ^ d i) (gaussianMeasure (Auxiliary L) v) := by
    convert gaussian_monomial_integrable L σ hσ v hv d using 1
    funext h
    rw [auxiliaryMonomial, Complex.ofReal_prod]
    simp only [Complex.ofReal_pow]
    exact Finsupp.prod_fintype d (fun i n ↦ (h i : ℂ) ^ n) (by simp)
  exact (link_coefficient_integrable L (P.coeff d)).mul_prod hi

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
open FiniteGrassmannCoframe FiniteGrassmannEvaluation GaussianGrassmannAuxiliary
open FiniteGrassmannSourceAuxiliary

@[simp] theorem haarPolynomialEvaluation_C (L : Torus) (U : Links L)
    (h : Auxiliary L → ℝ) (a : LinkCoefficient L) :
    haarPolynomialEvaluation L U h (MvPolynomial.C a) = a U :=
  MvPolynomial.eval₂_C _ _ _

@[simp] theorem haarPolynomialEvaluation_X (L : Torus) (U : Links L)
    (h : Auxiliary L → ℝ) (a : Auxiliary L) :
    haarPolynomialEvaluation L U h (MvPolynomial.X a) = (h a : ℂ) :=
  MvPolynomial.eval₂_X _ _ _

def constantHaarPolynomial (L : Torus) (c : ℂ) : HaarPolynomial L :=
  MvPolynomial.C (ContinuousMap.const (Links L) c)

@[simp] theorem haarPolynomialEvaluation_constant (L : Torus) (U : Links L)
    (h : Auxiliary L → ℝ) (c : ℂ) :
    haarPolynomialEvaluation L U h (constantHaarPolynomial L c) = c := by
  rw [constantHaarPolynomial, haarPolynomialEvaluation_C]
  rfl

/-- A finite Hermite polynomial in the original site's auxiliary coordinates. -/
def hermiteHaarPolynomial (L : Torus) (σ : ℝ) (x : Site L) (α : D →₀ ℕ) :
    HaarPolynomial L :=
  ∏ i : D, Polynomial.eval₂ (Int.castRingHom (HaarPolynomial L))
    (constantHaarPolynomial L ((σ : ℂ)⁻¹) * MvPolynomial.X (x,i))
    (Polynomial.hermite (α i))

theorem integer_polynomial_complex_eval (P : Polynomial ℤ) (x : ℝ) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (x : ℂ) P =
      ((Polynomial.aeval x P : ℝ) : ℂ) := by
  rw [Polynomial.aeval_def]
  change _ = Complex.ofRealHom (Polynomial.eval₂ (algebraMap ℤ ℝ) x P)
  rw [Polynomial.hom_eval₂]
  rfl

/-- This is the actual scaled Hermite polynomial, not a chosen integrable replacement. -/
theorem hermiteHaarPolynomial_eval (L : Torus) (σ : ℝ) (x : Site L)
    (α : D →₀ ℕ) (U : Links L) (h : Auxiliary L → ℝ) :
    haarPolynomialEvaluation L U h (hermiteHaarPolynomial L σ x α) =
      (auxiliaryHermite σ α (fun i ↦ h (x,i)) : ℂ) := by
  rw [hermiteHaarPolynomial, map_prod, auxiliaryHermite, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.ringHom_eval₂_intCastRingHom]
  simp only [map_mul, haarPolynomialEvaluation_constant, haarPolynomialEvaluation_X]
  rw [show (σ : ℂ)⁻¹ * (h (x,i) : ℂ) = ((h (x,i) / σ : ℝ) : ℂ) by
    push_cast
    ring]
  exact integer_polynomial_complex_eval _ _

/-- A fixed finite roster replaces varying support only by inserting proved zero coefficients. -/
theorem auxiliaryWeight_bounded {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (σ : ℝ) (P : MvPolynomial ι ℂ) (hP : P.totalDegree ≤ M) (h : ι → ℝ) :
    auxiliaryWeight σ P h =
      ∑ α ∈ boundedIndices M,
        P.coeff α * ((σ ^ auxiliaryDegree α)⁻¹ : ℝ) * (auxiliaryHermite σ α h : ℂ) := by
  classical
  unfold auxiliaryWeight
  apply Finset.sum_subset
  · intro α hα
    apply (mem_boundedIndices M α).mpr
    exact (MvPolynomial.le_totalDegree hα).trans hP
  · intro α _ hα
    have hz : P.coeff α = 0 := by
      simpa only [MvPolynomial.mem_support_iff, not_not] using hα
    rw [hz, zero_mul, zero_mul]

/-- Continuous exact coefficients of the original compensated action. -/
def compensationLinkCoefficient (L : Torus) (σ : ℝ)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (x : Site L) (α : D →₀ ℕ) : LinkCoefficient L :=
  ⟨fun U ↦ (compensationPolynomial (4 * volume L) σ (S U x)).coeff α,
    compensation_coeff_continuous (4 * volume L) σ (fun U ↦ S U x)
      (fun U ↦ hS U x) (hC x) α⟩

/-- All retained original compensation coefficients, on a uniform common-4V roster. -/
def siteWeightHaarPolynomial (L : Torus) (σ : ℝ)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α)) (x : Site L) :
    HaarPolynomial L :=
  ∑ α ∈ boundedIndices (4 * volume L),
    MvPolynomial.C (compensationLinkCoefficient L σ S hS hC x α) *
      constantHaarPolynomial L (((σ ^ auxiliaryDegree α)⁻¹ : ℝ) : ℂ) *
      hermiteHaarPolynomial L σ x α

theorem siteWeightHaarPolynomial_eval (L : Torus) (σ : ℝ)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (x : Site L) (U : Links L) (h : Auxiliary L → ℝ) :
    haarPolynomialEvaluation L U h (siteWeightHaarPolynomial L σ S hS hC x) =
      auxiliaryWeight σ (compensationPolynomial (4 * volume L) σ (S U x))
        (fun i ↦ h (x,i)) := by
  rw [auxiliaryWeight_bounded (4 * volume L) σ _
    (compensationPolynomial_totalDegree _ _ _) (fun i ↦ h (x,i))]
  simp only [siteWeightHaarPolynomial, map_sum, map_mul, haarPolynomialEvaluation_C,
    haarPolynomialEvaluation_constant, hermiteHaarPolynomial_eval, compensationLinkCoefficient,
    ContinuousMap.coe_mk]

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
open FiniteGrassmannCoframe FiniteGrassmannEvaluation GaussianGrassmannAuxiliary
open FiniteGrassmannSourceAuxiliary

/-- Each original hopping block is continuous even when its anchors coincide. -/
theorem hopping_continuous (L : Torus) (x : Site L) (μ C : Fin 4) (y z : Site L) :
    Continuous (fun U : Links L ↦ hopping L U x μ C y z) := by
  have hd := link_dirac_continuous L x μ
  have hb := link_dirac_continuous L (backward L x μ) μ
  unfold hopping
  split_ifs <;> fun_prop

/-- Symbolic original Dirac matrix; each scalar h coordinate is an actual polynomial variable. -/
def diracHaarPolynomial (L : Torus) :
    Matrix (Fermion L) (Fermion L) (HaarPolynomial L) :=
  fun p q ↦ ∑ a : Auxiliary L, MvPolynomial.X a *
    MvPolynomial.C (⟨fun U ↦ hopping L U a.1 a.2.1 a.2.2 p.1 q.1 p.2 q.2,
      (hopping_continuous L a.1 a.2.1 a.2.2 p.1 q.1).matrix_elem p.2 q.2⟩ :
        LinkCoefficient L)

/-- Evaluation recovers the full original global matrix, not just its determinant. -/
theorem diracHaarPolynomial_eval (L : Torus) (U : Links L) (h : Auxiliary L → ℝ) :
    (haarPolynomialEvaluation L U h).mapMatrix (diracHaarPolynomial L) =
      globalMatrix L U (fun a ↦ (h a : ℂ)) := by
  classical
  ext p q
  change haarPolynomialEvaluation L U h (diracHaarPolynomial L p q) = _
  simp only [diracHaarPolynomial, globalMatrix, map_sum, map_mul,
    haarPolynomialEvaluation_X, haarPolynomialEvaluation_C, ContinuousMap.coe_mk]

/-- The original determinant and EVERY original site weight, as one finite joint polynomial. -/
def completeHaarPolynomial (L : Torus) (σ : ℝ)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α)) : HaarPolynomial L :=
  (∏ x, siteWeightHaarPolynomial L σ S hS hC x) * (diracHaarPolynomial L).det

theorem completeHaarPolynomial_eval (L : Torus) (σ : ℝ)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α))
    (U : Links L) (h : Auxiliary L → ℝ) :
    haarPolynomialEvaluation L U h (completeHaarPolynomial L σ S hS hC) =
      fullWeight L σ (S U) h * (globalMatrix L U (fun a ↦ (h a : ℂ))).det := by
  classical
  rw [completeHaarPolynomial, map_mul, map_prod,
    (haarPolynomialEvaluation L U h).map_det, diracHaarPolynomial_eval]
  simp only [siteWeightHaarPolynomial_eval, fullWeight]

/-- Joint integrability from finite continuous coefficients, without assuming the target integral. -/
theorem original_joint_integrable (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α)) :
    Integrable (fun z : Links L × (Auxiliary L → ℝ) ↦
      fullWeight L σ (S z.1) z.2 * (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det)
      ((linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) := by
  simpa only [completeHaarPolynomial_eval] using
    haarPolynomial_integrable L σ hσ v hv (completeHaarPolynomial L σ S hS hC)

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
open FiniteGrassmannCoframe FiniteGrassmannEvaluation GaussianGrassmannAuxiliary
open FiniteGrassmannSourceAuxiliary

instance spin4HaarInvariant : Measure.IsMulLeftInvariant spin4Haar := by
  unfold spin4Haar
  infer_instance
instance linkHaarInvariant (L : Torus) : Measure.IsMulLeftInvariant (linkHaar L) := by
  letI : Measure.IsMulLeftInvariant (Measure.pi (fun _ : Fin 4 ↦ spin4Haar)) :=
    Measure.pi.isMulLeftInvariant _
  exact Measure.pi.isMulLeftInvariant _

theorem original_link_measure_normalized (L : Torus) : linkHaar L Set.univ = 1 :=
  measure_univ

/-- The original finite Berezin partition integrand is integrable on all original compact links. -/
theorem original_partition_integrable (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α)) :
    Integrable (fun U : Links L ↦ berezin L (nilExp (4 * volume L)
      (∑ x, ((MvPolynomial.aeval (localCoframe L U x) (S U x) :
        bilinearAlgebra L) : Grassmann L)))) (linkHaar L) := by
  have hi := (original_joint_integrable L σ hσ v hv S hS hC).integral_prod_left
  apply hi.congr
  exact Filter.Eventually.of_forall (fun U ↦
    (original_fixed_link_determinant L U σ hσ v hv (S U) (hS U)).symm)

/-- Full original finite-regulator Eq10, including the actual outer compact-link Haar measure.
The coefficient hypotheses are discharged below for BOTH actual source words. -/
theorem original_eq10 (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α)) :
    (∫ U : Links L, berezin L (nilExp (4 * volume L)
      (∑ x, ((MvPolynomial.aeval (localCoframe L U x) (S U x) :
        bilinearAlgebra L) : Grassmann L))) ∂linkHaar L) =
      ∫ z : Links L × (Auxiliary L → ℝ),
        fullWeight L σ (S z.1) z.2 * (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det
        ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v) := by
  rw [integral_prod _ (original_joint_integrable L σ hσ v hv S hS hC)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun U ↦
    original_fixed_link_determinant L U σ hσ v hv (S U) (hS U)))

/-- Fubini is justified by the full joint polynomial bound, not merely pointwise integrability. -/
theorem original_eq10_gaussian_outer (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Links L → Site L → Polynomial)
    (hS : ∀ U x, (S U x).constantCoeff = 0)
    (hC : ∀ x α, Continuous (fun U ↦ (S U x).coeff α)) :
    (∫ U : Links L, berezin L (nilExp (4 * volume L)
      (∑ x, ((MvPolynomial.aeval (localCoframe L U x) (S U x) :
        bilinearAlgebra L) : Grassmann L))) ∂linkHaar L) =
      ∫ h : Auxiliary L → ℝ, ∫ U : Links L,
        fullWeight L σ (S U) h * (globalMatrix L U (fun a ↦ (h a : ℂ))).det
        ∂linkHaar L ∂gaussianMeasure (Auxiliary L) v := by
  rw [original_eq10 L σ hσ v hv S hS hC,
    integral_prod _ (original_joint_integrable L σ hσ v hv S hS hC)]
  exact integral_integral_swap (original_joint_integrable L σ hσ v hv S hS hC)

theorem printed_source_coeff_continuous (L : Torus) (x : Site L) (g1 g2 : ℂ)
    (α : D →₀ ℕ) : Continuous (fun U : Links L ↦ (printedSource L U x g1 g2).coeff α) :=
  source_coeff_continuous (fun U ↦ plaquettePrinted L U x)
    (printed_plaquette_continuous L x) g1 g2 α

theorem closed_source_coeff_continuous (L : Torus) (x : Site L) (g1 g2 : ℂ)
    (α : D →₀ ℕ) : Continuous (fun U : Links L ↦ (closedSource L U x g1 g2).coeff α) :=
  source_coeff_continuous (fun U ↦ plaquetteClosed L U x)
    (closed_plaquette_continuous L x) g1 g2 α

/-- Joint absolute integrability for the actual printed word, with arbitrary complex couplings. -/
theorem printed_joint_integrable (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    Integrable (fun z : Links L × (Auxiliary L → ℝ) ↦
      fullWeight L σ (fun x ↦ printedSource L z.1 x g1 g2) z.2 *
        (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det)
      ((linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) :=
  original_joint_integrable L σ hσ v hv (fun U x ↦ printedSource L U x g1 g2)
    (fun U x ↦ printedSource_constantCoeff L U x g1 g2)
    (fun x α ↦ printed_source_coeff_continuous L x g1 g2 α)

/-- Joint absolute integrability for the distinct closed word, without identifying the two words. -/
theorem closed_joint_integrable (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    Integrable (fun z : Links L × (Auxiliary L → ℝ) ↦
      fullWeight L σ (fun x ↦ closedSource L z.1 x g1 g2) z.2 *
        (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det)
      ((linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) :=
  original_joint_integrable L σ hσ v hv (fun U x ↦ closedSource L U x g1 g2)
    (fun U x ↦ closedSource_constantCoeff L U x g1 g2)
    (fun x α ↦ closed_source_coeff_continuous L x g1 g2 α)

/-- Full Eq10 for the literal printed curvature/source polynomial. -/
theorem printed_full_eq10 (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    (∫ U : Links L, berezin L (nilExp (4 * volume L)
      (∑ x, ((MvPolynomial.aeval (localCoframe L U x)
        (printedSource L U x g1 g2) : bilinearAlgebra L) : Grassmann L))) ∂linkHaar L) =
      ∫ z : Links L × (Auxiliary L → ℝ),
        fullWeight L σ (fun x ↦ printedSource L z.1 x g1 g2) z.2 *
          (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det
        ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v) :=
  original_eq10 L σ hσ v hv (fun U x ↦ printedSource L U x g1 g2)
    (fun U x ↦ printedSource_constantCoeff L U x g1 g2)
    (fun x α ↦ printed_source_coeff_continuous L x g1 g2 α)

/-- Full Eq10 for the independently retained closed curvature/source polynomial. -/
theorem closed_full_eq10 (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    (∫ U : Links L, berezin L (nilExp (4 * volume L)
      (∑ x, ((MvPolynomial.aeval (localCoframe L U x)
        (closedSource L U x g1 g2) : bilinearAlgebra L) : Grassmann L))) ∂linkHaar L) =
      ∫ z : Links L × (Auxiliary L → ℝ),
        fullWeight L σ (fun x ↦ closedSource L z.1 x g1 g2) z.2 *
          (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det
        ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v) :=
  original_eq10 L σ hσ v hv (fun U x ↦ closedSource L U x g1 g2)
    (fun U x ↦ closedSource_constantCoeff L U x g1 g2)
    (fun x α ↦ closed_source_coeff_continuous L x g1 g2 α)

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin

namespace SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
open FiniteGrassmannCoframe FiniteGrassmannEvaluation GaussianGrassmannAuxiliary
open FiniteGrassmannSourceAuxiliary

/-- Compact-link bounds are genuine sup-norm bounds on each constructed continuous coefficient. -/
theorem link_coefficient_norm_bound (L : Torus) (a : LinkCoefficient L) (U : Links L) :
    ‖a U‖ ≤ ‖a‖ := ContinuousMap.norm_coe_le_norm a U

/-- All original link factors and every independent auxiliary Gaussian are probability measures. -/
theorem original_joint_measure_normalized (L : Torus) (v : ℝ≥0) :
    ((linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) Set.univ = 1 := measure_univ

theorem original_haar_unit_control : (∫ _ : Links oneSite, (1 : ℂ) ∂linkHaar oneSite) = 1 := by
  simp

/-- Actual nonunit variances give the same complete original printed-word partition. -/
theorem printed_full_two_scales (L : Torus) (g1 g2 : ℂ) :
    (∫ z : Links L × (Auxiliary L → ℝ),
      fullWeight L 2 (fun x ↦ printedSource L z.1 x g1 g2) z.2 *
        (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) 4)) =
    ∫ z : Links L × (Auxiliary L → ℝ),
      fullWeight L (1/2) (fun x ↦ printedSource L z.1 x g1 g2) z.2 *
        (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) (1/4)) :=
  (printed_full_eq10 L 2 (by norm_num) 4 (by norm_num) g1 g2).symm.trans
    (printed_full_eq10 L (1/2) (by norm_num) (1/4) (by norm_num) g1 g2)

/-- The separately retained closed word obeys the same complete variance-independence check. -/
theorem closed_full_two_scales (L : Torus) (g1 g2 : ℂ) :
    (∫ z : Links L × (Auxiliary L → ℝ),
      fullWeight L 2 (fun x ↦ closedSource L z.1 x g1 g2) z.2 *
        (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) 4)) =
    ∫ z : Links L × (Auxiliary L → ℝ),
      fullWeight L (1/2) (fun x ↦ closedSource L z.1 x g1 g2) z.2 *
        (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) (1/4)) :=
  (closed_full_eq10 L 2 (by norm_num) 4 (by norm_num) g1 g2).symm.trans
    (closed_full_eq10 L (1/2) (by norm_num) (1/4) (by norm_num) g1 g2)

/-- The original positive-volume carrier does not normalize the empty fermionic action to one. -/
theorem berezin_one_zero (L : Torus) : berezin L 1 = 0 := by
  have hp : 0 < volume L := Fintype.card_pos
  exact berezin_grade_zero L (SetLike.one_mem_graded (grade L)) (by omega)

/-- With zero original action, every source weight is still retained and the full integral vanishes.
This control makes no nonzero-denominator or positive-state assumption. -/
theorem original_zero_action_integral (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) :
    (∫ z : Links L × (Auxiliary L → ℝ),
      fullWeight L σ (fun _ ↦ 0) z.2 *
        (globalMatrix L z.1 (fun a ↦ (z.2 a : ℂ))).det
      ∂(linkHaar L).prod (gaussianMeasure (Auxiliary L) v)) = 0 := by
  have he := original_eq10 L σ hσ v hv (fun _ _ ↦ 0)
    (by intro U x; simp) (by intro x α; exact continuous_const)
  simpa only [map_zero, ZeroMemClass.coe_zero, Finset.sum_const_zero, nilExp_zero, berezin_one_zero,
    integral_zero] using he.symm

end SKEFTHawking.ADW.FiniteGrassmannDiracBerezin
