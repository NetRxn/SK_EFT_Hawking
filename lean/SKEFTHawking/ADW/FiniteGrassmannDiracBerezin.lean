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
