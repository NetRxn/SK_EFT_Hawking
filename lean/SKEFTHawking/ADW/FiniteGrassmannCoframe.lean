import Mathlib
import SKEFTHawking.PauliMatrices

/-!
# Finite periodic Grassmann coframes

The complex exterior algebra has independent barred and unbarred coordinates.
Source: Diakonov, arXiv:1109.0091v1, pp. 11–15, Eqs. 14, 16 and 23.
The source labels 1,2,3,4 become Fin 4 labels 0,1,2,3 in that order.
This module defines no EHC action or identification of plaquette functionals.
-/
noncomputable section
open scoped BigOperators
open Matrix
namespace SKEFTHawking.ADW.FiniteGrassmannCoframe

/-- Positive extents of the fixed periodic four-torus. -/
structure Torus where
  extent : Fin 4 → ℕ
  positive : ∀ μ, 0 < extent μ

abbrev Site (L : Torus) := (μ : Fin 4) → ZMod (L.extent μ)
instance (L : Torus) (μ : Fin 4) : NeZero (L.extent μ) := ⟨Nat.ne_of_gt (L.positive μ)⟩
instance (L : Torus) : Fintype (Site L) := Pi.instFintype
abbrev volume (L : Torus) := Fintype.card (Site L)
abbrev Gen (L : Torus) := Site L × (Fin 4 ⊕ Fin 4)
abbrev Coordinate (L : Torus) := Gen L → ℂ
abbrev Grassmann (L : Torus) := ExteriorAlgebra ℂ (Coordinate L)
abbrev grade (L : Torus) (n : ℕ) := ExteriorAlgebra.exteriorPower ℂ n (Coordinate L)

def forward (L : Torus) (x : Site L) (μ : Fin 4) : Site L :=
  x + Pi.single μ 1

def backward (L : Torus) (x : Site L) (μ : Fin 4) : Site L :=
  x - Pi.single μ 1

theorem backward_forward (L : Torus) (x : Site L) (μ : Fin 4) :
    backward L (forward L x μ) μ = x := by simp [backward, forward]

theorem forward_backward (L : Torus) (x : Site L) (μ : Fin 4) :
    forward L (backward L x μ) μ = x := by simp [backward, forward]

theorem card_generators (L : Torus) : Fintype.card (Gen L) = 8 * volume L := by
  simp [Gen, volume]; omega

/-- The actual named independent generators; the two summands are not adjoints. -/
def theta (L : Torus) (g : Gen L) : Grassmann L :=
  ExteriorAlgebra.ι ℂ (Pi.basisFun ℂ (Gen L) g)
def psi (L : Torus) (x : Site L) (i : Fin 4) := theta L (x, Sum.inl i)
def barpsi (L : Torus) (x : Site L) (i : Fin 4) := theta L (x, Sum.inr i)

theorem theta_independent (L : Torus) : LinearIndependent ℂ (theta L) := by
  apply (Pi.basisFun ℂ (Gen L)).linearIndependent.map'
  exact LinearMap.ker_eq_bot.mpr (ExteriorAlgebra.ι_leftInverse (R := ℂ)).injective

theorem theta_square_zero (L : Torus) (a : Gen L) : theta L a * theta L a = 0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem theta_odd_swap (L : Torus) (a b : Gen L) :
    theta L a * theta L b = -(theta L b * theta L a) := by
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem theta_grade (L : Torus) (a : Gen L) : theta L a ∈ grade L 1 := by
  change theta L a ∈ LinearMap.range (ExteriorAlgebra.ι ℂ) ^ 1
  rw [pow_one]
  exact LinearMap.mem_range_self _ _

/-- Coordinate pairs include overlaps and all sites. -/
def pair (L : Torus) (a b : Gen L) := theta L a * theta L b

theorem pair_grade (L : Torus) (a b : Gen L) : pair L a b ∈ grade L 2 :=
  SetLike.mul_mem_graded (theta_grade L a) (theta_grade L b)

private theorem pair_theta_commute (L : Torus) (a b c : Gen L) :
    pair L a b * theta L c = theta L c * pair L a b := by
  unfold pair
  calc
    (theta L a * theta L b) * theta L c = theta L a * (theta L b * theta L c) := mul_assoc _ _ _
    _ = theta L a * -(theta L c * theta L b) := by rw [theta_odd_swap L b c]
    _ = -(theta L a * theta L c) * theta L b := by noncomm_ring
    _ = theta L c * (theta L a * theta L b) := by rw [theta_odd_swap L a c]; simp [mul_assoc]

theorem pairs_commute (L : Torus) (a b c d : Gen L) :
    Commute (pair L a b) (pair L c d) := by
  change pair L a b * (theta L c * theta L d) = (theta L c * theta L d) * pair L a b
  rw [← mul_assoc, pair_theta_commute, mul_assoc, pair_theta_commute, ← mul_assoc]

/-- The commutative bilinear subalgebra, inside the original exterior algebra. -/
def bilinearAlgebra (L : Torus) : Subalgebra ℂ (Grassmann L) :=
  Algebra.adjoin ℂ (Set.range fun p : Gen L × Gen L => pair L p.1 p.2)

instance (L : Torus) : IsMulCommutative (bilinearAlgebra L) :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨⟨a,b⟩,rfl⟩ _ ⟨⟨c,d⟩,rfl⟩
    exact pairs_commute L a b c d)

open scoped IsMulCommutative

theorem pair_mem (L : Torus) (a b : Gen L) : pair L a b ∈ bilinearAlgebra L :=
  Algebra.subset_adjoin ⟨(a,b),rfl⟩

theorem inclusion_injective (L : Torus) :
    Function.Injective (bilinearAlgebra L).val := Subtype.val_injective

/-- No conjugation is applied to the independent barred generator. -/
def bilinear (L : Torus) (y z : Site L) (A : Matrix (Fin 4) (Fin 4) ℂ) : Grassmann L :=
  ∑ i, ∑ j, A i j • pair L (y,Sum.inr i) (z,Sum.inl j)

theorem bilinear_grade (L : Torus) (y z : Site L) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    bilinear L y z A ∈ grade L 2 := by
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (pair_grade L _ _)

theorem bilinear_mem (L : Torus) (y z : Site L) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    bilinear L y z A ∈ bilinearAlgebra L := by
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (pair_mem L _ _) _

private def bilinearMap (L : Torus) (y z : Site L) :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Grassmann L where
  toFun := bilinear L y z
  map_add' A B := by simp [bilinear, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by simp [bilinear, smul_smul, Finset.smul_sum]

/-- Source sigma-minus tuple, in source order. -/
def q : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![(-Complex.I) • σ_x, (-Complex.I) • σ_y, (-Complex.I) • σ_z, 1]

/-- Direct-sum Dirac index, followed by the explicit Fin4 reindexing. -/
def diracIndex : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv

def gamma (C : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex diracIndex diracIndex (Matrix.fromBlocks 0 (q C) (q C)ᴴ 0)

def gamma5 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex diracIndex diracIndex (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (-1))

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ
abbrev Spin4 := SU2 × SU2

/-- Independent SU(2)L and SU(2)R blocks, not a tensor product. -/
def dirac (U : Spin4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex diracIndex diracIndex (Matrix.fromBlocks U.1.val 0 0 U.2.val)

abbrev Links (L : Torus) := Site L → Fin 4 → Spin4

/-- Literal dimensionless Eq23 at alpha=1/2. All four anchors and orders are retained. -/
def coframe (L : Torus) (U : Links L) (x : Site L) (μ C : Fin 4) : Grassmann L :=
  (1/4 : ℂ) • (bilinear L x (forward L x μ) (gamma C * (dirac (U x μ))ᴴ)
    - bilinear L (forward L x μ) x (dirac (U x μ) * gamma C)
    - bilinear L x (backward L x μ) (gamma C * dirac (U (backward L x μ) μ))
    + bilinear L (backward L x μ) x ((dirac (U (backward L x μ) μ))ᴴ * gamma C))

theorem coframe_grade (L : Torus) (U : Links L) (x : Site L) (μ C : Fin 4) :
    coframe L U x μ C ∈ grade L 2 := by
  exact Submodule.smul_mem _ _ (Submodule.add_mem _
    (Submodule.sub_mem _ (Submodule.sub_mem _ (bilinear_grade L _ _ _) (bilinear_grade L _ _ _))
      (bilinear_grade L _ _ _)) (bilinear_grade L _ _ _))

theorem coframe_mem (L : Torus) (U : Links L) (x : Site L) (μ C : Fin 4) :
    coframe L U x μ C ∈ bilinearAlgebra L := by
  exact Subalgebra.smul_mem _ (Subalgebra.add_mem _
    (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (bilinear_mem L _ _ _) (bilinear_mem L _ _ _))
      (bilinear_mem L _ _ _)) (bilinear_mem L _ _ _)) _

def coframeEven (L : Torus) (U : Links L) (i : Site L × Fin 4 × Fin 4) : bilinearAlgebra L :=
  ⟨coframe L U i.1 i.2.1 i.2.2, coframe_mem L U _ _ _⟩

theorem coframes_commute (L : Torus) (U : Links L) (x y : Site L) (μ C ν D : Fin 4) :
    Commute (coframe L U x μ C) (coframe L U y ν D) := by
  exact congrArg Subtype.val (mul_comm (coframeEven L U (x,μ,C)) (coframeEven L U (y,ν,D)))

theorem grade_above_dimension (L : Torus) (n : ℕ) (hn : 8 * volume L < n) :
    grade L n = ⊥ := by
  rw [← Submodule.finrank_eq_zero, exteriorPower.finrank_eq]
  rw [Module.finrank_pi, card_generators]
  exact Nat.choose_eq_zero_of_lt hn

/-- This joint bound permits arbitrary mixtures of sites, overlaps and repeated factors. -/
theorem list_product_grade (L : Torus) (xs : List (Grassmann L))
    (h : ∀ a ∈ xs, a ∈ grade L 2) : xs.prod ∈ grade L (2 * xs.length) := by
  induction xs with
  | nil => exact SetLike.one_mem_graded (grade L)
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simpa [Nat.mul_add, Nat.add_comm] using SetLike.mul_mem_graded ha ht

theorem joint_nilpotence (L : Torus) (xs : List (Grassmann L))
    (h : ∀ a ∈ xs, a ∈ grade L 2) (hn : 4 * volume L < xs.length) : xs.prod = 0 := by
  have hm := list_product_grade L xs h
  rw [grade_above_dimension L _ (by omega)] at hm
  exact hm

/-- The bound for the actual global coframes, with no nonzero-field or link premise. -/
theorem coframe_joint_nilpotence (L : Torus) (U : Links L)
    (xs : List (Site L × Fin 4 × Fin 4)) (hn : 4 * volume L < xs.length) :
    (xs.map fun i => coframe L U i.1 i.2.1 i.2.2).prod = 0 := by
  apply joint_nilpotence L
  · intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact coframe_grade L U _ _ _
  · simpa using hn

theorem coframe_product_grade (L : Torus) (U : Links L)
    (xs : List (Site L × Fin 4 × Fin 4)) :
    (xs.map fun i => coframe L U i.1 i.2.1 i.2.2).prod ∈ grade L (2 * xs.length) := by
  have h := list_product_grade L (xs.map fun i => coframe L U i.1 i.2.1 i.2.2) (by
    intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact coframe_grade L U _ _ _)
  simpa using h

/-- Powers preserve the actual exterior grading, with degree multiplied. -/
theorem power_grade (L : Torus) (a : Grassmann L) (h : a ∈ grade L 2) (n : ℕ) :
    a ^ n ∈ grade L (2 * n) := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ, Nat.mul_add] using SetLike.mul_mem_graded ih h

/-- Finite commutative products are checked after inclusion in the exterior algebra. -/
theorem weighted_product_grade (L : Torus) {ι : Type*} (s : Finset ι)
    (f : ι → bilinearAlgebra L) (e : ι → ℕ)
    (h : ∀ i ∈ s, (f i : Grassmann L) ∈ grade L 2) :
    ((∏ i ∈ s, f i ^ e i : bilinearAlgebra L) : Grassmann L) ∈
      grade L (2 * ∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, mul_zero]; exact SetLike.one_mem_graded (grade L)
  | @insert i s hi ih =>
    have ha := power_grade L (f i) (h i (by simp)) (e i)
    have ht := ih (fun j hj => h j (by simp [hj]))
    simpa [Finset.prod_insert hi, Finset.sum_insert hi, mul_add] using SetLike.mul_mem_graded ha ht

/-- Every global mixed monomial above total degree 4V vanishes in the actual subalgebra. -/
theorem coframe_monomial_zero (L : Torus) (U : Links L)
    (d : (Site L × Fin 4 × Fin 4) →₀ ℕ) (c : ℂ)
    (hd : 4 * volume L < d.sum (fun _ n => n)) :
    MvPolynomial.aeval (coframeEven L U) (MvPolynomial.monomial d c) = 0 := by
  rw [MvPolynomial.aeval_monomial]
  suffices hz : d.prod (fun i n => coframeEven L U i ^ n) = 0 by simp [hz]
  apply Subtype.ext
  have hm := weighted_product_grade L d.support (coframeEven L U) d
    (fun i _ => coframe_grade L U _ _ _)
  rw [grade_above_dimension L _ (by change 8 * volume L < 2 * d.sum (fun _ n => n); omega)] at hm
  exact hm

/-- Explicit overlapping-pair control: a repeated left generator kills the product. -/
theorem overlapping_pairs_zero (L : Torus) (a b c : Gen L) :
    pair L a b * pair L a c = 0 := by
  unfold pair
  calc
    (theta L a * theta L b) * (theta L a * theta L c) =
      theta L a * (theta L b * theta L a) * theta L c := by noncomm_ring
    _ = -(theta L a * theta L a) * (theta L b * theta L c) := by
      rw [theta_odd_swap L b a]; noncomm_ring
    _ = 0 := by rw [theta_square_zero]; simp

/-- An actual finite exterior basis supplies the generic top-degree control. -/
def generatorIndex (L : Torus) : Gen L ≃ Fin (4 * volume L * 2) :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_fin]; rw [card_generators]; omega)

def coordinateBasis (L : Torus) : Module.Basis (Fin (4 * volume L * 2)) ℂ (Coordinate L) :=
  (Pi.basisFun ℂ (Gen L)).reindex (generatorIndex L)

def topOrder (L : Torus) : Fin (4 * volume L * 2) ↪o Fin (4 * volume L * 2) :=
  Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofCard (by simp :
      (Finset.univ : Finset (Fin (4 * volume L * 2))).card = 4 * volume L * 2))

def orderedGenerator (L : Torus) (i : Fin (4 * volume L * 2)) : Gen L :=
  (generatorIndex L).symm (topOrder L i)

def topPairs (L : Torus) : List (Grassmann L) :=
  List.ofFn fun k : Fin (4 * volume L) => pair L
    (orderedGenerator L ⟨k.val * 2, by omega⟩)
    (orderedGenerator L ⟨k.val * 2 + 1, by omega⟩)

theorem top_word_nonzero (L : Torus) :
    (List.ofFn fun i => theta L (orderedGenerator L i)).prod ≠ 0 := by
  have hn := (coordinateBasis L).ExteriorAlgebra.ne_zero
    (Finset.univ : Finset (Fin (4 * volume L * 2)))
  rw [ExteriorAlgebra.basis_apply_ofCard (coordinateBasis L) (by simp :
    (Finset.univ : Finset (Fin (4 * volume L * 2))).card = 4 * volume L * 2)] at hn
  simpa [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    coordinateBasis, orderedGenerator, topOrder, theta] using hn

theorem top_pairs_nonzero (L : Torus) : (topPairs L).prod ≠ 0 := by
  have hn := top_word_nonzero L
  rw [List.ofFn_mul, List.prod_flatten, List.map_ofFn] at hn
  simpa [topPairs, pair, List.ofFn_succ] using hn

theorem top_pairs_length (L : Torus) : (topPairs L).length = 4 * volume L := by
  simp [topPairs]

theorem top_pairs_grade (L : Torus) : (topPairs L).prod ∈ grade L (8 * volume L) := by
  have h := list_product_grade L (topPairs L) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact pair_grade L _ _)
  rw [top_pairs_length, show 2 * (4 * volume L) = 8 * volume L by omega] at h
  exact h

/-- Two even square-zero words need not have square-zero sum. -/
theorem square_pair_sum (L : Torus) (a b c d : Gen L) :
    (pair L a b + pair L c d)^2 = (2 : ℂ) • (pair L a b * pair L c d) := by
  have hab := overlapping_pairs_zero L a b b
  have hcd := overlapping_pairs_zero L c d d
  have hcomm := (pairs_commute L a b c d).eq
  rw [pow_two, add_mul, mul_add, mul_add, hab, hcd, ← hcomm]
  simp [two_smul]

private theorem four_coordinate_word_nonzero :
    (ExteriorAlgebra.ι ℂ (Pi.basisFun ℂ (Fin 4) 0) *
      ExteriorAlgebra.ι ℂ (Pi.basisFun ℂ (Fin 4) 1)) *
    (ExteriorAlgebra.ι ℂ (Pi.basisFun ℂ (Fin 4) 2) *
      ExteriorAlgebra.ι ℂ (Pi.basisFun ℂ (Fin 4) 3)) ≠ 0 := by
  let s := Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin 4)).toOrderEmbedding
  have hn := (Pi.basisFun ℂ (Fin 4)).ExteriorAlgebra.ne_zero s.val
  rw [ExteriorAlgebra.basis_apply_powersetCard _ s] at hn
  simpa [s, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    List.ofFn_succ, Matrix.vecTail, mul_assoc] using hn

/-- A coordinate projection detects every word on four distinct named generators. -/
theorem four_named_word_nonzero (L : Torus) (f : Fin 4 → Gen L)
    (hf : Function.Injective f) :
    pair L (f 0) (f 1) * pair L (f 2) (f 3) ≠ 0 := by
  let P := ExteriorAlgebra.map (LinearMap.funLeft ℂ ℂ f)
  have hp (i : Fin 4) : P (theta L (f i)) = ExteriorAlgebra.ι ℂ (Pi.basisFun ℂ (Fin 4) i) := by
    simp only [P, theta, ExteriorAlgebra.map_apply_ι]
    congr 1
    ext j
    simp [Pi.basisFun_apply, LinearMap.funLeft_apply, Pi.single_apply, hf.eq_iff]
  intro hz
  have hz' := congrArg P hz
  simp only [pair, map_mul, map_zero, hp] at hz'
  exact four_coordinate_word_nonzero hz'

/-- The square of a sum of two disjoint bilinears is nonzero, not merely a formal expansion. -/
theorem square_pair_sum_nonzero (L : Torus) (f : Fin 4 → Gen L)
    (hf : Function.Injective f) :
    (pair L (f 0) (f 1) + pair L (f 2) (f 3)) ^ 2 ≠ 0 := by
  rw [square_pair_sum]
  exact smul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (four_named_word_nonzero L f hf)

/-- Distinct sites give a nonzero mixed bilinear product before the global cutoff. -/
theorem two_site_bilinear_product_nonzero (L : Torus) (x y : Site L) (hxy : x ≠ y) :
    pair L (x,Sum.inr 0) (x,Sum.inl 0) *
      pair L (y,Sum.inr 0) (y,Sum.inl 0) ≠ 0 := by
  let f : Fin 4 → Gen L := ![(x,Sum.inr 0),(x,Sum.inl 0),(y,Sum.inr 0),(y,Sum.inl 0)]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, Matrix.cons_val, Ne.symm hxy]
  simpa [f, Matrix.cons_val, Matrix.cons_val', Matrix.vecTail] using four_named_word_nonzero L f hf

/-- The two chiral blocks are explicitly reindexed into Fin4. -/
theorem gamma_upper_block (C : Fin 4) (i j : Fin 2) :
    gamma C (diracIndex (Sum.inl i)) (diracIndex (Sum.inr j)) = q C i j := by
  simp [gamma, Matrix.reindex_apply]

theorem gamma_lower_block (C : Fin 4) (i j : Fin 2) :
    gamma C (diracIndex (Sum.inr i)) (diracIndex (Sum.inl j)) = (q C)ᴴ i j := by
  simp [gamma, Matrix.reindex_apply]

theorem dirac_left_block (U : Spin4) (i j : Fin 2) :
    dirac U (diracIndex (Sum.inl i)) (diracIndex (Sum.inl j)) = U.1.val i j := by
  simp [dirac, Matrix.reindex_apply]

theorem dirac_right_block (U : Spin4) (i j : Fin 2) :
    dirac U (diracIndex (Sum.inr i)) (diracIndex (Sum.inr j)) = U.2.val i j := by
  simp [dirac, Matrix.reindex_apply]

theorem dirac_identity : dirac (1 : Spin4) = 1 := by
  ext i j
  simp [dirac, Matrix.reindex_apply, Matrix.fromBlocks_one, Matrix.one_apply]

/-- The Dirac representation really is unitary for every actual Spin(4) link. -/
theorem dirac_unitary (U : Spin4) : dirac U * (dirac U)ᴴ = 1 := by
  have hL := Matrix.mem_unitaryGroup_iff.mp
    (Matrix.mem_specialUnitaryGroup_iff.mp U.1.property).1
  have hR := Matrix.mem_unitaryGroup_iff.mp
    (Matrix.mem_specialUnitaryGroup_iff.mp U.2.property).1
  simp only [dirac, Matrix.conjTranspose_reindex]
  let E := Matrix.reindexAlgEquiv ℂ ℂ diracIndex
  change E (Matrix.fromBlocks U.1.val 0 0 U.2.val) *
    E (Matrix.fromBlocks U.1.val 0 0 U.2.val)ᴴ = 1
  rw [← map_mul]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_zero, zero_mul, mul_zero, zero_add, add_zero]
  simp only [Matrix.star_eq_conjTranspose] at hL hR
  rw [hL, hR]
  change E (Matrix.fromBlocks 1 0 0 1) = 1
  change dirac (1 : Spin4) = 1
  exact dirac_identity

/-- Matrix dagger is used for the links and gamma blocks only. -/
theorem gamma_hermitian (C : Fin 4) : (gamma C)ᴴ = gamma C := by
  simp [gamma, Matrix.fromBlocks_conjTranspose]

/-- The source gamma ordering fixes chirality, including its sign. -/
theorem gamma_order_chirality : gamma 0 * gamma 1 * gamma 2 * gamma 3 = gamma5 := by
  let E := Matrix.reindexAlgEquiv ℂ ℂ diracIndex
  change E (Matrix.fromBlocks 0 (q 0) (q 0)ᴴ 0) *
    E (Matrix.fromBlocks 0 (q 1) (q 1)ᴴ 0) *
    E (Matrix.fromBlocks 0 (q 2) (q 2)ᴴ 0) *
    E (Matrix.fromBlocks 0 (q 3) (q 3)ᴴ 0) =
    E (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (-1))
  rw [← map_mul, ← map_mul, ← map_mul]
  apply congrArg E
  have h0 : q 0 = (-Complex.I) • σ_x := rfl
  have h1 : q 1 = (-Complex.I) • σ_y := rfl
  have h2 : q 2 = (-Complex.I) • σ_z := rfl
  have h3 : q 3 = 1 := rfl
  rw [h0, h1, h2, h3]
  simp only [Matrix.fromBlocks_multiply, zero_mul, mul_zero, zero_add, add_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [σ_x, σ_y, σ_z, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct]

/-- A concrete nonidentity compact link; each minus-identity block has determinant one. -/
def minusIdentitySU2 : SU2 := ⟨-1, by
  norm_num [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, Matrix.det_fin_two]⟩

def specialSpin4 : Spin4 := (minusIdentitySU2, 1)

theorem special_link_blocks (i j : Fin 2) :
    dirac specialSpin4 (diracIndex (Sum.inl i)) (diracIndex (Sum.inl j)) = (-1 : Matrix (Fin 2) (Fin 2) ℂ) i j ∧
    dirac specialSpin4 (diracIndex (Sum.inr i)) (diracIndex (Sum.inr j)) = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  simp [dirac_left_block, dirac_right_block, specialSpin4, minusIdentitySU2]

/-- Explicit mixed-site bound; no separate per-site cutoff is assumed. -/
theorem mixed_coframe_powers_zero (L : Torus) (U : Links L)
    (x y : Site L) (μ C ν D : Fin 4) (n m : ℕ) (hn : 4 * volume L < n + m) :
    coframe L U x μ C ^ n * coframe L U y ν D ^ m = 0 := by
  have h := SetLike.mul_mem_graded
    (power_grade L _ (coframe_grade L U x μ C) n)
    (power_grade L _ (coframe_grade L U y ν D) m)
  rw [grade_above_dimension L _ (by omega)] at h
  exact h

/-- Arbitrary matrix bilinears, not just individual coordinate pairs, obey the same bound. -/
theorem bilinear_joint_nilpotence (L : Torus)
    (xs : List (Site L × Site L × Matrix (Fin 4) (Fin 4) ℂ))
    (hn : 4 * volume L < xs.length) :
    (xs.map fun i => bilinear L i.1 i.2.1 i.2.2).prod = 0 := by
  apply joint_nilpotence L
  · intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact bilinear_grade L _ _ _
  · simpa using hn

/-- The ordinary hopping coefficient matrix over all barred/unbarred coordinates. -/
def hopping (L : Torus) (U : Links L) (x : Site L) (μ C : Fin 4)
    (y z : Site L) : Matrix (Fin 4) (Fin 4) ℂ :=
  (1/4 : ℂ) •
    ((if y = x ∧ z = forward L x μ then gamma C * (dirac (U x μ))ᴴ else 0)
    - (if y = forward L x μ ∧ z = x then dirac (U x μ) * gamma C else 0)
    - (if y = x ∧ z = backward L x μ then gamma C * dirac (U (backward L x μ) μ) else 0)
    + (if y = backward L x μ ∧ z = x then (dirac (U (backward L x μ) μ))ᴴ * gamma C else 0))

/-- On extent at least three, the three participating site anchors are distinct. -/
theorem neighbor_separation (L : Torus) (x : Site L) (μ : Fin 4)
    (hμ : 3 ≤ L.extent μ) :
    forward L x μ ≠ x ∧ backward L x μ ≠ x ∧ forward L x μ ≠ backward L x μ := by
  have h1 : (1 : ZMod (L.extent μ)) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 1 (L.extent μ)).mp (by simpa using h)
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega
  have h2 : (2 : ZMod (L.extent μ)) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 (L.extent μ)).mp (by simpa using h)
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  constructor
  · intro h
    have he := congrFun h μ
    simp [forward] at he
    exact h1 he
  constructor
  · intro h
    have he := congrFun h μ
    simp [backward] at he
    exact h1 he
  · intro h
    have he := congrFun h μ
    simp only [forward, backward, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at he
    have : (2 : ZMod (L.extent μ)) = 0 := by linear_combination he
    exact h2 this

/-- All four quarter factors, anchors, signs and matrix orders in the actual source model. -/
theorem four_hopping_coefficients (L : Torus) (U : Links L) (x : Site L) (μ C : Fin 4)
    (hμ : 3 ≤ L.extent μ) :
    hopping L U x μ C x (forward L x μ) = (1/4 : ℂ) • (gamma C * (dirac (U x μ))ᴴ) ∧
    hopping L U x μ C (forward L x μ) x = (-1/4 : ℂ) • (dirac (U x μ) * gamma C) ∧
    hopping L U x μ C x (backward L x μ) = (-1/4 : ℂ) • (gamma C * dirac (U (backward L x μ) μ)) ∧
    hopping L U x μ C (backward L x μ) x = (1/4 : ℂ) • ((dirac (U (backward L x μ) μ))ᴴ * gamma C) := by
  obtain ⟨hf,hb,hfb⟩ := neighbor_separation L x μ hμ
  simp [hopping, hf, hb, hfb, Ne.symm hf, Ne.symm hb, Ne.symm hfb, smul_neg, neg_smul, neg_div]

/-- The displayed hopping coefficients reconstruct the actual exterior-algebra coframe. -/
theorem hopping_reconstructs_coframe (L : Torus) (U : Links L) (x : Site L) (μ C : Fin 4) :
    (∑ y, ∑ z, bilinear L y z (hopping L U x μ C y z)) = coframe L U x μ C := by
  classical
  change (∑ y, ∑ z, bilinearMap L y z (hopping L U x μ C y z)) = _
  simp only [hopping, map_smul, map_add, map_sub]
  simp only [apply_ite (bilinearMap L _ _), map_zero, ite_and]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
    bilinearMap, coframe]

/-- The trivial torus is a valid positive-extent periodic regulator. -/
def oneSite : Torus := ⟨fun _ => 1, by simp⟩

instance : Subsingleton (Site oneSite) := by
  unfold Site oneSite
  infer_instance

/-- Identity group links, not zero matrices, give a genuine zero-coframe control. -/
theorem one_site_identity_coframe (x : Site oneSite) (μ C : Fin 4) :
    coframe oneSite (fun _ _ => 1) x μ C = 0 := by
  have hf : forward oneSite x μ = x := Subsingleton.elim _ _
  have hb : backward oneSite x μ = x := Subsingleton.elim _ _
  simp [coframe, hf, hb, dirac_identity]

end SKEFTHawking.ADW.FiniteGrassmannCoframe
