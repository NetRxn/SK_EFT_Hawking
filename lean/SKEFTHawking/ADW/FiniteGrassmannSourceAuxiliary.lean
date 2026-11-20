import SKEFTHawking.ADW.FiniteGrassmannCoframe
import SKEFTHawking.ADW.GaussianGrassmannAuxiliary

/-!
# Original finite coframe source polynomials

Source: Diakonov, arXiv:1109.0091v1, Eqs. 17, 24, 25, 28; original auxiliary
construction Eq. 2. The printed and closed matrix words are kept distinct.
The original source families satisfy fixed-link G-valued local and independent-site
Gaussian Eq. 7, with integrability and explicit nested/uncurried measure transport.
The global weight is the original product of site compensation weights, using the
common 4V mixed cutoff. Action correspondence, compact-link Haar integration,
Berezin integration, nonzero partition function and physical states remain separate.
-/
noncomputable section
open scoped BigOperators IsMulCommutative
open Matrix MvPolynomial
namespace SKEFTHawking.ADW.FiniteGrassmannSourceAuxiliary
open FiniteGrassmannCoframe

abbrev D := Fin 4 × Fin 4
abbrev Polynomial := MvPolynomial D ℂ

/-- Normalized alternating Vandermonde on the four ordered labels. -/
def epsilon4 (a b c d : Fin 4) : ℂ :=
  (((b : ℂ) - a) * ((c : ℂ) - a) * ((d : ℂ) - a) *
    ((c : ℂ) - b) * ((d : ℂ) - b) * ((d : ℂ) - c)) / 12

theorem epsilon4_orientation : epsilon4 0 1 2 3 = 1 := by norm_num [epsilon4]
theorem epsilon4_odd : epsilon4 1 0 2 3 = -1 := by norm_num [epsilon4]
theorem epsilon4_swap (a b c d : Fin 4) :
    epsilon4 b a c d = -epsilon4 a b c d := by unfold epsilon4; ring
theorem epsilon4_repeat (a b c : Fin 4) : epsilon4 a a b c = 0 := by
  simp [epsilon4]

theorem epsilon4_swap_middle (a b c d : Fin 4) :
    epsilon4 a c b d = -epsilon4 a b c d := by unfold epsilon4; ring
theorem epsilon4_swap_last (a b c d : Fin 4) :
    epsilon4 a b d c = -epsilon4 a b c d := by unfold epsilon4; ring

theorem epsilon4_repeated (a b c d : Fin 4)
    (h : a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) :
    epsilon4 a b c d = 0 := by
  rcases h with h | h | h | h | h | h <;> subst_vars <;> simp [epsilon4]

/-- On Fin4, the normalized alternating expression has the epsilon values. -/
theorem epsilon4_values (a b c d : Fin 4) :
    epsilon4 a b c d = -1 ∨ epsilon4 a b c d = 0 ∨ epsilon4 a b c d = 1 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> norm_num [epsilon4]

/-- The literal printed word A B C† D†. -/
def plaquettePrinted (L : Torus) (U : Links L) (x : Site L) (k l : Fin 4) :=
  dirac (U x k) * dirac (U (forward L x k) l) *
    (dirac (U (forward L x l) k))ᴴ * (dirac (U x l))ᴴ

/-- The separately labeled closed word D† C† B A. -/
def plaquetteClosed (L : Torus) (U : Links L) (x : Site L) (k l : Fin 4) :=
  (dirac (U x l))ᴴ * (dirac (U (forward L x l) k))ᴴ *
    dirac (U (forward L x k) l) * dirac (U x k)

abbrev Curvature := Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ

/-- The ordered trace retains B1's gamma and chirality order. -/
def curvatureCoefficient (F : Curvature) (m n C D : Fin 4) : ℂ :=
  ∑ k, ∑ l, epsilon4 k l m n * trace (F k l * gamma C * gamma D * gamma5)

/-- Fixed spacetime directions: no additional reciprocal factorial. -/
def cosmological (g1 : ℂ) : Polynomial :=
  ∑ A, ∑ B, ∑ C, ∑ D,
    MvPolynomial.C (g1 * epsilon4 A B C D) *
      (X (0,A) * X (1,B) * X (2,C) * X (3,D))

/-- The quarter is an ordered prefactor, before repeated monomials accumulate. -/
def einsteinCartan (F : Curvature) (g2 : ℂ) : Polynomial :=
  ∑ m, ∑ n, ∑ C, ∑ D,
    MvPolynomial.C ((g2 / 4) * curvatureCoefficient F m n C D) * (X (m,C) * X (n,D))

/-- Positive-exponent source S, with arbitrary complex couplings.
There is no auxiliary sigma argument: the source is fixed before choosing a Gaussian measure. -/
def source (F : Curvature) (g1 g2 : ℂ) : Polynomial :=
  cosmological g1 + einsteinCartan F g2

def printedSource (L : Torus) (U : Links L) (x : Site L) (g1 g2 : ℂ) :=
  source (plaquettePrinted L U x) g1 g2
def closedSource (L : Torus) (U : Links L) (x : Site L) (g1 g2 : ℂ) :=
  source (plaquetteClosed L U x) g1 g2

theorem cosmological_homogeneous (g1 : ℂ) : (cosmological g1).IsHomogeneous 4 := by
  apply IsHomogeneous.sum; intro A _
  apply IsHomogeneous.sum; intro B _
  apply IsHomogeneous.sum; intro C _
  apply IsHomogeneous.sum; intro D _
  exact (((isHomogeneous_X ℂ (0,A)).mul (isHomogeneous_X ℂ (1,B))).mul
    (isHomogeneous_X ℂ (2,C))).mul (isHomogeneous_X ℂ (3,D)) |>.C_mul _

theorem einsteinCartan_homogeneous (F : Curvature) (g2 : ℂ) :
    (einsteinCartan F g2).IsHomogeneous 2 := by
  apply IsHomogeneous.sum; intro m _
  apply IsHomogeneous.sum; intro n _
  apply IsHomogeneous.sum; intro C _
  apply IsHomogeneous.sum; intro D _
  exact ((isHomogeneous_X ℂ (m,C)).mul (isHomogeneous_X ℂ (n,D))).C_mul _

/-- Ungrouping the curvature coefficient recovers every ordered term, with prefactor g2/4. -/
theorem einsteinCartan_ordered (F : Curvature) (g2 : ℂ) :
    einsteinCartan F g2 = ∑ m, ∑ n, ∑ C, ∑ D, ∑ k, ∑ l,
      MvPolynomial.C ((g2 / 4) * epsilon4 k l m n *
        trace (F k l * gamma C * gamma D * gamma5)) * (X (m,C) * X (n,D)) := by
  simp [einsteinCartan, curvatureCoefficient, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem source_constantCoeff (F : Curvature) (g1 g2 : ℂ) :
    (source F g1 g2).constantCoeff = 0 := by
  simp [source, cosmological, einsteinCartan]

theorem source_zero_g1 (F : Curvature) (g2 : ℂ) :
    source F 0 g2 = einsteinCartan F g2 := by simp [source, cosmological]
theorem source_zero_g2 (F : Curvature) (g1 : ℂ) :
    source F g1 0 = cosmological g1 := by simp [source, einsteinCartan]
theorem source_zero (F : Curvature) : source F 0 0 = 0 := by
  simp [source, cosmological, einsteinCartan]

theorem printedSource_constantCoeff (L : Torus) (U : Links L) (x : Site L) (g1 g2 : ℂ) :
    (printedSource L U x g1 g2).constantCoeff = 0 := source_constantCoeff _ _ _
theorem closedSource_constantCoeff (L : Torus) (U : Links L) (x : Site L) (g1 g2 : ℂ) :
    (closedSource L U x g1 g2).constantCoeff = 0 := source_constantCoeff _ _ _

/-- Local coframes take values in the proved commutative bilinear subalgebra. -/
def localCoframe (L : Torus) (U : Links L) (x : Site L) (i : D) :=
  coframeEven L U (x,i)

/-- Local to global variable renaming uses the actual site, without changing the regulator. -/
def atSite (L : Torus) (x : Site L) (P : Polynomial) :
    MvPolynomial (Site L × D) ℂ := rename (fun i ↦ (x,i)) P

theorem atSite_evaluation (L : Torus) (U : Links L) (x : Site L) (P : Polynomial) :
    aeval (coframeEven L U) (atSite L x P) = aeval (localCoframe L U x) P := by
  exact aeval_rename _ _ _

theorem cosmological_evaluation {R : Type*} [CommRing R] [Algebra ℂ R]
    (t : D → R) (g1 : ℂ) :
    aeval t (cosmological g1) = ∑ A, ∑ B, ∑ C, ∑ D,
      algebraMap ℂ R (g1 * epsilon4 A B C D) *
        (t (0,A) * t (1,B) * t (2,C) * t (3,D)) := by
  simp [cosmological]

theorem einsteinCartan_evaluation {R : Type*} [CommRing R] [Algebra ℂ R]
    (t : D → R) (F : Curvature) (g2 : ℂ) :
    aeval t (einsteinCartan F g2) = ∑ m, ∑ n, ∑ C, ∑ D,
      algebraMap ℂ R ((g2 / 4) * curvatureCoefficient F m n C D) *
        (t (m,C) * t (n,D)) := by simp [einsteinCartan]

/-- Evaluation of the original source at actual coframes, in C. -/
theorem coframe_source_evaluation (L : Torus) (U : Links L) (x : Site L)
    (F : Curvature) (g1 g2 : ℂ) :
    aeval (localCoframe L U x) (source F g1 g2) =
      (∑ A, ∑ B, ∑ C, ∑ D,
        algebraMap ℂ (bilinearAlgebra L) (g1 * epsilon4 A B C D) *
          (localCoframe L U x (0,A) * localCoframe L U x (1,B) *
            localCoframe L U x (2,C) * localCoframe L U x (3,D))) +
      ∑ m, ∑ n, ∑ C, ∑ D,
        algebraMap ℂ (bilinearAlgebra L) ((g2 / 4) * curvatureCoefficient F m n C D) *
          (localCoframe L U x (m,C) * localCoframe L U x (n,D)) := by
  rw [source, map_add, cosmological_evaluation, einsteinCartan_evaluation]

/-- The same evaluation inside the original noncommutative exterior algebra. -/
theorem coframe_source_image (L : Torus) (U : Links L) (x : Site L)
    (F : Curvature) (g1 g2 : ℂ) :
    (bilinearAlgebra L).val (aeval (localCoframe L U x) (source F g1 g2)) =
      (∑ A, ∑ B, ∑ C, ∑ D, (g1 * epsilon4 A B C D) •
        (coframe L U x 0 A * coframe L U x 1 B *
          coframe L U x 2 C * coframe L U x 3 D)) +
      ∑ m, ∑ n, ∑ C, ∑ D, ((g2 / 4) * curvatureCoefficient F m n C D) •
        (coframe L U x m C * coframe L U x n D) := by
  rw [coframe_source_evaluation]
  simp [localCoframe, coframeEven, Algebra.smul_def]

theorem cosmological_coframe_grade (L : Torus) (U : Links L) (x : Site L) (g1 : ℂ) :
    (bilinearAlgebra L).val (aeval (localCoframe L U x) (cosmological g1)) ∈ grade L 8 := by
  rw [cosmological_evaluation]
  simp only [map_sum, map_mul, AlgHom.commutes]
  apply Submodule.sum_mem; intro A _
  apply Submodule.sum_mem; intro B _
  apply Submodule.sum_mem; intro C _
  apply Submodule.sum_mem; intro D _
  rw [← map_mul, ← Algebra.smul_def]
  change (g1 * epsilon4 A B C D) •
    (coframe L U x 0 A * coframe L U x 1 B *
      coframe L U x 2 C * coframe L U x 3 D) ∈ grade L 8
  apply Submodule.smul_mem
  exact SetLike.mul_mem_graded (SetLike.mul_mem_graded
    (SetLike.mul_mem_graded (coframe_grade L U x 0 A) (coframe_grade L U x 1 B))
      (coframe_grade L U x 2 C)) (coframe_grade L U x 3 D)

theorem einsteinCartan_coframe_grade (L : Torus) (U : Links L) (x : Site L)
    (F : Curvature) (g2 : ℂ) :
    (bilinearAlgebra L).val (aeval (localCoframe L U x) (einsteinCartan F g2)) ∈
      grade L 4 := by
  rw [einsteinCartan_evaluation]
  simp only [map_sum, map_mul, AlgHom.commutes]
  apply Submodule.sum_mem; intro m _
  apply Submodule.sum_mem; intro n _
  apply Submodule.sum_mem; intro C _
  apply Submodule.sum_mem; intro D _
  rw [← map_mul, ← Algebra.smul_def]
  change ((g2 / 4) * curvatureCoefficient F m n C D) •
    (coframe L U x m C * coframe L U x n D) ∈ grade L 4
  exact Submodule.smul_mem _ _
    (SetLike.mul_mem_graded (coframe_grade L U x m C) (coframe_grade L U x n D))

theorem siteFamily_evaluation (L : Torus) (U : Links L)
    (P : Site L → Polynomial) :
    aeval (coframeEven L U) (∑ x, atSite L x (P x)) =
      ∑ x, aeval (localCoframe L U x) (P x) := by
  simp only [map_sum, atSite_evaluation]

/-- Physical inverse-spacing coframe, with no auxiliary variance parameter. -/
def ehat (L : Torus) (U : Links L) (x : Site L) (a : ℝ) (i : D) :=
  (a : ℂ)⁻¹ • coframe L U x i.1 i.2

theorem spacing_cancel_two (L : Torus) (U : Links L) (x : Site L)
    (a : ℝ) (ha : a ≠ 0) (i j : D) :
    (a : ℂ)^2 • (ehat L U x a i * ehat L U x a j) =
      coframe L U x i.1 i.2 * coframe L U x j.1 j.2 := by
  have hc : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  simp [ehat, smul_smul, ← pow_two, hc]

theorem spacing_cancel_four (L : Torus) (U : Links L) (x : Site L)
    (a : ℝ) (ha : a ≠ 0) (i j k l : D) :
    (a : ℂ)^4 • (ehat L U x a i * ehat L U x a j *
      ehat L U x a k * ehat L U x a l) =
      coframe L U x i.1 i.2 * coframe L U x j.1 j.2 *
        coframe L U x k.1 k.2 * coframe L U x l.1 l.2 := by
  have hc : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  simp only [ehat, smul_mul_assoc, mul_smul_comm, smul_smul]
  have he : (a : ℂ)^4 * (((a : ℂ)⁻¹ * (a : ℂ)⁻¹) *
      (a : ℂ)⁻¹ * (a : ℂ)⁻¹) = 1 := by field_simp
  simp only [mul_assoc] at he
  rw [he, one_smul]

theorem spacing_positive_two (L : Torus) (U : Links L) (x : Site L)
    (a : ℝ) (ha : 0 < a) (i j : D) :
    (a : ℂ)^2 • (ehat L U x a i * ehat L U x a j) =
      coframe L U x i.1 i.2 * coframe L U x j.1 j.2 :=
  spacing_cancel_two L U x a (ne_of_gt ha) i j

theorem spacing_positive_four (L : Torus) (U : Links L) (x : Site L)
    (a : ℝ) (ha : 0 < a) (i j k l : D) :
    (a : ℂ)^4 • (ehat L U x a i * ehat L U x a j *
      ehat L U x a k * ehat L U x a l) =
      coframe L U x i.1 i.2 * coframe L U x j.1 j.2 *
        coframe L U x k.1 k.2 * coframe L U x l.1 l.2 :=
  spacing_cancel_four L U x a (ne_of_gt ha) i j k l

def cosmologicalIndex : D →₀ ℕ :=
  Finsupp.single (0,0) 1 + Finsupp.single (1,1) 1 +
    Finsupp.single (2,2) 1 + Finsupp.single (3,3) 1

private theorem cosmologicalIndex_eq (A B C D : Fin 4) :
    Finsupp.single (0,A) 1 + Finsupp.single (1,B) 1 +
      Finsupp.single (2,C) 1 + Finsupp.single (3,D) 1 = cosmologicalIndex ↔
    A = 0 ∧ B = 1 ∧ C = 2 ∧ D = 3 := by
  constructor
  · intro h
    have hA : A = 0 := by
      by_contra hn
      have hh := congrArg (fun f : (Fin 4 × Fin 4) →₀ ℕ ↦ f (0,A)) h
      simp [cosmologicalIndex, hn] at hh
    have hB : B = 1 := by
      by_contra hn
      have hh := congrArg (fun f : (Fin 4 × Fin 4) →₀ ℕ ↦ f (1,B)) h
      simp [cosmologicalIndex, hn] at hh
    have hC : C = 2 := by
      by_contra hn
      have hh := congrArg (fun f : (Fin 4 × Fin 4) →₀ ℕ ↦ f (2,C)) h
      simp [cosmologicalIndex, hn] at hh
    have hD : D = 3 := by
      by_contra hn
      have hh := congrArg (fun f : (Fin 4 × Fin 4) →₀ ℕ ↦ f (3,D)) h
      simp [cosmologicalIndex, hn] at hh
    exact ⟨hA,hB,hC,hD⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩; rfl

theorem cosmological_coefficient (g1 : ℂ) :
    (cosmological g1).coeff cosmologicalIndex = g1 := by
  simp only [cosmological, coeff_sum, coeff_C_mul, X, monomial_mul, mul_one,
    coeff_monomial, cosmologicalIndex_eq]
  simp [Fin.sum_univ_succ, epsilon4_orientation]

def quadraticIndex : D →₀ ℕ := Finsupp.single (2,0) 1 + Finsupp.single (3,1) 1

private theorem quadraticIndex_eq (i j : D) :
    Finsupp.single i 1 + Finsupp.single j 1 = quadraticIndex ↔
    (i = (2,0) ∧ j = (3,1)) ∨ (i = (3,1) ∧ j = (2,0)) := by
  constructor
  · intro h
    have hor : i = (2,0) ∨ j = (2,0) := by
      by_contra hn
      push Not at hn
      have hh := congrArg (fun f : D →₀ ℕ ↦ f (2,0)) h
      simp [quadraticIndex, hn.1, hn.2] at hh
    rcases hor with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      by_contra hn
      have hh := congrArg (fun f : D →₀ ℕ ↦ f (3,1)) h
      simp [quadraticIndex, hn] at hh
    · right
      refine ⟨?_, rfl⟩
      by_contra hn
      have hh := congrArg (fun f : D →₀ ℕ ↦ f (3,1)) h
      simp [quadraticIndex, hn] at hh
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact add_comm _ _

theorem quadratic_coefficient (F : Curvature) (g2 : ℂ) :
    (einsteinCartan F g2).coeff quadraticIndex =
      (g2 / 4) * (curvatureCoefficient F 2 3 0 1 + curvatureCoefficient F 3 2 1 0) := by
  simp only [einsteinCartan, coeff_sum, coeff_C_mul, X, monomial_mul, mul_one,
    coeff_monomial, quadraticIndex_eq]
  simp [Fin.sum_univ_succ, Prod.mk.injEq, mul_add]

/-- A genuine nonidentity SU(2) matrix with eigenvalues i and -i. -/
def phaseSU2 : SU2 := ⟨!![Complex.I, 0; 0, -Complex.I], by
  constructor
  · change _ ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · norm_num [Matrix.det_fin_two]⟩

def phaseSpin4 : Spin4 := (phaseSU2, 1)

def controlTorus : Torus := ⟨fun _ ↦ 3, by intro _; norm_num⟩

/-- Only the 0-direction link at the origin is nonidentity. All values are compact links. -/
def controlLinks : Links controlTorus :=
  fun x k ↦ if x = 0 ∧ k = 0 then phaseSpin4 else 1

theorem control_plaquettePrinted01 :
    plaquettePrinted controlTorus controlLinks 0 0 1 = dirac phaseSpin4 := by
  have h0 : forward controlTorus 0 0 ≠ 0 := by decide
  have h1 : forward controlTorus 0 1 ≠ 0 := by decide
  simp [plaquettePrinted, controlLinks, h0, h1, dirac_identity]

theorem control_plaquettePrinted10 :
    plaquettePrinted controlTorus controlLinks 0 1 0 = (dirac phaseSpin4)ᴴ := by
  have h0 : forward controlTorus 0 0 ≠ 0 := by decide
  have h1 : forward controlTorus 0 1 ≠ 0 := by decide
  simp [plaquettePrinted, controlLinks, h0, h1, dirac_identity]

theorem control_plaquetteClosed01 :
    plaquetteClosed controlTorus controlLinks 0 0 1 = dirac phaseSpin4 := by
  have h0 : forward controlTorus 0 0 ≠ 0 := by decide
  have h1 : forward controlTorus 0 1 ≠ 0 := by decide
  simp [plaquetteClosed, controlLinks, h0, h1, dirac_identity]

theorem control_plaquetteClosed10 :
    plaquetteClosed controlTorus controlLinks 0 1 0 = (dirac phaseSpin4)ᴴ := by
  have h0 : forward controlTorus 0 0 ≠ 0 := by decide
  have h1 : forward controlTorus 0 1 ≠ 0 := by decide
  simp [plaquetteClosed, controlLinks, h0, h1, dirac_identity]

theorem curvatureCoefficient23 (F : Curvature) (C D : Fin 4) :
    curvatureCoefficient F 2 3 C D =
      trace (F 0 1 * gamma C * gamma D * gamma5) -
        trace (F 1 0 * gamma C * gamma D * gamma5) := by
  norm_num [curvatureCoefficient, Fin.sum_univ_succ, epsilon4, sub_eq_add_neg]

theorem curvatureCoefficient32 (F : Curvature) (C D : Fin 4) :
    curvatureCoefficient F 3 2 C D =
      -trace (F 0 1 * gamma C * gamma D * gamma5) +
        trace (F 1 0 * gamma C * gamma D * gamma5) := by
  norm_num [curvatureCoefficient, Fin.sum_univ_succ, epsilon4]

private theorem gamma01_product : gamma 0 * gamma 1 * gamma5 =
    Matrix.diagonal ![Complex.I, -Complex.I, -Complex.I, Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma, gamma5, q, diracIndex, finSumFinEquiv, Fin.addCases, Fin.castLT,
      Fin.subNat, Matrix.reindex_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, σ_x, σ_y, Matrix.conjTranspose_apply, Matrix.fromBlocks, Matrix.one_apply]

private theorem gamma10_product : gamma 1 * gamma 0 * gamma5 =
    -Matrix.diagonal ![Complex.I, -Complex.I, -Complex.I, Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gamma, gamma5, q, diracIndex, finSumFinEquiv, Fin.addCases, Fin.castLT,
      Fin.subNat, Matrix.reindex_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, σ_x, σ_y, Matrix.conjTranspose_apply, Matrix.fromBlocks, Matrix.one_apply]

private theorem phaseSpin4_matrix : dirac phaseSpin4 =
    Matrix.diagonal ![Complex.I, -Complex.I, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dirac, phaseSpin4, phaseSU2, diracIndex, finSumFinEquiv, Fin.addCases,
      Fin.castLT, Fin.subNat, Matrix.reindex_apply, Matrix.fromBlocks]

theorem phase_trace01 : trace (dirac phaseSpin4 * gamma 0 * gamma 1 * gamma5) = -2 := by
  rw [mul_assoc (dirac phaseSpin4), mul_assoc (dirac phaseSpin4),
    gamma01_product, phaseSpin4_matrix]
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]

theorem phase_dagger_trace01 :
    trace ((dirac phaseSpin4)ᴴ * gamma 0 * gamma 1 * gamma5) = 2 := by
  rw [mul_assoc (dirac phaseSpin4)ᴴ, mul_assoc (dirac phaseSpin4)ᴴ,
    gamma01_product, phaseSpin4_matrix]
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply]

theorem phase_trace10 : trace (dirac phaseSpin4 * gamma 1 * gamma 0 * gamma5) = 2 := by
  rw [mul_assoc (dirac phaseSpin4), mul_assoc (dirac phaseSpin4),
    gamma10_product, phaseSpin4_matrix]
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]

theorem phase_dagger_trace10 :
    trace ((dirac phaseSpin4)ᴴ * gamma 1 * gamma 0 * gamma5) = -2 := by
  rw [mul_assoc (dirac phaseSpin4)ᴴ, mul_assoc (dirac phaseSpin4)ᴴ,
    gamma10_product, phaseSpin4_matrix]
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply]

/-- The packed coefficient accumulates both ordered coframe monomials and both plaquettes. -/
theorem printed_control_quadratic_coefficient (g2 : ℂ) :
    (einsteinCartan (plaquettePrinted controlTorus controlLinks 0) g2).coeff
      quadraticIndex = -2 * g2 := by
  rw [quadratic_coefficient, curvatureCoefficient23, curvatureCoefficient32,
    control_plaquettePrinted01, control_plaquettePrinted10,
    phase_trace01, phase_dagger_trace01, phase_trace10, phase_dagger_trace10]
  ring

theorem closed_control_quadratic_coefficient (g2 : ℂ) :
    (einsteinCartan (plaquetteClosed controlTorus controlLinks 0) g2).coeff
      quadraticIndex = -2 * g2 := by
  rw [quadratic_coefficient, curvatureCoefficient23, curvatureCoefficient32,
    control_plaquetteClosed01, control_plaquetteClosed10,
    phase_trace01, phase_dagger_trace01, phase_trace10, phase_dagger_trace10]
  ring

theorem printed_control_quadratic_nonzero (g2 : ℂ) (hg2 : g2 ≠ 0) :
    (einsteinCartan (plaquettePrinted controlTorus controlLinks 0) g2).coeff
      quadraticIndex ≠ 0 := by
  rw [printed_control_quadratic_coefficient]
  exact mul_ne_zero (by norm_num) hg2

theorem closed_control_quadratic_nonzero (g2 : ℂ) (hg2 : g2 ≠ 0) :
    (einsteinCartan (plaquetteClosed controlTorus controlLinks 0) g2).coeff
      quadraticIndex ≠ 0 := by
  rw [closed_control_quadratic_coefficient]
  exact mul_ne_zero (by norm_num) hg2

theorem printedSource_quadratic_coefficient (g1 g2 : ℂ) :
    (printedSource controlTorus controlLinks 0 g1 g2).coeff quadraticIndex = -2 * g2 := by
  have hz := (cosmological_homogeneous g1).coeff_eq_zero
    (d := quadraticIndex) (by simp [quadraticIndex])
  simp only [printedSource, source, coeff_add, hz, zero_add]
  exact printed_control_quadratic_coefficient g2

theorem closedSource_quadratic_coefficient (g1 g2 : ℂ) :
    (closedSource controlTorus controlLinks 0 g1 g2).coeff quadraticIndex = -2 * g2 := by
  have hz := (cosmological_homogeneous g1).coeff_eq_zero
    (d := quadraticIndex) (by simp [quadraticIndex])
  simp only [closedSource, source, coeff_add, hz, zero_add]
  exact closed_control_quadratic_coefficient g2

theorem source_cosmological_coefficient (F : Curvature) (g1 g2 : ℂ) :
    (source F g1 g2).coeff cosmologicalIndex = g1 := by
  have hz := (einsteinCartan_homogeneous F g2).coeff_eq_zero
    (d := cosmologicalIndex) (by simp [cosmologicalIndex])
  simp only [source, coeff_add, hz, add_zero, cosmological_coefficient]

theorem identity_plaquettePrinted (L : Torus) (x : Site L) (k l : Fin 4) :
    plaquettePrinted L (fun _ _ ↦ 1) x k l = 1 := by
  simp [plaquettePrinted, dirac_identity]
theorem identity_plaquetteClosed (L : Torus) (x : Site L) (k l : Fin 4) :
    plaquetteClosed L (fun _ _ ↦ 1) x k l = 1 := by
  simp [plaquetteClosed, dirac_identity]

theorem identity_curvatureCoefficient (m n C D : Fin 4) :
    curvatureCoefficient (fun _ _ ↦ 1) m n C D = 0 := by
  have he : (∑ k, ∑ l, epsilon4 k l m n) = 0 := by
    fin_cases m <;> fin_cases n <;> norm_num [epsilon4, Fin.sum_univ_succ]
  simp only [curvatureCoefficient, one_mul, ← Finset.sum_mul, he, zero_mul]

theorem identity_printed_source (L : Torus) (x : Site L) (g1 g2 : ℂ) :
    printedSource L (fun _ _ ↦ 1) x g1 g2 = cosmological g1 := by
  have he : plaquettePrinted L (fun _ _ ↦ 1) x = (fun _ _ ↦ 1) := by
    funext k l; exact identity_plaquettePrinted L x k l
  simp [printedSource, source, einsteinCartan, he, identity_curvatureCoefficient]
theorem identity_closed_source (L : Torus) (x : Site L) (g1 g2 : ℂ) :
    closedSource L (fun _ _ ↦ 1) x g1 g2 = cosmological g1 := by
  have he : plaquetteClosed L (fun _ _ ↦ 1) x = (fun _ _ ↦ 1) := by
    funext k l; exact identity_plaquetteClosed L x k l
  simp [closedSource, source, einsteinCartan, he, identity_curvatureCoefficient]

theorem spacing_two_control (L : Torus) (U : Links L) (x : Site L) (i j : D) :
    (2 : ℂ)^2 • (ehat L U x 2 i * ehat L U x 2 j) =
      coframe L U x i.1 i.2 * coframe L U x j.1 j.2 :=
  spacing_positive_two L U x 2 (by norm_num) i j
theorem spacing_half_control (L : Torus) (U : Links L) (x : Site L) (i j : D) :
    (1/2 : ℂ)^2 • (ehat L U x (1/2) i * ehat L U x (1/2) j) =
      coframe L U x i.1 i.2 * coframe L U x j.1 j.2 := by
  simpa using spacing_positive_two L U x (1/2) (by norm_num) i j
theorem spacing_two_four_control (L : Torus) (U : Links L) (x : Site L) (i j k l : D) :
    (2 : ℂ)^4 • (ehat L U x 2 i * ehat L U x 2 j *
      ehat L U x 2 k * ehat L U x 2 l) =
      coframe L U x i.1 i.2 * coframe L U x j.1 j.2 *
        coframe L U x k.1 k.2 * coframe L U x l.1 l.2 :=
  spacing_positive_four L U x 2 (by norm_num) i j k l
theorem spacing_half_four_control (L : Torus) (U : Links L) (x : Site L) (i j k l : D) :
    (1/2 : ℂ)^4 • (ehat L U x (1/2) i * ehat L U x (1/2) j *
      ehat L U x (1/2) k * ehat L U x (1/2) l) =
      coframe L U x i.1 i.2 * coframe L U x j.1 j.2 *
        coframe L U x k.1 k.2 * coframe L U x l.1 l.2 := by
  simpa using spacing_positive_four L U x (1/2) (by norm_num) i j k l

/-- The source with the physical a⁴ and a² factors before inserting T = a ehat. -/
def sourceWithSpacing (L : Torus) (U : Links L) (x : Site L)
    (F : Curvature) (g1 g2 : ℂ) (a : ℝ) : Grassmann L :=
  (∑ A, ∑ B, ∑ C, ∑ D, (g1 * epsilon4 A B C D) •
    ((a : ℂ)^4 • (ehat L U x a (0,A) * ehat L U x a (1,B) *
      ehat L U x a (2,C) * ehat L U x a (3,D)))) +
  ∑ m, ∑ n, ∑ C, ∑ D, ((g2 / 4) * curvatureCoefficient F m n C D) •
    ((a : ℂ)^2 • (ehat L U x a (m,C) * ehat L U x a (n,D)))

theorem source_spacing_cancellation (L : Torus) (U : Links L) (x : Site L)
    (F : Curvature) (g1 g2 : ℂ) (a : ℝ) (ha : 0 < a) :
    sourceWithSpacing L U x F g1 g2 a =
      (bilinearAlgebra L).val (aeval (localCoframe L U x) (source F g1 g2)) := by
  rw [coframe_source_image]
  simp only [sourceWithSpacing, spacing_positive_four L U x a ha,
    spacing_positive_two L U x a ha]

theorem printed_source_spacing (L : Torus) (U : Links L) (x : Site L)
    (g1 g2 : ℂ) (a : ℝ) (ha : 0 < a) :
    sourceWithSpacing L U x (plaquettePrinted L U x) g1 g2 a =
      (bilinearAlgebra L).val (aeval (localCoframe L U x) (printedSource L U x g1 g2)) :=
  source_spacing_cancellation L U x _ g1 g2 a ha

theorem closed_source_spacing (L : Torus) (U : Links L) (x : Site L)
    (g1 g2 : ℂ) (a : ℝ) (ha : 0 < a) :
    sourceWithSpacing L U x (plaquetteClosed L U x) g1 g2 a =
      (bilinearAlgebra L).val (aeval (localCoframe L U x) (closedSource L U x g1 g2)) :=
  source_spacing_cancellation L U x _ g1 g2 a ha

theorem printed_source_global_rename (L : Torus) (U : Links L) (g1 g2 : ℂ) :
    aeval (coframeEven L U) (∑ x, atSite L x (printedSource L U x g1 g2)) =
      ∑ x, aeval (localCoframe L U x) (printedSource L U x g1 g2) :=
  siteFamily_evaluation L U _

theorem closed_source_global_rename (L : Torus) (U : Links L) (g1 g2 : ℂ) :
    aeval (coframeEven L U) (∑ x, atSite L x (closedSource L U x g1 g2)) =
      ∑ x, aeval (localCoframe L U x) (closedSource L U x g1 g2) :=
  siteFamily_evaluation L U _

open MeasureTheory ProbabilityTheory FiniteGrassmannEvaluation GaussianGrassmannAuxiliary
open scoped NNReal SKEFTHawking.ADW.FiniteGrassmannEvaluation

/-- Actual local Bochner integral, at the common global cutoff. -/
def localIntegral (L : Torus) (U : Links L) (x : Site L)
    (σ : ℝ) (v : ℝ≥0) (S : Polynomial) : Grassmann L :=
  ∫ h : D → ℝ, auxiliaryWeight σ (compensationPolynomial (4 * FiniteGrassmannCoframe.volume L) σ S) h •
    nilExp (4 * FiniteGrassmannCoframe.volume L) (linearField L (localCoframe L U x) h)
    ∂gaussianMeasure D v

theorem local_integrable (L : Torus) (U : Links L) (x : Site L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (S : Polynomial) :
    Integrable (fun h : D → ℝ ↦
      auxiliaryWeight σ (compensationPolynomial (4 * FiniteGrassmannCoframe.volume L) σ S) h •
        nilExp (4 * FiniteGrassmannCoframe.volume L) (linearField L (localCoframe L U x) h))
      (gaussianMeasure D v) :=
  integrable_weight_nilExp L _ σ hσ v hv _ _

theorem local_eq7 (L : Torus) (U : Links L) (x : Site L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Polynomial) (hS : S.constantCoeff = 0) :
    localIntegral L U x σ v S =
      ((nilExp (4 * FiniteGrassmannCoframe.volume L) (aeval (localCoframe L U x) S) :
        bilinearAlgebra L) : Grassmann L) := by
  change _ = (bilinearAlgebra L).val (nilExp _ _)
  rw [map_nilExp]
  exact (gaussian_eq7 L _ σ hσ v hv _ (local_coframe_jointZero L U x) S hS).symm

theorem printed_local_eq7 (L : Torus) (U : Links L) (x : Site L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    localIntegral L U x σ v (printedSource L U x g1 g2) =
      ((nilExp (4 * FiniteGrassmannCoframe.volume L) (aeval (localCoframe L U x)
        (printedSource L U x g1 g2)) : bilinearAlgebra L) : Grassmann L) :=
  local_eq7 L U x σ hσ v hv _ (printedSource_constantCoeff L U x g1 g2)

theorem closed_local_eq7 (L : Torus) (U : Links L) (x : Site L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    localIntegral L U x σ v (closedSource L U x g1 g2) =
      ((nilExp (4 * FiniteGrassmannCoframe.volume L) (aeval (localCoframe L U x)
        (closedSource L U x g1 g2)) : bilinearAlgebra L) : Grassmann L) :=
  local_eq7 L U x σ hσ v hv _ (closedSource_constantCoeff L U x g1 g2)

theorem nilExp_eval_sum {ι X A : Type*} [Fintype ι] [CommRing A] [Algebra ℂ A]
    (M : ℕ) (t : ι → A) (ht : JointZero M t)
    (s : Finset X) (P : X → MvPolynomial ι ℂ) (hP : ∀ x ∈ s, (P x).constantCoeff = 0) :
    nilExp M (aeval t (∑ x ∈ s, P x)) = ∏ x ∈ s, nilExp M (aeval t (P x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nilExp_zero]
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx,
      nilExp_eval_add M t ht _ _ (hP x (by simp))
        (by rw [map_sum]; exact Finset.sum_eq_zero (fun y hy ↦ hP y (by simp [hy])))]
    rw [ih (fun y hy ↦ hP y (by simp [hy]))]

theorem site_nilExp_product (L : Torus) (U : Links L)
    (S : Site L → Polynomial) (hS : ∀ x, (S x).constantCoeff = 0) :
    nilExp (4 * FiniteGrassmannCoframe.volume L) (∑ x, aeval (localCoframe L U x) (S x)) =
      ∏ x, nilExp (4 * FiniteGrassmannCoframe.volume L) (aeval (localCoframe L U x) (S x)) := by
  have he := nilExp_eval_sum (4 * FiniteGrassmannCoframe.volume L) (coframeEven L U)
    (coframe_jointZero L U) Finset.univ (fun x ↦ atSite L x (S x))
    (by intro x _; simpa [atSite] using hS x)
  simpa only [map_sum, atSite_evaluation] using he

/-- Ordered multiplication is performed in G only after the integral/image bridge. -/
theorem ordered_local_integrals (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Site L → Polynomial) (hS : ∀ x, (S x).constantCoeff = 0)
    (xs : List (Site L)) (hn : xs.Nodup) (hc : ∀ x, x ∈ xs) :
    (xs.map (fun x ↦ localIntegral L U x σ v (S x))).prod =
      ((nilExp (4 * FiniteGrassmannCoframe.volume L) (∑ x, aeval (localCoframe L U x) (S x)) :
        bilinearAlgebra L) : Grassmann L) := by
  classical
  simp_rw [local_eq7 L U _ σ hσ v hv _ (hS _)]
  have hm := map_list_prod (bilinearAlgebra L).val
    (xs.map (fun x ↦ nilExp (4 * FiniteGrassmannCoframe.volume L)
      (aeval (localCoframe L U x) (S x))))
  simp only [List.map_map, Function.comp_def, Subalgebra.coe_val] at hm
  rw [← hm]
  congr 1
  have he : xs.toFinset = Finset.univ := by ext x; simp [hc]
  rw [← List.prod_toFinset _ hn, he, ← site_nilExp_product L U S hS]

/-- Distribution in C, followed by its actual inclusion into G. -/
theorem included_product_expansion {X B : Type*} [Fintype X] [Fintype B] [DecidableEq X]
    (L : Torus) (f : X → B → ℂ) (z : X → B → bilinearAlgebra L) :
    ((∏ x, ∑ b, f x b • z x b : bilinearAlgebra L) : Grassmann L) =
      ∑ b : X → B, (∏ x, f x (b x)) •
        ((∏ x, z x (b x) : bilinearAlgebra L) : Grassmann L) := by
  classical
  change (bilinearAlgebra L).val (∏ x, ∑ b, f x b • z x b) = _
  rw [Fintype.prod_sum]
  simp only [Finset.prod_smul, map_sum, map_smul, Subalgebra.coe_val]

theorem integrable_separated_expansion {X B H : Type*} [Fintype X] [DecidableEq X]
    [Fintype B] [MeasurableSpace H] (μ : X → Measure H) [∀ x, SigmaFinite (μ x)]
    (L : Torus) (f : X → B → H → ℂ) (z : X → B → bilinearAlgebra L)
    (hf : ∀ x b, Integrable (f x b) (μ x)) :
    Integrable (fun h : X → H ↦
      ((∏ x, ∑ b, f x b (h x) • z x b : bilinearAlgebra L) : Grassmann L))
      (Measure.pi μ) := by
  classical
  simp_rw [included_product_expansion]
  exact integrable_finsetSum _ (fun b _ ↦
    (Integrable.fintype_prod (fun x ↦ hf x (b x))).smul_const _)

theorem integral_separated_expansion {X B H : Type*} [Fintype X] [DecidableEq X]
    [Fintype B] [MeasurableSpace H] (μ : X → Measure H) [∀ x, SigmaFinite (μ x)]
    (L : Torus) (f : X → B → H → ℂ) (z : X → B → bilinearAlgebra L)
    (hf : ∀ x b, Integrable (f x b) (μ x)) :
    (∫ h : X → H,
      ((∏ x, ∑ b, f x b (h x) • z x b : bilinearAlgebra L) : Grassmann L)
      ∂Measure.pi μ) =
      ((∏ x, ∑ b, (∫ h, f x b h ∂μ x) • z x b : bilinearAlgebra L) : Grassmann L) := by
  classical
  simp_rw [included_product_expansion]
  rw [integral_finsetSum _ (fun b _ ↦
    (Integrable.fintype_prod (fun x ↦ hf x (b x))).smul_const _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_smul_const, integral_fintype_prod_eq_prod]

/-- Common-budget factorization, before integration, in the actual commutative subalgebra. -/
theorem site_linear_nilExp_product (L : Torus) (U : Links L)
    (h : Site L → D → ℝ) :
    nilExp (4 * FiniteGrassmannCoframe.volume L)
      (∑ x, ∑ i, (h x i : ℂ) • localCoframe L U x i) =
      ∏ x, nilExp (4 * FiniteGrassmannCoframe.volume L)
        (∑ i, (h x i : ℂ) • localCoframe L U x i) := by
  let P : Site L → Polynomial := fun x ↦ ∑ i, MvPolynomial.C (h x i : ℂ) * X i
  have he := site_nilExp_product L U P (by intro x; simp [P])
  simpa [P, Algebra.smul_def] using he

/-- Finite local expansion expressed in C, without installing a normed ring on G. -/
theorem local_nilExp_expansion (L : Torus) (U : Links L) (x : Site L) (h : D → ℝ) :
    nilExp (4 * FiniteGrassmannCoframe.volume L)
      (∑ i, (h i : ℂ) • localCoframe L U x i) =
      ∑ β : ↥(boundedIndices (ι := D) (4 * FiniteGrassmannCoframe.volume L)),
        ((auxiliaryMonomial β.val h : ℂ) / (auxiliaryFactorial β.val : ℂ)) •
          β.val.prod (fun i e ↦ localCoframe L U x i ^ e) := by
  rw [nilExp_real_linear_multinomial]
  exact (Finset.sum_coe_sort _ (fun β ↦
    ((auxiliaryMonomial β h : ℂ) / (auxiliaryFactorial β : ℂ)) •
      β.prod (fun i e ↦ localCoframe L U x i ^ e))).symm

abbrev localIndices (L : Torus) :=
  ↥(boundedIndices (ι := D) (4 * FiniteGrassmannCoframe.volume L))

def siteMoment (L : Torus) (σ : ℝ) (S : Polynomial) (β : localIndices L)
    (h : D → ℝ) : ℂ :=
  (auxiliaryWeight σ (compensationPolynomial (4 * FiniteGrassmannCoframe.volume L) σ S) h *
    (auxiliaryMonomial β.val h : ℂ)) / (auxiliaryFactorial β.val : ℂ)

def siteVector (L : Torus) (U : Links L) (x : Site L) (β : localIndices L) :
    bilinearAlgebra L :=
  β.val.prod (fun i e ↦ localCoframe L U x i ^ e)

/-- The original product of independent site weights, with one global finite exponential. -/
def globalIntegrand (L : Torus) (U : Links L) (σ : ℝ)
    (S : Site L → Polynomial) (h : Site L → D → ℝ) : Grassmann L :=
  (∏ x, auxiliaryWeight σ
    (compensationPolynomial (4 * FiniteGrassmannCoframe.volume L) σ (S x)) (h x)) •
      nilExp (4 * FiniteGrassmannCoframe.volume L)
        (∑ x, ∑ i, (h x i : ℂ) • coframe L U x i.1 i.2)

theorem global_integrand_expansion (L : Torus) (U : Links L) (σ : ℝ)
    (S : Site L → Polynomial) (h : Site L → D → ℝ) :
    globalIntegrand L U σ S h =
      ((∏ x, ∑ β : localIndices L,
        siteMoment L σ (S x) β (h x) • siteVector L U x β :
          bilinearAlgebra L) : Grassmann L) := by
  have he :
      (∏ x, auxiliaryWeight σ
        (compensationPolynomial (4 * FiniteGrassmannCoframe.volume L) σ (S x)) (h x)) •
        nilExp (4 * FiniteGrassmannCoframe.volume L)
          (∑ x, ∑ i, (h x i : ℂ) • localCoframe L U x i) =
      ∏ x, ∑ β : localIndices L,
        siteMoment L σ (S x) β (h x) • siteVector L U x β := by
    rw [site_linear_nilExp_product, ← Finset.prod_smul]
    apply Finset.prod_congr rfl
    intro x _
    rw [local_nilExp_expansion, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro β _
    simp only [siteMoment, siteVector, smul_smul, mul_div_assoc]
  have hg := congrArg (bilinearAlgebra L).val he
  simpa only [map_smul, map_nilExp, map_sum, Subalgebra.coe_val,
    localCoframe, coframeEven, globalIntegrand] using hg

/-- Integrability uses the original product weights and finite separated moments, before evaluation. -/
theorem global_integrable (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Site L → Polynomial) :
    Integrable (globalIntegrand L U σ S)
      (Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) := by
  simp_rw [show globalIntegrand L U σ S = fun h ↦
      ((∏ x, ∑ β : localIndices L,
        siteMoment L σ (S x) β (h x) • siteVector L U x β :
          bilinearAlgebra L) : Grassmann L) from funext (global_integrand_expansion L U σ S)]
  exact integrable_separated_expansion _ L _ _
    (fun x β ↦ (integrable_auxiliaryWeight_mul_monomial σ hσ v hv _ β.val).div_const _)

theorem local_moment_expansion (L : Torus) (U : Links L) (x : Site L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Polynomial) (hS : S.constantCoeff = 0) :
    (∑ β : localIndices L, (∫ h, siteMoment L σ S β h ∂gaussianMeasure D v) •
      siteVector L U x β) =
      nilExp (4 * FiniteGrassmannCoframe.volume L) (aeval (localCoframe L U x) S) := by
  have he := local_eq7 L U x σ hσ v hv S hS
  rw [localIntegral, integral_weight_nilExp L _ σ hσ v hv] at he
  apply Subtype.val_injective
  change (bilinearAlgebra L).val _ = _
  simp only [map_sum, map_smul, Subalgebra.coe_val]
  convert he using 1
  unfold siteMoment siteVector
  simp_rw [integral_div]
  exact Finset.sum_coe_sort (boundedIndices (ι := D) (4 * FiniteGrassmannCoframe.volume L))
    (fun β ↦ ((∫ h : D → ℝ, auxiliaryWeight σ
      (compensationPolynomial (4 * FiniteGrassmannCoframe.volume L) σ S) h *
      (auxiliaryMonomial β h : ℂ) ∂gaussianMeasure D v) /
        (auxiliaryFactorial β : ℂ)) •
          ((β.prod (fun i e ↦ localCoframe L U x i ^ e) : bilinearAlgebra L) : Grassmann L))

theorem siteMoment_integrable (L : Torus) (σ : ℝ) (hσ : 0 < σ)
    (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (S : Polynomial) (β : localIndices L) :
    Integrable (siteMoment L σ S β) (gaussianMeasure D v) :=
  (integrable_auxiliaryWeight_mul_monomial σ hσ v hv _ β.val).div_const _

theorem global_integral_expansion (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Site L → Polynomial) :
    (∫ h : Site L → D → ℝ, globalIntegrand L U σ S h
      ∂Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) =
      ((∏ x, ∑ β : localIndices L,
        (∫ h, siteMoment L σ (S x) β h ∂gaussianMeasure D v) •
          siteVector L U x β : bilinearAlgebra L) : Grassmann L) := by
  simp_rw [global_integrand_expansion]
  exact integral_separated_expansion (fun _ : Site L ↦ gaussianMeasure D v) L
    (fun x β ↦ siteMoment L σ (S x) β) (siteVector L U)
    (fun x β ↦ siteMoment_integrable L σ hσ v hv (S x) β)

/-- Original independent-site Gaussian Eq7 at fixed compact links. -/
theorem global_eq7 (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Site L → Polynomial) (hS : ∀ x, (S x).constantCoeff = 0) :
    (∫ h : Site L → D → ℝ, globalIntegrand L U σ S h
      ∂Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) =
      nilExp (4 * FiniteGrassmannCoframe.volume L)
        (∑ x, ((aeval (localCoframe L U x) (S x) : bilinearAlgebra L) : Grassmann L)) := by
  rw [global_integral_expansion L U σ hσ v hv S]
  simp_rw [local_moment_expansion L U _ σ hσ v hv _ (hS _)]
  rw [← site_nilExp_product L U S hS]
  change (bilinearAlgebra L).val (nilExp _ _) = _
  simp only [map_nilExp, map_sum, Subalgebra.coe_val]

/-- Uncurrying preserves the genuine product of local Gaussian measures. -/
theorem gaussian_uncurry_preserving (L : Torus) (v : ℝ≥0) :
    MeasurePreserving (MeasurableEquiv.curry (Site L) D ℝ).symm
      (Measure.pi (fun _ : Site L ↦ gaussianMeasure D v))
      (gaussianMeasure (Site L × D) v) := by
  classical
  refine ⟨(MeasurableEquiv.curry (Site L) D ℝ).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have hp :
      (MeasurableEquiv.curry (Site L) D ℝ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun x : Site L ↦ Set.univ.pi (fun i : D ↦ s (x,i))) := by
    ext h
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun hh x i ↦ hh (x,i), fun hh i ↦ hh i.1 i.2⟩
  rw [hp, Measure.pi_pi]
  simp only [gaussianMeasure, Measure.pi_pi]
  exact (Finset.prod_product Finset.univ Finset.univ
    (fun i : Site L × D ↦ (gaussianReal 0 v) (s i))).symm.trans (by simp)

theorem gaussian_curry_preserving (L : Torus) (v : ℝ≥0) :
    MeasurePreserving (MeasurableEquiv.curry (Site L) D ℝ)
      (gaussianMeasure (Site L × D) v)
      (Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) :=
  (gaussian_uncurry_preserving L v).symm

/-- Explicit independent coordinates on Site × D, retaining each original site weight. -/
def uncurriedIntegrand (L : Torus) (U : Links L) (σ : ℝ)
    (S : Site L → Polynomial) (h : Site L × D → ℝ) : Grassmann L :=
  (∏ x, auxiliaryWeight σ
    (compensationPolynomial (4 * FiniteGrassmannCoframe.volume L) σ (S x))
      (fun i ↦ h (x,i))) •
    nilExp (4 * FiniteGrassmannCoframe.volume L)
      (∑ i, (h i : ℂ) • coframe L U i.1 i.2.1 i.2.2)

theorem uncurried_integrand_curry (L : Torus) (U : Links L) (σ : ℝ)
    (S : Site L → Polynomial) (h : Site L × D → ℝ) :
    uncurriedIntegrand L U σ S h =
      globalIntegrand L U σ S ((MeasurableEquiv.curry (Site L) D ℝ) h) := by
  unfold uncurriedIntegrand globalIntegrand
  congr 2
  exact Fintype.sum_prod_type _

theorem uncurried_global_integrable (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Site L → Polynomial) :
    Integrable (uncurriedIntegrand L U σ S) (gaussianMeasure (Site L × D) v) := by
  have he := (gaussian_curry_preserving L v).integrable_comp_emb
    (MeasurableEquiv.curry (Site L) D ℝ).measurableEmbedding
    (g := globalIntegrand L U σ S)
  have hi := he.mpr (global_integrable L U σ hσ v hv S)
  convert hi using 1
  funext h
  exact uncurried_integrand_curry L U σ S h

theorem uncurried_global_eq7 (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Site L → Polynomial) (hS : ∀ x, (S x).constantCoeff = 0) :
    (∫ h : Site L × D → ℝ, uncurriedIntegrand L U σ S h
      ∂gaussianMeasure (Site L × D) v) =
      nilExp (4 * FiniteGrassmannCoframe.volume L)
        (∑ x, ((aeval (localCoframe L U x) (S x) : bilinearAlgebra L) : Grassmann L)) := by
  simp_rw [uncurried_integrand_curry]
  rw [(gaussian_curry_preserving L v).integral_comp']
  exact global_eq7 L U σ hσ v hv S hS

theorem printed_local_integrable (L : Torus) (U : Links L) (x : Site L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    Integrable (fun h : D → ℝ ↦ auxiliaryWeight σ
      (compensationPolynomial (4 * FiniteGrassmannCoframe.volume L) σ
        (printedSource L U x g1 g2)) h •
      nilExp (4 * FiniteGrassmannCoframe.volume L)
        (linearField L (localCoframe L U x) h)) (gaussianMeasure D v) :=
  local_integrable L U x σ hσ v hv _

theorem printed_global_integrable (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    Integrable (globalIntegrand L U σ (fun x ↦ printedSource L U x g1 g2))
      (Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) :=
  global_integrable L U σ hσ v hv _

theorem printed_global_eq7 (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    (∫ h : Site L → D → ℝ,
      globalIntegrand L U σ (fun x ↦ printedSource L U x g1 g2) h
      ∂Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) =
      nilExp (4 * FiniteGrassmannCoframe.volume L)
        (∑ x, ((aeval (localCoframe L U x) (printedSource L U x g1 g2) :
          bilinearAlgebra L) : Grassmann L)) :=
  global_eq7 L U σ hσ v hv _ (fun x ↦ printedSource_constantCoeff L U x g1 g2)

theorem printed_uncurried_integrable (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    Integrable (uncurriedIntegrand L U σ (fun x ↦ printedSource L U x g1 g2))
      (gaussianMeasure (Site L × D) v) :=
  uncurried_global_integrable L U σ hσ v hv _

theorem printed_uncurried_eq7 (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    (∫ h : Site L × D → ℝ,
      uncurriedIntegrand L U σ (fun x ↦ printedSource L U x g1 g2) h
      ∂gaussianMeasure (Site L × D) v) =
      nilExp (4 * FiniteGrassmannCoframe.volume L)
        (∑ x, ((aeval (localCoframe L U x) (printedSource L U x g1 g2) :
          bilinearAlgebra L) : Grassmann L)) :=
  uncurried_global_eq7 L U σ hσ v hv _
    (fun x ↦ printedSource_constantCoeff L U x g1 g2)

theorem closed_local_integrable (L : Torus) (U : Links L) (x : Site L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    Integrable (fun h : D → ℝ ↦ auxiliaryWeight σ
      (compensationPolynomial (4 * FiniteGrassmannCoframe.volume L) σ
        (closedSource L U x g1 g2)) h •
      nilExp (4 * FiniteGrassmannCoframe.volume L)
        (linearField L (localCoframe L U x) h)) (gaussianMeasure D v) :=
  local_integrable L U x σ hσ v hv _

theorem closed_global_integrable (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    Integrable (globalIntegrand L U σ (fun x ↦ closedSource L U x g1 g2))
      (Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) :=
  global_integrable L U σ hσ v hv _

theorem closed_global_eq7 (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    (∫ h : Site L → D → ℝ,
      globalIntegrand L U σ (fun x ↦ closedSource L U x g1 g2) h
      ∂Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) =
      nilExp (4 * FiniteGrassmannCoframe.volume L)
        (∑ x, ((aeval (localCoframe L U x) (closedSource L U x g1 g2) :
          bilinearAlgebra L) : Grassmann L)) :=
  global_eq7 L U σ hσ v hv _ (fun x ↦ closedSource_constantCoeff L U x g1 g2)

theorem closed_uncurried_integrable (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    Integrable (uncurriedIntegrand L U σ (fun x ↦ closedSource L U x g1 g2))
      (gaussianMeasure (Site L × D) v) :=
  uncurried_global_integrable L U σ hσ v hv _

theorem closed_uncurried_eq7 (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ) :
    (∫ h : Site L × D → ℝ,
      uncurriedIntegrand L U σ (fun x ↦ closedSource L U x g1 g2) h
      ∂gaussianMeasure (Site L × D) v) =
      nilExp (4 * FiniteGrassmannCoframe.volume L)
        (∑ x, ((aeval (localCoframe L U x) (closedSource L U x g1 g2) :
          bilinearAlgebra L) : Grassmann L)) :=
  uncurried_global_eq7 L U σ hσ v hv _
    (fun x ↦ closedSource_constantCoeff L U x g1 g2)

theorem local_integrals_order_independent (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Site L → Polynomial) (hS : ∀ x, (S x).constantCoeff = 0)
    (xs ys : List (Site L)) (hnx : xs.Nodup) (hny : ys.Nodup)
    (hcx : ∀ x, x ∈ xs) (hcy : ∀ x, x ∈ ys) :
    (xs.map (fun x ↦ localIntegral L U x σ v (S x))).prod =
      (ys.map (fun x ↦ localIntegral L U x σ v (S x))).prod := by
  rw [ordered_local_integrals L U σ hσ v hv S hS xs hnx hcx,
    ordered_local_integrals L U σ hσ v hv S hS ys hny hcy]

theorem global_eq_ordered_local_integrals (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Site L → Polynomial) (hS : ∀ x, (S x).constantCoeff = 0)
    (xs : List (Site L)) (hn : xs.Nodup) (hc : ∀ x, x ∈ xs) :
    (∫ h, globalIntegrand L U σ S h
      ∂Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) =
      (xs.map (fun x ↦ localIntegral L U x σ v (S x))).prod := by
  rw [global_eq7 L U σ hσ v hv S hS,
    ordered_local_integrals L U σ hσ v hv S hS xs hn hc]
  change _ = (bilinearAlgebra L).val (nilExp _ _)
  simp only [map_nilExp, map_sum, Subalgebra.coe_val]

/-- Two nonzero-coupling sources can be selected without changing the global coframe family. -/
def twoSiteSource (L : Torus) (x y : Site L) (P Q : Polynomial) (z : Site L) :
    Polynomial := if z = x then P else if z = y then Q else 0

theorem twoSiteSource_constantCoeff (L : Torus) (x y : Site L)
    (P Q : Polynomial) (hP : P.constantCoeff = 0) (hQ : Q.constantCoeff = 0) :
    ∀ z, (twoSiteSource L x y P Q z).constantCoeff = 0 := by
  intro z
  unfold twoSiteSource
  split_ifs <;> simp_all

theorem two_site_source_sum (L : Torus) (U : Links L) (x y : Site L) (hxy : x ≠ y)
    (P Q : Polynomial) :
    (∑ z, aeval (localCoframe L U z) (twoSiteSource L x y P Q z)) =
      aeval (localCoframe L U x) P + aeval (localCoframe L U y) Q := by
  classical
  have hp (z : Site L) :
      aeval (localCoframe L U z) (twoSiteSource L x y P Q z) =
        if z = x then aeval (localCoframe L U z) P
        else if z = y then aeval (localCoframe L U z) Q else 0 := by
    by_cases hx : z = x <;> by_cases hy : z = y <;> simp [twoSiteSource, hx, hy, Ne.symm hxy]
  simp_rw [hp]
  simp [Finset.sum_ite, Finset.filter_eq', Ne.symm hxy]

/-- Genuine independent-site integral compared with the two actual local G integrals. -/
theorem two_site_original_product (L : Torus) (U : Links L)
    (x y : Site L) (hxy : x ≠ y)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (P Q : Polynomial) (hP : P.constantCoeff = 0) (hQ : Q.constantCoeff = 0) :
    (∫ h : Site L → D → ℝ, globalIntegrand L U σ (twoSiteSource L x y P Q) h
      ∂Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) =
      localIntegral L U x σ v P * localIntegral L U y σ v Q := by
  rw [global_eq7 L U σ hσ v hv _ (twoSiteSource_constantCoeff L x y P Q hP hQ),
    local_eq7 L U x σ hσ v hv P hP, local_eq7 L U y σ hσ v hv Q hQ]
  have he := site_nilExp_product L U (twoSiteSource L x y P Q)
    (twoSiteSource_constantCoeff L x y P Q hP hQ)
  rw [two_site_source_sum L U x y hxy P Q] at he
  have hp : (∏ z, nilExp (4 * FiniteGrassmannCoframe.volume L)
      (aeval (localCoframe L U z) (twoSiteSource L x y P Q z))) =
      nilExp (4 * FiniteGrassmannCoframe.volume L) (aeval (localCoframe L U x) P) *
      nilExp (4 * FiniteGrassmannCoframe.volume L) (aeval (localCoframe L U y) Q) := by
    have hp (z : Site L) :
        nilExp (4 * FiniteGrassmannCoframe.volume L)
          (aeval (localCoframe L U z) (twoSiteSource L x y P Q z)) =
        if z = x then nilExp (4 * FiniteGrassmannCoframe.volume L)
          (aeval (localCoframe L U z) P)
        else if z = y then nilExp (4 * FiniteGrassmannCoframe.volume L)
          (aeval (localCoframe L U z) Q) else 1 := by
      by_cases hx : z = x <;> by_cases hy : z = y <;> simp [twoSiteSource, hx, hy, Ne.symm hxy]
    simp_rw [hp]
    simp [Finset.prod_ite, Finset.filter_eq', Ne.symm hxy]
  rw [hp] at he
  have hs := congrArg (bilinearAlgebra L).val (two_site_source_sum L U x y hxy P Q)
  simp only [map_sum, map_add, Subalgebra.coe_val] at hs
  rw [hs]
  change _ = (bilinearAlgebra L).val (nilExp _ _) * (bilinearAlgebra L).val (nilExp _ _)
  rw [← map_mul, ← he]
  simp only [map_nilExp, map_add, Subalgebra.coe_val]

/-- Each site has its own arbitrary real field; no diagonal restriction is imposed. -/
def twoSiteField (L : Torus) (x y : Site L) (hx hy : D → ℝ) (z : Site L) : D → ℝ :=
  if z = x then hx else if z = y then hy else 0

theorem two_site_fields_independent (L : Torus) (x y : Site L) (hxy : x ≠ y)
    (hx hy : D → ℝ) :
    twoSiteField L x y hx hy x = hx ∧ twoSiteField L x y hx hy y = hy := by
  simp [twoSiteField, Ne.symm hxy]

/-- Pointwise comparison uses the same global coframes with two independent auxiliary fields. -/
theorem two_site_linear_comparison (L : Torus) (U : Links L)
    (x y : Site L) (hxy : x ≠ y) (hx hy : D → ℝ) :
    (∑ z, ∑ i, (twoSiteField L x y hx hy z i : ℂ) • coframe L U z i.1 i.2) =
      (∑ i, (hx i : ℂ) • coframe L U x i.1 i.2) +
      (∑ i, (hy i : ℂ) • coframe L U y i.1 i.2) := by
  classical
  have hp (z : Site L) :
      (∑ i, (twoSiteField L x y hx hy z i : ℂ) • coframe L U z i.1 i.2) =
        if z = x then ∑ i, (hx i : ℂ) • coframe L U z i.1 i.2
        else if z = y then ∑ i, (hy i : ℂ) • coframe L U z i.1 i.2 else 0 := by
    by_cases hzx : z = x <;> by_cases hzy : z = y <;> simp [twoSiteField, hzx, hzy, Ne.symm hxy]
  simp_rw [hp]
  simp [Finset.sum_ite, Finset.filter_eq', Ne.symm hxy]

theorem two_site_common_cutoff (L : Torus) (U : Links L)
    (x y : Site L) (hx hy : D → ℝ) (k l : ℕ)
    (hkl : 4 * FiniteGrassmannCoframe.volume L < k + l) :
    (∑ i, (hx i : ℂ) • localCoframe L U x i) ^ k *
      (∑ i, (hy i : ℂ) • localCoframe L U y i) ^ l = 0 := by
  let P : Polynomial := ∑ i, MvPolynomial.C (hx i : ℂ) * X i
  let Q : Polynomial := ∑ i, MvPolynomial.C (hy i : ℂ) * X i
  have he := coframe_positive_mixed_zero L U
    (atSite L x P) (atSite L y Q) (by simp [atSite, P]) (by simp [atSite, Q]) k l hkl
  simpa [atSite_evaluation, P, Q, Algebra.smul_def] using he

theorem printed_two_site_original_product (L : Torus) (U : Links L)
    (x y : Site L) (hxy : x ≠ y)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (gx1 gx2 gy1 gy2 : ℂ) :
    (∫ h : Site L → D → ℝ,
      globalIntegrand L U σ (twoSiteSource L x y
        (printedSource L U x gx1 gx2) (printedSource L U y gy1 gy2)) h
      ∂Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) =
      localIntegral L U x σ v (printedSource L U x gx1 gx2) *
        localIntegral L U y σ v (printedSource L U y gy1 gy2) :=
  two_site_original_product L U x y hxy σ hσ v hv _ _
    (printedSource_constantCoeff L U x gx1 gx2)
    (printedSource_constantCoeff L U y gy1 gy2)

theorem closed_two_site_original_product (L : Torus) (U : Links L)
    (x y : Site L) (hxy : x ≠ y)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (gx1 gx2 gy1 gy2 : ℂ) :
    (∫ h : Site L → D → ℝ,
      globalIntegrand L U σ (twoSiteSource L x y
        (closedSource L U x gx1 gx2) (closedSource L U y gy1 gy2)) h
      ∂Measure.pi (fun _ : Site L ↦ gaussianMeasure D v)) =
      localIntegral L U x σ v (closedSource L U x gx1 gx2) *
        localIntegral L U y σ v (closedSource L U y gy1 gy2) :=
  two_site_original_product L U x y hxy σ hσ v hv _ _
    (closedSource_constantCoeff L U x gx1 gx2)
    (closedSource_constantCoeff L U y gy1 gy2)

theorem one_site_original_weighted_integral (x : Site oneSite)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (F : Curvature) (g1 g2 : ℂ) :
    localIntegral oneSite (fun _ _ ↦ 1) x σ v (source F g1 g2) = 1 := by
  rw [local_eq7 oneSite _ x σ hσ v hv _ (source_constantCoeff F g1 g2)]
  have ht : localCoframe oneSite (fun _ _ ↦ 1) x =
      (fun _ : D ↦ (0 : bilinearAlgebra oneSite)) := by
    funext i
    apply Subtype.val_injective
    exact one_site_identity_coframe x i.1 i.2
  rw [ht, eval_zero_family, source_constantCoeff]
  simp

theorem source_zero_couplings_integral (L : Torus) (U : Links L) (x : Site L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (F : Curvature) :
    localIntegral L U x σ v (source F 0 0) = 1 := by
  rw [local_eq7 L U x σ hσ v hv _ (source_constantCoeff F 0 0), source_zero]
  simp

/-- The Gaussian scale changes the original weight and measure, while preserving the actual G value. -/
theorem original_source_two_scales (L : Torus) (U : Links L) (x : Site L)
    (F : Curvature) (g1 g2 : ℂ) :
    localIntegral L U x 2 4 (source F g1 g2) =
      localIntegral L U x (1/2) (1/4) (source F g1 g2) := by
  rw [local_eq7 L U x 2 (by norm_num) 4 (by norm_num) _ (source_constantCoeff F g1 g2),
    local_eq7 L U x (1/2) (by norm_num) (1/4) (by norm_num) _
      (source_constantCoeff F g1 g2)]

theorem original_global_two_scales (L : Torus) (U : Links L)
    (S : Site L → Polynomial) (hS : ∀ x, (S x).constantCoeff = 0) :
    (∫ h, globalIntegrand L U 2 S h
      ∂Measure.pi (fun _ : Site L ↦ gaussianMeasure D 4)) =
      ∫ h, globalIntegrand L U (1/2) S h
        ∂Measure.pi (fun _ : Site L ↦ gaussianMeasure D (1/4)) := by
  rw [global_eq7 L U 2 (by norm_num) 4 (by norm_num) S hS,
    global_eq7 L U (1/2) (by norm_num) (1/4) (by norm_num) S hS]

/-- Three sites in direction zero; the other periods are one. -/
abbrev threeLine : Torus := ⟨![3,1,1,1], by intro μ; fin_cases μ <;> norm_num⟩
def lineSite (k : ZMod 3) : Site threeLine := Pi.single 0 k
def retainedGenerators : Fin 4 → Gen threeLine :=
  ![(lineSite 0, Sum.inr 0), (lineSite 1, Sum.inl 2),
    (lineSite 1, Sum.inr 0), (lineSite 2, Sum.inl 2)]
abbrev FourExterior := ExteriorAlgebra ℂ (Fin 4 → ℂ)
def eta (i : Fin 4) : FourExterior := ExteriorAlgebra.ι ℂ (Pi.basisFun ℂ (Fin 4) i)
def controlProjection : Grassmann threeLine →ₐ[ℂ] FourExterior :=
  ExteriorAlgebra.map (LinearMap.funLeft ℂ ℂ retainedGenerators)

theorem control_projection_theta (g : Gen threeLine) :
    controlProjection (theta threeLine g) =
      ∑ i : Fin 4, (if retainedGenerators i = g then (1 : ℂ) else 0) • eta i := by
  unfold controlProjection theta
  rw [ExteriorAlgebra.map_apply_ι,
    ← (Pi.basisFun ℂ (Fin 4)).sum_repr ((LinearMap.funLeft ℂ ℂ retainedGenerators)
      (Pi.basisFun ℂ (Gen threeLine) g))]
  simp only [map_sum, map_smul, Pi.basisFun_repr, LinearMap.funLeft_apply,
    Pi.basisFun_apply, Pi.single_apply, eta]

theorem line_forward (k : ZMod 3) :
    forward threeLine (lineSite k) 0 = lineSite (k + 1) := by
  exact (Pi.single_add (f := fun μ : Fin 4 ↦ ZMod (threeLine.extent μ)) 0 k 1).symm

theorem line_backward (k : ZMod 3) :
    backward threeLine (lineSite k) 0 = lineSite (k - 1) := by
  exact (Pi.single_sub (f := fun μ : Fin 4 ↦ ZMod (threeLine.extent μ)) 0 k 1).symm

theorem lineSite_injective : Function.Injective lineSite := by
  intro k l h
  have he := congrFun h 0
  simpa [lineSite, threeLine] using he

theorem control_projection_bilinear (k l : ZMod 3)
    (A : Matrix (Fin 4) (Fin 4) ℂ) :
    controlProjection (bilinear threeLine (lineSite k) (lineSite l) A) =
      A 0 2 •
        (((if k = 0 then eta 0 else 0) + (if k = 1 then eta 2 else 0)) *
          ((if l = 1 then eta 1 else 0) + (if l = 2 then eta 3 else 0))) := by
  simp only [bilinear, pair, map_sum, map_smul, map_mul, control_projection_theta]
  have r0 : retainedGenerators 0 = (lineSite 0, Sum.inr 0) := rfl
  have r1 : retainedGenerators 1 = (lineSite 1, Sum.inl 2) := rfl
  have r2 : retainedGenerators 2 = (lineSite 1, Sum.inr 0) := rfl
  have r3 : retainedGenerators 3 = (lineSite 2, Sum.inl 2) := rfl
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h21 : (2 : Fin 4) ≠ 1 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  simp only [Fin.sum_univ_four, r0, r1, r2, r3, Prod.mk.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, Sum.inl.injEq, Sum.inr.injEq,
    lineSite_injective.eq_iff, h01, h02, h03, h20, h21, h23,
    and_false, and_true, if_false, zero_smul,
    zero_add, add_zero, mul_zero, zero_mul, smul_zero]
  have h0 : ((0 : ZMod 3) = k) = (k = 0) := propext eq_comm
  have h1 : ((1 : ZMod 3) = k) = (k = 1) := propext eq_comm
  have h2 : ((1 : ZMod 3) = l) = (l = 1) := propext eq_comm
  have h3 : ((2 : ZMod 3) = l) = (l = 2) := propext eq_comm
  simp only [h0, h1, h2, h3, ite_smul, one_smul, zero_smul]

theorem control_gamma302 : gamma 3 0 2 = 1 := by rfl

theorem control_projection_coframe_zero :
    controlProjection (coframe threeLine (fun _ _ ↦ 1) (lineSite 0) 0 3) =
      (1/4 : ℂ) • (eta 0 * eta 1 - eta 0 * eta 3) := by
  simp only [coframe, dirac_identity, map_smul, map_add, map_sub,
    Matrix.conjTranspose_one, mul_one, one_mul, line_forward, line_backward]
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  have hm1 : (-1 : ZMod 3) = 2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h10 : (1 : ZMod 3) ≠ 0 := by decide
  norm_num only [control_projection_bilinear, control_gamma302,
    h02, h12, h20, h21, hm1, h01, h10, ite_true, ite_false,
    zero_add, add_zero, zero_mul, mul_zero, zero_smul, one_smul, sub_zero, smul_add]
  simp only [hm1, h21, ite_true, ite_false, zero_add]

theorem control_projection_coframe_one :
    controlProjection (coframe threeLine (fun _ _ ↦ 1) (lineSite 1) 0 3) =
      (1/4 : ℂ) • (eta 2 * eta 3 + eta 0 * eta 1) := by
  simp only [coframe, dirac_identity, map_smul, map_add, map_sub,
    Matrix.conjTranspose_one, mul_one, one_mul, line_forward, line_backward]
  have h02 : (0 : ZMod 3) ≠ 2 := by decide
  have h12 : (1 : ZMod 3) ≠ 2 := by decide
  have h20 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  have hm1 : (-1 : ZMod 3) = 2 := by decide
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  have h10 : (1 : ZMod 3) ≠ 0 := by decide
  norm_num only [control_projection_bilinear, control_gamma302,
    h02, h12, h20, h21, hm1, h01, h10, ite_true, ite_false,
    zero_add, add_zero, zero_mul, mul_zero, zero_smul, one_smul, sub_zero, smul_add]

theorem eta_square (i : Fin 4) : eta i * eta i = 0 := ExteriorAlgebra.ι_sq_zero _
theorem eta_swap (i j : Fin 4) : eta i * eta j = -(eta j * eta i) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem eta_overlap_left (i j k : Fin 4) : eta i * eta j * (eta i * eta k) = 0 := by
  calc
    _ = -(eta i * eta i * (eta j * eta k)) := by
      rw [mul_assoc (eta i) (eta j), ← mul_assoc (eta j) (eta i) (eta k), eta_swap j i]
      noncomm_ring
    _ = 0 := by rw [eta_square]; simp

theorem eta_overlap_right (i j k : Fin 4) : eta i * eta j * (eta k * eta j) = 0 := by
  calc
    _ = -(eta i * (eta j * eta j) * eta k) := by
      rw [eta_swap k j]
      noncomm_ring
    _ = 0 := by rw [eta_square]; simp

theorem four_eta_word_nonzero : eta 0 * eta 1 * (eta 2 * eta 3) ≠ 0 := by
  let s := Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin 4)).toOrderEmbedding
  have hn := (Pi.basisFun ℂ (Fin 4)).ExteriorAlgebra.ne_zero s.val
  rw [ExteriorAlgebra.basis_apply_powersetCard _ s] at hn
  simpa [s, eta, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    List.ofFn_succ, Matrix.vecTail, mul_assoc] using hn

/-- An algebraic projection detects a surviving product of ACTUAL coframes at distinct sites. -/
theorem actual_two_site_projection :
    controlProjection
      (coframe threeLine (fun _ _ ↦ 1) (lineSite 0) 0 3 *
        coframe threeLine (fun _ _ ↦ 1) (lineSite 1) 0 3) =
      (1/16 : ℂ) • (eta 0 * eta 1 * (eta 2 * eta 3)) := by
  rw [map_mul, control_projection_coframe_zero, control_projection_coframe_one]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have he : (eta 0 * eta 1 - eta 0 * eta 3) * (eta 2 * eta 3 + eta 0 * eta 1) =
      eta 0 * eta 1 * (eta 2 * eta 3) := by
    rw [sub_mul, mul_add, mul_add, eta_overlap_left, eta_overlap_right, eta_overlap_left]
    simp
  rw [he]
  norm_num

theorem actual_two_site_coframe_product_nonzero :
    coframe threeLine (fun _ _ ↦ 1) (lineSite 0) 0 3 *
      coframe threeLine (fun _ _ ↦ 1) (lineSite 1) 0 3 ≠ 0 := by
  intro hz
  have hp := congrArg controlProjection hz
  rw [actual_two_site_projection, map_zero] at hp
  exact (smul_ne_zero (by norm_num : (1/16 : ℂ) ≠ 0) four_eta_word_nonzero) hp

theorem actual_control_sites_distinct : lineSite 0 ≠ lineSite 1 := by
  exact fun h ↦ zero_ne_one (lineSite_injective h)

/-- Sparse fields select an actual gamma3 coframe, with independent real amplitudes. -/
theorem actual_sparse_field (k : ZMod 3) (a : ℝ) :
    (∑ i : D, (((Pi.single (0,3) a : D → ℝ) i : ℝ) : ℂ) •
      coframe threeLine (fun _ _ ↦ 1) (lineSite k) i.1 i.2) =
      (a : ℂ) • coframe threeLine (fun _ _ ↦ 1) (lineSite k) 0 3 := by
  simp [Pi.single_apply]

/-- Independent auxiliary fields see a surviving mixed term in the SAME actual global coframes. -/
theorem actual_independent_field_mixed_nonzero (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∑ i : D, (((Pi.single (0,3) a : D → ℝ) i : ℝ) : ℂ) •
      coframe threeLine (fun _ _ ↦ 1) (lineSite 0) i.1 i.2) *
    (∑ i : D, (((Pi.single (0,3) b : D → ℝ) i : ℝ) : ℂ) •
      coframe threeLine (fun _ _ ↦ 1) (lineSite 1) i.1 i.2) ≠ 0 := by
  rw [actual_sparse_field, actual_sparse_field, smul_mul_assoc, mul_smul_comm, smul_smul]
  exact smul_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) (Complex.ofReal_ne_zero.mpr hb))
    actual_two_site_coframe_product_nonzero

theorem actual_independent_two_site_field (a b : ℝ) :
    (∑ z, ∑ i : D,
      (twoSiteField threeLine (lineSite 0) (lineSite 1)
        (Pi.single (0,3) a) (Pi.single (0,3) b) z i : ℂ) •
          coframe threeLine (fun _ _ ↦ 1) z i.1 i.2) =
      (a : ℂ) • coframe threeLine (fun _ _ ↦ 1) (lineSite 0) 0 3 +
      (b : ℂ) • coframe threeLine (fun _ _ ↦ 1) (lineSite 1) 0 3 := by
  rw [two_site_linear_comparison _ _ _ _ actual_control_sites_distinct,
    actual_sparse_field, actual_sparse_field]

theorem local_integral_in_image (L : Torus) (U : Links L) (x : Site L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (S : Polynomial) (hS : S.constantCoeff = 0) :
    ∃ c : bilinearAlgebra L, (c : Grassmann L) = localIntegral L U x σ v S :=
  ⟨_, (local_eq7 L U x σ hσ v hv S hS).symm⟩

theorem local_integrals_commute (L : Torus) (U : Links L) (x y : Site L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2)
    (P Q : Polynomial) (hP : P.constantCoeff = 0) (hQ : Q.constantCoeff = 0) :
    Commute (localIntegral L U x σ v P) (localIntegral L U y σ v Q) := by
  rw [local_eq7 L U x σ hσ v hv P hP, local_eq7 L U y σ hσ v hv Q hQ]
  exact (Commute.all
    (nilExp (4 * FiniteGrassmannCoframe.volume L) (aeval (localCoframe L U x) P))
    (nilExp (4 * FiniteGrassmannCoframe.volume L) (aeval (localCoframe L U y) Q))).map
      (bilinearAlgebra L).val

theorem printed_ordered_local_integrals (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ)
    (xs : List (Site L)) (hn : xs.Nodup) (hc : ∀ x, x ∈ xs) :
    (xs.map (fun x ↦ localIntegral L U x σ v (printedSource L U x g1 g2))).prod =
      ((nilExp (4 * FiniteGrassmannCoframe.volume L)
        (∑ x, aeval (localCoframe L U x) (printedSource L U x g1 g2)) :
          bilinearAlgebra L) : Grassmann L) :=
  ordered_local_integrals L U σ hσ v hv _
    (fun x ↦ printedSource_constantCoeff L U x g1 g2) xs hn hc

theorem closed_ordered_local_integrals (L : Torus) (U : Links L)
    (σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) (hv : (v : ℝ) = σ ^ 2) (g1 g2 : ℂ)
    (xs : List (Site L)) (hn : xs.Nodup) (hc : ∀ x, x ∈ xs) :
    (xs.map (fun x ↦ localIntegral L U x σ v (closedSource L U x g1 g2))).prod =
      ((nilExp (4 * FiniteGrassmannCoframe.volume L)
        (∑ x, aeval (localCoframe L U x) (closedSource L U x g1 g2)) :
          bilinearAlgebra L) : Grassmann L) :=
  ordered_local_integrals L U σ hσ v hv _
    (fun x ↦ closedSource_constantCoeff L U x g1 g2) xs hn hc

end SKEFTHawking.ADW.FiniteGrassmannSourceAuxiliary
