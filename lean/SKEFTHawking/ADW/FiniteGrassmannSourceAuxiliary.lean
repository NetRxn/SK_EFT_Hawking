import SKEFTHawking.ADW.FiniteGrassmannCoframe

/-!
# Original finite coframe source polynomials

Source: Diakonov, arXiv:1109.0091v1, Eqs. 17, 24, 25, 28; original auxiliary
construction Eq. 2. The printed and closed matrix words are kept distinct.
This source construction does not assert action correspondence or the Eq. 7 integral.
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

end SKEFTHawking.ADW.FiniteGrassmannSourceAuxiliary
