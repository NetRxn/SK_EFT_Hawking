import SKEFTHawking.ADW.QuaternionSU2HaarMonomial
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Anchored quaternion moments under the original link Haar measure

The coordinate powers at each site, direction and chirality are integrated
jointly. The product over these groups uses the actual nested Haar measure.
-/

set_option autoImplicit false

open MeasureTheory

namespace SKEFTHawking.ADW.QuaternionSU2Sphere

open FiniteGrassmannCoframe FiniteGrassmannDiracBerezin
open FiniteDiracQuaternionSpecialization (QuaternionVariables)

/-- Coordinates of the actual left (`false`) or right (`true`) chiral link. -/
def anchoredCoordinate {L : Torus} (U : Links L) (v : QuaternionVariables L) : ℝ :=
  coordinates (if v.2.2.1 then (U v.1 v.2.1).2.val else (U v.1 v.2.1).1.val) v.2.2.2

private def coordinateMonomial (p : Fin 4 → ℕ) (A : SU2) : ℝ :=
  ∏ i, coordinates A.val i ^ p i

/-- The joint moment of the four powers belonging to one chiral anchor. -/
noncomputable def chiralMoment (p : Fin 4 → ℕ) : ℝ := by
  classical
  exact if ∀ i, Even (p i) then
    (∏ i, ∏ j ∈ Finset.range (p i / 2), (2 * (j : ℝ) + 1)) /
      (∏ j ∈ Finset.range (∑ i, p i / 2), (4 + 2 * (j : ℝ)))
  else 0

/-- The closed chiral moment is the monomial integral against normalized SU(2) Haar. -/
theorem chiralMoment_eq_integral (p : Fin 4 → ℕ) :
    chiralMoment p = ∫ A : SU2, ∏ i, coordinates A.val i ^ p i ∂su2Haar := by
  change chiralMoment p = ∫ A : SU2, coordinateMonomial p A ∂su2Haar
  classical
  unfold chiralMoment
  split_ifs with h
  · have hp : (fun i ↦ 2 * (p i / 2)) = p :=
      funext fun i ↦ Nat.two_mul_div_two_of_even (h i)
    have hm := su2Haar_monomial_even_products fun i ↦ p i / 2
    change (∫ A : SU2, coordinateMonomial (fun i ↦ 2 * (p i / 2)) A ∂su2Haar) = _ at hm
    rw [hp] at hm
    exact hm.symm
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact (su2Haar_monomial_of_odd p i (Nat.not_even_iff_odd.mp hi)).symm

/-- The original finite link measure factors by full anchored chiral identity. -/
theorem linkHaar_monomial (L : Torus) (p : QuaternionVariables L → ℕ) :
    (∫ U : Links L, ∏ v, anchoredCoordinate U v ^ p v ∂linkHaar L) =
      ∏ x, ∏ μ, ∏ side, chiralMoment (fun i ↦ p (x, μ, side, i)) := by
  classical
  let f (x : Site L) (μ : Fin 4) (z : Spin4) :=
    coordinateMonomial (fun i ↦ p (x, μ, true, i)) z.2 *
      coordinateMonomial (fun i ↦ p (x, μ, false, i)) z.1
  have hpoint (U : Links L) :
      (∏ v, anchoredCoordinate U v ^ p v) = ∏ x, ∏ μ, f x μ (U x μ) := by
    simp_rw [Fintype.prod_prod_type, Fintype.prod_bool]
    simp [anchoredCoordinate, f, coordinateMonomial]
  simp_rw [hpoint, linkHaar]
  rw [integral_fintype_prod_eq_prod (fun x (U : Fin 4 → Spin4) ↦ ∏ μ, f x μ (U μ))]
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  rw [integral_fintype_prod_eq_prod (f x)]
  refine Finset.prod_congr rfl fun μ _ ↦ ?_
  rw [Fintype.prod_bool, chiralMoment_eq_integral, chiralMoment_eq_integral]
  simpa only [f, spin4Haar, coordinateMonomial, mul_comm] using
    (integral_prod_mul (μ := su2Haar) (ν := su2Haar)
      (coordinateMonomial fun i ↦ p (x, μ, false, i))
      (coordinateMonomial fun i ↦ p (x, μ, true, i)))


/-- The complex monomial used by the original coefficient integrals. -/
theorem linkHaar_monomial_complex (L : Torus) (p : QuaternionVariables L → ℕ) :
    (∫ U : Links L, ∏ v, (anchoredCoordinate U v : ℂ) ^ p v ∂linkHaar L) =
      ((∏ x, ∏ μ, ∏ side, chiralMoment (fun i ↦ p (x, μ, side, i))) : ℂ) := by
  calc
    _ = ∫ U : Links L, ((∏ v, anchoredCoordinate U v ^ p v : ℝ) : ℂ) ∂linkHaar L := by
      simp only [Complex.ofReal_prod, Complex.ofReal_pow]
    _ = _ := by
      rw [integral_complex_ofReal, linkHaar_monomial]
      simp only [Complex.ofReal_prod]

/-- An odd power in any one anchored coordinate kills the original link moment. -/
theorem linkHaar_monomial_of_odd (L : Torus) (p : QuaternionVariables L → ℕ)
    (v : QuaternionVariables L) (hv : Odd (p v)) :
    (∫ U : Links L, ∏ w, anchoredCoordinate U w ^ p w ∂linkHaar L) = 0 := by
  rcases v with ⟨x, μ, side, i⟩
  rw [linkHaar_monomial]
  refine Finset.prod_eq_zero (Finset.mem_univ x) ?_
  refine Finset.prod_eq_zero (Finset.mem_univ μ) ?_
  refine Finset.prod_eq_zero (Finset.mem_univ side) ?_
  rw [chiralMoment_eq_integral]
  exact su2Haar_monomial_of_odd _ i hv

/-- The even anchored link moments are products of the executable single-group ratios. -/
theorem linkHaar_monomial_even (L : Torus) (k : QuaternionVariables L → ℕ) :
    (∫ U : Links L, ∏ v, anchoredCoordinate U v ^ (2 * k v) ∂linkHaar L) =
      ∏ x, ∏ μ, ∏ side,
        (∏ i, ∏ j ∈ Finset.range (k (x, μ, side, i)), (2 * (j : ℝ) + 1)) /
          (∏ j ∈ Finset.range (∑ i, k (x, μ, side, i)), (4 + 2 * (j : ℝ))) := by
  rw [linkHaar_monomial]
  refine Finset.prod_congr rfl fun x _ ↦ Finset.prod_congr rfl fun μ _ ↦
    Finset.prod_congr rfl fun side _ ↦ ?_
  rw [chiralMoment_eq_integral, su2Haar_monomial_even_products]

/-- A chiral anchor with no powers contributes the multiplicative unit. -/
@[simp] theorem chiralMoment_zero : chiralMoment (fun _ ↦ 0) = 1 := by
  simp [chiralMoment]


/-- All powers at a single link integrate as the two independent chiral moments. -/
theorem linkHaar_at_anchor (L : Torus) (x : Site L) (μ : Fin 4) (p : Bool → Fin 4 → ℕ) :
    (∫ U : Links L, ∏ side, ∏ i, anchoredCoordinate U (x, μ, side, i) ^ p side i
      ∂linkHaar L) = ∏ side, chiralMoment (p side) := by
  classical
  let q : QuaternionVariables L → ℕ :=
    fun v ↦ if v.1 = x then if v.2.1 = μ then p v.2.2.1 v.2.2.2 else 0 else 0
  have hpoint (U : Links L) :
      (∏ v, anchoredCoordinate U v ^ q v) =
        ∏ side, ∏ i, anchoredCoordinate U (x, μ, side, i) ^ p side i := by
    simp_rw [Fintype.prod_prod_type]
    rw [Finset.prod_eq_single x]
    · rw [Finset.prod_eq_single μ]
      · simp [q]
      · intro ν _ hν
        simp [q, hν]
      · simp
    · intro y _ hy
      simp [q, hy]
    · simp
  have hmoment :
      (∏ y, ∏ ν, ∏ side, chiralMoment (fun i ↦ q (y, ν, side, i))) =
        ∏ side, chiralMoment (p side) := by
    rw [Finset.prod_eq_single x]
    · rw [Finset.prod_eq_single μ]
      · simp [q]
      · intro ν _ hν
        simp [q, hν]
      · simp
    · intro y _ hy
      simp [q, hy]
    · simp
  simpa only [hpoint, hmoment] using linkHaar_monomial L q


/-- Four copies of the left coordinate at one anchor form one joint fourth moment. -/
theorem linkHaar_left_fourth (L : Torus) (x : Site L) (μ : Fin 4) :
    (∫ U : Links L, anchoredCoordinate U (x, μ, false, 0) ^ 4 ∂linkHaar L) = 1 / 8 := by
  have h := linkHaar_at_anchor L x μ (fun side i ↦ if side = false ∧ i = 0 then 4 else 0)
  norm_num [Fintype.prod_bool, Fin.prod_univ_four, chiralMoment, Fin.forall_fin_succ,
    Nat.even_iff, Fin.sum_univ_four, Finset.prod_range_succ,
    show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide] at h
  exact h

/-- Left and right second powers at the same link integrate as independent factors. -/
theorem linkHaar_left_right_square (L : Torus) (x : Site L) (μ : Fin 4) :
    (∫ U : Links L,
      anchoredCoordinate U (x, μ, false, 0) ^ 2 * anchoredCoordinate U (x, μ, true, 0) ^ 2
        ∂linkHaar L) = 1 / 16 := by
  have h := linkHaar_at_anchor L x μ (fun _ i ↦ if i = 0 then 2 else 0)
  norm_num [Fintype.prod_bool, Fin.prod_univ_four, chiralMoment, Fin.forall_fin_succ,
    Nat.even_iff, Fin.sum_univ_four, Finset.prod_range_succ,
    show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide] at h
  simpa only [mul_comm] using h

end SKEFTHawking.ADW.QuaternionSU2Sphere
