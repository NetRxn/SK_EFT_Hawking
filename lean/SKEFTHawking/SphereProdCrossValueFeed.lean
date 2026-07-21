/-
# Phase 5q.H — the hcross FEED: the ±1 reducer relaxation and the fed `s2s2_hyp`

The consumer wiring of the cross-value witness (`SphereProdCrossWitnessInt`) into the Gram-pin
reducers (`SphereProdGramPinReduce`). Three pieces:

* `intCongr_eps_hyp` — the ±1 REDUCER RELAXATION at the lattice level: `!![0,ε;ε,0] ≅ Hyp` for any
  unit `ε` (change of basis `diag(1,ε)`). The `= 1` normalization demanded by the original reducer
  (`crossFamily_gram_eq_hyp`) is NOT needed for the congruence-shaped `s2s2_hyp`.
* `crossFamily_gram_intCongr_of_isUnit` — the family Gram matrix at ANY class `x` whose cross value
  is a unit is integrally congruent to the hyperbolic pin (diagonal zeros + symmetry are
  unconditional; the off-diagonal only needs `±1`).
* `sphereProd_s2s2_hyp_of_congr_of_hemiUnit` — **the fed consumer statement**: the S²×S²
  hyperbolic pin `s2s2_hyp` conditional ONLY on (i) the robust basis-ID congruence and (ii) the
  hemisphere-class unit — the Eilenberg–Zilber cross value is DISCHARGED through the witness
  chain (`hcross_pm_of_hemiUnit`), no longer a hypothesis.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereProdCrossWitnessInt
import SKEFTHawking.SphereProdGramPinReduce

namespace SKEFTHawking.SphereProdCrossValueFeed

open SKEFTHawking SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularLineMinusPointInt (topSphereIsoInt)
open SKEFTHawking.SphereProdHFourInt (sphereProdIntFundClassHonest)
open SKEFTHawking.SphereProdCrossInt (alphaOf betaOf crossFamily)
open SKEFTHawking.SphereWitnessTowerInt (sphereProdIntH2Basis)
open SKEFTHawking.SpinSigmaRoute (sphereProdFormDatum sphereProdFormDatum_hyp_pin)
open SKEFTHawking.SphereProdCrossWitnessInt (xS hemiClass hcross_pm_of_hemiUnit)

/-- **The ±1 reducer relaxation, lattice level**: `!![0,ε;ε,0]` is integrally congruent to the
hyperbolic plane for ANY unit `ε` — change of basis `diag(1,ε)`, determinant `ε`. -/
theorem intCongr_eps_hyp (ε : ℤ) (hu : IsUnit ε) : IntCongr !![0, ε; ε, 0] Hyp := by
  have hε : ε * ε = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h <;> subst h <;> norm_num
  refine ⟨!![1, 0; 0, ε], ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    simpa using hu
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Hyp, Matrix.mul_apply, Fin.sum_univ_two, hε]

/-- **The family Gram matrix is congruent to the pin from a UNIT cross value.** The two diagonal
zeros and symmetry are unconditional; a `±1` off-diagonal suffices for integral congruence to
`Hyp` — the honest relaxation of `crossFamily_gram_eq_hyp`'s `= 1` normalization. -/
theorem crossFamily_gram_intCongr_of_isUnit (x : Cohomology (Sph 2) 2)
    (hu : IsUnit (interFormInt sphereProdIntFundClassHonest (alphaOf x) (betaOf x))) :
    IntCongr
      (Matrix.of fun i j => interFormInt sphereProdIntFundClassHonest
        (crossFamily x i) (crossFamily x j))
      sphereProdFormDatum := by
  set ε := interFormInt sphereProdIntFundClassHonest (alphaOf x) (betaOf x) with hεdef
  have hG : (Matrix.of fun i j => interFormInt sphereProdIntFundClassHonest
      (crossFamily x i) (crossFamily x j)) = !![0, ε; ε, 0] := by
    have hαα : interFormInt sphereProdIntFundClassHonest (alphaOf x) (alphaOf x) = 0 :=
      SphereProdGramInt.interFormInt_honest_fst_eq_zero x x
    have hββ : interFormInt sphereProdIntFundClassHonest (betaOf x) (betaOf x) = 0 :=
      SphereProdGramInt.interFormInt_honest_snd_eq_zero x x
    have hβα : interFormInt sphereProdIntFundClassHonest (betaOf x) (alphaOf x) = ε := by
      rw [hεdef, interFormInt_symm]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [crossFamily, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.empty_val']
    · exact hαα
    · exact hεdef.symm
    · exact hβα
    · exact hββ
  rw [hG, show sphereProdFormDatum = Hyp from rfl]
  exact intCongr_eps_hyp ε hu

/-- **The relaxed `s2s2_hyp` reducer**: the S²×S² hyperbolic pin from the robust basis-ID
congruence plus a `±1` cross value (any witness class `x`). -/
theorem sphereProd_s2s2_hyp_of_congr_pm (x : Cohomology (Sph 2) 2)
    (hcong : IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis)
      (Matrix.of fun i j => interFormInt sphereProdIntFundClassHonest
        (crossFamily x i) (crossFamily x j)))
    (hu : IsUnit (interFormInt sphereProdIntFundClassHonest (alphaOf x) (betaOf x))) :
    ∃ N, IsHyperbolicForm N ∧
      IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis) N := by
  obtain ⟨N, hN, hpin⟩ := sphereProdFormDatum_hyp_pin
  exact ⟨N, hN, (hcong.trans (crossFamily_gram_intCongr_of_isUnit x hu)).trans hpin⟩

/-- **THE FED CONSUMER STATEMENT**: `s2s2_hyp` conditional ONLY on the basis-ID congruence and
the hemisphere-class unit. The Eilenberg–Zilber cross value is no longer a hypothesis — it is
DISCHARGED (up to the hemisphere coordinate) by the full MV cup–Stokes peel chain at the witness
generator `xS`. -/
theorem sphereProd_s2s2_hyp_of_congr_of_hemiUnit
    (hHemi : IsUnit (topSphereIsoInt 1 hemiClass))
    (hcong : IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis)
      (Matrix.of fun i j => interFormInt sphereProdIntFundClassHonest
        (crossFamily xS i) (crossFamily xS j))) :
    ∃ N, IsHyperbolicForm N ∧
      IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis) N :=
  sphereProd_s2s2_hyp_of_congr_pm xS hcong (hcross_pm_of_hemiUnit hHemi)

end SKEFTHawking.SphereProdCrossValueFeed
