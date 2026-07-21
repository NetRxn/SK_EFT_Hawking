/-
# Phase 5q.H — the COCYCLE-GENERIC torus right peel (hcross B-slice)

`TorusCrossPeel.kronecker_cup_snd_torCross` evaluates `⟨fst*w ⌣ snd*windS, torCross c⟩` for the
SPECIFIC winding cocycle `windS`. Inspection of its proof shows `windS` enters through exactly two
facts: (i) it kills constant (horizontal) edges — `windS_const`; (ii) its values on the two arc
edges, kept symbolic until the final glue. Fact (i) is NOT special to `windS`: **every 1-cocycle
kills constant edges** (evaluate `δη = 0` at the constant 2-simplex: all three faces are the
constant edge, and the alternating sum `1 − 1 + 1 = 1` leaves `η(const) = 0`).

This module ships the generalization: for ANY 1-cocycle `η` on `S¹`,

  `⟨fst*w ⌣ snd*η, torCross c⟩ = (−1)ⁿ · (η(eA) + η(eB)) · ⟨w, c⟩`

with `eA, eB` the two arc edges — i.e. the right peel evaluates against the CHAIN-LEVEL pairing
`⟨η, eA + eB⟩` of `η` with the explicit fundamental circle cycle, no winding normalization and no
`H¹(S¹)` decomposition needed. This is the form the S²×S² cross-value peel consumes: its seam
difference cochain is an abstract 1-cocycle (a difference of transported primitives), and the peel
converts the seam pairing directly into `⟨η, [S¹]⟩ · ⟨w, [S²]⟩`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.TorusCrossPeel

namespace SKEFTHawking.TorusCrossPeelGen

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctoriality (mapSimplex)
open SKEFTHawking.SingularCohomologyFunctorialityInt (cochainPullbackInt cochainPullbackInt_apply)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex face_constSimplex)
open SKEFTHawking.SingularHomotopyInvarianceInt
open SKEFTHawking.SingularPrism (prismSimplex)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularProdContractibleInt (prodFst)
open SKEFTHawking.KummerTorusStep (Tor)
open SKEFTHawking.CircleWindingCocycle (arcA arcB pathEdge)
open SKEFTHawking.TorusCrossPeel (prodSnd arcH torCross torCross_apply
  sndFace_prism_hi sndFace_prism_mid fstFace_prism predAbove_last_front
  kronecker_prismBasisInt kronecker_prismOpInt_of_basis)

/-- **Every 1-cocycle kills constant edges.** Evaluate `δη = 0` at the constant 2-simplex: all
three faces are the constant edge and the alternating sum is `η(const) − η(const) + η(const)`. -/
theorem cocycle_one_const {X : TopCat} (η : SingularCochainInt X 1)
    (hη : coboundaryₗ X 1 η = 0) (b : ↑X) : η (constSimplex b 1) = 0 := by
  have h0 : coboundary X 1 η (constSimplex b 2) = 0 := by
    rw [show coboundary X 1 η = coboundaryₗ X 1 η from rfl, hη]; rfl
  rw [coboundary_apply, Fin.sum_univ_three] at h0
  have hface : ∀ i : Fin 3, face i (constSimplex b 2) = constSimplex b 1 := fun i =>
    face_constSimplex b 1 i
  rw [hface 0, hface 1, hface 2] at h0
  simpa using h0

/-- **The cocycle-generic single-arc right peel**: for ANY 1-cocycle `η` on `S¹`,
`⟨fst*w ⌣ snd*η, P_arc c⟩ = (−1)ⁿ · η(arcEdge) · ⟨w, c⟩`. Verbatim the `windS` proof with
`windS_const` replaced by `cocycle_one_const`. -/
theorem kronecker_cup_snd_prism_gen (Y : TopCat) (arc : C(unitInterval, ↑(Sph 1))) {n : ℕ}
    (η : SingularCochainInt (Sph 1) 1) (hη : coboundaryₗ (Sph 1) 1 η = 0)
    (w : SingularCochainInt Y n) (c : SingularChainInt Y n) :
    kronecker (cup (cochainPullbackInt (prodFst Y (Sph 1)) n w)
        (cochainPullbackInt (prodSnd Y (Sph 1)) 1 η))
      (prismOpInt (arcH Y arc) n c)
      = (-1 : ℤ) ^ n * (η (pathEdge (Sph 1) arc) * kronecker w c) := by
  rw [show (-1 : ℤ) ^ n * (η (pathEdge (Sph 1) arc) * kronecker w c)
      = ((-1 : ℤ) ^ n * η (pathEdge (Sph 1) arc)) * kronecker w c by ring]
  refine kronecker_prismOpInt_of_basis _ _ _ _ (fun σ => ?_) c
  rw [kronecker_prismBasisInt]
  have hterm : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      (cup (cochainPullbackInt (prodFst Y (Sph 1)) n w)
        (cochainPullbackInt (prodSnd Y (Sph 1)) 1 η)) (prismSimplex (arcH Y arc) σ i) = 0 := by
    intro i hi
    rw [cup_apply, cochainPullbackInt_apply, cochainPullbackInt_apply]
    have hback : backFace (prismSimplex (arcH Y arc) σ i)
        = (TopCat.toSSet.obj (Tor Y)).map (backIncl n 1).op (prismSimplex (arcH Y arc) σ i) := rfl
    rw [hback]
    have hhi : ∀ j : Fin 2, i.castSucc < (ConcreteCategory.hom (backIncl n 1)) j := by
      intro j
      show ((i : ℕ) : ℕ) < n + (j : ℕ)
      have : (i : ℕ) < n := by
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with h | h
        · exact h
        · exact absurd (Fin.ext h) hi
      omega
    rw [sndFace_prism_hi Y arc σ i (backIncl n 1) hhi, cocycle_one_const η hη, mul_zero]
  rw [Finset.sum_eq_single (Fin.last n)
      (fun i _ hi => by rw [hterm i hi, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
  rw [cup_apply, cochainPullbackInt_apply, cochainPullbackInt_apply]
  have hback : backFace (prismSimplex (arcH Y arc) σ (Fin.last n))
      = (TopCat.toSSet.obj (Tor Y)).map (backIncl n 1).op
          (prismSimplex (arcH Y arc) σ (Fin.last n)) := rfl
  have hfront : frontFace (prismSimplex (arcH Y arc) σ (Fin.last n))
      = (TopCat.toSSet.obj (Tor Y)).map (frontIncl n 1).op
          (prismSimplex (arcH Y arc) σ (Fin.last n)) := rfl
  rw [hback, hfront]
  have hmid : mapSimplex (prodSnd Y (Sph 1))
      ((TopCat.toSSet.obj (Tor Y)).map (backIncl n 1).op
        (prismSimplex (arcH Y arc) σ (Fin.last n)))
      = pathEdge (Sph 1) arc := by
    refine sndFace_prism_mid Y arc σ (Fin.last n) (backIncl n 1) ?_ ?_
    · show ¬ (((Fin.last n : Fin (n + 1)) : ℕ) < n + 0)
      rw [Fin.val_last]
      omega
    · show ((Fin.last n : Fin (n + 1)) : ℕ) < n + 1
      rw [Fin.val_last]
      omega
  have hfst : mapSimplex (prodFst Y (Sph 1))
      ((TopCat.toSSet.obj (Tor Y)).map (frontIncl n 1).op
        (prismSimplex (arcH Y arc) σ (Fin.last n)))
      = σ := by
    rw [fstFace_prism Y arc σ (Fin.last n) (frontIncl n 1) (𝟙 (SimplexCategory.mk n))
        (fun j => by rw [predAbove_last_front]; rfl)]
    exact FunctorToTypes.map_id_apply _ _
  rw [hmid, hfst, Fin.val_last]
  ring

/-- **The cocycle-generic glued right peel**: for ANY 1-cocycle `η` on `S¹`,
`⟨fst*w ⌣ snd*η, torCross c⟩ = (−1)ⁿ · (η(eA) + η(eB)) · ⟨w, c⟩` — the peel value is the
chain-level pairing of `η` against the explicit fundamental circle cycle `eA + eB`. -/
theorem kronecker_cup_snd_torCross_gen (Y : TopCat) {n : ℕ}
    (η : SingularCochainInt (Sph 1) 1) (hη : coboundaryₗ (Sph 1) 1 η = 0)
    (w : SingularCochainInt Y n) (c : SingularChainInt Y n) :
    kronecker (cup (cochainPullbackInt (prodFst Y (Sph 1)) n w)
        (cochainPullbackInt (prodSnd Y (Sph 1)) 1 η))
      (torCross Y n c)
      = (-1 : ℤ) ^ n * ((η (pathEdge (Sph 1) arcA) + η (pathEdge (Sph 1) arcB)) * kronecker w c) := by
  rw [torCross_apply, kronecker_add_right, kronecker_cup_snd_prism_gen Y arcA η hη,
    kronecker_cup_snd_prism_gen Y arcB η hη]
  ring

end SKEFTHawking.TorusCrossPeelGen
