/-
# Phase 5q.H (E1 CSC-PD tower) — the openDuality-univ (2,1)-window bijectivity from `hcoreG` (integral)

Wires `pdWindowPInt_univ` to the `hD` input of the σ÷16 cap-equiv assembly
(`SingularIntCapEquivAssembly.sixteen_dvd_latticeSig_of_capEquiv`, `capEquivInt`). `pdWindowPInt_univ` (on a
closed charted 4-manifold, with `hproj`/`hfree` discharged internally by Kaplansky) gives the induction
predicate on `univ`, whose FIRST conjunct is the bijectivity of `openDuality` at the `(k=2, m=1)` window —
exactly the `hD` the ⊤-collapse bridge (`fundamentalDuality_bijective_of_openDuality_univ_bijectiveInt`) →
`capEquivInt` → `sixteen_dvd_latticeSig_of_capEquiv` chain consumes. `hbaseConvG` is discharged here from the
fundamental-class datum (`hcyc` + orientation `hloc`, via `hbaseConvG_of_localGenInt`); `hcoreG` (the
torsion-safe connecting core) remains threaded.

⟹ the WHOLE integral PD → σ÷16 leg rests on EXACTLY: `hcoreG` + the orientation input (`hcyc`/`hloc`) + the
finite Kronecker/basis/spin-Wu/topological-Rokhlin data. `hproj`/`hfree`/`hbaseConvG` are all discharged.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularPDWindowInt
import SKEFTHawking.SingularPDWindowBaseConvGInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularOpenDualityMVConnSquareInt (castChainInt chainBoundary_castChainInt_eq_zero)
open SKEFTHawking.SingularPDWindowInt (HcoreG pdWindowPInt_univ)

namespace SKEFTHawking.SingularOpenDualityUnivBijInt

/-- **The `(2,1)`-window openDuality on `univ` is bijective, given `hcoreG` + the fundamental-class datum**
(integral). The first conjunct of `pdWindowPInt_univ` (with `hbaseConvG` discharged from `hcyc`/`hloc` via
`hbaseConvG_of_localGenInt`, and `hproj`/`hfree` discharged internally). This is the `hD` input of the σ÷16
cap-equiv assembly — so the whole PD → σ÷16 leg rests on `hcoreG` + the orientation input + the finite data. -/
theorem openDuality_univ_bij_of_hcoreGInt {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcoreG : HcoreG M zM hzM)
    (hcyc : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    (hloc : ∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
        (X := TopCat.of M) x (2 + 2)
        (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = (SKEFTHawking.SingularBaseCaseD0Int.localIsoComplInt x).symm 1) :
    Function.Bijective
      (openDuality (k := 1 + 1) (m := 0 + 1)
        (isOpen_univ : IsOpen (Set.univ : Set ↑(TopCat.of M)))
        (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) zM)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM)) :=
  (pdWindowPInt_univ zM hzM hcoreG
    (SKEFTHawking.SingularPDWindowBaseConvGInt.hbaseConvG_of_localGenInt zM hzM hcyc hloc)
    isOpen_univ).1

end SKEFTHawking.SingularOpenDualityUnivBijInt
