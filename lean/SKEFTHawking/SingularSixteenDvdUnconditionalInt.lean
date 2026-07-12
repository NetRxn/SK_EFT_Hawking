/-
# Phase 5q.H (E1 CSC-PD tower) — the integral σ÷16 leg with `hcoreG` DISCHARGED (no PD input remains)

`sixteen_dvd_latticeSig_of_hcoreGInt` (the assembled integral Poincaré-duality → `16 ∣ σ` leg) wired to
`SingularHcoreGDischargeInt.hcoreG_intrinsicInt` (the two seam-matches), eliminating the leg's one
remaining PD/connecting-square hypothesis. The `16 ∣ σ` conclusion now rests on EXACTLY:
* the orientation input `hcyc` + `hloc` (the fundamental cycle restricts to the local generator);
* the finite data: the `H₂`-free Kronecker pairing (`kron`/`hkron`) + its basis `B`, the spin-Wu even-form
  datum `D`, and the topological-Rokhlin factor `htopo` (`2 ∣ σ/8`, = E2's Guillou–Marin content).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSixteenDvdLegInt
import SKEFTHawking.SingularHcoreGDischargeInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularOpenDualityMVConnSquareInt (castChainInt chainBoundary_castChainInt_eq_zero)
open SKEFTHawking.SingularSixteenDvdLegInt (sixteen_dvd_latticeSig_of_hcoreGInt)
open SKEFTHawking.SingularHcoreGDischargeInt (hcoreG_intrinsicInt)

namespace SKEFTHawking.SingularSixteenDvdUnconditionalInt

/-- **The integral σ÷16 leg, PD-input-free** — `16 ∣ σ` for a closed charted 4-manifold from orientation
(`hcyc`/`hloc`) + finite Kronecker/basis/spin-Wu data + the topological-Rokhlin factor `htopo` ALONE:
the connecting core `hcoreG` is supplied intrinsically by `hcoreG_intrinsicInt` (the seam-matches), so no
Poincaré-duality/naturality hypothesis survives in the signature. -/
theorem sixteen_dvd_latticeSigInt {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcyc : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    (hloc : ∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
        (X := TopCat.of M) x (2 + 2)
        (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = (SKEFTHawking.SingularBaseCaseD0Int.localIsoComplInt x).symm 1)
    (kron : Homology (TopCat.of M) 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology (TopCat.of M) 2))
    (hkron : ∀ (h : Homology (TopCat.of M) 2) (b : Cohomology (TopCat.of M) 2),
      kron h b = kroneckerHInt 2 b h)
    (B : IntH2Basis (TopCat.of M))
    (D : SpinWuDatum (intFundamentalClassOfHomology (Homology.mk (TopCat.of M) (2 + 1 + 1)
        ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
          chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩)))
    (htopo : (2 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfHomology
        (Homology.mk (TopCat.of M) (2 + 1 + 1)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
            chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩)) B) / 8) :
    (16 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfHomology
        (Homology.mk (TopCat.of M) (2 + 1 + 1)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
            chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩)) B) :=
  sixteen_dvd_latticeSig_of_hcoreGInt zM hzM (hcoreG_intrinsicInt zM hzM) hcyc hloc
    kron hkron B D htopo

end SKEFTHawking.SingularSixteenDvdUnconditionalInt
