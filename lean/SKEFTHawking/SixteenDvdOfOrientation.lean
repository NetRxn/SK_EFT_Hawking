/-
# Phase 5q.H (E1) — the σ÷16 leg fed by the ORIENTATION DATUM (`IntOrientationData`)

The orientation-side glue: `sixteen_dvd_latticeSigInt` (the PD-input-free leg) consumed its
fundamental-cycle data as raw `(zM, hzM, hcyc, hloc)`; this module feeds it from the brick-18
orientation datum `IntOrientationData M` (the `orient` ±1-section + `[M]` + per-point restriction +
mod-2 compatibility — constructible from orientability via `intOrientationDataOfOrientation`). The
extraction mirrors `SingularPD4Instances.exists_fundClass_P4_data` (representative + `castChainInt_eq`
identity-cast transport), and the conclusion is restated at the CLASS level
(`intFundamentalClassOfHomology d.fundClass`) so consumers never see the representative.

After this brick the leg's signature at a (plus-)oriented closed charted 4-manifold is:
`d : IntOrientationData M` (+ `orient ≡ 1` normalization) + `kron`/`hkron`/`B` (the H₂ Kronecker/basis
data) + `D` (spin-Wu — a THEOREM given spin, `SpinWuDatumClosed`) + `htopo` (E2) ⟹ `16 ∣ σ`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSixteenDvdUnconditionalInt
import SKEFTHawking.IntOrientationSection

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt (localGenerator)
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularOpenDualityMVConnSquareInt (castChainInt castChainInt_eq
  chainBoundary_castChainInt_eq_zero)
open SKEFTHawking.IntOrientationSection
open SKEFTHawking.SingularReducedGeneratorInt (intLocalHomologyIso_of_manifold')

namespace SKEFTHawking.SixteenDvdOfOrientation

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

omit [Nonempty M] in
/-- **The plus-oriented local generator is the `localIsoComplInt` generator**: at `s = 1` the oriented
local generator is exactly the `+1` preimage the σ÷16 leg's `hloc` demands (`localIsoComplInt` is
definitionally `manifoldLocalHomologyIsoInt`). -/
theorem orientedLocalGenerator_one (x : M) :
    orientedLocalGenerator x 1
      = (SKEFTHawking.SingularBaseCaseD0Int.localIsoComplInt x).symm 1 := by
  rw [orientedLocalGenerator, one_smul, localGenerator]
  rfl

set_option linter.unusedVariables false in
/-- **The leg's fundamental-cycle data from a plus-oriented orientation datum** — the integral mirror
of `SingularPD4Instances.exists_fundClass_P4_data`: a representative of `d.fundClass` at the leg's
degree spellings, with the local-generator property transported from `d.restricts`. -/
theorem exists_leg_data (d : IntOrientationData M) (h1 : ∀ x, d.orient x = 1) :
    ∃ (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
      (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
      (hcyc : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
        ∈ cycles (TopCat.of M) (2 + 2)),
      (∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
          (X := TopCat.of M) x (2 + 2)
          (Homology.mk (TopCat.of M) (2 + 2)
            ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
        = (SKEFTHawking.SingularBaseCaseD0Int.localIsoComplInt x).symm 1)
      ∧ Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩
        = d.fundClass := by
  obtain ⟨zc, hzc⟩ := Submodule.Quotient.mk_surjective _ d.fundClass
  have hcast : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega)
      (zc.1 : SingularChainInt (TopCat.of M) (1 + 0 + 3)) = zc.1 := by
    rw [castChainInt_eq]
  refine ⟨zc.1, LinearMap.mem_ker.mp zc.2, by rw [hcast]; exact zc.2, ?_, ?_⟩
  · intro x
    have hclass : Homology.mk (TopCat.of M) (2 + 2)
        ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zc.1,
          by rw [hcast]; exact zc.2⟩
        = d.fundClass :=
      (congrArg (Homology.mk (TopCat.of M) (2 + 2)) (Subtype.ext hcast)).trans hzc
    rw [hclass]
    have hres := d.restricts x
    rw [h1 x, orientedLocalGenerator_one] at hres
    exact hres
  · exact (congrArg (Homology.mk (TopCat.of M) (2 + 2)) (Subtype.ext hcast)).trans hzc

/-- **`16 ∣ σ` at a plus-oriented closed charted 4-manifold, stated at the CLASS level.** The σ÷16 leg
(`sixteen_dvd_latticeSigInt`, PD-input-free) fed by the orientation datum: the intersection matrix is
taken at `intFundamentalClassOfHomology d.fundClass` — consumers never see a chain representative. The
remaining inputs: the H₂ Kronecker/basis data (`kron`/`hkron`/`B`), the spin-Wu datum `D` (a THEOREM
given spin — `SpinWuDatumClosed.spinWuDatum_of_closed`), and the topological factor `htopo` (E2). -/
theorem sixteen_dvd_latticeSig_of_orientationData (d : IntOrientationData M)
    (h1 : ∀ x, d.orient x = 1)
    (kron : Homology (TopCat.of M) 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology (TopCat.of M) 2))
    (hkron : ∀ (h : Homology (TopCat.of M) 2) (b : Cohomology (TopCat.of M) 2),
      kron h b = kroneckerHInt 2 b h)
    (B : IntH2Basis (TopCat.of M))
    (D : SpinWuDatum (intFundamentalClassOfHomology d.fundClass))
    (htopo : (2 : ℤ) ∣ latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) B) / 8) :
    (16 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfHomology d.fundClass) B) := by
  obtain ⟨zM, hzM, hcyc, hloc, hclass⟩ := exists_leg_data d h1
  -- identify the leg's (2+1+1)-spelled class with `d.fundClass`
  have hcast' : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM
      = castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM := by
    rw [castChainInt_eq]
  have hclass' : Homology.mk (TopCat.of M) (2 + 1 + 1)
      ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
        chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩
      = d.fundClass :=
    (congrArg (Homology.mk (TopCat.of M) (2 + 2)) (Subtype.ext hcast')).trans hclass
  have hfc : intFundamentalClassOfHomology (Homology.mk (TopCat.of M) (2 + 1 + 1)
      ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
        chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩)
      = intFundamentalClassOfHomology d.fundClass :=
    congrArg intFundamentalClassOfHomology hclass'
  rw [← hfc] at D htopo ⊢
  exact SKEFTHawking.SingularSixteenDvdUnconditionalInt.sixteen_dvd_latticeSigInt
    zM hzM hcyc hloc kron hkron B D htopo

end SKEFTHawking.SixteenDvdOfOrientation
