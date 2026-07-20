import Mathlib
import SKEFTHawking.KummerResolutionPiece
import SKEFTHawking.SingularFunctorialityInt

/-!
# Phase 5q.H — K6′a leg 3: the zero-section homology packaging (the K7 feeder)

The Euler−2 disk bundle `E` (`KummerResolutionPiece.ResE`) deformation-retracts onto its zero
section `S²` (`KummerResolutionPiece.BaseS2`): the fiber-scaling homotopy `deform` (with the base
projection `baseProj` as retraction) exhibits a genuine homotopy equivalence `E ≃ S²`. Feeding this
into the banked **integral** homotopy-invariance engine
(`SingularFunctorialityInt.Homology.mapInt_bijective_of_homotopyEquiv`) shows the zero-section
inclusion induces an **isomorphism** on integral homology in every positive degree:

  `Homology.mapInt zeroSectionC (n+1) : Hₙ₊₁(S²; ℤ) ≅ Hₙ₊₁(E; ℤ)`  (bijective, hence a `≃ₗ[ℤ]`).

The headline `H₂` case — `H₂(E; ℤ) ≅ H₂(S²; ℤ)` with the zero-section class as the inducing map —
is exactly what the K7 Mayer–Vietoris accounting consumes when it splits `K3` along the `16 × ∂E`
seam. The map is `Homology.mapInt zeroSectionC 2`; the packaged equivalences are
`zeroSectionHomologyEquivInt` (all degrees `n+1`) and `zeroSectionH2EquivInt` (the `H₂` headline).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry` / `axiom` / `native_decide` /
`maxHeartbeats`. The geometry is entirely reused from `KummerResolutionPiece`; only the homology
functor step is new, mirroring `SingularConvexRadialRetractInt`.
-/

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)

namespace SKEFTHawking.KummerResolutionPieceH2

noncomputable section

/-- `E` (the Euler−2 disk bundle) as a bundled `TopCat`. -/
def Etop : TopCat := TopCat.of ResE

/-- The zero-section base `S²` as a bundled `TopCat`. -/
def Btop : TopCat := TopCat.of BaseS2

/-- **The zero-section inclusion** `S² ↪ E` as a `ContinuousMap` (the K7 generator map). -/
def zeroSectionC : C(↑Btop, ↑Etop) := ⟨zeroSection, continuous_zeroSection⟩

/-- **The base projection** `E → S²` as a `ContinuousMap` (the homotopy inverse of `zeroSectionC`). -/
def baseProjC : C(↑Etop, ↑Btop) := ⟨baseProj, continuous_baseProj⟩

/-- **The fiber-scaling deformation** `E × [0,1] → E` as a `ContinuousMap` — the homotopy
`zeroSection ∘ baseProj ≃ id_E`. -/
def deformC : C(↑Etop × unitInterval, ↑Etop) := ⟨deform, continuous_deform⟩

/-- The trivial homotopy on `S²` (witnessing `baseProj ∘ zeroSection = id_{S²}` strictly). -/
def trivHtpyB : C(↑Btop × unitInterval, ↑Btop) := ⟨fun p => p.1, continuous_fst⟩

/-- **The zero-section inclusion induces an isomorphism on integral homology** in every positive
degree: `Hₙ₊₁(zeroSection)` is bijective. From the homotopy equivalence `E ≃ S²` (retraction
`baseProj`, deformation `deform`) fed to the integral homotopy-invariance engine. -/
theorem zeroSection_mapInt_bijective (n : ℕ) :
    Function.Bijective (Homology.mapInt zeroSectionC (n + 1)) := by
  refine SingularFunctorialityInt.Homology.mapInt_bijective_of_homotopyEquiv
    zeroSectionC baseProjC trivHtpyB ?_ ?_ deformC ?_ ?_ n
  · -- slice trivHtpyB 0 = baseProjC.comp zeroSectionC  (i.e. id = baseProj ∘ zeroSection)
    refine ContinuousMap.ext fun p => ?_
    show p = baseProj (zeroSection p)
    exact (baseProj_zeroSection p).symm
  · -- slice trivHtpyB 1 = id
    exact ContinuousMap.ext fun _ => rfl
  · -- slice deformC 0 = zeroSectionC.comp baseProjC  (i.e. deform(·,0) = zeroSection ∘ baseProj)
    refine ContinuousMap.ext fun p => ?_
    show deform (p, 0) = zeroSection (baseProj p)
    exact deform_zero p
  · -- slice deformC 1 = id  (i.e. deform(·,1) = id)
    refine ContinuousMap.ext fun p => ?_
    show deform (p, 1) = p
    exact deform_one p

/-- **`Hₙ₊₁(S²; ℤ) ≅ Hₙ₊₁(E; ℤ)`** — the zero-section homology isomorphism in every positive degree,
packaged as a `ℤ`-linear equivalence (`LinearEquiv.ofBijective` of the bijective induced map). -/
noncomputable def zeroSectionHomologyEquivInt (n : ℕ) :
    Homology Btop (n + 1) ≃ₗ[ℤ] Homology Etop (n + 1) :=
  LinearEquiv.ofBijective (Homology.mapInt zeroSectionC (n + 1)) (zeroSection_mapInt_bijective n)

/-- **The `H₂` headline (bijective form)**: `Homology.mapInt zeroSectionC 2` is bijective — the
zero-section inclusion is an isomorphism on `H₂(·; ℤ)`. This is the exact statement the K7
Mayer–Vietoris accounting consumes. -/
theorem zeroSection_mapInt_two_bijective :
    Function.Bijective (Homology.mapInt zeroSectionC 2) :=
  zeroSection_mapInt_bijective 1

/-- **`H₂(S²; ℤ) ≅ H₂(E; ℤ)`** — the headline zero-section homology isomorphism, `S²`-side to
`E`-side, induced by the zero-section inclusion `zeroSectionC`. Its inverse `.symm` is the
`H₂(E; ℤ) ≅ H₂(S²; ℤ)` identification the K7 MV pairing reads off. -/
noncomputable def zeroSectionH2EquivInt : Homology Btop 2 ≃ₗ[ℤ] Homology Etop 2 :=
  LinearEquiv.ofBijective (Homology.mapInt zeroSectionC 2) zeroSection_mapInt_two_bijective

end

end SKEFTHawking.KummerResolutionPieceH2
