/-
# Phase 5q.H — K7 residual (b): the deck functional on `H₁(Q;ℤ)` and the seam-loop evaluation

The `Q = T⁴°/τ` mirror of the `KummerRP3SmithSES` §5 norm-parity machinery, plus the per-seam
evaluation that drives the δ₁-image (parity) analysis:

* **The norm-parity functional** `phiB : H₀(B;ℤ) → ℤ/2` for the free double cover
  `qmk : T⁴° ↠ Q` (`B = D·C` the difference subcomplex): for `b = D c`, `φ[b] = ε(c) mod 2` —
  well-defined because `ker D = A = N·C` has even augmentation (`aug_normChain`), and
  `B`-boundaries die (`ε∘∂ = 0`).
* **The deck functional** `qDeck : H₁(Q;ℤ) → ℤ/2` — `φ_B ∘ δ₀` through the Smith SES-III
  connecting map. It kills everything lifted from `T⁴°` (`qDeck_projH`), and:
* **THE seam-loop evaluation** (`qDeck_qBdryMap`): for EVERY exceptional index `c`, the image in
  `Q` of the `ℝP³` generator under the seam boundary map `qBdryMap c` has deck value `1` —
  each of the 16 seam loops is deck-odd. The lift is the explicit sphere embedding
  `sphereEmbedPT c = centeredChartParam c ∘ scaleToChart : S³ → T⁴°`, whose `τ`-equivariance
  (`tauFun_sphereEmbedPT`) is the arithmetic fact `2c ∈ ℤ⁴` for a half-lattice fixed point.

This is row 1 (of 5) of the δ₁-image matrix: consumed by `KummerK7Delta1Image` to prove
`im δ₁ ⊆ {parity-zero}` — the first exact cut of `coker Σ₂` below `(ℤ/2)¹⁶`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerQuotientSmithSES
import SKEFTHawking.KummerRP3H1Pin

open CategoryTheory Opposite
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop tauC tauFun qmkC tauC_comp_self)
open SKEFTHawking.KummerPuncturedTorus (puncturedTorus centeredChartParam
  centeredChartParam_involution continuous_centeredChartParam sphere_subset_puncturedTorus)
open SKEFTHawking.KummerFreeQuotient (qmk neg_one_smul_val)
open SKEFTHawking.KummerWeld (EIndex scaleToChart scaleToChart_negS3 sqNorm_scaleToChart
  continuous_scaleToChart s3ToQ qBdryMap qBdryMap_mk continuous_qBdryMap eIndex_fixedSet)
open SKEFTHawking.KummerResolutionPiece (RP3 S3 negS3 mkRP3 mkRP3_neg)
open SKEFTHawking.KummerRP3Covering (S3top RP3top mkRP3C diffChain normChain
  chainBoundary_diffChain)
open SKEFTHawking.KummerInvolution (torusFourInvolution)
open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary Homology)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt mapChainInt_single
  chainBoundary_mapChainInt Homology.mapInt Homology.mapInt_mk)
open SKEFTHawking.SingularFunctoriality (mapSimplex mapSimplex_comp)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)
open SKEFTHawking.CircleWindingCocycle (mapSimplex_constSimplex)
open SKEFTHawking.SingularLineMinusPointInt (augmentationInt augmentationInt_single
  augmentationInt_chainBoundary)
open SKEFTHawking.SingularInvolutionSmithInt (ker_diffChain_eq_range_normChain diffChain_single)
open SKEFTHawking.KummerQuotientTransferInt (mapSimplex_tauC_ne)
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerQuotientSmithSES
open SKEFTHawking.KummerRP3SmithSES (hmlEquivHomology)
open SKEFTHawking.KummerRP3H1Pin (genS3Simplex genRP3Simplex boundary_genS3 genRP3_cycle)

namespace SKEFTHawking.KummerQuotientDeckFunctional

noncomputable section

/-- The `S³` basepoint of the pinned generator machinery. -/
abbrev sBase : S3 := SKEFTHawking.KummerRP3SmithSES.basePt

/-! ## §1. The norm-parity functional `φ_B : H₀(B;ℤ) → ℤ/2` — the `T⁴°` clone -/

/-- The mod-2 augmentation `C₀(T⁴°;ℤ) → ℤ/2`. -/
def mod2aug : SingularChainInt PTtop 0 →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap.comp (augmentationInt PTtop)

theorem mod2aug_apply (c : SingularChainInt PTtop 0) :
    mod2aug c = ((augmentationInt PTtop c : ℤ) : ZMod 2) := rfl

/-- `mod2aug` kills the norm subcomplex `A₀` (its augmentations are even). -/
theorem mod2aug_Amod (a : SingularChainInt PTtop 0) (ha : a ∈ Amod 0) : mod2aug a = 0 := by
  obtain ⟨c, rfl⟩ := ha
  rw [mod2aug_apply, aug_normChain]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨augmentationInt PTtop c, by push_cast; ring⟩

/-- `ker D₀ = A₀` — the generic free-involution Smith exactness at level 0 for `τ` on `T⁴°`. -/
theorem kerD_eq_Amod : LinearMap.ker (diffChain tauC 0) = Amod 0 := by
  rw [ker_diffChain_eq_range_normChain tauC_comp_self (fun σ => mapSimplex_tauC_ne σ)]
  rfl

/-- The first-isomorphism identification `B₀ ≅ C₀/A₀`. -/
def bQuotEquiv : Bc 0 ≃ₗ[ℤ] (SingularChainInt PTtop 0 ⧸ Amod 0) :=
  (LinearMap.quotKerEquivRange (diffChain tauC 0)).symm.trans
    (Submodule.quotEquivOfEq _ _ kerD_eq_Amod)

/-- The mod-2 augmentation descended to `C₀/A₀`. -/
def thetaA : (SingularChainInt PTtop 0 ⧸ Amod 0) →ₗ[ℤ] ZMod 2 :=
  Submodule.liftQ (Amod 0) mod2aug (fun a ha => mod2aug_Amod a ha)

/-- **The norm-parity functional** `ψ : B₀ → ℤ/2`: for `b = D c`, `ψ b = ε(c) mod 2`
(well-defined: two `D`-preimages differ by `ker D = A₀`, whose augmentation is even). -/
def psiB : Bc 0 →ₗ[ℤ] ZMod 2 := thetaA.comp bQuotEquiv.toLinearMap

/-- **The `ψ` computation rule**: for ANY `c` with `D c = b`, `ψ b = ε(c) mod 2`. -/
theorem psiB_spec (b : Bc 0) (c : SingularChainInt PTtop 0)
    (hc : diffChain tauC 0 c = (b : SingularChainInt PTtop 0)) :
    psiB b = ((augmentationInt PTtop c : ℤ) : ZMod 2) := by
  have h1 : LinearMap.quotKerEquivRange (diffChain tauC 0)
      (Submodule.Quotient.mk c) = b := by
    apply Subtype.ext
    rw [LinearMap.quotKerEquivRange_apply_mk]
    exact hc
  have h2 : (LinearMap.quotKerEquivRange (diffChain tauC 0)).symm b
      = Submodule.Quotient.mk c := by
    rw [← h1, LinearEquiv.symm_apply_apply]
  show thetaA (bQuotEquiv b) = _
  rw [show bQuotEquiv b = (Submodule.quotEquivOfEq _ _ kerD_eq_Amod)
      ((LinearMap.quotKerEquivRange (diffChain tauC 0)).symm b) from rfl,
    h2, Submodule.quotEquivOfEq_mk]
  show mod2aug c = _
  rw [mod2aug_apply]

/-- `ψ` kills the `B`-boundaries (`∂B₁ ∋ ∂(D w) = D(∂ w)`, and `ε∘∂ = 0`). -/
theorem psiB_boundary (z : ↥(Bmod 0)) (hz : z ∈ ChainComplexLESInt.boundaries dB 0) :
    psiB z = 0 := by
  obtain ⟨w, hw⟩ := hz
  obtain ⟨v, hv⟩ := w.2
  have hzc : diffChain tauC 0 (chainBoundary PTtop 0 v) = (z : SingularChainInt PTtop 0) := by
    have h1 : (z : SingularChainInt PTtop 0) = chainBoundary PTtop 0 (w : _) := by
      rw [← hw]
      rfl
    rw [h1, ← hv, chainBoundary_diffChain]
  rw [psiB_spec z _ hzc, augmentationInt_chainBoundary]
  rfl

/-- **`φ_B : H₀(B;ℤ) → ℤ/2`, on classes** — descends `ψ` through the boundary quotient. -/
def phiB : Hml dB 0 →ₗ[ℤ] ZMod 2 :=
  Submodule.liftQ _ (psiB.comp (ChainComplexLESInt.cycles dB 0).subtype) (by
    rintro z hz
    rw [mem_submoduleOf] at hz
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact psiB_boundary _ hz)

theorem phiB_mk (z : ChainComplexLESInt.cycles dB 0) :
    phiB (Hml.mk dB 0 z) = psiB (z : ↥(Bmod 0)) := rfl

/-! ## §2. The deck functional on `H₁(Q;ℤ)` -/

/-- **The deck functional** (engine form) `H₁(Q;ℤ) → ℤ/2`: norm-parity of the SES-III
connecting image. -/
def qDeckHml : Hml (chainBoundary Qtop) 1 →ₗ[ℤ] ZMod 2 := phiB.comp (deltaIII 0)

/-- **The deck functional** `qDeck : H₁(Q;ℤ) → ℤ/2`. -/
def qDeck : Homology Qtop 1 →ₗ[ℤ] ZMod 2 :=
  qDeckHml.comp (hmlEquivHomology Qtop 1).symm.toLinearMap

/-- **The deck functional kills the `T⁴°`-lifted classes**: `qDeck ∘ p̄₊ = 0` (SES-III LES
exactness) — the deck functional factors through `H₁(Q)/im(projH)`, the genuinely-quotient part. -/
theorem qDeckHml_projH (x : Hml (chainBoundary PTtop) 1) : qDeckHml (projH 1 x) = 0 := by
  show phiB (deltaIII 0 (projH 1 x)) = 0
  rw [(exact_projH_deltaIII 0).apply_apply_eq_zero x, map_zero]

/-! ## §3. The sphere lift `S³ → T⁴°` at each fixed point, and its `τ`-equivariance -/

/-- **The sphere lift** `S³ → T⁴°` at the exceptional index `c`: the radius-`ρ` chart sphere
around the fixed point (the PT-side content of `s3ToQ`). -/
def sphereEmbedPT (c : EIndex) (a : S3) : ↥puncturedTorus :=
  ⟨centeredChartParam c.1 (scaleToChart a),
    sphere_subset_puncturedTorus (eIndex_fixedSet c)
      ⟨scaleToChart a, sqNorm_scaleToChart a, rfl⟩⟩

/-- The sphere lift as a bundled continuous map. -/
def sphereEmbedPTC (c : EIndex) : C(S3top, PTtop) :=
  ⟨sphereEmbedPT c,
    Continuous.subtype_mk ((continuous_centeredChartParam c.1).comp continuous_scaleToChart) _⟩

/-- **`τ`-equivariance of the sphere lift**: `τ ∘ ι_c = ι_c ∘ (−1)` — the deck involution
restricts to the antipode on the chart sphere (the arithmetic fact `2c ∈ ℤ⁴`). -/
theorem tauFun_sphereEmbedPT (c : EIndex) (a : S3) :
    tauFun (sphereEmbedPT c a) = sphereEmbedPT c (negS3 a) := by
  apply Subtype.ext
  rw [show tauFun (sphereEmbedPT c a) = (-1 : ℤˣ) • sphereEmbedPT c a from rfl,
    neg_one_smul_val]
  show torusFourInvolution (centeredChartParam c.1 (scaleToChart a))
    = centeredChartParam c.1 (scaleToChart (negS3 a))
  rw [centeredChartParam_involution c.1 (eIndex_fixedSet c), scaleToChart_negS3]

/-- The Q-side seam boundary map, bundled. -/
def qBdryMapC (c : EIndex) : C(RP3top, Qtop) := ⟨qBdryMap c, continuous_qBdryMap c⟩

/-- **The covering square**: `qmk ∘ ι_c = qBdryMap c ∘ mkRP3` — the sphere lift covers the seam
boundary map (definitional: both are `s3ToQ c`). -/
theorem qmkC_comp_sphereEmbedPTC (c : EIndex) :
    qmkC.comp (sphereEmbedPTC c) = (qBdryMapC c).comp mkRP3C :=
  ContinuousMap.ext fun _ => rfl

/-! ## §4. The seam loop in `Q` and its deck value -/

/-- **The seam-`c` loop simplex in `Q`**: the image of the pinned `ℝP³` generator under the seam
boundary map. -/
def seamLoopSimplex (c : EIndex) : (TopCat.toSSet.obj Qtop).obj (op (SimplexCategory.mk 1)) :=
  mapSimplex (qBdryMapC c) genRP3Simplex

/-- The seam-`c` loop is a `1`-cycle of `Q`. -/
theorem seamLoop_cycle (c : EIndex) :
    chainBoundary Qtop 0 (Finsupp.single (seamLoopSimplex c) (1 : ℤ)) = 0 := by
  have h1 : Finsupp.single (seamLoopSimplex c) (1 : ℤ)
      = mapChainInt (qBdryMapC c) 1 (Finsupp.single genRP3Simplex 1) := by
    rw [mapChainInt_single]
    rfl
  rw [h1, chainBoundary_mapChainInt, genRP3_cycle, map_zero]

/-- The PT-side lift of the seam-`c` loop: the sphere-lifted `S³` half-loop. -/
def liftChain (c : EIndex) : SingularChainInt PTtop 1 :=
  Finsupp.single (mapSimplex (sphereEmbedPTC c) genS3Simplex) 1

/-- **The lift projects onto the seam loop**: `p₊(lift) = seam loop` (the covering square). -/
theorem mapChainInt_liftChain (c : EIndex) :
    mapChainInt qmkC 1 (liftChain c) = Finsupp.single (seamLoopSimplex c) 1 := by
  rw [liftChain, mapChainInt_single, seamLoopSimplex, genRP3Simplex, ← mapSimplex_comp,
    ← mapSimplex_comp, qmkC_comp_sphereEmbedPTC]

/-- **The lift's boundary is the antipodal point-pair difference** at the `c`-th sphere. -/
theorem boundary_liftChain (c : EIndex) :
    chainBoundary PTtop 0 (liftChain c)
      = Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c (negS3 sBase)) 0) 1
        - Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0) 1 := by
  have h1 : liftChain c = mapChainInt (sphereEmbedPTC c) 1 (Finsupp.single genS3Simplex 1) := by
    rw [mapChainInt_single]; rfl
  rw [h1, chainBoundary_mapChainInt, boundary_genS3, map_sub, mapChainInt_single,
    mapChainInt_single, mapSimplex_constSimplex, mapSimplex_constSimplex]
  rfl

/-- The point-pair difference as an element of the difference subcomplex `B₀` — the deck
involution pairs the two endpoints (`τ`-equivariance of the lift). -/
theorem liftBd_mem_Bmod (c : EIndex) :
    Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c (negS3 sBase)) 0) (1 : ℤ)
        - Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0) 1 ∈ Bmod 0 := by
  refine ⟨-(Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0) (1 : ℤ)), ?_⟩
  rw [map_neg, diffChain_single]
  have h1 : mapSimplex tauC (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0)
      = constSimplex (X := PTtop) (sphereEmbedPT c (negS3 sBase)) 0 := by
    rw [show (constSimplex (X := PTtop) (sphereEmbedPT c (negS3 sBase)) 0)
        = constSimplex (X := PTtop) (tauFun (sphereEmbedPT c sBase)) 0 from by
      rw [tauFun_sphereEmbedPT]]
    exact mapSimplex_constSimplex tauC (sphereEmbedPT c sBase) 0
  rw [h1]
  abel

/-- **The connecting computation**: `δ₀[seam-c loop] = [point-pair diff at the c-th sphere]`. -/
theorem deltaIII_seamLoop (c : EIndex) :
    deltaIII 0 (Hml.mk (chainBoundary Qtop) 1
        ⟨Finsupp.single (seamLoopSimplex c) 1, mem_cycles_succ.mpr (seamLoop_cycle c)⟩)
      = Hml.mk dB 0
          ⟨⟨Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c (negS3 sBase)) 0) 1
              - Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0) 1,
            liftBd_mem_Bmod c⟩,
            Submodule.mem_top⟩ := by
  refine delta_mk_eq hf_inclB hg_proj hddC hfinj_inclB hgsurj_proj hexact_III _
    (liftChain c) ?_ _ ?_ Submodule.mem_top
  · exact mapChainInt_liftChain c
  · show (Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c (negS3 sBase)) 0) (1 : ℤ)
        - Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0) 1)
      = chainBoundary PTtop 0 (liftChain c)
    rw [boundary_liftChain]

/-- **THE seam-loop deck value**: every seam loop is deck-odd — `qDeck[seam-c loop] = 1`. -/
theorem qDeck_seamLoop (c : EIndex) :
    qDeck (SKEFTHawking.SingularHomologyInt.Homology.mk Qtop 1
        ⟨Finsupp.single (seamLoopSimplex c) 1, mem_cycles_succ.mpr (seamLoop_cycle c)⟩) = 1 := by
  have h1 : qDeck (SKEFTHawking.SingularHomologyInt.Homology.mk Qtop 1
        ⟨Finsupp.single (seamLoopSimplex c) 1, mem_cycles_succ.mpr (seamLoop_cycle c)⟩)
      = phiB (deltaIII 0 (Hml.mk (chainBoundary Qtop) 1
          ⟨Finsupp.single (seamLoopSimplex c) 1, mem_cycles_succ.mpr (seamLoop_cycle c)⟩)) := rfl
  rw [h1, deltaIII_seamLoop]
  have h2 : phiB (Hml.mk dB 0
        ⟨⟨Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c (negS3 sBase)) 0) 1
            - Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0) 1,
          liftBd_mem_Bmod c⟩,
          Submodule.mem_top⟩)
      = psiB ⟨Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c (negS3 sBase)) 0) 1
          - Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0) 1,
        liftBd_mem_Bmod c⟩ := rfl
  rw [h2, psiB_spec _
    (-(Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0) (1 : ℤ))) ?hD]
  case hD =>
    rw [map_neg, diffChain_single]
    have h3 : mapSimplex tauC (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0)
        = constSimplex (X := PTtop) (sphereEmbedPT c (negS3 sBase)) 0 := by
      rw [show (constSimplex (X := PTtop) (sphereEmbedPT c (negS3 sBase)) 0)
          = constSimplex (X := PTtop) (tauFun (sphereEmbedPT c sBase)) 0 from by
        rw [tauFun_sphereEmbedPT]]
      exact mapSimplex_constSimplex tauC (sphereEmbedPT c sBase) 0
    rw [h3]
    show _ = Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c (negS3 sBase)) 0) (1 : ℤ)
        - Finsupp.single (constSimplex (X := PTtop) (sphereEmbedPT c sBase) 0) 1
    abel
  · rw [map_neg, augmentationInt_single]
    decide

/-- The pinned `H₁(ℝP³;ℤ)` generator class. -/
def genRP3Class : Homology (TopCat.of RP3) 1 :=
  SKEFTHawking.SingularHomologyInt.Homology.mk RP3top 1
    ⟨Finsupp.single genRP3Simplex 1,
      mem_cycles_succ.mpr genRP3_cycle⟩

/-- **THE deck row of the δ₁-image matrix**: `qDeck (qBdryMap c)_* [gen] = 1` for every
exceptional index — the seam boundary map carries the `ℝP³` generator to a deck-odd class of
`H₁(Q;ℤ)`, uniformly in `c`. -/
theorem qDeck_qBdryMap (c : EIndex) :
    qDeck (Homology.mapInt (qBdryMapC c) 1 genRP3Class) = 1 := by
  have h1 : Homology.mapInt (qBdryMapC c) 1 genRP3Class
      = SKEFTHawking.SingularHomologyInt.Homology.mk Qtop 1
          ⟨Finsupp.single (seamLoopSimplex c) 1, mem_cycles_succ.mpr (seamLoop_cycle c)⟩ := by
    rw [genRP3Class, Homology.mapInt_mk]
    congr 1
    apply Subtype.ext
    show mapChainInt (qBdryMapC c) 1 (Finsupp.single genRP3Simplex 1) = _
    rw [mapChainInt_single]
    rfl
  rw [h1]
  exact qDeck_seamLoop c

end

end SKEFTHawking.KummerQuotientDeckFunctional
