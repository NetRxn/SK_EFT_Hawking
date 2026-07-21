import Mathlib
import SKEFTHawking.KummerRP3HomologySolve
import SKEFTHawking.KummerRP3TauHomotopy
import SKEFTHawking.CircleWindingCocycle

/-!
# The pinned generator of `H₁(ℝP³;ℤ) ≅ ℤ/2` — the projected phase half-loop

Falsifiable strengthening of `rp3H1EquivZMod2`: the generator of `H₁(ℝP³;ℤ)` is pinned as an
**explicit** singular cycle — the `mkRP3`-projection of the phase half-loop
`t ↦ (e^{iπt}, 0)` from the basepoint to its antipode (a genuine loop downstairs since
`mkRP3(−x) = mkRP3(x)`), and

`rp3H1EquivZMod2 [projected half-loop] = 1`.

The computation runs the connecting map's choice-free rule (`delta_mk_eq`): the half-loop
upstairs is a `p₊`-preimage, its boundary is the antipodal point-pair difference
`[−x₀] − [x₀] = D(−[x₀]) ∈ B₀`, whose norm-parity is `ε(−[x₀]) = −1 ≡ 1 (mod 2)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerRP3Covering (S3top RP3top mkRP3C negS3C diffChain)
open SKEFTHawking.KummerRP3TauHomotopy (phase phase_zero phase_one norm_phase continuous_phase)
open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary Homology)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt mapChainInt_single
  chainBoundary_mapChainInt)
open SKEFTHawking.SingularFunctoriality (mapSimplex)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)
open SKEFTHawking.SingularH0PathConnected (pathSimplex)
open SKEFTHawking.SingularH0PathConnectedInt (chainBoundary_pathSimplexInt)
open SKEFTHawking.CircleWindingCocycle (mapSimplex_constSimplex)
open SKEFTHawking.SingularLineMinusPointInt (augmentationInt augmentationInt_single)
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerRP3SmithSES
open SKEFTHawking.KummerRP3HomologySolve

namespace SKEFTHawking.KummerRP3H1Pin

noncomputable section

/-! ## §1. The phase half-loop `basePt ⤳ −basePt` -/

/-- **The phase half-loop** `t ↦ (e^{iπt}, 0)` from the basepoint to its antipode. -/
def genPath : Path (basePt : ↑S3top) (negS3 basePt) where
  toFun t := ⟨(phase t, 0), by simp [norm_phase]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_phase.prodMk continuous_const
  source' := by
    apply Subtype.ext
    apply Prod.ext
    · exact phase_zero
    · rfl
  target' := by
    apply Subtype.ext
    apply Prod.ext
    · show phase 1 = (negS3 basePt).1.1
      rw [phase_one]
      simp [negS3, basePt]
    · show (0 : ℂ) = (negS3 basePt).1.2
      simp [negS3, basePt]

/-- The half-loop as a singular `1`-simplex of `S³`. -/
def genS3Simplex : (TopCat.toSSet.obj S3top).obj (op (SimplexCategory.mk 1)) :=
  pathSimplex (X := S3top) genPath

/-- **The pinned `H₁(ℝP³)` generator simplex**: the projected half-loop (a loop downstairs). -/
def genRP3Simplex : (TopCat.toSSet.obj RP3top).obj (op (SimplexCategory.mk 1)) :=
  mapSimplex mkRP3C genS3Simplex

/-- The boundary of the upstairs half-loop: the antipodal point-pair difference. -/
theorem boundary_genS3 :
    chainBoundary S3top 0 (Finsupp.single genS3Simplex (1 : ℤ))
      = Finsupp.single (constSimplex (X := S3top) (negS3 basePt) 0) 1
        - Finsupp.single (constSimplex (X := S3top) basePt 0) 1 :=
  chainBoundary_pathSimplexInt (X := S3top) genPath

/-- **The projected half-loop is a cycle**: its boundary is `[mkRP3(−x₀)] − [mkRP3(x₀)] = 0`. -/
theorem genRP3_cycle :
    chainBoundary RP3top 0 (Finsupp.single genRP3Simplex (1 : ℤ)) = 0 := by
  have h1 : Finsupp.single genRP3Simplex (1 : ℤ)
      = mapChainInt mkRP3C 1 (Finsupp.single genS3Simplex 1) := by
    rw [mapChainInt_single]
    rfl
  rw [h1, chainBoundary_mapChainInt, boundary_genS3, map_sub, mapChainInt_single,
    mapChainInt_single, mapSimplex_constSimplex, mapSimplex_constSimplex]
  have h2 : (mkRP3C (negS3 basePt) : RP3) = mkRP3C basePt := mkRP3_neg basePt
  rw [h2, sub_self]

/-- The point-pair difference as an element of the difference subcomplex `B₀`. -/
theorem bd_mem_Bmod :
    Finsupp.single (constSimplex (X := S3top) (negS3 basePt) 0) (1 : ℤ)
        - Finsupp.single (constSimplex (X := S3top) basePt 0) 1 ∈ Bmod 0 := by
  refine ⟨-(Finsupp.single (constSimplex (X := S3top) basePt 0) (1 : ℤ)), ?_⟩
  rw [map_neg, SKEFTHawking.SingularInvolutionSmithInt.diffChain_single]
  have h1 : mapSimplex negS3C (constSimplex (X := S3top) basePt 0)
      = constSimplex (X := S3top) (negS3 basePt) 0 := mapSimplex_constSimplex negS3C basePt 0
  rw [h1]
  abel

/-! ## §2. The pin -/

/-- The engine-level connecting computation: `δ₀[projected half-loop] = [point-pair diff]`. -/
theorem deltaIII_genClass :
    deltaIII 0 (Hml.mk (chainBoundary RP3top) 1
        ⟨Finsupp.single genRP3Simplex 1, mem_cycles_succ.mpr genRP3_cycle⟩)
      = Hml.mk dB 0
          ⟨⟨Finsupp.single (constSimplex (X := S3top) (negS3 basePt) 0) 1
              - Finsupp.single (constSimplex (X := S3top) basePt 0) 1, bd_mem_Bmod⟩,
            Submodule.mem_top⟩ := by
  refine delta_mk_eq hf_inclB hg_proj hddC hfinj_inclB hgsurj_proj hexact_III _
    (Finsupp.single genS3Simplex 1) ?_ _ ?_ Submodule.mem_top
  · rw [mapChainInt_single]
    rfl
  · show (Finsupp.single (constSimplex (X := S3top) (negS3 basePt) 0) (1 : ℤ)
        - Finsupp.single (constSimplex (X := S3top) basePt 0) 1)
      = chainBoundary S3top 0 (Finsupp.single genS3Simplex 1)
    rw [boundary_genS3]

/-- **The `H₁(ℝP³;ℤ) ≅ ℤ/2` generator pin (falsifiable)**: the class of the projected phase
half-loop maps to `1 ∈ ℤ/2` — it IS the generator. -/
theorem rp3H1_generator_pin :
    rp3H1EquivZMod2 (SKEFTHawking.SingularHomologyInt.Homology.mk RP3top 1
        ⟨Finsupp.single genRP3Simplex 1, mem_cycles_succ.mpr genRP3_cycle⟩) = 1 := by
  have h1 : rp3H1EquivZMod2 (SKEFTHawking.SingularHomologyInt.Homology.mk RP3top 1
        ⟨Finsupp.single genRP3Simplex 1, mem_cycles_succ.mpr genRP3_cycle⟩)
      = hmlB_zero_equiv (deltaIII 0 (Hml.mk (chainBoundary RP3top) 1
          ⟨Finsupp.single genRP3Simplex 1, mem_cycles_succ.mpr genRP3_cycle⟩)) := rfl
  rw [h1, deltaIII_genClass]
  have h2 : hmlB_zero_equiv (Hml.mk dB 0
        ⟨⟨Finsupp.single (constSimplex (X := S3top) (negS3 basePt) 0) 1
            - Finsupp.single (constSimplex (X := S3top) basePt 0) 1, bd_mem_Bmod⟩,
          Submodule.mem_top⟩)
      = psiB ⟨Finsupp.single (constSimplex (X := S3top) (negS3 basePt) 0) 1
          - Finsupp.single (constSimplex (X := S3top) basePt 0) 1, bd_mem_Bmod⟩ := rfl
  rw [h2, psiB_spec _ (-(Finsupp.single (constSimplex (X := S3top) basePt 0) (1 : ℤ))) ?hD]
  case hD =>
    rw [map_neg, SKEFTHawking.SingularInvolutionSmithInt.diffChain_single,
      mapSimplex_constSimplex]
    show _ = Finsupp.single (constSimplex (X := S3top) (negS3 basePt) 0) (1 : ℤ)
        - Finsupp.single (constSimplex (X := S3top) basePt 0) 1
    abel
  · rw [map_neg, augmentationInt_single]
    decide

end

end SKEFTHawking.KummerRP3H1Pin
