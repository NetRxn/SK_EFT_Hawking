/-
# Phase 5q.H — THE SEAM TRANSPORT: `orientInput` DISCHARGED

The last span of the `K3` orientation chain. `KummerK3OrientFromSeamKernel` reduced the whole
`orientInput` atom, **losslessly** (an `↔`), to

> `LinearMap.ker qSeamCoord3 ≠ ⊥` — one nontrivial ℤ-linear relation among the sixteen boundary
> `ℝP³` classes of `∂Q` inside `H₃(Q;ℤ)`

and `KummerPunctureSphereSeam` proved the exact mirror on the double cover, unconditionally, in the
sixteen boundary-`S³` classes of `T⁴°` — i.e. in the coordinates the free `ℤ/2` covering
`p = qmk : T⁴° ↠ Q` acts on. This module transports the relation across `p` and closes the chain.

## The three links, and why the transport is now free

1. **The covering square is definitional.** `KummerWeld.s3ToQ c = qmk ∘ σ_c` where
   `σ_c a = centeredChartParam c (scaleToChart a)` is `KummerPunctureSphereSeam.sphToPT c`, and
   `qBdryMap c ∘ mkRP3 = s3ToQ c` (`qBdryMap_mk`). So

       qmkC ∘ sphToPT c = qBdryMapC c ∘ mkRP3C      (`qmk_comp_sphToPT`, proved by `rfl`)

   — no geometry to establish, the weld was *built* from this map.
2. **The `Q`-side seam coordinate is the weld boundary map** (§1–2). The degree-1 identification
   `KummerK7Delta1Image.qThickEquiv_incl_single` is degree-generic; its `n+1` form
   (`qThickEquiv_incl_single_gen`) at `n = 2` gives

       qSeamCoord3 (Pi.single c 1) = (qBdryMapC c)_* rp3Gen.

   The two continuous-map squares it rests on (`incl_comp_seam_eq`,
   `qImageHomeo_symm_comp_seam` — the `weldMk_seam` glue) carry no degree at all and are reused
   verbatim.
3. **The degree-2 defect is not a defect** (`KummerRP3TopDegree.projHomRP3_three_injective`):
   `p_* : H₃(S³;ℤ) → H₃(ℝP³;ℤ)` is injective, so `p_* s3Gen = m • rp3Gen` with `m ≠ 0`. The
   relation survives multiplied by `m`, and `ℤ¹⁶` is torsion-free, so `m • v ≠ 0`.
   `KummerQTopVanish.h3Q_twoTorsionFree` is not even needed.

## Headline

* **`exists_nonzero_qSeam_relation`** — `∃ v ≠ 0, qSeamCoord3 v = 0`;
* **`ker_qSeamCoord3_ne_bot`** — the hypothesis of `nonempty_intOrientation_of_ker_ne_bot`,
  discharged;
* **`nonempty_intOrientation_kummerK3_uncond`** — `Nonempty (IntOrientation KummerK3)`,
  **UNCONDITIONALLY**. `orientInput` (`KummerK3E1Package.KummerK3H3TwoTorsionFree`) is no longer
  needed by anything;
* **`nontrivial_h4K3`** — `H₄(K3;ℤ)` is nontrivial: the welded Kummer `K3` is
  orientable, obtained from the *integral geometric* input `H₄(T⁴;ℤ) ≅ ℤ` carried down the
  covering, exactly as the settled no-go
  `k3-orientation-needs-an-integral-geometric-input-not-mod-2` requires;
* **`nonempty_kummerK3E1Atoms_of_pd`** — the `K3` E1 atom triple with `orientInput` and `h1Free`
  both gone; only the duality (unimodularity) atom `pdInput` remains a hypothesis.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerK7Delta1Image
import SKEFTHawking.KummerK3OrientFromSeamKernel
import SKEFTHawking.KummerRP3TopDegree
import SKEFTHawking.KummerPunctureSphereSeam

namespace SKEFTHawking.KummerK3SeamTransport

open SKEFTHawking.SingularHomologyInt (Homology IntOrientation)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt Homology.mapInt_comp)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (subIncl)
open SKEFTHawking.SingularFiniteProdSingleInt (eInclC eIndexProdHnEquivInt_mapInt_single
  homologyCongrInt_apply)
open SKEFTHawking.SingularFiniteProdDiscreteHnInt (homologyCongrInt)
open SKEFTHawking.KummerK7Opener (KummerK3top seamHomologyEquivInt seamHomeoCM)
open SKEFTHawking.KummerResolutionPiece (RP3)
open SKEFTHawking.KummerRP3Covering (S3top RP3top mkRP3C projHomRP3)
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop qmkC)
open SKEFTHawking.KummerWeld (EIndex KummerK3 eImage qImage seam qBdryMap)
open SKEFTHawking.KummerK7MVAssembly (qThick seamInclC seamIncl_mapInt_bijective interHnEquivInt
  qThickHnEquivInt qInclC qIncl_mapInt_bijective qImageHomeo)
open SKEFTHawking.KummerK7Delta1Image (seamToQImageC incl_comp_seam_eq qImageHomeo_symm_comp_seam)
open SKEFTHawking.KummerQuotientDeckFunctional (qBdryMapC)
open SKEFTHawking.KummerK3H3SeamWindow (qSeamCoord3 collarToQThick3)
open SKEFTHawking.KummerRP3HomologyUnconditional (rp3H3EquivInt_unconditional)
open SKEFTHawking.KummerRP3TopDegree (rp3Gen rp3H3EquivInt_rp3Gen eq_zero_of_smul_rp3Gen_eq_zero
  projHomRP3_three_ne_zero)
open SKEFTHawking.KummerPunctureSphereSeam (sphToPT s3Gen s3Gen_ne_zero piCongrRight_single
  smul_eq_sum_single exists_nonzero_sphere_seam_relation)
open SKEFTHawking.KummerK7H1Window (genInclC)
open scoped SKEFTHawking.KummerK7H1Window
open scoped SKEFTHawking.KummerK3E1Package

noncomputable section

/-! ## §1. The collar seam generators, in every degree -/

/-- **The collar equivalence at a single seam, degree-generic.** The inverse of
`Hₙ₊₁(collar;ℤ) ≅ ⊕₁₆ Hₙ₊₁(ℝP³;ℤ)` carries `Pi.single c y` to the `c`-th seam pushforward. The
degree-`1` case is `KummerK7Delta1Image.interEquiv_symm_single`; nothing in that proof depends on
the degree. -/
theorem interEquiv_symm_single_gen (n : ℕ) (c : EIndex) (y : Homology (TopCat.of RP3) (n + 1)) :
    (interHnEquivInt n).symm (Pi.single c y)
      = Homology.mapInt seamInclC (n + 1) (Homology.mapInt seamHomeoCM (n + 1)
          (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
            (eInclC c) (n + 1) y)) := by
  rw [LinearEquiv.symm_apply_eq, interHnEquivInt, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply]
  have e1 : (LinearEquiv.ofBijective (Homology.mapInt seamInclC (n + 1))
      (seamIncl_mapInt_bijective n)).symm
        (Homology.mapInt seamInclC (n + 1) (Homology.mapInt seamHomeoCM (n + 1)
          (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
            (eInclC c) (n + 1) y)))
      = Homology.mapInt seamHomeoCM (n + 1)
          (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
            (eInclC c) (n + 1) y) := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  rw [e1]
  have e2 : (seamHomologyEquivInt (n + 1)).symm
      (Homology.mapInt seamHomeoCM (n + 1)
        (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
          (eInclC c) (n + 1) y))
      = Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
          (eInclC c) (n + 1) y := by
    rw [LinearEquiv.symm_apply_eq, seamHomologyEquivInt, LinearEquiv.ofBijective_apply]
  rw [e2]
  exact (eIndexProdHnEquivInt_mapInt_single (n + 1) c y).symm

/-- **The `Q`-image of the `c`-th seam generator is `(qBdryMap c)_*`, degree-generic.** The collar
class transported through the thickening retraction and the `Q`-piece identification; the weld glue
(`weldMk_seam`, via `KummerK7Delta1Image.qImageHomeo_symm_comp_seam`) is what turns the abstract
collar coordinate into the concrete `Q`-side boundary map. Degree-`1` case:
`KummerK7Delta1Image.qThickEquiv_incl_single`. -/
theorem qThickEquiv_incl_single_gen (n : ℕ) (c : EIndex)
    (y : Homology (TopCat.of RP3) (n + 1)) :
    (qThickHnEquivInt n) (Homology.mapInt (subIncl (X := KummerK3top)
        (Set.inter_subset_left (s := qThick) (t := eImage))) (n + 1)
        ((interHnEquivInt n).symm (Pi.single c y)))
      = Homology.mapInt (X := RP3top) (Y := TopCat.of FreeQuotient)
          (qBdryMapC c) (n + 1) y := by
  rw [interEquiv_symm_single_gen]
  have h1 : Homology.mapInt (subIncl (X := KummerK3top)
      (Set.inter_subset_left (s := qThick) (t := eImage))) (n + 1)
        (Homology.mapInt seamInclC (n + 1) (Homology.mapInt seamHomeoCM (n + 1)
          (Homology.mapInt (X := TopCat.of RP3) (Y := TopCat.of (EIndex × RP3))
            (eInclC c) (n + 1) y)))
      = Homology.mapInt qInclC (n + 1)
          (Homology.mapInt (seamToQImageC c) (n + 1) y) := by
    rw [← LinearMap.comp_apply, ← Homology.mapInt_comp, ← LinearMap.comp_apply,
      ← Homology.mapInt_comp, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
      incl_comp_seam_eq]
    exact LinearMap.congr_fun (Homology.mapInt_comp qInclC (seamToQImageC c) (n + 1)) y
  rw [h1, qThickHnEquivInt, LinearEquiv.trans_apply]
  have h2 : (LinearEquiv.ofBijective (Homology.mapInt qInclC (n + 1))
      (qIncl_mapInt_bijective n)).symm
        (Homology.mapInt qInclC (n + 1) (Homology.mapInt (seamToQImageC c) (n + 1) y))
      = Homology.mapInt (seamToQImageC c) (n + 1) y := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  rw [h2, homologyCongrInt_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
    qImageHomeo_symm_comp_seam]

/-! ## §2. The `Q`-side seam coordinate in degree 3 -/

/-- **THE `Q`-SIDE SEAM BASIS, IDENTIFIED.** The `c`-th coordinate vector of `ℤ¹⁶` maps under
`qSeamCoord3` to the pushforward of the `ℝP³` fundamental class along the weld's boundary map
`qBdryMap c : ℝP³ → ∂Q_c ⊆ Q`. -/
theorem qSeamCoord3_single (c : EIndex) :
    qSeamCoord3 (Pi.single c (1 : ℤ))
      = Homology.mapInt (X := RP3top) (Y := TopCat.of FreeQuotient) (qBdryMapC c) 3 rp3Gen := by
  have hpi : (SKEFTHawking.KummerK7MVAssembly.interH3EquivInt).symm (Pi.single c (1 : ℤ))
      = (interHnEquivInt 2).symm (Pi.single c rp3Gen) := by
    rw [SKEFTHawking.KummerK7MVAssembly.interH3EquivInt, LinearEquiv.symm_trans_apply]
    congr 1
    have hone := piCongrRight_single rp3H3EquivInt_unconditional c rp3Gen
    rw [rp3H3EquivInt_rp3Gen] at hone
    rw [LinearEquiv.symm_apply_eq]
    funext d
    rw [LinearEquiv.piCongrRight_apply, ← congrFun hone d]
    congr 1
  show (qThickHnEquivInt 2) (collarToQThick3
    ((SKEFTHawking.KummerK7MVAssembly.interH3EquivInt).symm (Pi.single c (1 : ℤ)))) = _
  rw [hpi]
  exact qThickEquiv_incl_single_gen 2 c rp3Gen

/-! ## §3. The covering square -/

/-- **THE COVERING SQUARE, DEFINITIONALLY.** The `c`-th boundary sphere of `T⁴°`, projected to `Q`,
is the weld's `Q`-side seam boundary map precomposed with the antipodal covering `S³ ↠ ℝP³`. This is
not a computation: `KummerWeld.s3ToQ` was *defined* as `qmk ∘ σ_c`, and `qBdryMap c` as its
antipodal descent. -/
theorem qmk_comp_sphToPT (c : EIndex) :
    qmkC.comp (sphToPT c) = (qBdryMapC c).comp mkRP3C := ContinuousMap.ext fun _ => rfl

/-! ## §4. The transport -/

/-- The nonzero integer by which the covering multiplies the top `S³` class. -/
def coverDeg : ℤ := rp3H3EquivInt_unconditional (projHomRP3 3 s3Gen)

/-- **`coverDeg ≠ 0`** — `p_*` is injective in top degree
(`KummerRP3TopDegree.projHomRP3_three_injective`) and `s3Gen ≠ 0`. -/
theorem coverDeg_ne_zero : coverDeg ≠ 0 := by
  intro h
  refine projHomRP3_three_ne_zero s3Gen_ne_zero ?_
  refine rp3H3EquivInt_unconditional.injective ?_
  rw [map_zero]
  exact h

/-- **The projected boundary-sphere class is `coverDeg • rp3Gen`.** -/
theorem projHomRP3_s3Gen : projHomRP3 3 s3Gen = coverDeg • rp3Gen := by
  refine rp3H3EquivInt_unconditional.injective ?_
  rw [map_smul, rp3H3EquivInt_rp3Gen, smul_eq_mul, mul_one]
  rfl

/-- **THE SEAM TRANSPORT.** The `c`-th boundary-`S³` class of `T⁴°`, pushed to `Q`, is
`coverDeg` times the `c`-th seam coordinate vector's image. -/
theorem qmk_mapInt_sphToPT (c : EIndex) :
    Homology.mapInt qmkC 3 (Homology.mapInt (sphToPT c) 3 s3Gen)
      = qSeamCoord3 (Pi.single c coverDeg) := by
  have h : Homology.mapInt qmkC 3 (Homology.mapInt (sphToPT c) 3 s3Gen)
      = Homology.mapInt (X := RP3top) (Y := TopCat.of FreeQuotient) (qBdryMapC c) 3
          (projHomRP3 3 s3Gen) := by
    rw [← LinearMap.comp_apply, ← Homology.mapInt_comp, qmk_comp_sphToPT,
      Homology.mapInt_comp]
    rfl
  rw [h, projHomRP3_s3Gen, map_smul, ← qSeamCoord3_single, ← map_smul]
  congr 1
  funext d
  rcases eq_or_ne d c with rfl | hne
  · rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul, mul_one]
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne, smul_zero]

/-! ## §5. `orientInput` discharged -/

/-- **THE SIXTEEN SEAM `ℝP³` CLASSES OF `∂Q` ARE ℤ-LINEARLY DEPENDENT — UNCONDITIONALLY.**

The `T⁴°`-side relation `KummerPunctureSphereSeam.exists_nonzero_sphere_seam_relation` pushed
forward along the free `ℤ/2` covering `qmk : T⁴° ↠ Q`, scaled by the nonzero covering degree
`coverDeg`. -/
theorem exists_nonzero_qSeam_relation : ∃ v : EIndex → ℤ, v ≠ 0 ∧ qSeamCoord3 v = 0 := by
  classical
  obtain ⟨v, hv, hrel⟩ := exists_nonzero_sphere_seam_relation
  refine ⟨coverDeg • v, ?_, ?_⟩
  · intro h
    obtain ⟨c, hc⟩ := Function.ne_iff.mp hv
    have := congrFun h c
    rw [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact coverDeg_ne_zero h1
    · exact hc h1
  · have hsum : qSeamCoord3 (coverDeg • v)
        = Homology.mapInt qmkC 3 (∑ c : EIndex, v c • Homology.mapInt (sphToPT c) 3 s3Gen) := by
      rw [smul_eq_sum_single, map_sum, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smul, map_smul, qmk_mapInt_sphToPT]
      rfl
    rw [hsum, hrel]
    exact map_zero _

/-- **`ker qSeamCoord3 ≠ ⊥`** — the exact hypothesis of
`KummerK3OrientFromSeamKernel.nonempty_intOrientation_of_ker_ne_bot`, discharged. -/
theorem ker_qSeamCoord3_ne_bot : LinearMap.ker qSeamCoord3 ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := exists_nonzero_qSeam_relation
  intro hbot
  refine hv ?_
  have hmem : v ∈ LinearMap.ker qSeamCoord3 := LinearMap.mem_ker.mpr h0
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

/-- **THE `K3` ORIENTATION ATOM, UNCONDITIONALLY.** `Nonempty (IntOrientation KummerK3)` with no
hypothesis at all — `KummerK3E1Package.KummerK3H3TwoTorsionFree` (`orientInput`) is discharged and
no longer gates anything.

The integral geometric input is `KummerHomologyT4Full.torusFourFundamentalClass_ne_zero`
(`H₄(T⁴;ℤ) ≅ ℤ`) carried down the free `ℤ/2` covering — exactly the shape the settled no-go
`k3-orientation-needs-an-integral-geometric-input-not-mod-2` says is required. No mod-2 argument
appears anywhere in the chain. -/
theorem nonempty_intOrientation_kummerK3_uncond : Nonempty (IntOrientation KummerK3) :=
  SKEFTHawking.KummerK3OrientFromSeamKernel.nonempty_intOrientation_of_ker_ne_bot
    ker_qSeamCoord3_ne_bot

/-- **`H₄(K3;ℤ)` IS NONTRIVIAL** — the welded Kummer `K3` is orientable. Transported from the seam
kernel along `KummerQTopVanish.h4K3EquivKerQSeamCoord3`. -/
theorem nontrivial_h4K3 : Nontrivial (Homology KummerK3top 4) :=
  SKEFTHawking.KummerK3OrientFromSeamKernel.nontrivial_h4K3_of_ker_ne_bot ker_qSeamCoord3_ne_bot

/-! ## §6. The E1 atom triple with only the duality atom left -/

open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularCohomologyInt (IntPoincareDuality)
open SKEFTHawking.SingularHomologyInt (intFundamentalClassOfIntOrientation)

/-- **The `K3` E1 atom triple, with `orient` and `h1Free` both unconditional.** The only remaining
hypothesis is the duality (unimodularity) atom. This is
`KummerK3OrientFromSeamKernel.nonempty_kummerK3E1Atoms_of_ker_pd` with its seam-kernel hypothesis
discharged by §5. -/
theorem nonempty_kummerK3E1Atoms_of_pd
    (pdInput : ∀ o : IntOrientation KummerK3,
      Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o))) :
    Nonempty KummerK3E1Atoms :=
  SKEFTHawking.KummerK3OrientFromSeamKernel.nonempty_kummerK3E1Atoms_of_ker_pd
    ker_qSeamCoord3_ne_bot pdInput

end

end SKEFTHawking.KummerK3SeamTransport
