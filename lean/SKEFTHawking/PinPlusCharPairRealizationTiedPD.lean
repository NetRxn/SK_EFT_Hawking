/-
# Audit M4, BLAST RADIUS — the PD-corrected transport on the REALIZED carrier's seam

`CharSurfacePDBundled` §6 makes it kernel-checked that the realized carrier's seam bases
`GeoRealizationTied.derivedEσ`/`derivedEτ` are the SAME raw Kronecker/UCT transport that audit M4
refuted for the surface bridge: no field of `GeoRealizationTied` mentions `bσ`, so the identical
geometry is a datum for the gauged basis, and its derived seam basis moves CONTRAVARIANTLY
(`gaugeGeoRealizationTied_derivedEσ`) while `hpolar` moves the enhancement covariantly. Those bases
feed `transportedBInc`'s kernel `L`, on which `TaylorLegVanishes`/`JointLagrangian` evaluate the
enhancements — so the realized carrier's Taylor leg is gauge-dependent at nonzero rank.

This module CLOSES that radius: it carries the `CharSurfacePDTransport` repair
(`homologyBasisPD Q e := (homologyBasisOfCohomologyBasis e).trans (gramEquiv Q).symm`, an
equivalence UNCONDITIONALLY since `Z4Quadratic.nondeg` IS the Gram operator's invertibility) through
`derivedEσ`/`derivedEτ` into the seam's `L`, and proves the Taylor leg gauge-INVARIANT at every rank.

* §1 `sumArrowCongr` — the block-diagonal reparametrization of the seam's coordinate space
  `(Fin nσ ⊕ Fin nτ → ℤ/2)`; the shape both the Gram correction and the gauge take there.
* §2 `derivedEσPD`/`derivedEτPD`/`toDataPD`/`toMembranePD` — the corrected seam. `toMembranePD_L`
  shows the corrected leg is STILL the honest geometric fold-kernel `ker(H₁(∂Q) → H₁(Q))` read
  through bases, never a free submodule (the `free-membrane-kernel-kills-nonsplit` fence holds).
* §3 `ker_transportedBInc_toDataPD` — the exact dictionary between the corrected and raw legs:
  `L_PD = comap (sumArrowCongr (gramEquiv qσ) (gramEquiv qτ)) L_raw`. An EQUIVALENCE (both directions
  by the equiv), not a one-way sufficiency.
* §4 `taylorLegVanishes_gaugeTied_iff` / `jointLagrangian_gaugeTied_iff` — **THE HEADLINE**. Under a
  two-sided basis gauge of the realized carrier, with the enhancements moved as `hpolar` forces, the
  corrected seam's Taylor-leg and Lagrangian conditions are UNCHANGED — an IFF, at every rank, with
  NO new hypothesis. This is exactly the property §6 of `CharSurfacePDBundled` refutes for the raw
  seam.
* §5 `seam_joint_taylor_flip` — **NON-VACUITY**, quantifier-free: on the seam's own coordinate space
  with a genus-1 enhancement at each end, the joint enhancement `TaylorLegVanishes` tests vanishes on
  the a-cycle class in PD-corrected coordinates and FAILS in the live raw coordinates.
  `seam_taylor_flip` / `derivedEσPD_ne_derivedEσ` carry the same disagreement onto any realized datum
  with a genus-1 σ-end (the inhabiting family is `cylRealizationTied`).
* §6 `toDataPD_eq_of_rank_zero` / `toMembranePD_eq_of_rank_zero` — **EQUIVALENCE CERTIFICATE**. At
  rank zero the corrected seam is *equal* to the live one, so the live rank-zero realization chain is
  provably untouched. The defect, and the repair, are strictly nonzero-rank.
* §7 `derivedEσPD_pd` — the PD-normalization, stated CONDITIONALLY on the surface's `hpolar` + PD
  tower as EXPLICIT hypotheses. `GeoRealizationTied` does not carry them (see the module note below);
  naming them is the honest alternative to inventing them.

**SUFFICIENT vs EQUIVALENT.** §3 and §4 are equivalences (`=` of submodules, `↔` of the Props) — the
correction reparametrizes, it does not weaken. §5 is a refutation (an explicit disagreement). §6 is an
equality. §7 is the only CONDITIONAL bridge: `homologyBasisPD` is gauge-covariant unconditionally, but
its identification with the *Poincaré dual* of the carried cohomology basis is sufficient-given
`hpolar`/`hpd` and is NOT claimed otherwise.

**STRUCTURAL NOTE (operator-visible, not performed here).** `GeoRealizationTied` carries `bσ`/`bτ` as
type parameters and the enhancements `qσ`/`qτ` only as arguments at `toMembrane`. Nothing asserts the
polar coherence `qσ.B (bσ a) (bσ b) = ⟨a ⌣ b, [Σσ]⟩` — the same missing-coherence shape audit M4
found in `PinCharSurface` (`Q` and `H1Iso` independent, sharing only the index type). The repair here
is unconditional in the gauge, so it is sound without that field; but §7 shows the PD *meaning* of the
corrected basis needs it. Adding an `hpolarσ`/`hpolarτ` coherence field to the realization datum is a
design change and is left to the operator.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairRealizationTied
import SKEFTHawking.CharSurfacePDBundled

open CategoryTheory Opposite Topology
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularDisjointUnion SKEFTHawking.SingularDisjointUnionHn
open SKEFTHawking.SingularKroneckerEquiv SKEFTHawking.SingularKroneckerBasisBridge
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.CharSurfacePDTransport
open SKEFTHawking.CharSurfacePDBundled

namespace SKEFTHawking.PinPlusCharPairRealizationTiedPD

/-! ## §1. The block-diagonal reparametrization of the seam's coordinate space -/

/-- **The block-diagonal automorphism** of the seam's coordinate space `(Fin nσ ⊕ Fin nτ → ℤ/2)`
induced by automorphisms of the two ends' coordinate spaces. Both the Gram correction (§3) and the
basis gauge (§4) act on the seam in exactly this shape, because `srcEquiv` splits `H₁(∂Q)` across the
clopen partition before transporting each summand through its own end basis. -/
def sumArrowCongr {nσ nτ : ℕ}
    (a : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (b : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) :
    (Fin nσ ⊕ Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ ⊕ Fin nτ → ZMod 2) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin nσ) (Fin nτ) (ZMod 2) (ZMod 2)).trans
    ((LinearEquiv.prodCongr a b).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin nσ) (Fin nτ) (ZMod 2) (ZMod 2)).symm)

@[simp] theorem sumArrowCongr_apply_inl {nσ nτ : ℕ}
    (a : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (b : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))
    (x : Fin nσ ⊕ Fin nτ → ZMod 2) (i : Fin nσ) :
    sumArrowCongr a b x (Sum.inl i) = a (fun j => x (Sum.inl j)) i := rfl

@[simp] theorem sumArrowCongr_apply_inr {nσ nτ : ℕ}
    (a : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (b : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))
    (x : Fin nσ ⊕ Fin nτ → ZMod 2) (i : Fin nτ) :
    sumArrowCongr a b x (Sum.inr i) = b (fun j => x (Sum.inr j)) i := rfl

theorem sumArrowCongr_comp_inl {nσ nτ : ℕ}
    (a : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (b : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))
    (x : Fin nσ ⊕ Fin nτ → ZMod 2) :
    (fun i => sumArrowCongr a b x (Sum.inl i)) = a (fun j => x (Sum.inl j)) := rfl

theorem sumArrowCongr_comp_inr {nσ nτ : ℕ}
    (a : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (b : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))
    (x : Fin nσ ⊕ Fin nτ → ZMod 2) :
    (fun i => sumArrowCongr a b x (Sum.inr i)) = b (fun j => x (Sum.inr j)) := rfl

/-! ## §2. The PD-corrected seam -/

variable {nσ nτ : ℕ} {Sσ Sτ : TopCat}
variable {bσ : Cohomology Sσ 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)}
variable {bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)}

/-- **The PD-corrected σ-boundary homology basis.** `GeoRealizationTied.derivedEσ` with the raw
Kronecker/UCT dual replaced by the Gram-corrected `homologyBasisPD`. Still a *derived* basis — a
function of `bσ`, `homσ` and the enhancement `qσ` alone, never a free field, so the F2 basis-gauge
exploit stays killed. -/
noncomputable def derivedEσPD (qσ : Z4Quadratic (Fin nσ)) (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    Homology (sub d.U) 1 ≃ₗ[ZMod 2] (Fin nσ → ZMod 2) :=
  (homeoHomologyEquiv d.homσ 1).trans (homologyBasisPD (N := 0) qσ bσ)

/-- **The PD-corrected τ-boundary homology basis.** -/
noncomputable def derivedEτPD (qτ : Z4Quadratic (Fin nτ)) (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    Homology (sub d.Uᶜ) 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2) :=
  (homeoHomologyEquiv d.homτ 1).trans (homologyBasisPD (N := 0) qτ bτ)

/-- **The exact dictionary, σ-side**: the raw seam basis is the Gram operator applied to the
corrected one. Read right-to-left: a class with PD-correct seam coordinates `v` is reported by the
live seam as `gramMap qσ v`. This is what §5 turns into a truth-value flip. -/
theorem gramMap_derivedEσPD (qσ : Z4Quadratic (Fin nσ)) (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (x : Homology (sub d.U) 1) :
    gramMap qσ (derivedEσPD qσ d x) = d.derivedEσ x :=
  gramMap_homologyBasisPD (N := 0) qσ bσ _

/-- **The exact dictionary, τ-side.** -/
theorem gramMap_derivedEτPD (qτ : Z4Quadratic (Fin nτ)) (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (x : Homology (sub d.Uᶜ) 1) :
    gramMap qτ (derivedEτPD qτ d x) = d.derivedEτ x :=
  gramMap_homologyBasisPD (N := 0) qτ bτ _

theorem derivedEσPD_symm (qσ : Z4Quadratic (Fin nσ)) (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (v : Fin nσ → ZMod 2) :
    (derivedEσPD qσ d).symm v = d.derivedEσ.symm (gramMap qσ v) := rfl

theorem derivedEτPD_symm (qτ : Z4Quadratic (Fin nτ)) (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (v : Fin nτ → ZMod 2) :
    (derivedEτPD qτ d).symm v = d.derivedEτ.symm (gramMap qτ v) := rfl

/-- **The corrected realization datum.** Same geometry as `GeoRealizationTied.toData` — same `∂Q`,
`Q`, clopen split, boundary inclusion and interior basis — with the two boundary bases PD-corrected.
Only the `H₁`-side coordinate convention changes; no new tie, no new hypothesis. -/
noncomputable def toDataPD (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) : GeoRealizationData nσ nτ d.mid where
  bdry := d.bdry
  Q := d.Q
  U := d.U
  hU := d.hU
  ι := d.ι
  eσ := derivedEσPD qσ d
  eτ := derivedEτPD qτ d
  eQ := d.eQ

@[simp] theorem toDataPD_eσ (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) : (toDataPD qσ qτ d).eσ = derivedEσPD qσ d := rfl

@[simp] theorem toDataPD_eτ (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) : (toDataPD qσ qτ d).eτ = derivedEτPD qτ d := rfl

@[simp] theorem toDataPD_ι (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) : (toDataPD qσ qτ d).ι = d.ι := rfl

/-- **The corrected membrane.** -/
noncomputable def toMembranePD (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) : GeoMembrane qσ qτ :=
  GeoMembrane.ofGeometric qσ qτ (toDataPD qσ qτ d)

/-- **The correction preserves the geometric-fold-kernel property.** The corrected membrane's Taylor
leg is still the image of `ker(H₁(∂Q) → H₁(Q))` under the (corrected) basis equiv — a COMPUTED
geometric kernel, never a free submodule. The `free-membrane-kernel-kills-nonsplit` fence is
untouched by the repair. -/
theorem toMembranePD_L (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    (toMembranePD qσ qτ d).L
      = Submodule.map (srcEquiv (toDataPD qσ qτ d)).toLinearMap
          (LinearMap.ker (Homology.map d.ι 1)) :=
  GeoMembrane.ofGeometric_L qσ qτ (toDataPD qσ qτ d)

/-! ## §3. The corrected leg vs the raw leg — the exact dictionary -/

/-- The corrected source equivalence's inverse is the raw one precomposed with the block Gram
reparametrization. -/
theorem srcEquiv_toDataPD_symm (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) (x : Fin nσ ⊕ Fin nτ → ZMod 2) :
    (srcEquiv (toDataPD qσ qτ d)).symm x
      = (srcEquiv d.toData).symm (sumArrowCongr (gramEquiv qσ) (gramEquiv qτ) x) := by
  rw [srcEquiv_symm_apply, srcEquiv_symm_apply]
  rfl

/-- **The corrected transported boundary-inclusion is the raw one, reparametrized by the block Gram
operator.** Nothing about the geometry changes — only the coordinates in which `H₁(∂Q)` is read. -/
theorem transportedBInc_toDataPD (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    transportedBInc (toDataPD qσ qτ d)
      = (transportedBInc d.toData).comp
          (sumArrowCongr (gramEquiv qσ) (gramEquiv qτ)).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  show d.eQ (Homology.map d.ι 1 ((srcEquiv (toDataPD qσ qτ d)).symm x))
    = d.eQ (Homology.map d.ι 1 ((srcEquiv d.toData).symm
        (sumArrowCongr (gramEquiv qσ) (gramEquiv qτ) x)))
  rw [srcEquiv_toDataPD_symm]

/-- **THE DICTIONARY BETWEEN THE TWO TAYLOR LEGS.** The corrected leg `L_PD` is the exact Gram
preimage of the live leg `L_raw` — an EQUALITY of submodules (both directions, since the block Gram
map is an equivalence), not a one-way sufficiency. So no geometric information is added or lost by
the repair; only the coordinates in which the enhancement is evaluated are fixed. -/
theorem ker_transportedBInc_toDataPD (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    LinearMap.ker (transportedBInc (toDataPD qσ qτ d))
      = Submodule.comap (sumArrowCongr (gramEquiv qσ) (gramEquiv qτ)).toLinearMap
          (LinearMap.ker (transportedBInc d.toData)) := by
  rw [transportedBInc_toDataPD, LinearMap.ker_comp]

/-! ## §4. THE HEADLINE — the corrected Taylor leg is gauge-INVARIANT at every rank -/

/-- **The two-sided basis gauge of a realized carrier.** As `CharSurfacePDBundled.§6` establishes, no
field of `GeoRealizationTied` mentions `bσ`/`bτ`, so the identical datum is a legitimate realization
for the gauged bases. This is the σ-and-τ generalization of `gaugeGeoRealizationTied`. -/
def gaugeTied (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (_g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (_h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) :
    GeoRealizationTied Sσ Sτ (bσ.trans _g) (bτ.trans _h) :=
  { d with }

@[simp] theorem gaugeTied_U (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) :
    (gaugeTied d g h).U = d.U := rfl

@[simp] theorem gaugeTied_mid (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) :
    (gaugeTied d g h).mid = d.mid := rfl

/-- **The corrected seam basis is COVARIANT under the carrier gauge** — it moves by `g` itself, the
SAME variance as the enhancement's forced move `gaugePullback qσ g.symm`. Contrast
`CharSurfacePDBundled.gaugeGeoRealizationTied_derivedEσ`, where the raw seam basis moves by the
transpose-inverse `dualGauge g`; that variance mismatch is the whole M4 defect. -/
theorem derivedEσPD_gaugeTied (qσ : Z4Quadratic (Fin nσ)) (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) (x : Homology (sub d.U) 1) :
    derivedEσPD (gaugePullback qσ g.symm) (gaugeTied d g h) x = g (derivedEσPD qσ d x) :=
  homologyBasisPD_gauge (N := 0) qσ bσ g _

/-- **The corrected seam basis is covariant on the τ-side too.** -/
theorem derivedEτPD_gaugeTied (qτ : Z4Quadratic (Fin nτ)) (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) (x : Homology (sub d.Uᶜ) 1) :
    derivedEτPD (gaugePullback qτ h.symm) (gaugeTied d g h) x = h (derivedEτPD qτ d x) :=
  homologyBasisPD_gauge (N := 0) qτ bτ h _

/-- **The σ-only specialization, against the live `gaugeGeoRealizationTied`** — the exact
counterpart of `CharSurfacePDBundled.gaugeGeoRealizationTied_derivedEσ`, with `dualGauge g` (the
transpose-inverse) replaced by `g`. Stated over the imported def so the cross-reference is a real
call, not a docstring claim. -/
theorem derivedEσPD_gaugeGeoRealizationTied (qσ : Z4Quadratic (Fin nσ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2)) (x : Homology (sub d.U) 1) :
    derivedEσPD (gaugePullback qσ g.symm) (gaugeGeoRealizationTied d g) x
      = g (derivedEσPD qσ d x) :=
  homologyBasisPD_gauge (N := 0) qσ bσ g _

/-- The gauged corrected source equivalence, in coordinates. -/
theorem srcEquiv_gaugeTied_symm (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) (x : Fin nσ ⊕ Fin nτ → ZMod 2) :
    (srcEquiv (toDataPD (gaugePullback qσ g.symm) (gaugePullback qτ h.symm)
        (gaugeTied d g h))).symm x
      = (srcEquiv (toDataPD qσ qτ d)).symm ((sumArrowCongr g h).symm x) := by
  rw [srcEquiv_symm_apply, srcEquiv_symm_apply]
  congr 1
  · refine congrArg (homIncl d.U 1) ?_
    refine (LinearEquiv.symm_apply_eq _).mpr ?_
    show (fun i => x (Sum.inl i))
      = derivedEσPD (gaugePullback qσ g.symm) (gaugeTied d g h)
          ((derivedEσPD qσ d).symm (fun i => (sumArrowCongr g h).symm x (Sum.inl i)))
    rw [derivedEσPD_gaugeTied qσ d g h, LinearEquiv.apply_symm_apply]
    exact (g.apply_symm_apply _).symm
  · refine congrArg (homIncl d.Uᶜ 1) ?_
    refine (LinearEquiv.symm_apply_eq _).mpr ?_
    show (fun i => x (Sum.inr i))
      = derivedEτPD (gaugePullback qτ h.symm) (gaugeTied d g h)
          ((derivedEτPD qτ d).symm (fun i => (sumArrowCongr g h).symm x (Sum.inr i)))
    rw [derivedEτPD_gaugeTied qτ d g h, LinearEquiv.apply_symm_apply]
    exact (h.apply_symm_apply _).symm

/-- **The gauged corrected transport is the ungauged one, reparametrized by the gauge.** -/
theorem transportedBInc_gaugeTied (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) :
    transportedBInc (toDataPD (gaugePullback qσ g.symm) (gaugePullback qτ h.symm)
        (gaugeTied d g h))
      = (transportedBInc (toDataPD qσ qτ d)).comp (sumArrowCongr g h).symm.toLinearMap := by
  refine LinearMap.ext fun x => ?_
  show d.eQ (Homology.map d.ι 1 ((srcEquiv (toDataPD (gaugePullback qσ g.symm)
      (gaugePullback qτ h.symm) (gaugeTied d g h))).symm x))
    = d.eQ (Homology.map d.ι 1 ((srcEquiv (toDataPD qσ qτ d)).symm ((sumArrowCongr g h).symm x)))
  rw [srcEquiv_gaugeTied_symm]

/-- **The gauged corrected Taylor leg is the image of the ungauged one under the gauge.** -/
theorem ker_transportedBInc_gaugeTied (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) :
    LinearMap.ker (transportedBInc (toDataPD (gaugePullback qσ g.symm)
        (gaugePullback qτ h.symm) (gaugeTied d g h)))
      = Submodule.map (sumArrowCongr g h).toLinearMap
          (LinearMap.ker (transportedBInc (toDataPD qσ qτ d))) := by
  rw [transportedBInc_gaugeTied, Submodule.map_equiv_eq_comap_symm]
  -- NB: `rw [LinearMap.ker_comp]` fails here — the goal's `∘ₗ` and the lemma's `∘ₛₗ` are defeq but
  -- not syntactically matchable at `rw`'s reducible transparency. `exact` closes it.
  exact LinearMap.ker_comp _ _

/-- **The joint enhancement is invariant under the block gauge**, because the enhancement's forced
move (`gaugePullback _ g.symm`, what `hpolar` dictates) exactly cancels the coordinate move. This is
the algebraic core of the headline. -/
theorem jointEnhancement_q_gaugePullback (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) (l : Fin nσ ⊕ Fin nτ → ZMod 2) :
    (jointEnhancement (gaugePullback qσ g.symm) (gaugePullback qτ h.symm)).q
        (sumArrowCongr g h l)
      = (jointEnhancement qσ qτ).q l := by
  show qσ.q (g.symm (fun i => sumArrowCongr g h l (Sum.inl i)))
      + -(qτ.q (h.symm (fun i => sumArrowCongr g h l (Sum.inr i))))
    = qσ.q (fun i => l (Sum.inl i)) + -(qτ.q (fun i => l (Sum.inr i)))
  rw [sumArrowCongr_comp_inl, sumArrowCongr_comp_inr, g.symm_apply_apply, h.symm_apply_apply]

/-- **The polar form is invariant under the block gauge** too. -/
theorem jointEnhancement_B_gaugePullback (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) (u v : Fin nσ ⊕ Fin nτ → ZMod 2) :
    (jointEnhancement (gaugePullback qσ g.symm) (gaugePullback qτ h.symm)).B
        (sumArrowCongr g h u) (sumArrowCongr g h v)
      = (jointEnhancement qσ qτ).B u v := by
  show qσ.B (g.symm (fun i => sumArrowCongr g h u (Sum.inl i)))
        (g.symm (fun i => sumArrowCongr g h v (Sum.inl i)))
      + qτ.B (h.symm (fun i => sumArrowCongr g h u (Sum.inr i)))
        (h.symm (fun i => sumArrowCongr g h v (Sum.inr i)))
    = qσ.B (fun i => u (Sum.inl i)) (fun i => v (Sum.inl i))
      + qτ.B (fun i => u (Sum.inr i)) (fun i => v (Sum.inr i))
  rw [sumArrowCongr_comp_inl, sumArrowCongr_comp_inl, sumArrowCongr_comp_inr,
    sumArrowCongr_comp_inr, g.symm_apply_apply, g.symm_apply_apply, h.symm_apply_apply,
    h.symm_apply_apply]

/-- **THE HEADLINE — the realized carrier's Taylor leg is gauge-INVARIANT through the corrected
seam, at EVERY rank.** Gauge the carried cohomology bases of both ends by arbitrary `g`, `h` and move
the enhancements as `hpolar` forces; the corrected seam's Taylor-leg condition on the computed kernel
`L = ker (transportedBInc …)` is unchanged. This is an IFF and needs no new hypothesis — the Gram
operator is invertible unconditionally (`Z4Quadratic.nondeg`). `CharSurfacePDBundled.§6` shows the
raw seam has no such property at nonzero rank; §5 below exhibits the disagreement concretely. -/
theorem taylorLegVanishes_gaugeTied_iff (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) :
    TaylorLegVanishes (gaugePullback qσ g.symm) (gaugePullback qτ h.symm)
        (LinearMap.ker (transportedBInc (toDataPD (gaugePullback qσ g.symm)
          (gaugePullback qτ h.symm) (gaugeTied d g h))))
      ↔ TaylorLegVanishes qσ qτ (LinearMap.ker (transportedBInc (toDataPD qσ qτ d))) := by
  rw [ker_transportedBInc_gaugeTied]
  constructor
  · exact fun hyp l hl =>
      (jointEnhancement_q_gaugePullback qσ qτ g h l).symm.trans (hyp _ ⟨l, hl, rfl⟩)
  · rintro hyp _ ⟨l, hl, rfl⟩
    exact (jointEnhancement_q_gaugePullback qσ qτ g h l).trans (hyp l hl)

/-- **The Lagrangian condition is gauge-invariant too** — so the anti-collapse engine
`brown_eq_of_taylorLeg_lagrangian` consumes gauge-independent input through the corrected seam. -/
theorem jointLagrangian_gaugeTied_iff (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)) :
    JointLagrangian (gaugePullback qσ g.symm) (gaugePullback qτ h.symm)
        (LinearMap.ker (transportedBInc (toDataPD (gaugePullback qσ g.symm)
          (gaugePullback qτ h.symm) (gaugeTied d g h))))
      ↔ JointLagrangian qσ qτ (LinearMap.ker (transportedBInc (toDataPD qσ qτ d))) := by
  rw [ker_transportedBInc_gaugeTied]
  constructor
  · intro hyp v hv
    have hv' : ∀ l ∈ Submodule.map (sumArrowCongr g h).toLinearMap
        (LinearMap.ker (transportedBInc (toDataPD qσ qτ d))),
        (jointEnhancement (gaugePullback qσ g.symm) (gaugePullback qτ h.symm)).B
          (sumArrowCongr g h v) l = 0 := by
      rintro _ ⟨l, hl, rfl⟩
      exact (jointEnhancement_B_gaugePullback qσ qτ g h v l).trans (hv l hl)
    obtain ⟨w, hw, hwv⟩ := hyp _ hv'
    exact (sumArrowCongr g h).injective hwv ▸ hw
  · intro hyp v hv
    refine ⟨(sumArrowCongr g h).symm v, hyp _ fun l hl => ?_, LinearEquiv.apply_symm_apply _ _⟩
    have key := jointEnhancement_B_gaugePullback qσ qτ g h ((sumArrowCongr g h).symm v) l
    rw [LinearEquiv.apply_symm_apply] at key
    exact key.symm.trans (hv (sumArrowCongr g h l) ⟨l, hl, rfl⟩)

/-- **The anti-collapse engine now runs on gauge-independent input.** If the corrected seam's Taylor
leg and Lagrangian conditions hold in ANY gauge of the realized carrier's carried bases, then the
ORIGINAL enhancements already have equal Brown invariants. So `abk8 := brown ∘ q` descends along the
realized `Bor` without a choice of basis — the conclusion `brown_eq_of_taylorLeg_lagrangian` supplies
is no longer contingent on which honest carrier of the geometry one reads. Through the RAW seam this
inference is unavailable: `CharSurfacePDBundled.gaugeGeoRealizationTied_derivedEσ` shows the leg
itself moves with the gauge, and §5 exhibits an explicit disagreement. -/
theorem brown_eq_of_gaugeTied_corrected_seam (qσ : Z4Quadratic (Fin nσ))
    (qτ : Z4Quadratic (Fin nτ)) (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (g : (Fin nσ → ZMod 2) ≃ₗ[ZMod 2] (Fin nσ → ZMod 2))
    (h : (Fin nτ → ZMod 2) ≃ₗ[ZMod 2] (Fin nτ → ZMod 2))
    (htaylor : TaylorLegVanishes (gaugePullback qσ g.symm) (gaugePullback qτ h.symm)
      (LinearMap.ker (transportedBInc (toDataPD (gaugePullback qσ g.symm)
        (gaugePullback qτ h.symm) (gaugeTied d g h)))))
    (hlag : JointLagrangian (gaugePullback qσ g.symm) (gaugePullback qτ h.symm)
      (LinearMap.ker (transportedBInc (toDataPD (gaugePullback qσ g.symm)
        (gaugePullback qτ h.symm) (gaugeTied d g h))))) :
    qσ.brown = qτ.brown :=
  brown_eq_of_taylorLeg_lagrangian qσ qτ _
    ((taylorLegVanishes_gaugeTied_iff qσ qτ d g h).mp htaylor)
    ((jointLagrangian_gaugeTied_iff qσ qτ d g h).mp hlag)

/-! ## §5. NON-VACUITY — the corrected seam genuinely differs from the live one -/

/-- The block Gram reparametrization of §3 on the genus-1/genus-1 seam, evaluated on the a-cycle of
the σ-end: it is the coordinate SWAP there, not the identity (`gramMap_hyperbolic2`). -/
theorem sumArrowCongr_gram_hyperbolic2_witness :
    sumArrowCongr (gramEquiv hyperbolic2) (gramEquiv hyperbolic2) (Sum.elim ![1, 0] ![0, 0])
      = Sum.elim ![0, 1] ![0, 0] := by
  funext i
  cases i with
  | inl i =>
      show gramMap hyperbolic2 (fun j => Sum.elim ![1, 0] ![0, 0] (Sum.inl j)) i
        = Sum.elim ![0, 1] ![0, 0] (Sum.inl i)
      rw [show (fun j => (Sum.elim ![1, 0] ![0, 0] : Fin 2 ⊕ Fin 2 → ZMod 2) (Sum.inl j))
            = ![1, 0] from rfl, gramMap_hyperbolic2]
      revert i; decide
  | inr i =>
      show gramMap hyperbolic2 (fun j => Sum.elim ![1, 0] ![0, 0] (Sum.inr j)) i
        = Sum.elim ![0, 1] ![0, 0] (Sum.inr i)
      rw [show (fun j => (Sum.elim ![1, 0] ![0, 0] : Fin 2 ⊕ Fin 2 → ZMod 2) (Sum.inr j))
            = ![0, 0] from rfl, gramMap_hyperbolic2]
      revert i; decide

/-- **THE NON-VACUITY CERTIFICATE — unconditional, no realization datum required.** On the seam's own
coordinate space `(Fin 2 ⊕ Fin 2 → ℤ/2)` with a genus-1 enhancement at each end, the τ-end-negated
joint enhancement `TaylorLegVanishes` tests VANISHES on the a-cycle class read in PD-corrected
coordinates and FAILS to vanish on the same class read in the live seam's raw Kronecker coordinates
(the two are related by the block Gram map, §3 `ker_transportedBInc_toDataPD`). So the corrected and
live Taylor legs are genuinely different conditions at nonzero rank — the repair is not a
renormalization no-op. This statement quantifies over nothing, so it cannot be vacuous. -/
theorem seam_joint_taylor_flip :
    (jointEnhancement hyperbolic2 hyperbolic2).q (Sum.elim ![1, 0] ![0, 0]) = 0
      ∧ (jointEnhancement hyperbolic2 hyperbolic2).q
          (sumArrowCongr (gramEquiv hyperbolic2) (gramEquiv hyperbolic2)
            (Sum.elim ![1, 0] ![0, 0])) ≠ 0 := by
  refine ⟨by decide, ?_⟩
  rw [sumArrowCongr_gram_hyperbolic2_witness]
  decide

/-- **The genus-1 seam witness.** For ANY realized datum whose σ-end has rank 2 and carries the
genus-1 (symplectic) enhancement `hyperbolic2`, the class `x` whose PD-corrected seam coordinates are
the a-cycle `![1, 0]` is read by the LIVE seam as `![0, 1]` — because the Gram operator of a
symplectic basis is the coordinate swap, not the identity (`gramMap_hyperbolic2`). No inhabitation of
`GeoRealizationTied` is required: `x` is produced by the corrected seam basis's own `symm`. -/
theorem derivedEσ_of_derivedEσPD_hyperbolic2 {Sσ Sτ : TopCat}
    {bσ : Cohomology Sσ 1 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)}
    {bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)}
    (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    d.derivedEσ ((derivedEσPD hyperbolic2 d).symm ![1, 0]) = ![0, 1] := by
  rw [← gramMap_derivedEσPD hyperbolic2 d, LinearEquiv.apply_symm_apply, gramMap_hyperbolic2]
  rfl

/-- **THE SEAM-LEVEL TRUTH-VALUE FLIP — the non-vacuity certificate.** On the SAME geometric class of
the SAME realized membrane, the genus-1 enhancement reads `0` through the corrected seam (the honest
Taylor/Klug value on the a-cycle metabolizer) and `≠ 0` through the live seam. So the realized
carrier's `TaylorLegVanishes` is not merely unproven at nonzero rank through the raw bases — it is
mis-stated, exactly as `CharSurfacePDTransport.hyperbolic2_taylor_flip` establishes for the surface
bridge. This is what the repair fixes.

**Vacuity disclosure.** This form is universally quantified over `d`, so its force depends on a
rank-2 realized datum existing; `PinPlusCharPairCylRealization.cylRealizationTied` is the inhabiting
family (any compact-T2 `Y` with a rank-2 carried basis). `seam_joint_taylor_flip` above is the
quantifier-free version and carries the certificate unconditionally. -/
theorem seam_taylor_flip {Sσ Sτ : TopCat}
    {bσ : Cohomology Sσ 1 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)}
    {bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)}
    (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    hyperbolic2.q (derivedEσPD hyperbolic2 d ((derivedEσPD hyperbolic2 d).symm ![1, 0])) = 0
      ∧ hyperbolic2.q (d.derivedEσ ((derivedEσPD hyperbolic2 d).symm ![1, 0])) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [LinearEquiv.apply_symm_apply]; decide
  · rw [derivedEσ_of_derivedEσPD_hyperbolic2]; decide

/-- **The corrected and live seam bases are genuinely different equivalences at nonzero rank** — the
statement that the repair is not a no-op. -/
theorem derivedEσPD_ne_derivedEσ {Sσ Sτ : TopCat}
    {bσ : Cohomology Sσ 1 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)}
    {bτ : Cohomology Sτ 1 ≃ₗ[ZMod 2] (Fin nτ → ZMod 2)}
    (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    derivedEσPD hyperbolic2 d ≠ d.derivedEσ := by
  intro hcontra
  have h1 : derivedEσPD hyperbolic2 d ((derivedEσPD hyperbolic2 d).symm ![1, 0]) = ![1, 0] :=
    LinearEquiv.apply_symm_apply _ _
  have h2 : d.derivedEσ ((derivedEσPD hyperbolic2 d).symm ![1, 0]) = ![0, 1] :=
    derivedEσ_of_derivedEσPD_hyperbolic2 d
  have h3 : (![1, 0] : Fin 2 → ZMod 2) = ![0, 1] := by
    rw [← h1, ← h2]
    exact DFunLike.congr_fun hcontra _
  exact absurd (congrFun h3 0) (by decide)

/-! ## §6. EQUIVALENCE CERTIFICATE — the live rank-zero realization chain is untouched -/

/-- At rank zero the corrected σ seam basis is *equal* to the live one. -/
theorem derivedEσPD_eq_of_rank_zero (hn : nσ = 0) (qσ : Z4Quadratic (Fin nσ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) : derivedEσPD qσ d = d.derivedEσ := by
  haveI : IsEmpty (Fin nσ) := by rw [hn]; infer_instance
  exact LinearEquiv.ext fun _ => Subsingleton.elim (α := Fin nσ → ZMod 2) _ _

/-- At rank zero the corrected τ seam basis is *equal* to the live one. -/
theorem derivedEτPD_eq_of_rank_zero (hn : nτ = 0) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) : derivedEτPD qτ d = d.derivedEτ := by
  haveI : IsEmpty (Fin nτ) := by rw [hn]; infer_instance
  exact LinearEquiv.ext fun _ => Subsingleton.elim (α := Fin nτ → ZMod 2) _ _

/-- **THE EQUIVALENCE CERTIFICATE.** At rank zero on both ends the corrected realization datum is
*equal* to the live one, so `GeoRealizationTied.toData`, `toMembrane`, `toMembrane_L` and everything
the rank-zero realization chain derives from them may be restated over the corrected seam with no
proof changes. The M4 blast radius, like the M4 defect itself, is strictly nonzero-rank. -/
theorem toDataPD_eq_of_rank_zero (hσ : nσ = 0) (hτ : nτ = 0) (qσ : Z4Quadratic (Fin nσ))
    (qτ : Z4Quadratic (Fin nτ)) (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    toDataPD qσ qτ d = d.toData :=
  congrArg₂ (fun a b => GeoRealizationData.mk d.bdry d.Q d.U d.hU d.ι a b d.eQ)
    (derivedEσPD_eq_of_rank_zero hσ qσ d) (derivedEτPD_eq_of_rank_zero hτ qτ d)

/-- The corrected membrane is *equal* to the live one at rank zero — hence so is its computed
Taylor-leg submodule. -/
theorem toMembranePD_eq_of_rank_zero (hσ : nσ = 0) (hτ : nτ = 0) (qσ : Z4Quadratic (Fin nσ))
    (qτ : Z4Quadratic (Fin nτ)) (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    toMembranePD qσ qτ d = d.toMembrane qσ qτ :=
  congrArg (GeoMembrane.ofGeometric qσ qτ) (toDataPD_eq_of_rank_zero hσ hτ qσ qτ d)

/-- The rank-zero Taylor legs coincide — the form the downstream `TaylorLegVanishes` consumers use. -/
theorem ker_transportedBInc_eq_of_rank_zero (hσ : nσ = 0) (hτ : nτ = 0)
    (qσ : Z4Quadratic (Fin nσ)) (qτ : Z4Quadratic (Fin nτ))
    (d : GeoRealizationTied Sσ Sτ bσ bτ) :
    LinearMap.ker (transportedBInc (toDataPD qσ qτ d))
      = LinearMap.ker (transportedBInc d.toData) :=
  congrArg (fun e => LinearMap.ker (transportedBInc e)) (toDataPD_eq_of_rank_zero hσ hτ qσ qτ d)

/-! ## §7. The PD normalization — CONDITIONAL, with the missing coherence named -/

/-- **Why `derivedEσPD` is the right seam basis — sufficient, given the surface's polar tie and PD
tower.** If the σ-end surface carries a Poincaré-duality map `pd` with the cap adjunction, and the
enhancement `qσ` satisfies the carrier's `hpolar` against the same fundamental class, then the
corrected seam basis sends the PD image of the carried cohomology basis to the standard basis. That
is the Guillou–Marin/Taylor requirement on `H₁`, and it is FALSE for the raw seam basis unless the
Gram operator is the identity (§5).

**This is a SUFFICIENT bridge, not an equivalence**, and `hpolar`/`hpd` are hypotheses that
`GeoRealizationTied` does NOT carry — the missing-coherence gap flagged in the module docstring. They
are named here rather than assumed silently; the gauge-invariance results of §4 hold without them. -/
theorem derivedEσPD_pd (qσ : Z4Quadratic (Fin nσ)) (d : GeoRealizationTied Sσ Sτ bσ bτ)
    (surfClassσ : Homology Sσ 2)
    (hpolar : ∀ a b : Cohomology Sσ 1, qσ.B (bσ a) (bσ b) = kroneckerH 2 (cupH a b) surfClassσ)
    (pd : Cohomology Sσ 1 → Homology Sσ 1)
    (hpd : ∀ ω a : Cohomology Sσ 1, kroneckerH 1 ω (pd a) = kroneckerH 2 (cupH ω a) surfClassσ)
    (a : Cohomology Sσ 1) :
    derivedEσPD qσ d ((homeoHomologyEquiv d.homσ 1).symm (pd a)) = bσ a := by
  show homologyBasisPD (N := 0) qσ bσ
      (homeoHomologyEquiv d.homσ 1 ((homeoHomologyEquiv d.homσ 1).symm (pd a))) = bσ a
  rw [LinearEquiv.apply_symm_apply]
  exact homologyBasisPD_pd qσ bσ surfClassσ hpolar pd hpd a

end SKEFTHawking.PinPlusCharPairRealizationTiedPD
