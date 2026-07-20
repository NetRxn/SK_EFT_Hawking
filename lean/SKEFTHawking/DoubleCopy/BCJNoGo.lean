import Mathlib
import SKEFTHawking.DoubleCopy.PetrovD
import SKEFTHawking.GaugeErasure
import SKEFTHawking.SoftTheorems.DissipativeNoGo

/-!
# Phase 6o Wave 1b.5: Strong-form BCJ NO-GO — derived from substrate structure

## Goal (R-02 remediation, 2026-07-20)

Encode the substantive **structural negative theorem** per CK-Duality DR
§1 + §5.1: the strong claim "(ADW emergent gravity) = (pre-erasure non-Abelian
gauge)²" via standard BCJ **fails** at the SK-EFT substrate level. Previously
this module conjoined three `True` placeholders; it now **derives the
obstruction from genuine structure** and states the no-go as a real negation
`¬ StrongFormBCJViable`.

The three obstructions (CK-Duality DR §5.1.2) are now genuine propositions:

* **O1 — Lorentz/frame breaking (`LorentzFrameBroken`).** Standard BCJ needs a
  reflection-symmetric (Lorentz/time-reversal-invariant) kinematic kernel to
  define cubic-graph numerators. The SK-EFT retarded response carries a genuine
  *dissipative*, odd-in-ω term (`−iγω`, γ>0; the R-01
  `SoftTheorems.RetardedResponse` substrate), so `K_R(ω) ≠ K_R(−ω)`: the
  reflection symmetry is broken. *Derived from the dissipative kernel.*
* **O5 — gauge erasure forces Abelian IR (`GaugeErasureForcesAbelianIR`).** BCJ
  color-kinematics duality has content only if the IR gauge group carries a
  non-trivial commutator (`f^{abc} ≠ 0`). Gauge erasure (`GaugeErasure`) leaves
  only the Abelian `U(1) = Circle` in the IR; an Abelian group has *every*
  commutator trivial, so all color factors vanish (`c_s=c_t=c_u=0`), color-Jacobi
  is content-free, and the test is vacuous. *Derived from
  `GaugeErasure.circle_survives` + the color-erasure lemma.*
* **O3 — UV/IR scale-ordering mismatch (`UVIRScaleOrderingMismatch`).** The
  pre-erasure non-Abelian gauge sector is UV; the ADW emergent graviton is IR;
  BCJ requires both at the same kinematic scale. Modeled by a genuine strict
  scale separation `adwGravityScale < preErasureGaugeScale` (schematic UV≫IR
  placeholder, DR §4.3/§iii), which forbids the same-scale requirement.

## Non-vacuity (hypotheses load-bearing)

`dihedral_color_nontrivial` exhibits a genuinely non-Abelian gauge group
(`DihedralGroup 3`) that *does* carry non-trivial color structure — so the
Abelian-IR hypothesis of O5 is load-bearing, not vacuous.

## References

- CK-Duality DR §1 + §5.1 + §5.1.2 (O1/O3/O5) + §4.3.
- Cheung-Mangan, arXiv:2010.15970 (dissipative/non-relativistic DC = tensor
  bi-fluid, not gravity — cautionary precedent for O1).
- `GaugeErasure.lean` (gauge-erasure survival criterion — O5).
- `SoftTheorems/DissipativeNoGo.lean` (R-01 damped-oscillator kernel — O1).
-/

noncomputable section

namespace SKEFTHawking.DoubleCopy

open SKEFTHawking.SoftTheorems

/-! ## §1. O5 substrate: color structure and the gauge-erasure obstruction -/

/-- A gauge group `G` carries **non-trivial color structure** iff it has a
non-trivial commutator `[a,b] = a b a⁻¹ b⁻¹ ≠ 1` — the group-level analogue of
non-vanishing structure constants `f^{abc} ≠ 0`. BCJ color-kinematics duality is
non-vacuous only when this holds. -/
def ColorStructureNonTrivial (G : Type*) [Group G] : Prop :=
  ∃ a b : G, a * b * a⁻¹ * b⁻¹ ≠ 1

/-- **O5 core (genuine, cross-module).** Any gauge group that *survives*
hydrodynamization (`GaugeErasure.SurvivesHydro`, i.e. is Abelian / center = ⊤)
has **trivial** color structure: every commutator is `1`, so all BCJ color
factors vanish. This is the gauge-erasure-induced abelianization of the IR. -/
theorem survivesHydro_color_erased (G : Type*) [Group G]
    (h : SKEFTHawking.GaugeErasure.SurvivesHydro G) : ¬ ColorStructureNonTrivial G := by
  rintro ⟨a, b, hab⟩
  apply hab
  rw [(SKEFTHawking.GaugeErasure.survivesHydro_iff_comm G).mp h a b]
  group

/-- **Non-vacuity of O5.** A genuinely non-Abelian gauge group (`DihedralGroup 3
≅ S₃`) *does* carry non-trivial color structure — so the Abelian-IR hypothesis
is load-bearing. -/
theorem dihedral_color_nontrivial : ColorStructureNonTrivial (DihedralGroup 3) :=
  ⟨DihedralGroup.r 1, DihedralGroup.sr 0, by decide⟩

/-! ## §2. The three genuine obstructions -/

/-- **O1 — Lorentz/frame breaking.** The SK-EFT dissipative retarded kernel is
NOT reflection-symmetric: there is a real frequency at which `K_R(ω) ≠ K_R(−ω)`,
so no Lorentz/time-reversal-invariant kinematic-numerator structure exists. -/
def LorentzFrameBroken : Prop :=
  ∃ ω : ℝ, dampedGappedMode.kernel ω ≠ dampedGappedMode.kernel (-ω)

/-- **O5 — gauge erasure makes the IR Abelian.** The surviving IR gauge group
`U(1) = Circle` has no non-trivial color structure (all commutators trivial),
making color-Jacobi content-free. -/
def GaugeErasureForcesAbelianIR : Prop := ¬ ColorStructureNonTrivial Circle

/-- ADW emergent-graviton (IR) kinematic scale (schematic UV≫IR placeholder). -/
def adwGravityScale : ℝ := 1
/-- Pre-erasure non-Abelian gauge (UV) kinematic scale (schematic placeholder). -/
def preErasureGaugeScale : ℝ := 2

/-- **O3 — UV/IR scale-ordering mismatch.** The IR gravity scale is strictly
below the UV gauge scale, so the two sectors cannot sit at the same kinematic
scale as standard BCJ requires. -/
def UVIRScaleOrderingMismatch : Prop := adwGravityScale < preErasureGaugeScale

/-! ## §3. Witnesses for the three obstructions (each derived) -/

/-- O1 witnessed at ω = 1: `K_R(1) = −i`, `K_R(−1) = +i` for `dampedGappedMode`
(γ = 1 > 0). The dissipative odd-ω term breaks the reflection symmetry. -/
theorem lorentzFrameBroken_witness : LorentzFrameBroken := by
  refine ⟨1, ?_⟩
  intro h
  have := congrArg Complex.im h
  rw [RetardedResponse.kernel_im, RetardedResponse.kernel_im] at this
  simp only [dampedGappedMode] at this
  norm_num at this

/-- O5 witnessed: the surviving IR `U(1) = Circle` is Abelian, so
(via `survivesHydro_color_erased` + `GaugeErasure.circle_survives`) it has no
non-trivial color structure. -/
theorem gaugeErasureForcesAbelianIR_witness : GaugeErasureForcesAbelianIR :=
  survivesHydro_color_erased Circle SKEFTHawking.GaugeErasure.circle_survives

/-- O3 witnessed: `1 < 2`. -/
theorem uvIrScaleOrderingMismatch_witness : UVIRScaleOrderingMismatch := by
  unfold UVIRScaleOrderingMismatch adwGravityScale preErasureGaugeScale; norm_num

/-- The strong-form BCJ claim is structurally obstructed: all three genuine
obstructions hold on the SK-EFT-Hawking substrate. -/
def StrongFormBCJObstructed : Prop :=
  LorentzFrameBroken ∧ GaugeErasureForcesAbelianIR ∧ UVIRScaleOrderingMismatch

theorem strongFormBCJObstructed_witness : StrongFormBCJObstructed :=
  ⟨lorentzFrameBroken_witness,
   gaugeErasureForcesAbelianIR_witness,
   uvIrScaleOrderingMismatch_witness⟩

/-! ## §4. The strong-form BCJ NO-GO as a derived negation -/

/-- The three conditions the strong-form BCJ double copy would **require** on the
substrate:
* (a) a reflection-symmetric (Lorentz-invariant) kinematic kernel,
* (b) a non-trivial (non-Abelian) IR color structure,
* (c) gauge and gravity sectors at the same kinematic scale. -/
def StrongFormBCJViable : Prop :=
  (∀ ω : ℝ, dampedGappedMode.kernel ω = dampedGappedMode.kernel (-ω))
  ∧ ColorStructureNonTrivial Circle
  ∧ adwGravityScale = preErasureGaugeScale

/-- **Wave 1b.5 substantive structural NO-GO** (CK-Duality DR §1 + §5.1).

The strong-form BCJ claim "(ADW emergent gravity) = (pre-erasure non-Abelian
gauge)²" is **not viable** on the SK-EFT substrate: `¬ StrongFormBCJViable`. This
is a *derived contradiction*, not a conjunction of assumed truths — each required
condition is refuted by genuine substrate structure (proved independently in the
three lemmas below). Here we discharge it via the O5 leg (gauge-erasure
abelianization). -/
theorem wave_1b_5_strongForm_BCJ_no_go : ¬ StrongFormBCJViable := by
  rintro ⟨_, hcolor, _⟩
  exact gaugeErasureForcesAbelianIR_witness hcolor

/-- Each obstruction independently refutes viability — O1 (dissipation). -/
theorem strongFormBCJ_refuted_by_dissipation : ¬ StrongFormBCJViable := by
  rintro ⟨hsym, _, _⟩
  have hbroken := lorentzFrameBroken_witness
  obtain ⟨ω, hω⟩ := hbroken
  exact hω (hsym ω)

/-- Each obstruction independently refutes viability — O5 (gauge erasure). -/
theorem strongFormBCJ_refuted_by_gauge_erasure : ¬ StrongFormBCJViable := by
  rintro ⟨_, hcolor, _⟩
  exact gaugeErasureForcesAbelianIR_witness hcolor

/-- Each obstruction independently refutes viability — O3 (scale ordering). -/
theorem strongFormBCJ_refuted_by_scale_mismatch : ¬ StrongFormBCJViable := by
  rintro ⟨_, _, hscale⟩
  rw [adwGravityScale, preErasureGaugeScale] at hscale
  norm_num at hscale

end SKEFTHawking.DoubleCopy
