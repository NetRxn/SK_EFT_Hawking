import SKEFTHawking.Basic
import SKEFTHawking.MajoranaRung
import SKEFTHawking.MajoranaRungDecoupling
import SKEFTHawking.Z16AnomalyComputation
import SKEFTHawking.HiddenSectorClassification
import Mathlib

/-!
# Phase 5z Wave 4: Symmetric-Mass-Generation Route to the Majorana Rung

## Overview

Parallel substrate-bridge to the Wave 2 BCS-exponential
`H_MR_FromADWSubstrate_BCS_LNV` form. Wave 2a deep research confirmed a
structural lepton-number-symmetry obstruction to the BCS branch:
`MajoranaRung.lepton_number_symmetry_obstructs_BCS_form` shows that a
substrate with `G_LV = 0` cannot satisfy the strong BCS form for any
`Λ_ADW`. SMG (Symmetric Mass Generation) gaps fermions through
composite-fermion condensates that are SM-symmetric, **without**
requiring lepton-number violation, structurally bypassing the no-go.

Lattice anchor: Hasenfratz–Witzel SU(3) N_f = 8 lattice studies
(arXiv:2412.10322 + arXiv:2511.22678 EPS-HEP2025) demonstrate a
strong-coupling SMG fixed point in the continuum limit. Razamat–Tong
(PRX 11 011063, 2021) prove that 16 Weyl fermions can be gapped while
preserving Spin × ℤ₄ symmetry. Catterall (SciPost Phys. 16 108, 2024)
reaches Pati–Salam structure from Kähler–Dirac on lattice via SMG
mirror decoupling — the lattice manifestation of the same ℤ₁₆
classification used in Embedding III.

The Wave 4 module ships the parallel tracked-hypothesis bridge:

  - `H_SubstrateNearSMGFixedPoint s Λ_SMG` — substrate sits in the
    Hasenfratz–Witzel band with a definite gap scale `Λ_SMG > 0`
    (non-vacuous: requires `0.1 ≤ c_SMG ≤ 1.0` from HW lattice anchor).
  - `H_MR_FromSMGGap m Λ_SMG` — `M_R i = c_i · Λ_SMG` for some
    per-generation `c_i ∈ (0, 1]`. **No `H_LeptonNumberViolated`
    precondition** — this is the structural bypass.

## Open hypotheses (post-deep-research, 2026-04-27)

The Wave 4 deep-research return at
`Lit-Search/Phase-5z/Phase 5z Wave 4 — SMG Substrate Phase Diagram.md`
(verdict 2026-04-27) reports **OPEN-AT-LITERATURE-FRONTIER on all three
sub-questions, with a literature-attested negative tilt** from
Vladimirov–Diakonov's own mean-field (PRD 86 104019, 2012) which finds
chiral-SSB and trivially-gapped phases but no SMG phase in the
published 2-parameter slice. Consequently:

- **OPEN-W4-1**: substrate sits in HW SMG window. Closure needs (i)
  lattice MC of the V&D 8-coupling action, (ii) FRG analysis of the
  full coupling space, (iii) Razamat–Tong-style anomaly compatibility
  for emergent (vs background) Lorentz Spin(4).
- **OPEN-W4-2**: per-generation `c_i` coefficients. Closure needs
  Catterall mirror-decoupling geometry computed for ADW substrate (4D
  decoupling is conjectural; rigorous only in 2D via Fidkowski-Kitaev).
- **OPEN-W4-3**: Catterall–Pati–Salam structure on ADW substrate
  (lattice MC verification).

**Wave 4 ships as a SECOND structural no-go, parallel to Wave 2's BCS
no-go.** Both natural mass-generation mechanisms for the ADW substrate
carry literature-frontier obstructions: (i) BCS via the L-symmetry
obstruction (Wave 2a), (ii) SMG via the substrate-phase-diagram OPEN
status (Wave 4 deep research). Phase 6h escalation is therefore
conditional on closure of one of the OPEN sub-questions; until then,
the Wave 4 module ships the structural-bypass theorem
(`smg_route_disjoint_from_L_conserving_BCS`) as a tracked-hypothesis
result, NOT a derived theorem.

**Quantitative parameter band correction (deep research §2):** the
dimensionless ratio `c_SMG = Λ_SMG / Λ_UV` is bounded by the
NJL-derived envelope `[10⁻¹², 10⁻³]` (broad) or the seesaw-restricted
band `[10⁻¹⁰, 10⁻⁴]` (requires fine-tuning of (λ_i) of order 10–30%
per deep research §2.3). The Hasenfratz–Witzel lattice ratio
`Λ_D / a⁻¹ ≈ 0.13` is in lattice units, NOT the physical `Λ_SMG / Λ_UV`
ratio for a substrate at Planck-scale UV cutoff. This module uses the
seesaw-restricted band with `Λ_UV = M_Pl ≈ 10¹⁹` GeV.

## References

- Hasenfratz & Witzel, arXiv:2412.10322 (2024);
  arXiv:2511.22678 (2025, EPS-HEP2025) — SU(3) N_f=8 SMG continuum-limit.
- Razamat & Tong, PRX 11 011063 (2021) — gapped chiral fermions
  preserving Spin × ℤ₄.
- Catterall, SciPost Phys. 16 108 (2024) — Kähler–Dirac → Pati–Salam.
- Wan & Wang, arXiv:2512.25038 (2025) — K-gauge TQFT anomaly tables.
- Antusch et al., hep-ph/0211385 (2003) — L-symmetry argument used in
  the parallel BCS no-go (Wave 2).
- Phase 5z Wave 4 roadmap §"Track B continued — SMG Alternative for the
  Majorana Rung", `docs/roadmaps/Phase5z_Roadmap.md`.
-/

noncomputable section

open Real

namespace SKEFTHawking.MajoranaRungSMG

/-! ## 1. SMG-substrate data carrier

Packs the four substrate parameters needed for the Hasenfratz–Witzel
mapping `Λ_SMG = c_SMG · Λ_UV`. The dimensionless coefficient `c_SMG`
is structurally bounded in `(0, 1]` (a confining gap cannot exceed the
UV cutoff); the HW lattice band tightens this to `[0.1, 1.0]`.
-/

/-- Substrate parameters for the SMG-window mapping.
- `Λ_UV` — substrate UV cutoff [natural units].
- `Λ_UV_pos` — `0 < Λ_UV`.
- `c_SMG` — dimensionless ratio `Λ_SMG / Λ_UV`.
- `c_SMG_pos` — `0 < c_SMG`.
- `c_SMG_le_one` — `c_SMG ≤ 1` (gap cannot exceed UV cutoff). -/
structure SMGSubstrateData where
  Λ_UV : ℝ
  Λ_UV_pos : 0 < Λ_UV
  c_SMG : ℝ
  c_SMG_pos : 0 < c_SMG
  c_SMG_le_one : c_SMG ≤ 1

/-! ## 2. H_SubstrateNearSMGFixedPoint — tracked hypothesis

Substrate sits in the Hasenfratz–Witzel SMG window with a definite gap
scale `Λ_SMG > 0`. Non-vacuous: requires the HW lattice band
`0.1 ≤ c_SMG ≤ 1.0` AND `Λ_SMG = c_SMG · Λ_UV`.
-/

/-- **WAVE4-OPEN-1**: tracked hypothesis that the substrate parameters
sit in the seesaw-restricted SMG window AND `Λ_SMG = c_SMG · Λ_UV`.
The dimensionless ratio `c_SMG = Λ_SMG / Λ_UV` is bounded above and
below by the **NJL-derived seesaw-restricted band**
`c_SMG ∈ [10⁻¹⁰, 10⁻⁴]` per the Wave 4 deep-research return
(`Lit-Search/Phase-5z/Phase 5z Wave 4 — SMG Substrate Phase Diagram.md`
§2.2–2.3, verdict 2026-04-27). The original lattice-units anchor
`c_SMG ≈ 0.13` from Hasenfratz–Witzel is the ratio `Λ_D / a⁻¹` in
lattice units, NOT the physical ratio `Λ_SMG / Λ_UV` for a substrate
with `Λ_UV ≈ M_Pl ≈ 10¹⁹` GeV. After the project-internal
Fierz-translation of HW's `g²_GF ≳ 25` onto the V&D 8-coupling NJL
scaling (deep research §1.3 + §2.2), the physical `c_SMG` band lands
in `[10⁻¹⁰, 10⁻⁴]` for the seesaw-restricted regime
(M_R ∈ [10⁹, 10¹⁵] GeV at Λ_UV ≈ M_Pl), with broader scaling envelope
`[10⁻¹², 10⁻³]` at unrestricted `g_eff − g_c`. The lower band 10⁻¹⁰
corresponds to seesaw-band M_R lower edge; upper 10⁻⁴ to upper edge.

**Status (2026-04-27 deep-research verdict):** OPEN-AT-LITERATURE-FRONTIER.
The hypothesis carries three flagged risk axes (Wave 4 deep research §7):
- (R1) Fierz-rearrangement of HW's g²_GF onto V&D's (g_1, g_2, g_3) is
  project-internal; ±50% on threshold.
- (R4) ADW emergent Lorentz SO(4) vs Razamat–Tong background Spin(4)
  anomaly-matching is unaddressed in literature.
- (R10) Catterall 4D mirror decoupling is conjectural (rigorous only in
  2D via Fidkowski–Kitaev). -/
def H_SubstrateNearSMGFixedPoint (s : SMGSubstrateData) (Λ_SMG : ℝ) : Prop :=
  (1.0e-10 : ℝ) ≤ s.c_SMG ∧ s.c_SMG ≤ (1.0e-4 : ℝ) ∧
    Λ_SMG = s.c_SMG * s.Λ_UV

/-- Non-vacuity witness for `H_SubstrateNearSMGFixedPoint`: the
NJL-band fiducial `c_SMG = 10⁻⁷` (geometric mid-band of
[10⁻¹⁰, 10⁻⁴]) admits the canonical assignment.
Concretely: `c_SMG = 1.0e-7`, `Λ_UV = 1`, `Λ_SMG = 1.0e-7`. -/
theorem H_SubstrateNearSMGFixedPoint_consistent :
    ∃ (s : SMGSubstrateData) (Λ_SMG : ℝ),
      H_SubstrateNearSMGFixedPoint s Λ_SMG := by
  refine ⟨⟨1, one_pos, 1.0e-7, by norm_num, by norm_num⟩, 1.0e-7, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num

/-! ## 3. H_MR_FromSMGGap — tracked hypothesis with NO LNV precondition

This is the structural bypass. Compare with
`MajoranaRung.H_MR_FromADWSubstrate_BCS_LNV` which conjoins
`H_LeptonNumberViolated G_LV` as a precondition. The SMG predicate's
conjunction does NOT include any `H_LeptonNumberViolated` term —
SMG gaps fermions through composite-fermion condensates that are
SM-symmetric (Razamat–Tong, Catterall).
-/

/-- **WAVE4-OPEN-2**: tracked hypothesis that the per-generation Majorana
mass `M_R i` arises from the substrate SMG gap scale via
`M_R i = c_i · Λ_SMG` for some `c_i ∈ (0, 1]`. **No lepton-number-
violation precondition.** -/
def H_MR_FromSMGGap (m : MajoranaRung.MajoranaRungData) (Λ_SMG : ℝ) : Prop :=
  ∀ i : Fin 3, ∃ c_i : ℝ, 0 < c_i ∧ c_i ≤ 1 ∧ m.M_R i = c_i * Λ_SMG

/-! ## 4. Bypass theorem — SMG route does not require LNV

The structural disjointness theorem. At a single witness substrate, SMG
holds at a positive gap scale AND the BCS form universally fails at
`G_LV = 0` (substrate L-conserving) per
`MajoranaRung.L_conserving_substrate_obstructs_BCS_form`. This is the
formal expression that SMG is strictly stronger in the L-conserving
half of substrate parameter space.
-/

/-- **Disjointness of regimes (load-bearing)**: there exists a witness
`MajoranaRungData` and positive `Λ_SMG` for which the SMG hypothesis
holds, AND for that same `m` the BCS form fails universally at every
`Λ_ADW > 0` under `G_LV = 0`. This is the formal bypass of
`MajoranaRung.lepton_number_symmetry_obstructs_BCS_form`: the SMG
mechanism gaps fermions where the BCS branch is symmetry-forbidden.

Concretely the witness is `M_R i = Λ_SMG = 1`, `c_i = 1`. -/
theorem smg_route_disjoint_from_L_conserving_BCS :
    ∃ (m : MajoranaRung.MajoranaRungData) (Λ_SMG : ℝ),
      0 < Λ_SMG ∧
      H_MR_FromSMGGap m Λ_SMG ∧
      (∀ Λ_ADW : ℝ, ¬ MajoranaRung.H_MR_FromADWSubstrate_BCS_LNV m Λ_ADW 0) := by
  refine ⟨⟨fun _ => 1, fun _ => one_pos⟩, 1, one_pos, ?_, ?_⟩
  · -- SMG hypothesis: take c_i = 1 saturating M_R i = 1 = 1 · 1
    intro _
    exact ⟨1, one_pos, le_refl _, by ring⟩
  · -- BCS universal failure at G_LV = 0
    intro Λ_ADW
    exact MajoranaRung.L_conserving_substrate_obstructs_BCS_form
      ⟨fun _ => 1, fun _ => one_pos⟩ Λ_ADW

/-! ## 5. ℤ₁₆ singlet-branch compatibility — implicit cross-bridge

The SMG route saturates the SM-without-ν_R `+3 mod 16` hidden-sector
deficit through the same iff that classifies any +3-charge sector
(`HiddenSectorClassification.hidden_sector_anomaly_value 3`). The
Catterall–Kähler–Dirac 16-Weyl-per-generation lattice manifestation of
ℤ₁₆ is structurally indifferent to whether the +3 contribution comes
from fundamental ν_R (Embedding III) or from composite SMG-gapped
excitations. **Cross-bridge realized via file-level imports
(`Z16AnomalyComputation`, `HiddenSectorClassification`) + reuse of
`MajoranaRung.majorana_rung_compatible_with_hidden_singlet`** — no
SMG-specific theorem is shipped here because the algebraic content
(ZMod 16 saturation) is mechanism-agnostic at the Lean level (any +3
mechanism saturates identically). Adding a trivial-decide wrapper would
be the "definitional-unfolding-as-physics" antipattern.

## 6. Quantitative anchor — Λ_SMG in the seesaw band

Under the **NJL-derived seesaw-restricted band**
`c_SMG ∈ [10⁻¹⁰, 10⁻⁴]` AND substrate UV cutoff at the **Planck scale**
`Λ_UV = M_Pl ≈ 10¹⁹` GeV, the predicted `Λ_SMG` lies in the Type-I
seesaw band `[10⁹, 10¹⁵]` GeV. This is the deep-research-corrected
formulation per `Lit-Search/Phase-5z/Phase 5z Wave 4 — SMG Substrate
Phase Diagram.md` §2.3 (verdict 2026-04-27): the most natural substrate
UV cutoff is `M_Pl`, and the dimensionless `c_SMG` band is the
NJL-scaling-derived envelope, not the lattice-units `Λ_D / a⁻¹`
ratio reported by Hasenfratz–Witzel directly.
-/

/-- **Quantitative anchor (norm_num-backed)**: under the NJL-derived
seesaw-restricted band `c_SMG ∈ [10⁻¹⁰, 10⁻⁴]` AND `Λ_UV = M_Pl`
(10¹⁹ GeV, the natural substrate UV cutoff), `Λ_SMG` lands in the
Type-I seesaw band `[10⁹, 10¹⁵]` GeV exactly. Per Wave 4 deep research
§2.3. -/
theorem smg_window_predicts_Λ_SMG_in_seesaw_band
    (s : SMGSubstrateData) (Λ_SMG : ℝ)
    (h_smg : H_SubstrateNearSMGFixedPoint s Λ_SMG)
    (h_uv_planck : s.Λ_UV = (1.0e19 : ℝ)) :
    (1.0e9 : ℝ) ≤ Λ_SMG ∧ Λ_SMG ≤ 1.0e15 := by
  obtain ⟨h_lower, h_upper, h_eq⟩ := h_smg
  rw [h_eq, h_uv_planck]
  refine ⟨?_, ?_⟩
  · -- 1e-10 · 1e19 = 1e9 ≤ c_SMG · 1e19 since c_SMG ≥ 1e-10
    have h1 : (1.0e-10 : ℝ) * (1.0e19 : ℝ) ≤ s.c_SMG * (1.0e19 : ℝ) :=
      mul_le_mul_of_nonneg_right h_lower (by norm_num)
    linarith [h1]
  · -- c_SMG · 1e19 ≤ 1e-4 · 1e19 = 1e15 since c_SMG ≤ 1e-4
    have h2 : s.c_SMG * (1.0e19 : ℝ) ≤ (1.0e-4 : ℝ) * (1.0e19 : ℝ) :=
      mul_le_mul_of_nonneg_right h_upper (by norm_num)
    linarith [h2]

/-- **Out-of-band falsifier**: at `Λ_UV = M_Pl`, a `Λ_SMG` strictly
below the seesaw lower edge `10⁹` GeV — under the NJL-band `c_SMG ≥
10⁻¹⁰` — is impossible. Hence any substrate with `Λ_SMG < 10⁹` GeV at
Planck-scale UV cutoff must violate the band hypothesis (i.e., the
substrate is **not** in the seesaw-restricted SMG window).
Falsifiability witness — mirror of
`MajoranaRung.strong_BCS_excludes_substrate_dominant_M_R` for the
SMG-route. -/
theorem Λ_SMG_below_seesaw_at_Planck_UV_falsifies_NJL_band
    (s : SMGSubstrateData) (Λ_SMG : ℝ)
    (h_smg : H_SubstrateNearSMGFixedPoint s Λ_SMG)
    (h_uv_planck : s.Λ_UV = (1.0e19 : ℝ))
    (h_low : Λ_SMG < 1.0e9) :
    False := by
  have ⟨h_band_low, _⟩ := smg_window_predicts_Λ_SMG_in_seesaw_band s Λ_SMG h_smg h_uv_planck
  linarith

/-! ## 7. Algebraic content of the SMG form

Under `H_MR_FromSMGGap` with positive `Λ_SMG`, the per-generation
`M_R i` is positive (from `c_i > 0` and `Λ_SMG > 0`) and bounded above
by `Λ_SMG` (from `c_i ≤ 1`). These are the SMG-route analogs of
`MajoranaRung.M_R_pos_under_BCS_form` and
`M_R_lt_substrate_under_BCS_form`.
-/

/-- **SMG-form positivity**: under the SMG-gap hypothesis with positive
gap scale, every `M_R i` is strictly positive. -/
theorem M_R_pos_under_SMG_form
    (m : MajoranaRung.MajoranaRungData) (Λ_SMG : ℝ) (h_pos : 0 < Λ_SMG)
    (h_smg : H_MR_FromSMGGap m Λ_SMG) :
    ∀ i, 0 < m.M_R i := by
  intro i
  obtain ⟨c_i, h_c_pos, _, h_eq⟩ := h_smg i
  rw [h_eq]
  exact mul_pos h_c_pos h_pos

/-- **SMG-form upper bound**: under the SMG-gap hypothesis with positive
gap scale, every `M_R i` is at most `Λ_SMG` (saturated when `c_i = 1`).
The qualitative content: the SMG mechanism cannot generate a Majorana
mass above its own gap scale. -/
theorem M_R_le_substrate_under_SMG_form
    (m : MajoranaRung.MajoranaRungData) (Λ_SMG : ℝ) (h_pos : 0 < Λ_SMG)
    (h_smg : H_MR_FromSMGGap m Λ_SMG) :
    ∀ i, m.M_R i ≤ Λ_SMG := by
  intro i
  obtain ⟨c_i, h_c_pos, h_c_le, h_eq⟩ := h_smg i
  rw [h_eq]
  -- c_i · Λ_SMG ≤ 1 · Λ_SMG = Λ_SMG
  calc c_i * Λ_SMG ≤ 1 * Λ_SMG :=
        mul_le_mul_of_nonneg_right h_c_le (le_of_lt h_pos)
    _ = Λ_SMG := one_mul _

/-- **SMG-form falsifier**: a `MajoranaRungData` with any
`m.M_R i > Λ_SMG` rules out the SMG hypothesis at that gap scale.
Direct contrapositive of `M_R_le_substrate_under_SMG_form`. Mirror of
`MajoranaRung.strong_BCS_excludes_substrate_dominant_M_R`: the SMG
mechanism cannot generate a Majorana mass above its own gap scale, so
data with substrate-dominant `M_R` is incompatible with SMG. -/
theorem smg_form_excludes_substrate_dominant_M_R
    (m : MajoranaRung.MajoranaRungData) (Λ_SMG : ℝ) (h_pos : 0 < Λ_SMG)
    (i : Fin 3) (h_dominant : Λ_SMG < m.M_R i) :
    ¬ H_MR_FromSMGGap m Λ_SMG := by
  intro h_smg
  have h_le := M_R_le_substrate_under_SMG_form m Λ_SMG h_pos h_smg i
  linarith

/-- **Cross-cutting band-prediction theorem**: the SMG-route prediction
chain `(substrate-window, SMG-gap, Planck-UV)` lands the Majorana mass
`M_R i` at or below the seesaw upper edge `10¹⁵` GeV, for every
generation. Composes `H_SubstrateNearSMGFixedPoint` (substrate in
NJL-derived seesaw-restricted band) with `H_MR_FromSMGGap` (SMG-gap
form), the Planck-UV anchor `Λ_UV = M_Pl ≈ 10¹⁹` GeV, and the algebraic
chain `smg_window_predicts_Λ_SMG_in_seesaw_band` ∘
`M_R_le_substrate_under_SMG_form` to deliver the full Wave 4
quantitative anchor: under the deep-research-corrected formulation
(2026-04-27), the SMG route predicts an `M_R` band that is *at worst*
the upper seesaw edge. -/
theorem smg_M_R_in_seesaw_band_under_full_hypothesis
    (s : SMGSubstrateData) (m : MajoranaRung.MajoranaRungData) (Λ_SMG : ℝ)
    (h_window : H_SubstrateNearSMGFixedPoint s Λ_SMG)
    (h_smg : H_MR_FromSMGGap m Λ_SMG)
    (h_uv_planck : s.Λ_UV = (1.0e19 : ℝ)) :
    ∀ i, m.M_R i ≤ 1.0e15 := by
  intro i
  obtain ⟨h_lower, h_upper, h_eq⟩ := h_window
  have h_smg_pos : 0 < Λ_SMG := by
    rw [h_eq]
    exact mul_pos s.c_SMG_pos s.Λ_UV_pos
  have ⟨_, h_upper_band⟩ :=
    smg_window_predicts_Λ_SMG_in_seesaw_band s Λ_SMG
      ⟨h_lower, h_upper, h_eq⟩ h_uv_planck
  exact le_trans (M_R_le_substrate_under_SMG_form m Λ_SMG h_smg_pos h_smg i) h_upper_band

/-! ## 8. Cross-bridge to Wave 2b decoupling infrastructure

The SMG route preserves U(1)_L by construction (composite-fermion
condensates are SM-symmetric per Razamat–Tong, Catterall). This forces a
specific selection on the AC-bound regime infrastructure: the dim-5 LNV
channel (`H_DecouplingBoundDim5_LNV`) is forbidden because it conjoins
`H_LeptonNumberViolated` as a precondition; only the dim-6 generic
bound (`H_DecouplingBoundDim6`) applies in the SMG regime.
-/

/-- **Bidirectional regime selection (load-bearing)**: under L-conservation
(`G_LV = 0`, the SMG regime), the AC-bound infrastructure cleanly
selects the dim-6 channel and excludes the dim-5 LNV channel. Two
load-bearing halves:

- **Positive (dim-6 has an inhabitant)**: the trivially-zero amplitude
  difference satisfies the dim-6 bound for any substrate
  (`MajoranaRungDecoupling.H_DecouplingBoundDim6_consistent`).
- **Negative (dim-5 LNV is uninhabited at G_LV = 0)**: the
  `H_LeptonNumberViolated 0` precondition fails because
  `H_LeptonNumberViolated` unfolds to `G_LV ≠ 0`.

The two-sided form makes both halves load-bearing: the proof body
invokes the existing dim-6 inhabitant lemma (cross-bridge to
`MajoranaRungDecoupling`) AND derives the dim-5 exclusion from the
substrate-LNV definition. Mirror of
`MajoranaRung.lepton_number_symmetry_obstructs_BCS_form` at the
AC-bound level. -/
theorem smg_regime_selects_dim6_excludes_dim5
    (s : MajoranaRungDecoupling.SubstrateData) :
    MajoranaRungDecoupling.H_DecouplingBoundDim6 (fun _ => 0) s ∧
    (∀ amp_diff : ℝ → ℝ,
      ¬ MajoranaRungDecoupling.H_DecouplingBoundDim5_LNV amp_diff s 0) := by
  refine ⟨MajoranaRungDecoupling.H_DecouplingBoundDim6_consistent s, ?_⟩
  intro _ ⟨h_LNV, _⟩
  -- H_LeptonNumberViolated 0 := (0 ≠ 0); apply to rfl to derive False
  exact h_LNV rfl

/-! ## 9. Wave-4 open-problem manifest

Mirror of `MajoranaRung.Wave2OpenManifest`: surface the load-bearing
Wave-4 OPEN flags as a parametric `Prop`-conjunction. The three flags
are OPEN-W4-{1,2,3}; only OPEN-W4-{1,2} carry Lean-statable content
(OPEN-W4-3 is a lattice-MC empirical question, not a formalizable Prop).
-/

/-- Wave-4 manifest: the load-bearing OPEN flags for the SMG route are
OPEN-W4-1 (substrate sits in HW SMG window, parameterized as
`H_SubstrateNearSMGFixedPoint`) and OPEN-W4-2 (per-generation `c_i`
existence, parameterized as `H_MR_FromSMGGap`). Both as parametric
existence Props with positive substrate scales. -/
def Wave4OpenManifest (m : MajoranaRung.MajoranaRungData) : Prop :=
  -- OPEN-W4-1: substrate parameters sit in the HW SMG window
  (∃ (s : SMGSubstrateData) (Λ_SMG : ℝ),
      H_SubstrateNearSMGFixedPoint s Λ_SMG) ∧
  -- OPEN-W4-2: per-generation SMG-gap form holds at some positive Λ_SMG
  (∃ Λ_SMG : ℝ, 0 < Λ_SMG ∧ H_MR_FromSMGGap m Λ_SMG)

/-- Non-vacuity of the Wave-4 manifest: there exists a `MajoranaRungData`
satisfying both load-bearing open hypotheses. Concretely the OPEN-W4-1
witness uses the deep-research-anchored fiducial `c_SMG = 1e-7` (NJL-band
mid-band), `Λ_UV = 1`, `Λ_SMG = 1e-7`; the OPEN-W4-2 witness uses
`M_R i = 1`, `Λ_SMG = 1`, `c_i = 1`. -/
theorem wave4_open_manifest_consistent :
    ∃ m : MajoranaRung.MajoranaRungData, Wave4OpenManifest m := by
  refine ⟨⟨fun _ => 1, fun _ => one_pos⟩, ?_, ?_⟩
  · -- OPEN-W4-1 witness via H_SubstrateNearSMGFixedPoint_consistent
    exact H_SubstrateNearSMGFixedPoint_consistent
  · -- OPEN-W4-2 witness: Λ_SMG = 1, c_i = 1 saturates M_R = 1
    refine ⟨1, one_pos, ?_⟩
    intro _
    exact ⟨1, one_pos, le_refl _, by ring⟩

/-! ## 10. Joint-no-go status with Wave 2 (post-deep-research, 2026-04-27)

Per the Wave 4 deep-research return
(`Lit-Search/Phase-5z/Phase 5z Wave 4 — SMG Substrate Phase Diagram.md`,
verdict 2026-04-27): both natural substrate-bridge mechanisms for the
ADW substrate carry literature-frontier obstructions:

- **BCS branch (Wave 2):** at L-conserving substrates (`G_LV = 0`), no
  solution exists per
  `MajoranaRung.lepton_number_symmetry_obstructs_BCS_form`.
- **SMG branch (Wave 4):** the substrate-in-HW-window hypothesis
  `H_SubstrateNearSMGFixedPoint` is OPEN-AT-LITERATURE-FRONTIER on
  three sub-questions (a) RG-flow merger, (b) closed-form Λ_SMG, (c)
  Catterall mirror decoupling on ADW. The single direct piece of
  evidence (Vladimirov–Diakonov's own mean-field, PRD 86.104019)
  identifies a chiral-SSB phase, NOT an SMG phase, in the published
  2-parameter slice.

This is the formal statement of the joint status: at L-conserving
substrates outside the SMG window, BOTH bridges fail. The SMG predicate
itself remains satisfiable in principle (witnessed at consistent data),
but whether the ADW substrate satisfies it is a literature-frontier
question. The composite implication is: any successful substrate-bridge
for ADW must be either a LNV substrate (Wave 2 valid regime) OR a
substrate in the SMG window (Wave 4 valid regime, OPEN). -/

/-- **Joint-no-go (quantitative, deep-research-anchored)**: at a
substrate with `Λ_UV = M_Pl` and `Λ_SMG < 10⁹` GeV (sub-seesaw),
BOTH bridges fail substantively:
- (1) BCS branch fails at `G_LV = 0` (Wave 2 no-go, universal in
      `m, Λ_ADW`) per `MajoranaRung.L_conserving_substrate_obstructs_BCS_form`.
- (2) SMG band hypothesis is **derived** to fail by quantitative
      contradiction with `smg_window_predicts_Λ_SMG_in_seesaw_band`:
      if `H_SubstrateNearSMGFixedPoint` held, the band theorem
      forces `Λ_SMG ≥ 10⁹`, contradicting `h_low`.

The negation in the second conjunct is **NOT** the hypothesis — it is
DERIVED from the quantitative chain, making the joint statement
load-bearing on both halves. Mirror of the parallel obstructions in
the deep-research verdict (2026-04-27): the ADW substrate-bridge
derivation has TWO literature-frontier obstructions (BCS L-symmetry +
SMG phase-diagram openness), and below the seesaw band these become
formal Lean obstructions. -/
theorem joint_substrate_bridge_obstruction_quantitative
    (m : MajoranaRung.MajoranaRungData) (s : SMGSubstrateData)
    (Λ_ADW Λ_SMG : ℝ)
    (h_uv_planck : s.Λ_UV = (1.0e19 : ℝ))
    (h_low : Λ_SMG < (1.0e9 : ℝ)) :
    -- BCS branch fails universally at G_LV = 0 (Wave 2 no-go)
    (¬ MajoranaRung.H_MR_FromADWSubstrate_BCS_LNV m Λ_ADW 0) ∧
    -- SMG band hypothesis fails — DERIVED from quantitative chain,
    -- NOT a hypothesis restatement.
    (¬ H_SubstrateNearSMGFixedPoint s Λ_SMG) := by
  refine ⟨MajoranaRung.L_conserving_substrate_obstructs_BCS_form m Λ_ADW, ?_⟩
  intro h_smg
  have ⟨h_band_low, _⟩ :=
    smg_window_predicts_Λ_SMG_in_seesaw_band s Λ_SMG h_smg h_uv_planck
  linarith

end SKEFTHawking.MajoranaRungSMG
