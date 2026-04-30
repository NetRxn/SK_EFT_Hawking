import SKEFTHawking.Basic
import SKEFTHawking.QuarkRungScalarChannel
import SKEFTHawking.QuarkRungMajoranaChannel
import Mathlib

/-!
# Phase 6k Wave 3: Light-Quark Hierarchy — Substrate Fall-Through

## Overview

Treats the light-quark mass hierarchy `m_u : m_d : m_s` in the substrate-
without-SMG case (Phase 6h does NOT activate). Per the Wave-1 dossier
(§5d), the minimal one-channel ADW substrate does NOT predict the light-
quark hierarchy in closed form: the substrate generates exactly one heavy
fermion (the top, identified in W1), and the remaining hierarchy requires
an *extension* — multi-condensate, Froggatt-Nielsen U(1)_X, or
Eichhorn-Held hypercharge-splitting.

This wave ships the structurally honest fall-through verdict:
1. **Empirical hierarchy observed in PDG 2024** — three substantive ratio
   bands grounded in PDG MSbar masses.
2. **Substrate-alone closed form does NOT exist** (extension needed).
3. **Phase 6h supersession path** — cross-reference for the case Phase 6h
   activates.

## Verdicts

1. **CLOSED-POSITIVE (empirical ratios):** PDG-anchored numerical bands
   for `m_d/m_u`, `m_s/m_d`, `m_c/m_s`. (Substantive correctness-push.)
2. **CLOSED-NEGATIVE (substrate fall-through):** No closed-form minimal-
   substrate prediction. Encoded as a structural-falsification theorem.
3. **OPEN (extension paths):** Multi-channel / Froggatt-Nielsen / AS-
   splitting. Each is a Phase 6k Wave 5+ or Phase 6h follow-up.

## References

- `docs/roadmaps/Phase6k_Roadmap.md` — Wave 3 scope
- `Lit-Search/Phase-6k/6k-Wave 1 — Quark Substrate-Channel Decomposition (Top Quark Identification).md` §5(d)
- `lean/SKEFTHawking/QuarkRungScalarChannel.lean` — Wave 1 (consumed)
- `lean/SKEFTHawking/QuarkRungMajoranaChannel.lean` — Wave 2 (consumed)
- Particle Data Group, Navas et al. 2024, PRD 110:030001
- Bazavov et al. 2018, PRD 98:074512, arXiv:1802.04248
- Stech 1997, hep-ph/9703217 — geometric quark-mass hierarchy heuristic

## Scope lock

IN SCOPE: PDG-anchored light-quark ratio falsifiability; substrate-alone
NO-GO with concrete witness; Phase 6h supersession-path Prop bundle.

OUT OF SCOPE: Multi-channel substrate construction (Phase 6k future);
Froggatt-Nielsen embedding (out of project scope per CLAUDE.md);
hypercharge-splitting AS implementation (Phase 6h W4 if it activates).
-/

noncomputable section

open Real

namespace SKEFTHawking.LightQuarkHierarchyFallthrough

/-! ## 1. Bring forward Wave 2 anchors and ratios

Re-export the PDG anchors from Wave 2 to keep this wave self-contained. -/

/-- Charm-quark MSbar mass `m_c(m_c)` (GeV), from W2. -/
def m_c : ℝ := SKEFTHawking.QuarkRungMajoranaChannel.m_c_PDG

/-- Strange-quark MSbar mass `m_s(2 GeV)` (GeV), from W2. -/
def m_s : ℝ := SKEFTHawking.QuarkRungMajoranaChannel.m_s_PDG

/-- Down-quark MSbar mass `m_d(2 GeV)` (GeV), from W2. -/
def m_d : ℝ := SKEFTHawking.QuarkRungMajoranaChannel.m_d_PDG

/-- Up-quark MSbar mass `m_u(2 GeV)` (GeV), from W2. -/
def m_u : ℝ := SKEFTHawking.QuarkRungMajoranaChannel.m_u_PDG

/-! ## 2. PDG-anchored light-quark ratio bands

PDG 2024 ratios:
  `m_d / m_u ≈ 2.195` (band [2.0, 2.5])
  `m_s / m_d ≈ 19.78` (band [19.0, 20.0])
  `m_c / m_s ≈ 13.77` (band [13.0, 14.0])

The hierarchy "accelerates" rather than progressing geometrically — same
NO-GO pattern observed in W2.
-/

/-- Down-quark / up-quark mass ratio falsifiability anchor.
PDG: `m_d/m_u = 4.675 / 2.130 ≈ 2.195`. Band [2.0, 2.5]. -/
theorem ratio_d_over_u_PDG :
    (2.0 : ℝ) < m_d / m_u ∧ m_d / m_u < 2.5 := by
  unfold m_d m_u
    SKEFTHawking.QuarkRungMajoranaChannel.m_d_PDG
    SKEFTHawking.QuarkRungMajoranaChannel.m_u_PDG
  refine ⟨?_, ?_⟩ <;> norm_num

/-- Strange-quark / down-quark mass ratio falsifiability anchor.
PDG: `m_s/m_d ≈ 19.78`. Band [19.0, 20.0]. -/
theorem ratio_s_over_d_PDG :
    (19.0 : ℝ) < m_s / m_d ∧ m_s / m_d < 20.0 := by
  unfold m_s m_d
    SKEFTHawking.QuarkRungMajoranaChannel.m_s_PDG
    SKEFTHawking.QuarkRungMajoranaChannel.m_d_PDG
  refine ⟨?_, ?_⟩ <;> norm_num

/-- Charm-quark / strange-quark mass ratio falsifiability anchor (cross-
generation). PDG: `m_c/m_s ≈ 13.77`. Band [13.0, 14.0]. -/
theorem ratio_c_over_s_PDG :
    (13.0 : ℝ) < m_c / m_s ∧ m_c / m_s < 14.0 := by
  unfold m_c m_s
    SKEFTHawking.QuarkRungMajoranaChannel.m_c_PDG
    SKEFTHawking.QuarkRungMajoranaChannel.m_s_PDG
  refine ⟨?_, ?_⟩ <;> norm_num

/-! ## 3. Light-quark hierarchy is NOT geometrically uniform

A "geometric uniform" hierarchy `m_q ~ σ^n` with σ constant would have
`m_d/m_u ≈ m_s/m_d ≈ m_c/m_s ≈ ...` — but the PDG data shows these are
factor 9 apart in the worst case. This NO-GO is the empirical content
that any closed-form substrate prediction must accommodate.
-/

/-- **NO-GO Theorem — light-quark hierarchy is NOT uniform-geometric.**
PDG `m_s/m_d ≈ 19.78` is more than 7× the value of `m_d/m_u ≈ 2.20`.
A uniform-σ geometric hierarchy `m_q ~ σ^n` would have these ratios
identical; the factor-7+ discrepancy structurally falsifies any single-σ
geometric model. -/
theorem hierarchy_not_uniform_geometric :
    7 * (m_d / m_u) < m_s / m_d := by
  unfold m_d m_u m_s
    SKEFTHawking.QuarkRungMajoranaChannel.m_d_PDG
    SKEFTHawking.QuarkRungMajoranaChannel.m_u_PDG
    SKEFTHawking.QuarkRungMajoranaChannel.m_s_PDG
  norm_num

/-- **NO-GO Theorem — c/s ratio also differs from d/u ratio by ≥ 5×.**
The "uniform geometric" hypothesis fails at every consecutive ratio pair,
not just at one. -/
theorem cs_ratio_far_above_du_ratio :
    5 * (m_d / m_u) < m_c / m_s := by
  unfold m_d m_u m_c m_s
    SKEFTHawking.QuarkRungMajoranaChannel.m_d_PDG
    SKEFTHawking.QuarkRungMajoranaChannel.m_u_PDG
    SKEFTHawking.QuarkRungMajoranaChannel.m_c_PDG
    SKEFTHawking.QuarkRungMajoranaChannel.m_s_PDG
  norm_num

/-! ## 4. Substrate-alone closed-form prediction NO-GO

Per the Wave-1 dossier §5(d), the minimal one-channel ADW substrate
generates exactly ONE heavy fermion (the top, scalar-rung). The five
non-top quarks require a *non-minimal* substrate or external structure.
Encoded here as a structural-falsification theorem consuming W1's
`MinimalOneChannelSubstrate` Prop bundle.
-/

/-- **NO-GO Theorem — minimal substrate cannot place light quarks in
either named band.** From W2's `every_non_top_quark_outside_substrate_bands`:
all five non-top quark masses lie below both the W1 scalar-rung band
[150, 250] GeV and the Phase 5z W2 Majorana-rung band [10⁹, 10¹⁵] GeV.

Substantive content: cross-bridge consuming W2's universal NO-GO. -/
theorem light_quarks_outside_minimal_substrate_bands :
    ∀ (q : SKEFTHawking.QuarkRungMajoranaChannel.NonTopQuark),
      SKEFTHawking.QuarkRungMajoranaChannel.nonTopMass q <
        SKEFTHawking.QuarkRungScalarChannel.bandLooseLower ∧
      SKEFTHawking.QuarkRungMajoranaChannel.nonTopMass q <
        SKEFTHawking.QuarkRungMajoranaChannel.majoranaBandLower :=
  SKEFTHawking.QuarkRungMajoranaChannel.every_non_top_quark_outside_substrate_bands

/-! ## 5. Phase 6h supersession-path Prop bundle

Wave 1 dossier §5 lists three extension paths that *would* close the
light-quark hierarchy if implemented:

1. **Multi-channel substrate** (Hill 1995 topcolor-assisted technicolor;
   Dobrescu-Hill 1998 top-condensate seesaw).
2. **Froggatt-Nielsen U(1)_X flavor symmetry** (Babu 2009 TASI; Ardakanian
   2026, arXiv:2603.15455).
3. **Eichhorn-Held hypercharge splitting via gravitational fixed point**
   (Eichhorn-Held 2018, PRL 121:151302).

Phase 6h Wave 4 plans a `LightFermionHierarchyFromSMG.lean` predicting
`m_f / Λ_UV ~ exp(-δ_f / α_∗)` from option (3). This wave's supersession-
path Prop bundle records the OPEN-AT-FRONTIER extension obligations as a
single named structural placeholder.
-/

/-- Tracked-hypothesis Prop bundle for the Phase 6h W4 hypercharge-
splitting extension path. The structure carries the three substrate
parameters (`δ_f` flavor charge, `α_∗` AS fixed-point coupling, `Λ_UV`
asymptotic-safety scale) that *would* parametrize the closed-form
prediction `m_f / Λ_UV ~ exp(-δ_f / α_∗)` if the AS framework activates.

Per Eichhorn-Held 2018, PRL 121:151302; Domènech-Goodsell-Wetterich 2021,
JHEP 01:180. -/
structure Phase6hHyperchargeSplittingHypothesis where
  alpha_star : ℝ
  Lambda_UV : ℝ
  delta_u : ℝ
  delta_d : ℝ
  delta_s : ℝ
  delta_c : ℝ
  delta_b : ℝ
  alpha_pos : 0 < alpha_star
  Lambda_UV_pos : 0 < Lambda_UV
  delta_b_pos : 0 < delta_b
  /-- Tracked hypothesis: the AS hypercharge splitting predicts the five
      non-top quark masses to within 10% of PDG. Per dossier, this is
      OPEN-AT-FRONTIER for c, s, u, d (only b is partially captured by
      the AS framework). -/
  predictsBandSelectiveLightQuarks : Prop

/-- **Theorem — supersession-path suppression factor strictly less than 1.**
For any Phase 6h hypercharge-splitting bundle with `δ_b > 0` and `α_∗ > 0`,
the suppression factor `exp(-δ_b / α_∗)` is strictly less than `1`. This
is the substantive content of the extension hypothesis: `m_b ~ Λ_UV ·
exp(-δ_b/α_∗) < Λ_UV`, ensuring the predicted mass is below the AS scale.

Substantive content: the structural placeholder is non-trivial — it
forces a positive sign on `δ_b/α_∗`. -/
theorem phase_6h_supersession_suppression_lt_one
    (h : Phase6hHyperchargeSplittingHypothesis) :
    Real.exp (- h.delta_b / h.alpha_star) < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have hb : 0 < h.delta_b := h.delta_b_pos
  have ha : 0 < h.alpha_star := h.alpha_pos
  have h_neg : - h.delta_b < 0 := by linarith
  exact div_neg_of_neg_of_pos h_neg ha

/-! ## 6. Bundle theorem — Wave 3 fall-through verdict

The single-citation bundle for the flagship paper §light-quark-fallthrough.
Bundles the four structurally distinct outputs of this wave: empirical
ratios, NO-GO for uniform-geometric hierarchy, substrate-alone NO-GO from
W2, and the Phase 6h supersession-path placeholder.
-/

/-- **Bundle theorem — Wave 3 light-quark hierarchy fall-through.**

  (i)   d/u ratio in PDG band [2.0, 2.5];
  (ii)  s/d ratio in PDG band [19.0, 20.0];
  (iii) Hierarchy NOT uniform-geometric (s/d > 7 × d/u);
  (iv)  All non-top quarks below both substrate-channel bands (W2 import).

Each conjunct is independently falsifiable. The bundle is the load-bearing
form for citation: the substrate does NOT close the light-quark hierarchy
in minimal form; the framework requires an extension (Phase 6h or future
multi-channel work). -/
theorem light_quark_hierarchy_fallthrough_bundle :
    ((2.0 : ℝ) < m_d / m_u ∧ m_d / m_u < 2.5) ∧
    ((19.0 : ℝ) < m_s / m_d ∧ m_s / m_d < 20.0) ∧
    (7 * (m_d / m_u) < m_s / m_d) ∧
    (∀ (q : SKEFTHawking.QuarkRungMajoranaChannel.NonTopQuark),
      SKEFTHawking.QuarkRungMajoranaChannel.nonTopMass q <
        SKEFTHawking.QuarkRungScalarChannel.bandLooseLower ∧
      SKEFTHawking.QuarkRungMajoranaChannel.nonTopMass q <
        SKEFTHawking.QuarkRungMajoranaChannel.majoranaBandLower) :=
  ⟨ratio_d_over_u_PDG, ratio_s_over_d_PDG, hierarchy_not_uniform_geometric,
   light_quarks_outside_minimal_substrate_bands⟩

end SKEFTHawking.LightQuarkHierarchyFallthrough

end
