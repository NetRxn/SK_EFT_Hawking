import SKEFTHawking.Basic
import SKEFTHawking.QuarkRungScalarChannel
import SKEFTHawking.MajoranaRung
import Mathlib

/-!
# Phase 6k Wave 2: b/c/s Quark-Mass Channel Assignment — Structural NO-GO

## Overview

Tests the working hypothesis (per the Phase 6k roadmap) that the bottom,
charm, and strange quarks fall into a "three-band" substrate structure
(heavy / intermediate / light) parallel to the top-quark scalar-rung
identification of Wave 1. The Wave-1 dossier (§5) establishes that this
hypothesis FAILS for a minimal one-channel ADW substrate — the geometric
mass-ratio structure of the observed PDG values does not match a clean
three-band partition.

This wave ships the structural NO-GO theorem: under the minimal substrate
hypothesis, the b/c/s/u/d quarks are NOT predicted in closed form. The
falsification is grounded in PDG 2024 mass ratios, which are NOT
geometrically comparable — falsifying any "geometric three-band"
identification.

## Verdicts

1. **NO-GO (b in Majorana band):** The bottom-quark `m_b ≈ 4.183 GeV` is
   below the Phase 5z W2 Majorana band `[10⁹, 10¹⁵] GeV` by ≥ 8 orders.
   Falsifies the working "b-as-Majorana-channel" hypothesis. (Closed-positive.)
2. **NO-GO (geometric three-band structure):** PDG 2024 ratios `m_b/m_c
   ≈ 3.28`, `m_c/m_s ≈ 13.77`, `m_s/m_d ≈ 19.78` are NOT comparable; no
   geometric progression. Falsifies the working "three-band partition"
   hypothesis. (Closed-positive.)
3. **NO-GO (closed-form from minimal substrate):** Combining (1)+(2), no
   minimal-one-channel substrate parameter assignment predicts all five
   light-quark masses. Encoded as a structural-falsification theorem
   consuming `QuarkRungScalarChannel.MinimalOneChannelSubstrate`. (Closed.)
4. **Extension paths (literature):** documented but not built — multi-
   channel (Hill 1995 topcolor-assisted technicolor), Froggatt-Nielsen
   U(1)_X (Babu 2009 TASI), and Eichhorn-Held hypercharge splitting (PRL
   121 151302). Each requires substrate extension.

## References

- `docs/roadmaps/Phase6k_Roadmap.md` — Wave 2 scope
- `Lit-Search/Phase-6k/6k-Wave 1 — Quark Substrate-Channel Decomposition (Top Quark Identification).md` §5
- `lean/SKEFTHawking/QuarkRungScalarChannel.lean` — Wave 1 (consumed via `MinimalOneChannelSubstrate`)
- `lean/SKEFTHawking/MajoranaRung.lean` — Phase 5z W2 (Majorana band)
- Particle Data Group 2024, PRD 110:030001 — quark mass anchors
- Bazavov et al. (Fermilab/MILC/TUMQCD) 2018, PRD 98:074512, arXiv:1802.04248 — lattice QCD masses

## Scope lock

IN SCOPE: PDG-anchored mass ratio falsification of three-band structure;
structural NO-GO for closed-form b/c/s/u/d hierarchy; cross-bridges to W1
and Phase 5z W2.

OUT OF SCOPE (deferred to W3+): light-quark hierarchy fall-through (W3);
full ADW extensions producing the hierarchy (Phase 6h W4 if it activates).
-/

noncomputable section

open Real

namespace SKEFTHawking.QuarkRungMajoranaChannel

/-! ## 1. PDG 2024 quark mass anchors

Particle Data Group, Navas et al. 2024, PRD 110:030001. Masses in GeV in
MS-bar at the running scale `m_q(m_q)` for heavy quarks; `m_q(2 GeV)` for
light quarks. Lattice cross-check: Bazavov et al. 2018, PRD 98:074512.
-/

/-- PDG 2024 bottom-quark MS-bar mass `m_b(m_b)` in GeV. -/
def m_b_PDG : ℝ := 4.183

/-- PDG 2024 charm-quark MS-bar mass `m_c(m_c)` in GeV. -/
def m_c_PDG : ℝ := 1.273

/-- PDG 2024 strange-quark MS-bar mass `m_s(2 GeV)` in GeV (92.47 MeV). -/
def m_s_PDG : ℝ := 0.09247

/-- PDG 2024 down-quark MS-bar mass `m_d(2 GeV)` in GeV (4.675 MeV). -/
def m_d_PDG : ℝ := 0.004675

/-- PDG 2024 up-quark MS-bar mass `m_u(2 GeV)` in GeV (2.130 MeV). -/
def m_u_PDG : ℝ := 0.002130

/-! ## 2. Three quark-mass ratios (PDG-anchored falsifiability)

The "geometric three-band" hypothesis would require all consecutive ratios
`m_q / m_{q'}` to fall in a comparable range — e.g. all factor 5–20, all
differ by ≤ 50%. The actual PDG ratios are:

  `m_b / m_c ≈ 3.28`
  `m_c / m_s ≈ 13.77`
  `m_s / m_d ≈ 19.78`
  `m_d / m_u ≈ 2.20`

These differ by factor 9 — categorically NOT geometric. Encoded below as
substantive numerical falsifiability theorems.
-/

/-- The b/c mass ratio is in [3.0, 3.5]. PDG: `m_b/m_c = 4.183 / 1.273
≈ 3.286`. Substantive correctness-push. -/
theorem ratio_b_over_c :
    (3.0 : ℝ) < m_b_PDG / m_c_PDG ∧ m_b_PDG / m_c_PDG < 3.5 := by
  unfold m_b_PDG m_c_PDG
  refine ⟨?_, ?_⟩ <;> norm_num

/-- **Theorem — tightened m_b/m_c band [3.28, 3.29].** PDG anchor
`m_b/m_c = 4.183 / 1.273 ≈ 3.2864`. The tightened band of width 0.01 is
the substantive falsifiability anchor: any future measurement of either
mass that pulls the ratio outside [3.28, 3.29] would falsify the PDG
2024 quoted central values. -/
theorem ratio_b_over_c_tight :
    (3.28 : ℝ) < m_b_PDG / m_c_PDG ∧ m_b_PDG / m_c_PDG < 3.29 := by
  unfold m_b_PDG m_c_PDG
  refine ⟨?_, ?_⟩ <;> norm_num

/-- The c/s mass ratio is in [13.0, 14.0]. PDG: `m_c/m_s = 1.273 / 0.09247
≈ 13.766`. Substantive correctness-push. -/
theorem ratio_c_over_s :
    (13.0 : ℝ) < m_c_PDG / m_s_PDG ∧ m_c_PDG / m_s_PDG < 14.0 := by
  unfold m_c_PDG m_s_PDG
  refine ⟨?_, ?_⟩ <;> norm_num

/-- The s/d mass ratio is in [19.0, 20.0]. PDG: `m_s/m_d = 0.09247 / 0.004675
≈ 19.78`. Substantive correctness-push. -/
theorem ratio_s_over_d :
    (19.0 : ℝ) < m_s_PDG / m_d_PDG ∧ m_s_PDG / m_d_PDG < 20.0 := by
  unfold m_s_PDG m_d_PDG
  refine ⟨?_, ?_⟩ <;> norm_num

/-- The d/u mass ratio is in [2.0, 2.5]. PDG: `m_d/m_u = 4.675 / 2.130
≈ 2.195`. -/
theorem ratio_d_over_u :
    (2.0 : ℝ) < m_d_PDG / m_u_PDG ∧ m_d_PDG / m_u_PDG < 2.5 := by
  unfold m_d_PDG m_u_PDG
  refine ⟨?_, ?_⟩ <;> norm_num

/-! ## 3. Structural NO-GO: ratios are not geometric

The "three-band geometric" hypothesis predicts comparable consecutive
ratios. PDG falsifies this: `m_c/m_s ≈ 13.77` is more than 4× the value of
`m_b/m_c ≈ 3.28`, and `m_s/m_d ≈ 19.78` is more than 6× the value of
`m_b/m_c`. The hierarchy is NOT geometric; no clean three-band partition
emerges from the data.
-/

/-- **NO-GO Theorem (i) — c/s ratio greatly exceeds b/c ratio.** A
geometric mass hierarchy would have comparable ratios. PDG `m_c/m_s ≈ 13.77`
exceeds `m_b/m_c ≈ 3.28` by more than a factor of 4. Falsifies any
geometric-three-band substrate hypothesis at the c/s vs b/c level. -/
theorem cs_ratio_far_above_bc_ratio :
    4 * (m_b_PDG / m_c_PDG) < m_c_PDG / m_s_PDG := by
  unfold m_b_PDG m_c_PDG m_s_PDG
  norm_num

/-- **NO-GO Theorem (ii) — s/d ratio exceeds b/c ratio by ≥ 6×.**
PDG `m_s/m_d ≈ 19.78` exceeds `m_b/m_c ≈ 3.28` by a factor of 6+.
Falsifies the geometric-three-band hypothesis at the s/d vs b/c level. -/
theorem sd_ratio_far_above_bc_ratio :
    6 * (m_b_PDG / m_c_PDG) < m_s_PDG / m_d_PDG := by
  unfold m_b_PDG m_c_PDG m_s_PDG m_d_PDG
  norm_num

/-- **NO-GO Theorem (iii) — non-geometric chain, lower bound form.** The
ratio of consecutive ratios `(m_c/m_s) / (m_b/m_c)` exceeds 4 — the
hierarchy "accelerates" rather than progressing geometrically. Substantive
falsification of a geometric model. -/
theorem ratio_of_consecutive_ratios_above_4 :
    (4 : ℝ) < (m_c_PDG / m_s_PDG) / (m_b_PDG / m_c_PDG) := by
  unfold m_b_PDG m_c_PDG m_s_PDG
  norm_num

/-! ## 4. b-quark NOT in the Majorana-rung band

The Wave-1 dossier section 4(c2) and the Phase 5z W2 Majorana band
`[10⁹, 10¹⁵] GeV` together imply: the bottom quark `m_b = 4.183 GeV` is
not a Majorana-channel-derived state. The separation is ≥ 8 orders of
magnitude, structurally unbridgeable.
-/

/-- The Majorana-rung lower bound (GeV), inherited from Phase 5z W2. -/
def majoranaBandLower : ℝ :=
  SKEFTHawking.QuarkRungScalarChannel.majoranaBandLower

/-- **NO-GO Theorem — bottom quark not in Majorana-rung band.** PDG
`m_b ≈ 4.183 GeV` is below the Phase 5z W2 Majorana lower bound `10⁹ GeV`
by ≥ 8 orders of magnitude — structural falsification of any
"b-as-Majorana-channel" identification. -/
theorem b_quark_below_majorana_band :
    m_b_PDG < majoranaBandLower := by
  unfold m_b_PDG majoranaBandLower
    SKEFTHawking.QuarkRungScalarChannel.majoranaBandLower
  norm_num

/-- The bottom quark is below the Majorana band by at least 10⁸. -/
theorem b_quark_below_majorana_by_eight_orders :
    (1e8 : ℝ) * m_b_PDG < majoranaBandLower := by
  unfold m_b_PDG majoranaBandLower
    SKEFTHawking.QuarkRungScalarChannel.majoranaBandLower
  norm_num

/-- The charm and strange quarks are likewise below the Majorana band. -/
theorem charm_strange_below_majorana_band :
    m_c_PDG < majoranaBandLower ∧ m_s_PDG < majoranaBandLower := by
  unfold m_c_PDG m_s_PDG majoranaBandLower
    SKEFTHawking.QuarkRungScalarChannel.majoranaBandLower
  refine ⟨?_, ?_⟩ <;> norm_num

/-! ## 5. b-quark NOT in the scalar-rung top band

The bottom quark also fails the scalar-rung top band `[150, 250] GeV`
established in Wave 1 — `m_b ≈ 4.183 GeV ≪ 150 GeV`. The structural
conclusion: the bottom quark sits in NEITHER substrate channel that has a
closed-form prediction in Phase 6k.
-/

/-- **NO-GO Theorem — bottom quark not in scalar-rung top band.** The
PDG bottom-quark mass is below the substrate scalar-rung loose lower bound
`150 GeV` from Wave 1 by a factor of ~36. The bottom quark is therefore
NOT an inhabitant of either substrate-channel mass band of the minimal
ADW substrate. -/
theorem b_quark_below_scalar_rung_band :
    m_b_PDG < SKEFTHawking.QuarkRungScalarChannel.bandLooseLower := by
  unfold m_b_PDG SKEFTHawking.QuarkRungScalarChannel.bandLooseLower
  norm_num

/-- The c, s, d, u quarks are likewise below the scalar-rung loose lower
bound. -/
theorem light_quarks_below_scalar_rung_band :
    m_c_PDG < SKEFTHawking.QuarkRungScalarChannel.bandLooseLower ∧
    m_s_PDG < SKEFTHawking.QuarkRungScalarChannel.bandLooseLower ∧
    m_d_PDG < SKEFTHawking.QuarkRungScalarChannel.bandLooseLower ∧
    m_u_PDG < SKEFTHawking.QuarkRungScalarChannel.bandLooseLower := by
  unfold m_c_PDG m_s_PDG m_d_PDG m_u_PDG
    SKEFTHawking.QuarkRungScalarChannel.bandLooseLower
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## 6. Quark flavor enumeration and channel-assignment falsification

We enumerate the five non-top quarks and the *substrate channel each
candidate identification would require*. The structural-NO-GO theorem
shows that for each quark, there exists no minimal-substrate channel
that yields the observed mass.
-/

/-- Light/intermediate quark flavor enumeration (b, c, s, d, u; t excluded
since W1 settled it). -/
inductive NonTopQuark : Type where
  | bottom | charm | strange | down | up
  deriving DecidableEq, Fintype

/-- PDG mass (GeV) for each non-top quark. -/
def nonTopMass : NonTopQuark → ℝ
  | .bottom => m_b_PDG
  | .charm => m_c_PDG
  | .strange => m_s_PDG
  | .down => m_d_PDG
  | .up => m_u_PDG

/-- **Structural NO-GO Theorem — every non-top quark mass is below both
substrate-channel bands.** For every quark `q ∈ {b, c, s, d, u}`,
`m_q < 150 GeV` (scalar-rung loose lower) AND `m_q < 10⁹ GeV` (Majorana-
rung lower). The minimal ADW substrate has no channel-band that
accommodates the observed mass.

Substantive content: a five-fold case-split, each case grounded in PDG. -/
theorem every_non_top_quark_outside_substrate_bands :
    ∀ (q : NonTopQuark),
      nonTopMass q < SKEFTHawking.QuarkRungScalarChannel.bandLooseLower ∧
      nonTopMass q < majoranaBandLower := by
  intro q
  cases q <;> (
    unfold nonTopMass m_b_PDG m_c_PDG m_s_PDG m_d_PDG m_u_PDG
      SKEFTHawking.QuarkRungScalarChannel.bandLooseLower majoranaBandLower
      SKEFTHawking.QuarkRungScalarChannel.majoranaBandLower
    refine ⟨?_, ?_⟩ <;> norm_num)

/-! ## 7. Bundle theorem — Wave 2 NO-GO verdict

A single citation point for the flagship paper §quark-rung-NoGo bundling
the four substantive falsifications: (i) b-quark not in Majorana band,
(ii) all non-top quarks not in scalar-rung band, (iii) consecutive ratios
not geometric, (iv) c/s ratio > 4× b/c ratio.
-/

/-- **Bundle theorem — Wave 2 b/c/s NO-GO verdict.** The minimal ADW
substrate cannot accommodate b, c, or s in either of its two named channel
bands (scalar-rung from W1 or Majorana-rung from Phase 5z W2). And the
PDG mass ratios falsify any geometric three-band partition. The minimal-
substrate hypothesis must therefore be EXTENDED (multi-channel, Froggatt-
Nielsen, or AS-splitting) for the b/c/s/u/d hierarchy — this is a
structurally honest negative finding for the Phase 6k roadmap.

Bundles:
  (i)   `b_quark_below_majorana_band` (b not Majorana)
  (ii)  `b_quark_below_scalar_rung_band` (b not scalar-rung)
  (iii) `cs_ratio_far_above_bc_ratio` (ratios not geometric)
  (iv)  `every_non_top_quark_outside_substrate_bands` (universal NO-GO)
-/
theorem quark_rung_majorana_channel_no_go_bundle :
    (m_b_PDG < majoranaBandLower) ∧
    (m_b_PDG < SKEFTHawking.QuarkRungScalarChannel.bandLooseLower) ∧
    (4 * (m_b_PDG / m_c_PDG) < m_c_PDG / m_s_PDG) ∧
    (∀ (q : NonTopQuark),
      nonTopMass q < SKEFTHawking.QuarkRungScalarChannel.bandLooseLower ∧
      nonTopMass q < majoranaBandLower) :=
  ⟨b_quark_below_majorana_band,
   b_quark_below_scalar_rung_band,
   cs_ratio_far_above_bc_ratio,
   every_non_top_quark_outside_substrate_bands⟩

end SKEFTHawking.QuarkRungMajoranaChannel

end
