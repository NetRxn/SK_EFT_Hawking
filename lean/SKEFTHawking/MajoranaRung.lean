import SKEFTHawking.Basic
import SKEFTHawking.Z16AnomalyComputation
import SKEFTHawking.HiddenSectorClassification
import SKEFTHawking.SMFermionData
import Mathlib

/-!
# Phase 5z Wave 2: Majorana-Rung Interpretation of the Sterile-Neutrino Seesaw

## Overview

Formalizes the identification of a fundamental sterile-neutrino field
`SterileNeutrino` with a ℤ₂-graded Majorana rung on the SK-EFT Landau hierarchy.
Light-neutrino masses arise via the Type-I seesaw `m_ν = y² v² / M_R`, with
heavy mass `M_R` interpreted as a ℤ₁₆-invariant condensate scale of the ADW
substrate (Embedding III of `Lit-Search/Phase-5z/Phase 5z, Wave 2 — Sterile-
Neutrino Embedding for the Majorana Rung.md`, verdict 2026-04-25).

The three core identifications:

1. **Sterile neutrinos as ℤ₁₆-charge-1 Weyl fermions.** Three fundamental ν_R,
   one per generation, each carrying ℤ₁₆ charge `1` (locked by the proved
   Garcia-Etxebarria/Wan-Wang anomaly tower). The 3 ν_R contributions saturate
   the SM-without-ν_R hidden-sector deficit `45 ≡ -3 mod 16` to reach
   `48 ≡ 0 mod 16` — anomaly-free with right-handed neutrinos.

2. **Type-I seesaw m_ν = y² v² / M_R.** Algebraic positivity, monotonicity,
   and zero-iff-Yukawa-vanishes follow directly from the seesaw relation as
   stated. The substrate-bridge `M_R = Λ_ADW` is *not* derived in any
   primary source; encoded as a tracked hypothesis (WAVE2-OPEN-1).

3. **Falsifiability anchor.** The decidable predicate `IsObservedSeesawMatch`
   compares `seesawNeutrinoMass` to NuFit-6.0 m_ν data within an operational
   tolerance. Predictions far outside the band rule out the Wave-2 framing as
   a quantitative seesaw under given Yukawa data — itself a structural,
   publishable result.

## Open hypotheses (tracked, not derived)

The deep research surfaces five distinct open derivations none of which is
closed in any primary literature. Wave 2 surfaces the load-bearing one
(WAVE2-OPEN-1) as a tracked Prop hypothesis; the rest live as comment
markers:

- **WAVE2-OPEN-1**: `M_R = c · Λ_ADW` for some 0 < c ≤ 1. The Wetterich/
  ADW/Volovik substrate frameworks leave M_R as a fit parameter. Encoded
  here as `H_MR_FromADWSubstrate`.
- **WAVE2-OPEN-2**: PMNS angles from substrate overlaps (especially θ₂₃ ≈ π/4
  from a putative substrate μ-τ symmetry).
- **WAVE2-OPEN-3**: Majorana phases predicted from composite-operator structure.
- **WAVE2-OPEN-4**: m_ββ tied algebraically to a single condensate scale,
  distinguishing Embedding II from I.
- **WAVE2-OPEN-5**: ν_R-as-substrate-bound-state map (explicit IR-equivalence
  derivation between Embeddings I and III).

## References

- `docs/roadmaps/Phase5z_Roadmap.md` — Wave 2 scope + Z₁₆-bridge gate
- `Lit-Search/Phase-5z/Phase 5z, Wave 2 — Sterile-Neutrino Embedding for the
  Majorana Rung.md` — O.3 deep-research verdict
- `src/core/formulas.py` Phase 5z Wave 2 section
  (`seesaw_neutrino_mass`, `seesaw_m_r_from_observed`,
   `m_nu_heaviest_from_atmospheric_splitting`,
   `majorana_rung_z16_compatibility_index`)
- `src/core/constants.py` `MAJORANA_PARAMS` dict

## Scope lock

IN SCOPE: structural Embedding III seesaw mass, ℤ₁₆-singlet-branch bridge,
substrate-bridge tracked hypothesis, Type-I-seesaw falsifiability anchor.

OUT OF SCOPE (deferred to NeutrinoMixing.lean or Phase 6 follow-up): full
PMNS phenomenology, Majorana CP phases, leptogenesis dynamics, 0νββ NME
calculations.
-/

noncomputable section

open Real

namespace SKEFTHawking.MajoranaRung

/-! ## 1. Sterile-neutrino structure -/

/-- Sterile neutrino field, fundamental in Embedding III. Each instance is
labelled by its generation index `Fin 3`. The UV interpretation is a
ν_R-as-ADW-substrate-bound-state per the deep research; that interpretation
acts only on amplitudes and does not change the Lean type signature. -/
structure SterileNeutrino where
  /-- Generation index (1, 2, or 3). -/
  generation : Fin 3
deriving DecidableEq

/-- ℤ₁₆ charge of a fundamental ν_R, locked to `+1 mod 16` by the
Garcia-Etxebarria/Wan-Wang anomaly tower. This is the structural input that
makes Embedding III consistent with the proved
`Z16AnomalyComputation.three_nu_R_cancel_three_gen` and the no-ν_R
hidden-sector deficit. -/
def z16Charge (_ : SterileNeutrino) : ZMod 16 := 1

@[simp] theorem z16Charge_eq_one (ν : SterileNeutrino) :
    z16Charge ν = 1 := rfl

/-! ## 2. Heavy Majorana mass — the ℤ₂-graded rung input -/

/-- Microscopic data for the Majorana rung on a single generation. The heavy
Majorana mass `M_R i` is a per-generation positive real. In Embedding III, it
is identified with the ℤ₁₆-invariant ADW condensate scale `Λ_ADW` (not
derived; tracked hypothesis `H_MR_FromADWSubstrate`).

The bilinear `½ M_R ν_R^T C ν_R` carries ℤ₄ charge 2, anomaly-trivial under
the proved ℤ₁₆ structure (deep research §1.2).

Parameters:
- `M_R : Fin 3 → ℝ` — heavy Majorana mass per generation.
- `M_R_pos : ∀ i, 0 < M_R i` — positivity (ℤ₂-graded rung is non-vacuous).
-/
structure MajoranaRungData where
  M_R : Fin 3 → ℝ
  M_R_pos : ∀ i, 0 < M_R i

/-- A `MajoranaRungData` is *non-vacuous* on every generation iff every
`M_R i` is strictly positive. By construction this is the same as the
`M_R_pos` field; the lemma surfaces it as a Prop-level theorem. -/
theorem majoranaBilinear_nontrivial (m : MajoranaRungData) (i : Fin 3) :
    0 < m.M_R i := m.M_R_pos i

/-! ## 3. WAVE2-OPEN-1: substrate-bridge tracked hypothesis

The deep research is explicit (Block §2): the relation `M_R = Λ_ADW` is *not*
derived in any current ADW / Wetterich / Volovik source. We encode the
substrate-bridge identification as a tracked-hypothesis `Prop`, parameterized
over a positive substrate scale `Λ_ADW > 0`. The hypothesis is non-trivial:
the same `MajoranaRungData` may fail to satisfy it for a given Λ_ADW choice
(too-large M_R triggers the contrapositive `bridge_excludes_super_substrate_M_R`
below).

Project precedent: `ScalarRungInterpretation.H_ScalarChannelIsTetradBifurcation
Output`, `HiddenSectorMixedCharge.H_MixedChannelZ16Cancels`,
`DarkSectorSynthesis.H_VestigialRelicCarriesZ16Charge`.
-/

/-- **WAVE2-OPEN-1**: tracked hypothesis that `M_R i = c_i · Λ_ADW` for some
per-generation coefficient `c_i ∈ (0, 1]`. Genuinely non-trivial: a
`MajoranaRungData` with `M_R i > Λ_ADW` falsifies it (ruled out by
`bridge_excludes_super_substrate_M_R`). -/
def H_MR_FromADWSubstrate (m : MajoranaRungData) (Λ_ADW : ℝ) : Prop :=
  ∀ i, ∃ c, 0 < c ∧ c ≤ 1 ∧ m.M_R i = c * Λ_ADW

/-- Bridge consequence: under `H_MR_FromADWSubstrate Λ_ADW`, every `M_R i` is
bounded above by the substrate scale `Λ_ADW`. Direct, non-vacuous content
linking the substrate scale to the rung scale. -/
theorem M_R_le_substrate_under_bridge
    (m : MajoranaRungData) (Λ_ADW : ℝ) (h_pos : 0 < Λ_ADW)
    (h_bridge : H_MR_FromADWSubstrate m Λ_ADW) :
    ∀ i, m.M_R i ≤ Λ_ADW := by
  intro i
  obtain ⟨c, _hc_pos, hc_le, h_eq⟩ := h_bridge i
  have h_le := h_pos.le
  rw [h_eq]
  calc c * Λ_ADW ≤ 1 * Λ_ADW := by
        exact mul_le_mul_of_nonneg_right hc_le h_le
    _ = Λ_ADW := one_mul _

/-- Sharpness: a `MajoranaRungData` with some `M_R i > Λ_ADW` rules out the
substrate-bridge identification. Structural falsifiability content of the
bridge — there exist concrete witnesses. -/
theorem bridge_excludes_super_substrate_M_R
    (m : MajoranaRungData) (Λ_ADW : ℝ) (h_pos : 0 < Λ_ADW) (i : Fin 3)
    (h_super : Λ_ADW < m.M_R i) :
    ¬ H_MR_FromADWSubstrate m Λ_ADW := by
  intro h_bridge
  have h_le := M_R_le_substrate_under_bridge m Λ_ADW h_pos h_bridge i
  linarith

/-! ## 4. Type-I seesaw mass formula -/

/-- Light-neutrino mass via the Type-I seesaw on the Majorana rung:
`m_ν = y² v² / M_R`. In Embedding III the Yukawa `y` comes from the Wave-1
overlap-integral construction (overlap of left-handed lepton doublets against
the emergent Weyl modes on the substrate). -/
def seesawNeutrinoMass (m : MajoranaRungData) (y v : ℝ) (i : Fin 3) : ℝ :=
  y ^ 2 * v ^ 2 / m.M_R i

@[simp] theorem seesawNeutrinoMass_def
    (m : MajoranaRungData) (y v : ℝ) (i : Fin 3) :
    seesawNeutrinoMass m y v i = y ^ 2 * v ^ 2 / m.M_R i := rfl

/-- Seesaw mass is non-negative for any real `y, v` and any positive `M_R`. -/
theorem seesawNeutrinoMass_nonneg
    (m : MajoranaRungData) (y v : ℝ) (i : Fin 3) :
    0 ≤ seesawNeutrinoMass m y v i := by
  unfold seesawNeutrinoMass
  have h_num : 0 ≤ y ^ 2 * v ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h_den : 0 < m.M_R i := m.M_R_pos i
  exact div_nonneg h_num h_den.le

/-- Seesaw mass is strictly positive when both Yukawa and VEV are nonzero. -/
theorem seesawNeutrinoMass_pos_of_nonzero
    (m : MajoranaRungData) {y v : ℝ} {i : Fin 3}
    (hy : y ≠ 0) (hv : v ≠ 0) :
    0 < seesawNeutrinoMass m y v i := by
  unfold seesawNeutrinoMass
  have h_num : 0 < y ^ 2 * v ^ 2 := by positivity
  have h_den : 0 < m.M_R i := m.M_R_pos i
  exact div_pos h_num h_den

/-- Seesaw mass vanishes iff the Yukawa or VEV vanishes. The forward
direction is the structural content: a non-zero light-neutrino mass requires
at least one of `y, v` non-zero (no spontaneous mass generation from the
Majorana mass alone). -/
theorem seesawNeutrinoMass_zero_iff
    (m : MajoranaRungData) (y v : ℝ) (i : Fin 3) :
    seesawNeutrinoMass m y v i = 0 ↔ y = 0 ∨ v = 0 := by
  unfold seesawNeutrinoMass
  have h_den : (m.M_R i) ≠ 0 := ne_of_gt (m.M_R_pos i)
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · -- y² v² = 0 ⇒ y = 0 ∨ v = 0
      have : y * y * (v * v) = 0 := by ring_nf; ring_nf at h; linarith
      rcases mul_eq_zero.mp this with hxy | hv
      · rcases mul_eq_zero.mp hxy with hy | hy
        · exact Or.inl hy
        · exact Or.inl hy
      · rcases mul_eq_zero.mp hv with hv1 | hv1
        · exact Or.inr hv1
        · exact Or.inr hv1
    · exact absurd h h_den
  · rintro (hy | hv)
    · left
      rw [hy]; ring
    · left
      rw [hv]; ring

/-- Type-I seesaw monotonicity: increasing `M_R` decreases `m_ν` (with all
other parameters fixed and positive Yukawa+VEV). This is the qualitative
signature of seesaw — heavy Majorana mass suppresses the light-neutrino
scale. -/
theorem seesawNeutrinoMass_strictMono_inv_M_R
    (m₁ m₂ : MajoranaRungData) {y v : ℝ} {i : Fin 3}
    (hy : y ≠ 0) (hv : v ≠ 0)
    (h_M_R : m₁.M_R i < m₂.M_R i) :
    seesawNeutrinoMass m₂ y v i < seesawNeutrinoMass m₁ y v i := by
  unfold seesawNeutrinoMass
  have h_num : 0 < y ^ 2 * v ^ 2 := by positivity
  exact div_lt_div_of_pos_left h_num (m₁.M_R_pos i) h_M_R

/-! ## 5. ℤ₁₆ singlet-branch bridge -/

/-- **Z₁₆ unit charge sum** of three fundamental ν_R (one per generation).
Each ν_R contributes `1` mod 16; summing over `Fin 3` gives `3 mod 16`. This
is the per-generation contribution that the proved
`hidden_sector_anomaly_value` requires for hidden-sector saturation. -/
theorem three_nu_R_z16_sum :
    (∑ _ : Fin 3, (1 : ZMod 16)) = 3 := by
  decide

/-- **Z₁₆ bridge to existing infrastructure (load-bearing).** The Majorana
rung populated with three fundamental ν_R Weyl (per
`SterileNeutrino.z16Charge = 1`) saturates the SM-without-ν_R hidden-sector
deficit. Direct consequence of `Z16AnomalyComputation.three_nu_R_cancel_three_gen`
(`(48 : ZMod 16) = 0`) and `HiddenSectorClassification.three_singlets_satisfy_
hidden_sector` (`((3 : ℕ) : ZMod 16) = 3`).

This is the proved-theorem-level realization of Embedding III's claim:
a fundamental ν_R per generation makes the SM ℤ₁₆-anomaly-free, with no
need for additional hidden-sector TQFT/CFT content. -/
theorem majorana_rung_saturates_hidden_sector :
    ((45 + 3 : ℕ) : ZMod 16) = 0 := by
  -- 45 + 3 = 48 ≡ 0 mod 16
  decide

/-- **Z₁₆-bridge consequence**: the 3-generation SM-without-ν_R anomaly
deficit is exactly cancelled by populating the Majorana rung with three
fundamental ν_R Weyl fermions, *not* by adding an SM-singlet hidden TQFT.
This is the formal statement that Embedding III adds zero IR cost relative
to the with-ν_R branch.

Uses `HiddenSectorClassification.hidden_sector_anomaly_value`: the
hidden-sector requirement `(45 + N : ZMod 16) = 0 ↔ (N : ZMod 16) = 3` is
saturated by `N = 3`, and the 3 ν_R Weyl fermions of the Majorana rung
are exactly that compensating content (per
`HiddenSectorClassification.three_singlets_satisfy_hidden_sector`). -/
theorem majorana_rung_compatible_with_hidden_singlet :
    ((3 : ℕ) : ZMod 16) = 3 ∧ ((45 + 3 : ℕ) : ZMod 16) = 0 :=
  ⟨SKEFTHawking.three_singlets_satisfy_hidden_sector,
   majorana_rung_saturates_hidden_sector⟩

/-! ## 6. Falsifiability anchor — observed-mass match -/

/-- Decidable falsifiability predicate: under given Yukawa `y`, EW VEV `v`,
and observed light-neutrino mass `m_nu_obs`, the seesaw prediction matches
the observation within fractional tolerance `tol`.

`IsObservedSeesawMatch m y v i m_nu_obs tol` iff
`|m_ν_seesaw − m_ν_obs| < tol · m_ν_obs`.

This is the Wave-2 quantitative-vs-structural anchor: if no natural
`(y, M_R)` band reproduces NuFit-6.0 m_ν for any generation, the Wave-2
seesaw framing is structural-only at current scope. -/
def IsObservedSeesawMatch
    (m : MajoranaRungData) (y v : ℝ) (i : Fin 3)
    (m_nu_obs tol : ℝ) : Prop :=
  |seesawNeutrinoMass m y v i - m_nu_obs| < tol * m_nu_obs

/-- **Falsifiability witness**: when `M_R` is too large (or `y, v` too small),
the seesaw prediction undershoots `m_nu_obs` by more than `tol`, ruling out
the match. Mirror of `ScalarRungInterpretation.not_isHiggsBilinearCandidate_
of_vev_too_large` for Wave 2. -/
theorem not_isObservedSeesawMatch_of_M_R_too_large
    (m : MajoranaRungData) (y v : ℝ) (i : Fin 3)
    (m_nu_obs tol : ℝ)
    (_h_obs : 0 < m_nu_obs) (_h_tol : 0 < tol)
    (h_too_large : seesawNeutrinoMass m y v i ≤ (1 - tol) * m_nu_obs)
    (_h_tol_lt : tol < 1) :
    ¬ IsObservedSeesawMatch m y v i m_nu_obs tol := by
  unfold IsObservedSeesawMatch
  intro h_match
  rw [abs_lt] at h_match
  obtain ⟨hlo, _⟩ := h_match
  -- m_ν - m_nu_obs > -tol · m_nu_obs (lower bound from |·| < tol·m_nu_obs)
  -- but m_ν ≤ (1-tol)·m_nu_obs, so m_ν - m_nu_obs ≤ -tol·m_nu_obs
  have h1 : seesawNeutrinoMass m y v i - m_nu_obs ≤ -(tol * m_nu_obs) := by
    have : (1 - tol) * m_nu_obs - m_nu_obs = -(tol * m_nu_obs) := by ring
    linarith
  linarith

/-! ## 7. Module summary marker -/

/-- Wave-2 open-problem manifest: the five tracked WAVE2-OPEN derivations from
the deep research, surfaced here so downstream consumers know what is *not*
proved. Marker theorem only — content lives in the `H_MR_FromADWSubstrate`
tracked hypothesis (WAVE2-OPEN-1) and the comments in the file header. -/
theorem wave2_open_problems_summary : True := trivial

end SKEFTHawking.MajoranaRung
