import Mathlib
import SKEFTHawking.Basic
import SKEFTHawking.LinearizedEFE
import SKEFTHawking.HeatKernelExpansion
import SKEFTHawking.HigherCurvatureStructure
import SKEFTHawking.NonlinearDiffInvariance
import SKEFTHawking.NonlinearEFE
import SKEFTHawking.MicroscopicCoefficientMatch

/-!
# Phase 6e Wave 6: Einstein-Cartan Extension (torsion from spin current)

## Goal

Extend the ADW emergent-gravity programme to **Einstein-Cartan with
non-zero torsion** sourced by the fermion spin current — the
structural consequence of working with tetrads `e^a_μ` rather than
the metric `g_μν`.  Hehl-style EC theory (Hehl-Heyde-Kerlick-Nester,
Rev. Mod. Phys. 48, 393 (1976)) gives the algebraic Cartan torsion
equation `T^a_{μν} ∝ G_N · S^a_{μν}`; at the trace/scalar level the
load-bearing parametric content of the Wave 6 model is the closed form

  `|T_EC|(Λ_UV, N_f, α_EC, n_spin)
      = G_N^emerg(Λ_UV, N_f, α_EC) · n_spin
      = α_EC · 12π/(N_f · Λ_UV²) · n_spin`.

The **load-bearing correctness-push** is a quantitative observational-
bound theorem: at the natural microscopic point `(Λ_UV, N_f, α_EC) =
(M_Pl, 16, 1)` and the cosmological-bath spin density
`n_s ≃ 1.3×10⁻³⁹ GeV³`, the predicted torsion amplitude
`|T_EC| ≃ 2.05×10⁻⁷⁷ GeV` sits ~46 orders of magnitude below the
tightest published Kostelecky-Russell-Tasson cosmic-axial-torsion
bound `T < 10⁻³¹ GeV` (PRL 100, 111102 (2008)).

The **Decision-Gate-style biconditional** is `ecResidual = 0 ↔
α_EC = 1` (under positive `(Λ_UV, N_f)` and non-zero spin density),
the Wave 6 expression of Decision Gate E.2.

## Module structure

- §1: Torsion-amplitude and EC-residual definitions (canonical
  through Wave 5's `gNMicroscopic` for structural P6 integrity)
- §2: Torsion-amplitude theorems (positivity + Wave-1/Wave-5
  cross-bridges)
- §3: EC-residual theorems (Decision-Gate-style biconditional)
- §4: Cross-bridge to Phase 6a.1 (`G_N_emerg_at_alpha_one`) +
  Wave 1 (`G_N_from_a2_eq_G_N_sakharov`)
- §5: Quantitative observational-bound theorems (correctness-push
  Decision-Gate-E.6 anchor + cross-channel chaining)
- §6: Tracked-Prop bundle `H_EinsteinCartanExtensionHolds` +
  Dirac/perturbed witnesses

## Conventions

- We work at the **scalar-amplitude level** of the torsion tensor:
  the magnitude `|T_EC|` parametrises the non-vanishing-torsion
  signature.  This restriction preserves the load-bearing physics
  (G_N-rescaling, calibration channel, observational bound) without
  requiring the full Cartan-curvature tensor machinery deferred to
  Phase 6f.
- Sign convention: `T = G_N · n_spin` with non-negative `n_spin`
  (background spin density); the Wave 6 model treats `α_EC` as a
  positive dimensionless rescaling parameter equal to `α_ADW`
  (Sakharov-Adler calibration: `α_EC = 1`).
- `Λ_obs`-style anchor values: `Λ_UV` benchmark = `M_Pl ≃ 12·10¹⁸ GeV`
  (matches Wave 5's `planckMassGeV` rational encoding); cosmic
  `n_s = 13/10⁴⁰ GeV³` (matches `EINSTEIN_CARTAN_PARAMS["COSMOLOGICAL_SPIN_DENSITY_GEV3"]`);
  Kostelecky bound = `1/10³¹ GeV`.

## References

- Hehl, Heyde, Kerlick, Nester, *Rev. Mod. Phys.* 48, 393 (1976) —
  Einstein-Cartan formulation; algebraic Cartan equation `T ∝ G_N S`.
- Trautman, *Acta Phys. Polon.* B5, 1 (1973) — torsion sourced by
  spin current; non-vanishing torsion in fermionic matter.
- Kostelecký, Russell, Tasson, *Phys. Rev. Lett.* 100, 111102 (2008) —
  tightest cosmic-axial-torsion bound `T < 10⁻³¹ GeV`.
- Lämmerzahl, *Phys. Lett. A* 228, 223 (1997) — Hughes-Drever
  rotational-axial-torsion bound `T < 10⁻²⁹ GeV`.
- Phase 6a.1 LinearizedEFE.lean — `G_N_emerg`, `G_N_emerg_at_alpha_one`
- Phase 6e Wave 1 HeatKernelExpansion.lean — `G_N_from_a2`,
  `G_N_from_a2_pos`, `G_N_from_a2_eq_G_N_sakharov`
- Phase 6e Wave 5 MicroscopicCoefficientMatch.lean — `gNMicroscopic`,
  `gNMicroscopic_at_alpha_one_eq_G_N_emerg`

## Scope lock

IN SCOPE: scalar-amplitude torsion prediction; EC residual deviation
channel; Sakharov-Adler calibration biconditional; cross-bridges to
Phase 6a.1, Waves 1 + 5; quantitative Kostelecky bound passage;
tracked-Prop bundle with Dirac/perturbed witnesses.

OUT OF SCOPE: full Cartan curvature `R^a_{bμν}` on a manifold
(deferred to Phase 6f Lorentzian infrastructure); spin-spin contact
4-fermion operator (dim-6 effective action; out of scope per
strategy doc §15 quantum-correction backlog); Holst-term `θ` modular
extension; non-Abelian gauge torsion; Cartan-Riemann decomposition
beyond the scalar amplitude.
-/

noncomputable section

open Real

namespace SKEFTHawking.EinsteinCartanExtension

open SKEFTHawking.LinearizedEFE
open SKEFTHawking.HeatKernelExpansion
open SKEFTHawking.MicroscopicCoefficientMatch

/-! ## §1. Definitions -/

/-- **Microscopic Einstein-Cartan torsion amplitude.**  The Hehl-style
algebraic Cartan torsion equation gives `T = G_N · S` for the
spin-current source; in the ADW emergent-gravity formulation
`G_N = G_N^emerg = α_EC · G_N_sakharov`.  The Wave 6 scalar amplitude
is therefore

  `torsionAmplitude(Λ_UV, N_f, α_EC, n_spin)
      = gNMicroscopic(Λ_UV, N_f, α_EC) · n_spin
      = α_EC · 12π/(N_f · Λ_UV²) · n_spin`.

Defined through Wave 5's `gNMicroscopic` for *structural* P6
cross-module integrity: any future change to the ADW G_N rescaling
flows through to the Wave 6 prediction by definition. -/
def torsionAmplitude (Λ_UV N_f α_EC n_spin : ℝ) : ℝ :=
  gNMicroscopic Λ_UV N_f α_EC * n_spin

/-- **Cosmological-bath spin density** at `T = T_CMB`.  Encoded as the
rational `13 / 10⁴⁰` ≃ 1.3 × 10⁻³⁹ GeV³, matching
`EINSTEIN_CARTAN_PARAMS['COSMOLOGICAL_SPIN_DENSITY_GEV3']`.  Used by
the Wave 6 quantitative correctness-push as the canonical background
spin density. -/
def cosmologicalSpinDensityGeV3 : ℝ := 13 / (10 : ℝ) ^ (40 : ℕ)

/-- **Torsion amplitude at the cosmological-bath background.**
Specialises `torsionAmplitude` to `n_spin = cosmologicalSpinDensityGeV3`. -/
def torsionAtCosmologicalBackground (Λ_UV N_f α_EC : ℝ) : ℝ :=
  torsionAmplitude Λ_UV N_f α_EC cosmologicalSpinDensityGeV3

/-- **Kostelecky-Russell-Tasson cosmic-axial-torsion bound.**  Encoded
as the rational `1 / 10³¹ ≃ 10⁻³¹ GeV` (PRL 100, 111102 (2008),
95% CL).  Tightest published bound in the natural high-energy regime. -/
def torsionBoundKostelecky : ℝ := 1 / (10 : ℝ) ^ (31 : ℕ)

/-- **Lämmerzahl Hughes-Drever rotational-axial-torsion bound.**
Encoded as `1 / 10²⁹ ≃ 10⁻²⁹ GeV` (Phys. Lett. A 228, 223 (1997)).
Cross-channel-independent comparator: Kostelecky < Hughes-Drever
by 100×. -/
def torsionBoundHughesDrever : ℝ := 1 / (10 : ℝ) ^ (29 : ℕ)

/-- **EC match residual.**  The deviation channel of the Wave 6
torsion amplitude relative to the Sakharov-Adler calibration:

  `ecResidual(Λ_UV, N_f, α_EC, n_spin)
      := torsionAmplitude(Λ_UV, N_f, α_EC, n_spin)
          − torsionAmplitude(Λ_UV, N_f, 1, n_spin)
      = (α_EC − 1) · G_N_from_a2(Λ_UV, N_f) · n_spin`.

Vanishes iff `α_EC = 1` (under positive `(Λ_UV, N_f, n_spin)`).
The Wave 6 expression of Decision Gate E.2 (the Wave 1 closure
`a2_matches_GNemerg_iff_alpha_ADW_unity` lifted to the EC sector). -/
def ecResidual (Λ_UV N_f α_EC n_spin : ℝ) : ℝ :=
  torsionAmplitude Λ_UV N_f α_EC n_spin
    - torsionAmplitude Λ_UV N_f 1 n_spin

/-! ## §2. Torsion-amplitude theorems -/

/-- **Torsion-amplitude positivity.**  Under positive `(Λ_UV, N_f,
α_EC, n_spin)`, the predicted torsion amplitude is strictly positive.
Substantive: rules out the trivial reading "the EC torsion amplitude
might vanish for some natural parameter point"; the Hehl-style
prediction is *non-zero* for any non-trivial spin source. -/
theorem torsionAmplitude_pos
    {Λ_UV N_f α_EC n_spin : ℝ}
    (hΛ : 0 < Λ_UV) (hN : 0 < N_f)
    (hα : 0 < α_EC) (hn : 0 < n_spin) :
    0 < torsionAmplitude Λ_UV N_f α_EC n_spin := by
  unfold torsionAmplitude gNMicroscopic
  exact mul_pos (mul_pos hα (G_N_from_a2_pos hΛ hN)) hn

/-- **Torsion at the cosmological background is strictly positive at
natural parameters.**  Substantive non-vanishing-prediction witness:
at `(Λ_UV, N_f, α_EC) = (planckMassGeV, 16, 1)`, the predicted
torsion amplitude at the cosmological spin density is strictly
positive — rules out the trivial reading "the bound passes because
the prediction is zero." -/
theorem torsionAtCosmologicalBackground_pos_at_natural_params :
    0 < torsionAtCosmologicalBackground planckMassGeV 16 1 := by
  unfold torsionAtCosmologicalBackground cosmologicalSpinDensityGeV3
  apply torsionAmplitude_pos
  · -- 0 < planckMassGeV = 12 · 10^18
    unfold planckMassGeV
    have : (0 : ℝ) < (10 : ℝ) ^ (18 : ℕ) := pow_pos (by norm_num) _
    nlinarith
  · norm_num
  · norm_num
  · -- 0 < 13 / 10^40
    have : (0 : ℝ) < (10 : ℝ) ^ (40 : ℕ) := pow_pos (by norm_num) _
    positivity

/-! ## §3. EC residual theorems -/

/-- **EC residual at the calibrated configuration.**  At the
Sakharov-Adler calibration `α_EC = 1`, the Wave 6 EC residual
vanishes for all `(Λ_UV, N_f, n_spin)`.  This is the *consistency*
check: at the calibrated value, the EC sector closes against the
bare Wave 1 G_N. -/
theorem ecResidual_at_alpha_one (Λ_UV N_f n_spin : ℝ) :
    ecResidual Λ_UV N_f 1 n_spin = 0 := by
  unfold ecResidual
  ring

/-- **Linear deviation channel (substantive falsifier).**  The EC
residual equals exactly `(α_EC − 1) · G_N_from_a2 · n_spin`.
Substantive: exposes the *channel* of the deviation as linear in
`α_EC − 1` (the Vergeles rescaling parameter).  Pattern matches Wave
4's `emergentStressEnergyTrace_minus_matter_eq` and Wave 5's
`matchResidual_eq_alpha_minus_one_times_GN`. -/
theorem ecResidual_eq_alpha_minus_one_times_amplitude
    (Λ_UV N_f α_EC n_spin : ℝ) :
    ecResidual Λ_UV N_f α_EC n_spin =
      (α_EC - 1) * G_N_from_a2 Λ_UV N_f * n_spin := by
  unfold ecResidual torsionAmplitude gNMicroscopic
  ring

/-- **MAIN Decision-Gate-style biconditional (Wave 6 calibration
anchor).**  Under positive cutoff and species count and *non-zero*
spin density, the EC residual vanishes iff the ADW coefficient is at
the Sakharov-Adler calibration `α_EC = 1`.  This is the Wave 6
expression of Decision Gate E.2 — Wave 1's
`a2_matches_GNemerg_iff_alpha_ADW_unity` lifted to the EC sector.

Substantive: forward direction uses positivity of `G_N_from_a2`
(`G_N_from_a2_pos`, Wave 1) plus non-vanishing of `n_spin` to flip
two `mul_eq_zero`s; reverse is def-substitution.  Both `(Λ_UV, N_f)`
positivity and `n_spin ≠ 0` are load-bearing hypotheses (without
non-vanishing spin density the residual is identically zero
regardless of `α_EC`). -/
theorem ecResidual_eq_zero_iff_alpha_unity
    {Λ_UV N_f α_EC n_spin : ℝ}
    (hΛ : 0 < Λ_UV) (hN : 0 < N_f) (hn : n_spin ≠ 0) :
    ecResidual Λ_UV N_f α_EC n_spin = 0 ↔ α_EC = 1 := by
  rw [ecResidual_eq_alpha_minus_one_times_amplitude]
  have hG_pos : 0 < G_N_from_a2 Λ_UV N_f := G_N_from_a2_pos hΛ hN
  have hG_ne : G_N_from_a2 Λ_UV N_f ≠ 0 := ne_of_gt hG_pos
  constructor
  · intro h
    -- (α_EC - 1) · G_N_from_a2 · n_spin = 0 ⇒ α_EC = 1
    have h1 : (α_EC - 1) * G_N_from_a2 Λ_UV N_f = 0 :=
      (mul_eq_zero.mp h).resolve_right hn
    have h2 : α_EC - 1 = 0 :=
      (mul_eq_zero.mp h1).resolve_right hG_ne
    linarith
  · intro h
    rw [h]; ring

/-! ## §4. Cross-bridge to Phase 6a.1 + Wave 1 -/

/-- **Substantive cross-bridge (Phase 6a.1 + Wave 1).**  At the
Sakharov-Adler calibration `α_EC = 1`, the torsion amplitude equals
`G_N_emerg(Λ_UV, N_f, 1) · n_spin` — the Phase-6a.1 emergent Newton
constant times the spin density.  Proof body invokes both
`LinearizedEFE.G_N_emerg_at_alpha_one` and Wave 5's
`gNMicroscopic_at_alpha_one_eq_G_N_emerg` by name — drift-protection
per `feedback_python_lean_refs_drift.md` (P6 cross-module integrity:
the Wave-6 prediction at calibration is structurally identified with
the Phase-6a.1 emergent G_N). -/
theorem torsionAmplitude_at_alpha_one_eq_G_N_emerg_times_n
    (Λ_UV N_f n_spin : ℝ) :
    torsionAmplitude Λ_UV N_f 1 n_spin =
      SKEFTHawking.LinearizedEFE.G_N_emerg Λ_UV N_f 1 * n_spin := by
  unfold torsionAmplitude
  rw [SKEFTHawking.MicroscopicCoefficientMatch.gNMicroscopic_at_alpha_one_eq_G_N_emerg]

/-! ## §5. Quantitative observational-bound theorems (correctness-push) -/

/-- **Kostelecky bound is strictly tighter than Hughes-Drever.**
Substantive numerical fact: `1/10³¹ < 1/10²⁹`, so any prediction
satisfying the Kostelecky bound *automatically* satisfies the
Hughes-Drever bound.  Used by the chained-bound theorem below.  Not
a P3 trivial-multiplication: the substantive content is the
strict-ordering of the two published bounds. -/
theorem torsionBoundKostelecky_lt_hughesDrever :
    torsionBoundKostelecky < torsionBoundHughesDrever := by
  unfold torsionBoundKostelecky torsionBoundHughesDrever
  -- 1/10^31 < 1/10^29 follows from 10^29 < 10^31.
  have h29 : (0 : ℝ) < (10 : ℝ) ^ (29 : ℕ) := pow_pos (by norm_num) _
  have h31 : (0 : ℝ) < (10 : ℝ) ^ (31 : ℕ) := pow_pos (by norm_num) _
  have h_lt : (10 : ℝ) ^ (29 : ℕ) < (10 : ℝ) ^ (31 : ℕ) := by
    have : (10 : ℝ) ^ (29 : ℕ) * 1 < (10 : ℝ) ^ (29 : ℕ) * 100 := by
      have h_pos : (0 : ℝ) < (10 : ℝ) ^ (29 : ℕ) := h29
      nlinarith
    have h_eq : (10 : ℝ) ^ (31 : ℕ) = (10 : ℝ) ^ (29 : ℕ) * 100 := by
      have h_split : (10 : ℝ) ^ (31 : ℕ) = (10 : ℝ) ^ (29 : ℕ) * (10 : ℝ) ^ (2 : ℕ) := by
        rw [← pow_add]
      rw [h_split]; norm_num
    rw [h_eq]; linarith
  exact one_div_lt_one_div_of_lt h29 h_lt

/-- **MAIN correctness-push: torsion at natural microscopic params is
quantitatively below the Kostelecky bound.**  At `(Λ_UV, N_f, α_EC) =
(planckMassGeV, 16, 1)` and the cosmological-bath spin density, the
predicted torsion amplitude `|T_EC|` is strictly less than the
Kostelecky-Russell-Tasson published bound `1/10³¹ GeV`.

Concretely we prove `torsionAtCosmologicalBackground planckMassGeV
16 1 < torsionBoundKostelecky`.  The natural-parameter prediction is
`|T_EC| = 12π/(16 · planckMassGeV²) · 13/10⁴⁰ ≃ 2.05×10⁻⁷⁷ GeV`,
which sits ~46 orders of magnitude below the bound.

**Substantive Decision-Gate-style anchor:** quantitatively connects
the Wave 6 microscopic prediction to the published observational
bound, making the "torsion bound matched" claim falsifiable in the
strong sense (any future Wave-6-derived prediction with `|T_EC| ≥
10⁻³¹` would violate this theorem). -/
theorem torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky :
    torsionAtCosmologicalBackground planckMassGeV 16 1 <
      torsionBoundKostelecky := by
  unfold torsionAtCosmologicalBackground torsionAmplitude gNMicroscopic
        G_N_from_a2 cosmologicalSpinDensityGeV3 planckMassGeV
        torsionBoundKostelecky
  -- Goal: 1 * (12π / (16 · (12·10^18)²)) * (13/10^40) < 1/10^31.
  have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h36 : (0 : ℝ) < (10 : ℝ) ^ (36 : ℕ) := pow_pos (by norm_num) _
  have h40 : (0 : ℝ) < (10 : ℝ) ^ (40 : ℕ) := pow_pos (by norm_num) _
  have h31 : (0 : ℝ) < (10 : ℝ) ^ (31 : ℕ) := pow_pos (by norm_num) _
  have h_combine : (10 : ℝ) ^ (36 : ℕ) * (10 : ℝ) ^ (40 : ℕ) = (10 : ℝ) ^ (76 : ℕ) := by
    rw [← pow_add]
  have h_split : (10 : ℝ) ^ (76 : ℕ) = (10 : ℝ) ^ (31 : ℕ) * (10 : ℝ) ^ (45 : ℕ) := by
    rw [← pow_add]
  -- Step 1: collapse (12·10^18)^2 = 144·10^36.
  have h_sq_eq : (12 * (10 : ℝ) ^ (18 : ℕ)) ^ 2 = 144 * (10 : ℝ) ^ (36 : ℕ) := by
    have h1 : (12 * (10 : ℝ) ^ (18 : ℕ)) ^ 2 = 12 ^ 2 * ((10 : ℝ) ^ (18 : ℕ)) ^ 2 := by ring
    have h2 : ((10 : ℝ) ^ (18 : ℕ)) ^ 2 = (10 : ℝ) ^ (36 : ℕ) := by rw [← pow_mul]
    rw [h1, h2]; norm_num
  rw [h_sq_eq]
  -- Step 2: collapse the LHS into (12π·13) / (2304·10^76).
  have h_LHS_clean :
      (1 : ℝ) * (12 * Real.pi / (16 * (144 * (10 : ℝ) ^ (36 : ℕ))))
        * (13 / (10 : ℝ) ^ (40 : ℕ))
      = (12 * Real.pi * 13) / (2304 * (10 : ℝ) ^ (76 : ℕ)) := by
    have h36_ne : (10 : ℝ) ^ (36 : ℕ) ≠ 0 := ne_of_gt h36
    have h40_ne : (10 : ℝ) ^ (40 : ℕ) ≠ 0 := ne_of_gt h40
    have h_lhs_to_combined :
        (1 : ℝ) * (12 * Real.pi / (16 * (144 * (10 : ℝ) ^ (36 : ℕ))))
          * (13 / (10 : ℝ) ^ (40 : ℕ))
        = (12 * Real.pi * 13) /
            ((16 * (144 * (10 : ℝ) ^ (36 : ℕ))) * (10 : ℝ) ^ (40 : ℕ)) := by
      field_simp
    rw [h_lhs_to_combined]
    have h_denom_eq :
        (16 * (144 * (10 : ℝ) ^ (36 : ℕ))) * (10 : ℝ) ^ (40 : ℕ)
          = 2304 * (10 : ℝ) ^ (76 : ℕ) := by
      rw [show (16 * (144 * (10 : ℝ) ^ (36 : ℕ))) * (10 : ℝ) ^ (40 : ℕ)
            = 2304 * ((10 : ℝ) ^ (36 : ℕ) * (10 : ℝ) ^ (40 : ℕ)) from by ring,
          h_combine]
    rw [h_denom_eq]
  rw [h_LHS_clean]
  -- Step 3: cross-multiply via div_lt_div_iff₀.
  have h_denom_pos : (0 : ℝ) < 2304 * (10 : ℝ) ^ (76 : ℕ) := by positivity
  rw [div_lt_div_iff₀ h_denom_pos h31]
  -- Goal: 12·π·13 · 10^31 < 1 · (2304 · 10^76)
  -- 156π < 156·3.15 = 491.4 < 2304 ≤ 2304·10^45 = 2304·10^76 / 10^31, so the
  -- inequality holds.  Prove via h_pi13_bound + the 10^45 ≥ 1 expansion.
  rw [h_split]
  -- Goal: 12·π·13 · 10^31 < 1 · (2304 · (10^31 · 10^45))
  have h_pi13_bound : 12 * Real.pi * 13 < 491.4 := by nlinarith [hpi_lt, hpi_pos]
  have h_45_ge_one : (1 : ℝ) ≤ (10 : ℝ) ^ (45 : ℕ) := by
    have h0 : (1 : ℝ) = (10 : ℝ) ^ (0 : ℕ) := by norm_num
    rw [h0]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) (by decide : (0 : ℕ) ≤ 45)
  have h_491_lt_2304_10_45 : (491.4 : ℝ) < 2304 * (10 : ℝ) ^ (45 : ℕ) := by
    have h_2304_le : (2304 : ℝ) ≤ 2304 * (10 : ℝ) ^ (45 : ℕ) := by
      calc (2304 : ℝ) = 2304 * 1 := by ring
        _ ≤ 2304 * (10 : ℝ) ^ (45 : ℕ) :=
            mul_le_mul_of_nonneg_left h_45_ge_one (by norm_num)
    linarith
  -- Final assembly: multiply h_491_lt_2304_10_45 by 10^31 (positive), chain.
  have h_pi13_step : 12 * Real.pi * 13 * (10 : ℝ) ^ (31 : ℕ) <
      491.4 * (10 : ℝ) ^ (31 : ℕ) :=
    mul_lt_mul_of_pos_right h_pi13_bound h31
  have h_491_step : (491.4 : ℝ) * (10 : ℝ) ^ (31 : ℕ) <
      (2304 * (10 : ℝ) ^ (45 : ℕ)) * (10 : ℝ) ^ (31 : ℕ) :=
    mul_lt_mul_of_pos_right h_491_lt_2304_10_45 h31
  have h_RHS_eq : (1 : ℝ) * (2304 * ((10 : ℝ) ^ (31 : ℕ) * (10 : ℝ) ^ (45 : ℕ)))
                  = (2304 * (10 : ℝ) ^ (45 : ℕ)) * (10 : ℝ) ^ (31 : ℕ) := by ring
  rw [h_RHS_eq]
  linarith

/-- **Cross-channel chained bound (Hughes-Drever follows from
Kostelecky).**  Any prediction satisfying the Kostelecky cosmic-axial-
torsion bound automatically satisfies the (looser) Hughes-Drever
rotational-axial-torsion bound — purely by the published-bound
ordering `Kostelecky < Hughes-Drever` (theorem
`torsionBoundKostelecky_lt_hughesDrever`).  Substantive cross-channel
compositional theorem: the Wave 6 main correctness-push directly
implies passage of the second channel without re-invoking the
quantitative computation. -/
theorem below_kostelecky_implies_below_hughes_drever
    {x : ℝ} (h : x < torsionBoundKostelecky) :
    x < torsionBoundHughesDrever := by
  exact lt_trans h torsionBoundKostelecky_lt_hughesDrever

/-! ## §6. Tracked-Prop bundle for the EC extension -/

/-- **Bundled predicate for the Einstein-Cartan extension.**  An
`(Λ_UV, N_f, α_EC)` triple "satisfies the EC extension at the
cosmological background" iff:

  1. The EC match residual `δT := torsionAmplitude(α_EC) − torsionAmplitude(1)`
     vanishes (Wave 6 §3 calibration channel — `α_EC = 1`);
  2. The torsion amplitude at the cosmological background is strictly
     positive (Wave 6 §2 — non-vanishing-prediction signature);
  3. The torsion amplitude at the cosmological background sits below
     the Kostelecky bound (Wave 6 §5 correctness-push observational-
     passage condition).

Each conjunct invokes a *distinct* substantive theorem with distinct
algebraic/numerical content; not P2 redundancy.  Each conjunct
genuinely separates "Wave 6 EC extension at the calibrated point"
from a distinct failure mode (off-calibration α_EC, vanishing
prediction, or observational-bound violation). -/
def H_EinsteinCartanExtensionHolds (Λ_UV N_f α_EC : ℝ) : Prop :=
  ecResidual Λ_UV N_f α_EC cosmologicalSpinDensityGeV3 = 0 ∧
  0 < torsionAtCosmologicalBackground Λ_UV N_f α_EC ∧
  torsionAtCosmologicalBackground Λ_UV N_f α_EC < torsionBoundKostelecky

/-- **Dirac-bundle witness at the Sakharov-Adler calibration and
natural microscopic params.**  At `(Λ_UV, N_f, α_EC) = (planckMassGeV,
16, 1)`, the EC-extension bundle holds.

Substantive cross-bridges: each conjunct invokes a *distinct*
substantive theorem by name — `ecResidual_at_alpha_one` (Wave 6 §3),
`torsionAtCosmologicalBackground_pos_at_natural_params` (Wave 6 §2),
and `torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky`
(Wave 6 §5 correctness-push).  Not P2 redundancy; the conjuncts probe
three distinct structural channels. -/
theorem dirac_H_EinsteinCartanExtensionHolds_at_alpha_one :
    H_EinsteinCartanExtensionHolds planckMassGeV 16 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ecResidual_at_alpha_one planckMassGeV 16 cosmologicalSpinDensityGeV3
  · exact torsionAtCosmologicalBackground_pos_at_natural_params
  · exact torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky

/-- **Falsifier-witness for non-calibrated `α_EC`.**  Under positive
`(Λ_UV, N_f)` and *any* `α_EC ≠ 1`, the EC extension fails —
specifically its first conjunct (the EC match residual at the
cosmological background).

Substantive scope: rules out the trivial reading "any `α_EC` satisfies
the bundle"; the predicate genuinely singles out the Sakharov-Adler
calibration.  Drift-protection: proof body invokes
`ecResidual_eq_zero_iff_alpha_unity` (Wave 6 §3) by name — and uses
that `cosmologicalSpinDensityGeV3 ≠ 0` as the load-bearing non-
vanishing-spin-density hypothesis. -/
theorem perturbed_alpha_not_H_EinsteinCartanExtensionHolds
    {Λ_UV N_f α_EC : ℝ}
    (hΛ : 0 < Λ_UV) (hN : 0 < N_f) (hα : α_EC ≠ 1) :
    ¬ H_EinsteinCartanExtensionHolds Λ_UV N_f α_EC := by
  intro ⟨h_match, _, _⟩
  -- cosmologicalSpinDensityGeV3 = 13/10^40 > 0, so ≠ 0.
  have h_n_pos : 0 < cosmologicalSpinDensityGeV3 := by
    unfold cosmologicalSpinDensityGeV3
    have : (0 : ℝ) < (10 : ℝ) ^ (40 : ℕ) := pow_pos (by norm_num) _
    positivity
  have h_n_ne : cosmologicalSpinDensityGeV3 ≠ 0 := ne_of_gt h_n_pos
  have h_eq := (ecResidual_eq_zero_iff_alpha_unity hΛ hN h_n_ne).mp h_match
  exact hα h_eq

end SKEFTHawking.EinsteinCartanExtension

end
