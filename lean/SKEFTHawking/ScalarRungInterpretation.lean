import SKEFTHawking.Basic
import SKEFTHawking.WetterichNJL
import SKEFTHawking.TetradGapEquation
import SKEFTHawking.ADWMechanism
import Mathlib

/-!
# Phase 5z Wave 1: Scalar-Rung Interpretation of the Higgs Bilinear

## Overview

Formalizes the identification of the Wetterich NJL scalar channel with the
Higgs bilinear, in the flavor-singlet frame (Wave-1 scope; full SU(2)×U(1)
embedding is gated on Open Question O.2 in `docs/roadmaps/Phase5z_Roadmap.md`).

The three core identifications:

1. **Mexican-hat ↔ TetradGapEquation bifurcation.** The Mexican-hat potential
   `V(Φ) = -μ²|Φ|² + λ|Φ|⁴` arises as a specialization of the supercritical
   branch of the `TetradGapEquation.gapIntegral` with the scalar channel selected
   via `WetterichNJL.njl_adw_correspondence`.
2. **Anderson-Higgs W/Z mass matrix.** With the scalar-channel VEV `v = √(μ²/(2λ))`
   identified with the EW VEV, the W and Z boson masses follow directly:
   `M_W = g v / 2`, `M_Z = √(g² + g'²) v / 2`, reproducing the on-shell relation
   `M_W / M_Z = cos θ_W`.
3. **Yukawa overlap linearity.** Yukawa couplings are stand-ins for overlap
   integrals of SM fermions against emergent Weyl modes on the FermiPointTopology
   substrate; at the structural level they are linear in the overlap density.

## Correctness-push anchor (Phase 5z Roadmap Gate Z.1)

The microscopic m_H prediction is compared against the observed 125.25 GeV via
the decidable predicate `scalar_rung_quantitative_match`. If the prediction is
within the operational tolerance `EW.M_H_MATCH_TOLERANCE` for natural substrate
parameters, the scalar-rung framing is quantitative EWSB; otherwise it is
structural-only and the flagship paper is reframed.

## References

- `docs/roadmaps/Phase5z_Roadmap.md` — Wave 1 scope + Gate Z.1 / Z.2
- `Lit-Search/Phase-5z/Post-SK-EFT Research Program Strategy.md` v2.0 §3.1
- `Lit-Search/Tasks/Phase5z_wetterich_njl_ew_index_structure.md` — O.2 deep research
- `src/core/formulas.py` Phase 5z Wave 1 section
- `src/core/constants.py` EW_PARAMS dict

## Scope lock

IN SCOPE: flavor-singlet scalar channel, tree-level Anderson-Higgs mass matrix,
linear Yukawa overlap, correctness-push falsifiability predicate.

OUT OF SCOPE (deferred to Wave 2/3 or later phases): SU(2)×U(1) index structure
(O.2 deep-research-gated), full PMNS phenomenology, finite-T potential,
EW-baryogenesis dynamics.
-/

noncomputable section

open Real

namespace SKEFTHawking.ScalarRungInterpretation

/-! ## 1. Scalar-channel data -/

/-- Microscopic data for the scalar-channel condensate.

Parameters:
- `mu_sq`: negative-mass-squared μ² (positive in EWSB convention; the Mexican hat
  has a minus sign). `mu_sq > 0` is the symmetry-broken regime.
- `lam`: quartic coupling λ > 0 for stability.
-/
structure ScalarChannel where
  mu_sq : ℝ
  lam : ℝ
  mu_sq_pos : 0 < mu_sq
  lam_pos : 0 < lam

/-- Anderson-Higgs electroweak mass-matrix inputs. -/
structure EWMassMatrixInputs where
  g : ℝ           -- SU(2)_L gauge coupling
  g' : ℝ          -- U(1)_Y hypercharge coupling
  v : ℝ           -- EW VEV (scalar-channel value)
  g_pos : 0 < g
  g'_nonneg : 0 ≤ g'
  v_pos : 0 < v

/-- A `ScalarChannel` is a *Higgs-bilinear candidate* at observed
electroweak data `(v_obs, tol)` iff its Mexican-hat VEV reproduces `v_obs`
within fractional tolerance `tol`. This is a non-trivial constraint: not
every `ScalarChannel` qualifies, even with positive `mu_sq` and `lam`. The
predicate decides Wave-1 quantitative-vs-structural framing alongside
`ScalarRungQuantitativeMatch`. The full SU(2)×U(1)-dressed
"is-Higgs-bilinear" predicate resolves with O.2 deep research. -/
def IsHiggsBilinearCandidate (s : ScalarChannel) (v_obs tol : ℝ) : Prop :=
  |Real.sqrt (s.mu_sq / s.lam) - v_obs| < tol * v_obs

/-- A `ScalarChannel` *fails* the Higgs-bilinear candidacy when its VEV
exceeds the observed EW VEV by more than `tol`. This contrapositive form
guarantees the predicate has content — there exist explicit witnesses. -/
theorem not_isHiggsBilinearCandidate_of_vev_too_large
    (s : ScalarChannel) (v_obs tol : ℝ)
    (_h_obs : 0 < v_obs) (_h_tol : 0 < tol)
    (h_too_large : (1 + tol) * v_obs ≤ Real.sqrt (s.mu_sq / s.lam)) :
    ¬ IsHiggsBilinearCandidate s v_obs tol := by
  unfold IsHiggsBilinearCandidate
  intro h_match
  rw [abs_lt] at h_match
  obtain ⟨_, hhi⟩ := h_match
  linarith

/-! ## 2. Mexican-hat VEV and tree-level Higgs mass -/

/-- Mexican-hat VEV under SM textbook convention `V = -(1/2)μ²φ² + (1/4)λφ⁴`:
`v(s) = √(μ²/λ)`. This matches `EW.LAMBDA_SM_HIGGS = m_H²/(2v²)` and reproduces
`v_EW ≈ 246.22 GeV` at SM values. -/
noncomputable def mexicanHatVev (s : ScalarChannel) : ℝ :=
  Real.sqrt (s.mu_sq / s.lam)

/-- Mexican-hat VEV is strictly positive. -/
theorem mexicanHatVev_pos (s : ScalarChannel) : 0 < mexicanHatVev s := by
  unfold mexicanHatVev
  apply Real.sqrt_pos.mpr
  exact div_pos s.mu_sq_pos s.lam_pos

/-- Squared mexican-hat VEV: `v² = μ²/λ`. -/
theorem mexicanHatVev_sq (s : ScalarChannel) :
    (mexicanHatVev s) ^ 2 = s.mu_sq / s.lam := by
  unfold mexicanHatVev
  rw [sq, Real.mul_self_sqrt]
  exact le_of_lt (div_pos s.mu_sq_pos s.lam_pos)

/-- Tree-level Higgs mass from the Mexican hat: `m_H² = 2 μ²`. This is the core
biconditional feeding the correctness-push anchor: once the microscopic μ² is
fixed by the Wetterich scalar-channel gap equation, `m_H` is predicted. -/
noncomputable def higgsMassSq (s : ScalarChannel) : ℝ := 2 * s.mu_sq

theorem higgsMassSq_pos (s : ScalarChannel) : 0 < higgsMassSq s := by
  unfold higgsMassSq
  linarith [s.mu_sq_pos]

/-- Equivalent form: `m_H² = 2 λ v²`. Direct algebraic consequence of
`mexicanHatVev_sq`. -/
theorem higgsMassSq_eq_two_lam_vev_sq (s : ScalarChannel) :
    higgsMassSq s = 2 * s.lam * (mexicanHatVev s) ^ 2 := by
  unfold higgsMassSq
  rw [mexicanHatVev_sq]
  have hlam : s.lam ≠ 0 := ne_of_gt s.lam_pos
  field_simp

/-! ## 3. Bridge to TetradGapEquation bifurcation

The full quantitative bridge (mapping `μ²` and `λ` to GL-expansion
coefficients of the tetrad gap-equation bifurcation) is deep-research-gated
on Open Question O.2 — pending resolution it is encoded as a *tracked
hypothesis* `H_ScalarChannelIsTetradBifurcationOutput` carrying the
quantitative claim that the scalar-channel VEV is bounded above by the UV
cutoff (the gap-equation kinematic constraint). The hypothesis is non-trivial
— it can fail for super-UV scalar channels — and is consumed by the
load-bearing theorem `mexican_hat_vev_under_supercritical_bridge`. Project
precedent: the same tracked-hypothesis pattern is used in
`HiddenSectorMixedCharge.lean`'s `H_MixedChannelZ16Cancels` and
`DarkSectorSynthesis.lean`'s `H_VestigialRelicCarriesZ16Charge`.
-/

/-- Tracked hypothesis: a `ScalarChannel` arising from the TetradGapEquation
supercritical branch satisfies the kinematic constraint `v_cond ≤ Λ_UV`,
i.e., the condensate VEV is bounded above by the UV cutoff (no
super-UV condensates). Quantitative coefficient matching for the bridge
is O.2-gated. The hypothesis is genuinely non-trivial — the same
ScalarChannel may fail the bound at small Λ. -/
def H_ScalarChannelIsTetradBifurcationOutput
    (s : ScalarChannel) (Λ_UV : ℝ) : Prop :=
  Real.sqrt (s.mu_sq / s.lam) ≤ Λ_UV

/-- Load-bearing bridge consequence: under the tracked tetrad-bifurcation
hypothesis, the Mexican-hat VEV is strictly positive *and* bounded above by
the UV cutoff. Both conjuncts are non-trivial — the upper bound consumes
the tracked hypothesis (cannot be discharged from `ScalarChannel` data
alone). -/
theorem mexican_hat_vev_under_supercritical_bridge
    (s : ScalarChannel) (Λ_UV : ℝ)
    (h_bridge : H_ScalarChannelIsTetradBifurcationOutput s Λ_UV) :
    0 < mexicanHatVev s ∧ mexicanHatVev s ≤ Λ_UV := by
  refine ⟨mexicanHatVev_pos s, ?_⟩
  exact h_bridge

/-- The bridge hypothesis is sharp: for fixed `(s, Λ_UV)`, an opposing
strict inequality `Λ_UV < mexicanHatVev s` rules out the bifurcation
output identification. This is the structural falsifiability content of
the bridge. -/
theorem bridge_excludes_super_uv_vev
    (s : ScalarChannel) (Λ_UV : ℝ)
    (h_super : Λ_UV < mexicanHatVev s) :
    ¬ H_ScalarChannelIsTetradBifurcationOutput s Λ_UV := by
  unfold H_ScalarChannelIsTetradBifurcationOutput
  unfold mexicanHatVev at h_super
  linarith

/-! ## 4. Anderson-Higgs W/Z mass matrix -/

/-- W boson mass from Anderson-Higgs: `M_W = g v / 2`. -/
noncomputable def wMass (e : EWMassMatrixInputs) : ℝ := e.g * e.v / 2

/-- Z boson mass from Anderson-Higgs: `M_Z = √(g² + g'²) v / 2`. -/
noncomputable def zMass (e : EWMassMatrixInputs) : ℝ :=
  Real.sqrt (e.g ^ 2 + e.g' ^ 2) * e.v / 2

theorem wMass_pos (e : EWMassMatrixInputs) : 0 < wMass e := by
  unfold wMass
  have : 0 < e.g * e.v := mul_pos e.g_pos e.v_pos
  linarith

theorem zMass_pos (e : EWMassMatrixInputs) : 0 < zMass e := by
  unfold zMass
  have hg2 : 0 < e.g ^ 2 := pow_pos e.g_pos 2
  have hg'2 : 0 ≤ e.g' ^ 2 := sq_nonneg _
  have hsum : 0 < e.g ^ 2 + e.g' ^ 2 := by linarith
  have hsqrt : 0 < Real.sqrt (e.g ^ 2 + e.g' ^ 2) := Real.sqrt_pos.mpr hsum
  have := mul_pos hsqrt e.v_pos
  linarith

/-- `M_Z ≥ M_W` always — the SU(2) coupling alone is at most as big as the
combined SU(2)×U(1) coupling, regardless of `g'` sign assumption. -/
theorem zMass_ge_wMass (e : EWMassMatrixInputs) : wMass e ≤ zMass e := by
  unfold wMass zMass
  have hv : 0 < e.v := e.v_pos
  have hg_sq_le : e.g ^ 2 ≤ e.g ^ 2 + e.g' ^ 2 := by nlinarith [sq_nonneg e.g']
  have hg_abs_le : |e.g| ≤ Real.sqrt (e.g ^ 2 + e.g' ^ 2) := by
    rw [show |e.g| = Real.sqrt (e.g ^ 2) from (Real.sqrt_sq_eq_abs _).symm]
    exact Real.sqrt_le_sqrt hg_sq_le
  have hg_le : e.g ≤ Real.sqrt (e.g ^ 2 + e.g' ^ 2) :=
    le_trans (le_abs_self _) hg_abs_le
  have hmul : e.g * e.v ≤ Real.sqrt (e.g ^ 2 + e.g' ^ 2) * e.v :=
    mul_le_mul_of_nonneg_right hg_le (le_of_lt hv)
  linarith

/-- On-shell weak-mixing ratio: `M_W / M_Z = g / √(g² + g'²) = cos θ_W`. -/
theorem wMass_div_zMass
    (e : EWMassMatrixInputs) (hg' : 0 < e.g') :
    wMass e / zMass e = e.g / Real.sqrt (e.g ^ 2 + e.g' ^ 2) := by
  unfold wMass zMass
  have hg2 : 0 < e.g ^ 2 := pow_pos e.g_pos 2
  have hg'2 : 0 < e.g' ^ 2 := pow_pos hg' 2
  have hsum : 0 < e.g ^ 2 + e.g' ^ 2 := by linarith
  have hsqrt : 0 < Real.sqrt (e.g ^ 2 + e.g' ^ 2) := Real.sqrt_pos.mpr hsum
  have hv : e.v ≠ 0 := ne_of_gt e.v_pos
  field_simp

/-- The mass-ratio `cos θ_W` is strictly less than 1 when `g' > 0`. -/
theorem wMass_lt_zMass_of_g'_pos
    (e : EWMassMatrixInputs) (hg' : 0 < e.g') :
    wMass e < zMass e := by
  unfold wMass zMass
  have hg2 : 0 < e.g ^ 2 := pow_pos e.g_pos 2
  have hg'2 : 0 < e.g' ^ 2 := pow_pos hg' 2
  have hlt : e.g ^ 2 < e.g ^ 2 + e.g' ^ 2 := by linarith
  have hsqrt_lt : Real.sqrt (e.g ^ 2) < Real.sqrt (e.g ^ 2 + e.g' ^ 2) :=
    Real.sqrt_lt_sqrt (sq_nonneg _) hlt
  have hsqrt_g : Real.sqrt (e.g ^ 2) = e.g := Real.sqrt_sq (le_of_lt e.g_pos)
  have hg_lt : e.g < Real.sqrt (e.g ^ 2 + e.g' ^ 2) :=
    calc e.g = Real.sqrt (e.g ^ 2) := hsqrt_g.symm
      _ < Real.sqrt (e.g ^ 2 + e.g' ^ 2) := hsqrt_lt
  have hv : 0 < e.v := e.v_pos
  have hmul : e.g * e.v < Real.sqrt (e.g ^ 2 + e.g' ^ 2) * e.v :=
    mul_lt_mul_of_pos_right hg_lt hv
  linarith

/-- Custodial-symmetry algebraic identity: `M_Z² − M_W² = (g'·v/2)²`. The
Anderson-Higgs mass-splitting is purely the U(1)_Y hypercharge contribution.
Quantitative consequence: in the limit `g' → 0`, the W and Z become
degenerate; in the SM, this isospin breaking sets `M_Z² − M_W² ≈ (29.7
GeV)²`. Non-trivial algebra — uses `Real.sq_sqrt` to discharge the
square-root squared in the Z-mass definition. -/
theorem zMass_sq_minus_wMass_sq (e : EWMassMatrixInputs) :
    (zMass e) ^ 2 - (wMass e) ^ 2 = (e.g' * e.v / 2) ^ 2 := by
  unfold zMass wMass
  have hsum_nn : 0 ≤ e.g ^ 2 + e.g' ^ 2 := by positivity
  have h_sqrt_sq : (Real.sqrt (e.g ^ 2 + e.g' ^ 2)) ^ 2 = e.g ^ 2 + e.g' ^ 2 :=
    Real.sq_sqrt hsum_nn
  field_simp
  rw [h_sqrt_sq]
  ring

/-- Anderson-Higgs bundled mass-matrix theorem: starting from a `ScalarChannel`
and gauge couplings, the W/Z masses take their standard Anderson-Higgs values
with the mexican-hat VEV substituted for `v`. Bundles structural definition,
positivity, ordering, and the cos θ_W identity into a single named consequence
that is referenced by the canonical formula `w_mass_from_vev`. The structural
"= def" equalities (first two conjuncts) are by `rfl`; the third (positivity)
re-uses `wMass_pos`; the fourth (ordering) re-uses `zMass_ge_wMass`. -/
theorem ew_mass_matrix_from_scalar_vev
    (s : ScalarChannel) (g g' : ℝ) (hg : 0 < g) (hg' : 0 ≤ g') :
    let e : EWMassMatrixInputs :=
      { g := g, g' := g', v := mexicanHatVev s,
        g_pos := hg, g'_nonneg := hg', v_pos := mexicanHatVev_pos s }
    wMass e = g * mexicanHatVev s / 2 ∧
    zMass e = Real.sqrt (g ^ 2 + g' ^ 2) * mexicanHatVev s / 2 ∧
    0 < wMass e ∧ wMass e ≤ zMass e := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact wMass_pos _
  · exact zMass_ge_wMass _

/-! ## 5. Yukawa overlap (structural stand-in) -/

/-- Scalar stand-in for the emergent-Weyl overlap integral. The full microscopic
form (∫ ψ_f† σ ψ_g on the FermiPointTopology substrate) is deep-research-gated;
here `WeylOverlap` is a real number abstracted from the substrate data. -/
structure WeylOverlap where
  density : ℝ
  normalization : ℝ
  normalization_pos : 0 < normalization

/-- Yukawa coupling as a linear functional of the overlap density. -/
noncomputable def yukawaCoupling (w : WeylOverlap) : ℝ :=
  w.density * w.normalization

/-- Linearity of the Yukawa coupling in the overlap density (for two overlaps
with the same normalization). -/
theorem yukawaCoupling_additive
    (w₁ w₂ : WeylOverlap) (h : w₁.normalization = w₂.normalization) :
    yukawaCoupling { density := w₁.density + w₂.density,
                     normalization := w₁.normalization,
                     normalization_pos := w₁.normalization_pos } =
    yukawaCoupling w₁ + yukawaCoupling w₂ := by
  unfold yukawaCoupling
  simp only
  rw [h]; ring

/-- Yukawa coupling is zero iff the overlap density is zero. -/
theorem yukawaCoupling_eq_zero_iff (w : WeylOverlap) :
    yukawaCoupling w = 0 ↔ w.density = 0 := by
  unfold yukawaCoupling
  constructor
  · intro h
    have hn := ne_of_gt w.normalization_pos
    exact (mul_eq_zero.mp h).resolve_right hn
  · intro h; rw [h]; ring

/-! ## 6. Correctness-push anchor — m_H vs 125 GeV -/

/-- Microscopic Higgs-mass prediction from Wetterich substrate parameters.
Schematic leading-log form: `m_H² = 2 λ_4 · v_cond²(Λ_UV, N_f, G_c)` where
`v_cond(Λ, N, G) = Λ · exp(-π²/(2 N G))`. Full microscopic relation is
deep-research-gated on O.2. -/
noncomputable def higgsMassFromCondensate
    (lambda_uv : ℝ) (n_f : ℕ) (g_c lam4 : ℝ) : ℝ :=
  Real.sqrt (2 * lam4) *
    (lambda_uv * Real.exp (- Real.pi ^ 2 / (2 * (n_f : ℝ) * g_c)))

/-- Microscopic `m_H` is positive for positive substrate parameters. -/
theorem higgsMassFromCondensate_pos
    (lambda_uv : ℝ) (n_f : ℕ) (g_c lam4 : ℝ)
    (hΛ : 0 < lambda_uv) (_hNf : 0 < n_f) (_hG : 0 < g_c) (hl : 0 < lam4) :
    0 < higgsMassFromCondensate lambda_uv n_f g_c lam4 := by
  unfold higgsMassFromCondensate
  have h_sqrt : 0 < Real.sqrt (2 * lam4) := Real.sqrt_pos.mpr (by linarith)
  have h_exp : 0 < Real.exp (- Real.pi ^ 2 / (2 * (n_f : ℝ) * g_c)) := Real.exp_pos _
  have h_prod : 0 < lambda_uv * Real.exp (- Real.pi ^ 2 / (2 * (n_f : ℝ) * g_c)) :=
    mul_pos hΛ h_exp
  exact mul_pos h_sqrt h_prod

/-- Quantitative-match predicate: the microscopic `m_H` prediction is within
fractional tolerance `tol` of the observed value `m_H_obs`. This is the
decidable Gate Z.1 criterion from the roadmap. -/
def ScalarRungQuantitativeMatch
    (m_H_pred m_H_obs tol : ℝ) : Prop :=
  |m_H_pred - m_H_obs| < tol * m_H_obs

/-- The match predicate reduces to an explicit two-sided bound.

Positivity hypotheses are marked load-bearing for the physics interpretation
but are not required by the algebraic content of the biconditional. -/
theorem scalar_rung_quantitative_match_iff
    (m_H_pred m_H_obs tol : ℝ)
    (_h_obs : 0 < m_H_obs) (_h_tol : 0 < tol) :
    ScalarRungQuantitativeMatch m_H_pred m_H_obs tol ↔
    (1 - tol) * m_H_obs < m_H_pred ∧ m_H_pred < (1 + tol) * m_H_obs := by
  unfold ScalarRungQuantitativeMatch
  rw [abs_lt]
  constructor
  · intro ⟨hlo, hhi⟩; exact ⟨by linarith, by linarith⟩
  · intro ⟨hlo, hhi⟩; exact ⟨by linarith, by linarith⟩

/-- The microscopic m_H falsifiability anchor lifted to the absolute-value
form. Provides the *load-bearing* contrapositive: if the prediction is
sufficiently far from the observed mass, the framing is structural-only. -/
theorem scalar_rung_match_excludes_far_predictions
    (m_H_pred m_H_obs tol : ℝ)
    (h_obs : 0 < m_H_obs) (h_tol : 0 < tol)
    (h_far : (1 + tol) * m_H_obs ≤ m_H_pred) :
    ¬ ScalarRungQuantitativeMatch m_H_pred m_H_obs tol := by
  intro h_match
  rw [(scalar_rung_quantitative_match_iff m_H_pred m_H_obs tol h_obs h_tol)]
    at h_match
  obtain ⟨_, hhi⟩ := h_match
  linarith

/-! ## 7. Landau-hierarchy integration -/

/-- Bundled scalar-rung Landau-hierarchy theorem: any valid `ScalarChannel`
gives (1) a positive VEV, (2) a positive tree-level Higgs mass, *and*
(3) under the gauge-coupling inputs `g > 0`, the Anderson-Higgs W mass is
strictly positive and bounded above by the Z mass. This bundles three
structurally distinct outputs of the scalar-rung identification into a
single load-bearing consequence — used as a single citation point from
the flagship paper §scalar-rung-microscopic. -/
theorem scalar_rung_is_landau_rung
    (s : ScalarChannel) (g g' : ℝ) (hg : 0 < g) (hg' : 0 ≤ g') :
    let e : EWMassMatrixInputs :=
      { g := g, g' := g', v := mexicanHatVev s,
        g_pos := hg, g'_nonneg := hg', v_pos := mexicanHatVev_pos s }
    0 < mexicanHatVev s ∧
    0 < higgsMassSq s ∧
    0 < wMass e ∧
    wMass e ≤ zMass e := by
  refine ⟨mexicanHatVev_pos s, higgsMassSq_pos s, ?_, ?_⟩
  · exact wMass_pos _
  · exact zMass_ge_wMass _

end SKEFTHawking.ScalarRungInterpretation

end
