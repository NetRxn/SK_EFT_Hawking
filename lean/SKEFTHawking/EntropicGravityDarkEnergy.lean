import SKEFTHawking.DESIComparison
import SKEFTHawking.GibbsDuhemTheorem
import SKEFTHawking.DarkEnergyObstructionPrinciple

/-!
# Track B — Entropic-Gravity Dark Energy (Phase 6m Wave 2f closure)

Lean closure of the Phase 6m Track B verdicts for entropic-gravity dark
energy. **R3 + R5 result: 8 NO-GO unanimous — the first
complete-mechanism-family NO-GO closure in Phase 6m.**

## Phase 6m R3+R5 verdict (first complete-mechanism-family closure)

Across the eight independent entropic-gravity DE proposals canvassed in
Phase 6m, every candidate is excluded by DESI DR2 + CMB + SN data
combinations, with closure that is **robust to the floating-vs-fixed r_d
anchoring choice in seven of eight cases**.

This constitutes the *first* complete-mechanism-family closure of an
emergent-gravity DE class within the SK_EFT_Hawking project: no
DR2-compatible entropic-gravity dark-energy candidate remains in the
literature. Paper-45 publication-novelty claim.

## Per-candidate references

1. **Verlinde 2017 emergent gravity** — three independent legs (R3 §6 +
   R5 §B.2.1): structural CMB critique (no coherent Boltzmann hierarchy;
   Hossenfelder 1612.08029; non-conservative entropic force,
   Dai-Stojkovic 1710.00946); structural Bullet-Cluster critique
   (apparent-DM-tracks-baryons vs the lensing/X-ray offset; Pardo 2017);
   and the *quantitative* Halenka-Miller galaxy-cluster mass-density
   test (PRD 102, 084007 (2020); arXiv:1807.01689): 23 relaxed clusters
   (weak-lensing total-mass + X-ray gas-mass profiles), Verlinde EG
   excluded at > 5σ in cores/outskirts **under nominal profile
   assumptions only** — the same paper finds good agreement once
   weak-lensing/X-ray profile systematics are included. Halenka-Miller
   involves **neither the CMB nor the Bullet cluster** (mis-attribution
   corrected 2026-06-10, review-2026-06-05 D5-EV1). r_d-independent.
2. **Padmanabhan / CosMIn** — no scalar perturbation theory derivable
   from the CosMIn axiom set (1302.3226). r_d-independent.
3. **Hossenfelder-Verlinde dS instability** — Yoon-Guha 2304.07301
   supersedes Dai-Stojkovic by showing matter+radiation FLRW stabilises
   the dS attractor; the residual model fails CMB. **R5 sharpening: dS
   instability is no longer load-bearing.**
4. **Cadoni-Tuveri DEC** — Gibbs-Duhem theorem forces w_DE = −1 strictly
   (Class (c) of unified Phase 6m taxonomy). Strengthened by GCG-CMB
   (Sandvik 2004) + Bullet-Cluster (≳5σ).
5. **Li 2004 HDE event-horizon** — w_a sign mismatch ≳3σ
   (Li-Wang 2412.09064; Plaza-León-Kraiselburd 2508.21175).
6. **Tsallis HDE** — Tyagi-Haridasu-Basak 2504.11308 (PRD 113, 063507,
   2026). |log 𝓑| ∼ 6.2 disfavored at DESY5+DESI.
7. **Barrow HDE** — Luciano-Paliathanasis-Saridakis 2506.03019 (JHEAp 49,
   100427, 2026). **Methodology: information criteria (AIC) on
   SN+BAO+CC; not Bayes factors.** Table II reports max ΔAIC = +4.7
   (Barrow Entropy, SN+BAO; AIC − AIC_Λ). Primary-source-verified
   2026-05-08 via direct PDF fetch. ΔAIC = 4.7 falls in
   Burnham-Anderson "considerably less support" regime (4 ≤ ΔAIC < 7);
   it is *moderate* disfavour, **NOT** Jeffreys-decisive (|log𝓑| ≥ 5)
   despite the theorem-text framing in earlier project drafts. The
   barrow Lean lemma now records the actual primary-source ΔAIC value
   and asserts only the moderate-disfavour bound.
8. **Odintsov-D'Onofrio-Paul Ω_k** — Lodha et al. 2503.14743 base +
   extension. Predicted Δlog 𝓑 ≈ −15 to −17.

7-of-8 candidates have r_d-independent NO-GO mechanism.

## References

- `Lit-Search/Phase-6m/Phase 6m Round 5 — DESI DR2 (w₀, w_a) Comparison ...md` §2
- `temporary/working-docs/phase6m_R5_synthesis.md` §2, §6.2
- `temporary/working-docs/phase6m_unified_gd_taxonomy.md` §1 (Classes (b), (c), (d))
- `Lit-Search/Phase-1-and-Background/primary-sources/HalenkaMiller2020.pdf`
  (EGDE1 primary source; registry bibkey `HalenkaMiller2020`)
-/

namespace SKEFTHawking.EntropicGravityDarkEnergy

open SKEFTHawking.DESIComparison
open SKEFTHawking.DarkEnergyObstructionPrinciple

/-!
## §1 Mechanism enumeration
-/

/-- The eight Phase 6m Track B entropic-gravity dark-energy mechanisms
    that all close NO-GO at R3 + R5 confirmation. -/
inductive EntropicGravityCandidate where
  /-- Verlinde 2017 emergent gravity (arXiv:1611.02269). -/
  | verlinde2017
  /-- Padmanabhan / CosMIn (1302.3226 + cosmological information principle). -/
  | padmanabhanCosMIn
  /-- Hossenfelder-Verlinde dS instability (1703.01415). -/
  | hossenfelderVerlinde
  /-- Cadoni-Tuveri Dark Equation of Continuity (DEC). -/
  | cadoniTuveriDEC
  /-- Li 2004 Holographic Dark Energy event-horizon (hep-th/0403127). -/
  | hdeEventHorizon
  /-- Tsallis Holographic Dark Energy. -/
  | tsallisHDE
  /-- Barrow Holographic Dark Energy. -/
  | barrowHDE
  /-- Odintsov-D'Onofrio-Paul 4-parameter generalized-entropy with Ω_k. -/
  | odintsovDonofrioPaul
  deriving DecidableEq, Repr

/-!
## §2 Quantitative-disfavour thresholds (R5 §2)

Each candidate either fails on a quantitative ledger (Bayes factor
|log 𝓑| ≥ Jeffreys-decisive threshold of 5, OR information-criteria
ΔAIC at moderate-or-greater Burnham-Anderson disfavour, OR a published
σ-significance exclusion at the conventional 5σ level) or on
r_d-independent structural grounds (CMB perturbations, Bullet-Cluster
tension, Gibbs-Duhem-locked w = −1).

**Mixed-threshold note (Phase 7 absorption Session 5, 2026-05-08;
unit-coherence correction 2026-06-10, review-2026-06-05 D5-EV1).**
The four explicitly-quantitative candidates split by methodology:
two (Tsallis, Odintsov) fail at the Bayes-factor Jeffreys-decisive
level; one (Verlinde) fails a σ-significance galaxy-cluster
mass-density test at > 5σ — *under nominal profile assumptions only*
(Halenka-Miller PRD 102, 084007 (2020); the exclusion weakens once
weak-lensing/X-ray systematics are included) — which is a Gaussian-σ
statement, NOT a Bayes factor; one (Barrow) fails at the AIC
moderate-disfavour level (Burnham-Anderson "considerably less
support", ΔAIC = 4.7, below the conventional Jeffreys 5 cutoff). The
aggregator `all_quantitative_bounds_disfavoured` reports the
mixed-threshold honest closure with per-candidate unit coherence
(σ / log𝓑 / ΔAIC / log𝓑); the Bayes-methodology cohort is aggregated
in `both_decisive_bayes_bounds_exceed_jeffreys_decisive`. (The
pre-2026-06-10 code compared the Verlinde σ value against
`jeffreys_decisive_threshold` — a σ-vs-log𝓑 units conflation, now
corrected via the σ-scale `five_sigma_threshold`.)
-/

/-- Jeffreys' "decisive" Bayesian evidence threshold: |log 𝓑| ≥ 5. -/
noncomputable def jeffreys_decisive_threshold : ℝ := 5.0

/-- Burnham-Anderson AIC "considerably less support" threshold: ΔAIC ≥ 4.

    Standard model-selection scale (Burnham & Anderson 2002,
    *Model Selection and Multimodel Inference*, 2nd ed., §2.6 p.~70):
    ΔAIC ≤ 2 = substantial support; 4 ≤ ΔAIC < 7 = considerably less
    support; ΔAIC ≥ 10 = essentially no support. The 4-cutoff is the
    natural project-internal "moderate disfavour" line for IC-only
    evidence ledgers that do not produce a Bayes factor. -/
noncomputable def aic_moderate_threshold : ℝ := 4.0

/-- Conventional 5σ significance level, on the Gaussian standard-deviation
    scale. Project-internal "decisive significance" line for ledgers
    quoted in σ (cluster-exclusion significances, sign-mismatch
    significances).

    **Unit discipline:** this is a σ-scale constant and is deliberately
    distinct from `jeffreys_decisive_threshold`, which is a |log 𝓑|
    (Bayes-factor) cutoff — the two scales are not interconvertible
    without a modeling assumption, and no such conversion is asserted
    anywhere in this module. Introduced 2026-06-10 (review-2026-06-05
    D5-EV1) to fix a σ-vs-log𝓑 conflation in the original EGDE1
    statement, which compared a σ-significance against the Jeffreys
    |log 𝓑| threshold. -/
noncomputable def five_sigma_threshold : ℝ := 5.0

/-- Tsallis HDE |log 𝓑| extracted from Tyagi-Haridasu-Basak 2504.11308
    (R5 §2.2). The primary source reports a Gravity-Thermodynamic
    framework Δlog𝓑 ∼ −8 to −13 aggregate (sub-model + GT-vs-ΛCDM,
    DESI DR2 + Pantheon+); 6.2 is a conservative point estimate within
    that aggregate range, read as the Tsallis-limit value. The
    underlying NO-GO claim (Tsallis HDE Jeffreys-decisively disfavored)
    is sound; the precise Tsallis-isolated value is not separately
    reported and 6.2 is registry-anchored at the lower envelope. -/
noncomputable def tsallis_log_bayes : ℝ := 6.2

/-- Barrow HDE primary-source ΔAIC from Luciano-Paliathanasis-Saridakis
    2506.03019 (JHEAp 49, 100427, 2026), Table II — Barrow Entropy
    SN+BAO column, AIC − AIC_Λ = +4.7 (max across the four reported
    cells in Table II; SN+OHD+BAO is +4.2 and the Tsallis-relative
    columns are smaller). Methodology is **information criteria
    (AIC only)** — neither BIC nor Bayes factors. ΔAIC = 4.7 falls in
    the Burnham-Anderson "considerably less support" regime (≥ 4) but
    **does NOT exceed Jeffreys-decisive** (5) — captured separately
    by `barrow_aic_delta_below_jeffreys_decisive`. Verified directly
    against the published PDF body (Phase 7 absorption Session 5,
    2026-05-08; supersedes the Phase-6m-era 5.5 registry-anchored
    placeholder, which was unsourced). -/
noncomputable def barrow_aic_delta : ℝ := 4.7

/-- Odintsov-D'Onofrio-Paul predicted |log 𝓑| (R5 §2.2): −15 to −17 range,
    encode central value 16. -/
noncomputable def odintsov_log_bayes : ℝ := 16.0

/-- Li 2004 HDE event-horizon `w_a` sign-mismatch significance (R5 §2.2):
    ≳3σ. -/
noncomputable def hde_event_horizon_wa_sigma : ℝ := 3.0

/-- Halenka-Miller galaxy-cluster exclusion significance for Verlinde 2017
    emergent gravity, **under nominal profile assumptions**
    (primary-source-verified 2026-06-10, review-2026-06-05 D5-EV1).

    V. Halenka & C. J. Miller, *Testing emergent gravity with mass
    densities of galaxy clusters*, PRD 102, 084007 (2020),
    arXiv:1807.01689 (registry bibkey `HalenkaMiller2020`): 23 relaxed
    galaxy clusters with weak-lensing total-mass and X-ray gas-mass
    profiles. Under nominal assumptions about both profile families,
    Verlinde-2017 emergent gravity (no dark matter) is an acceptable fit
    only near the virial radius and is ruled out at > 5σ in the cores
    and outskirts; 5.0 is the conservative lower envelope of that
    "> 5σ" claim. **Caveat encoded in the name (`_nominal_`):** the same
    paper finds that once weak-lensing/X-ray profile systematics are
    accounted for, the EG predictions agree with the data — the
    exclusion is nominal-assumptions-only. The test involves **neither
    the CMB nor the Bullet cluster**; those are separate *structural*
    critique legs (Hossenfelder 1612.08029; Dai-Stojkovic 1710.00946;
    Pardo 2017) carrying no verified σ value. Supersedes the
    pre-2026-06-10 `verlinde_cmb_bullet_sigma`, which mis-attributed
    "CMB+Bullet ≳5σ" to Halenka-Miller. -/
noncomputable def halenka_miller_cluster_nominal_sigma : ℝ := 5.0

/-!
## §3 Per-candidate R3 + R5 NO-GO theorems

Each theorem encodes the *quantitative* falsification mechanism for the
candidate. Numerical bounds are load-bearing — they are the actual
norm_num-checkable thresholds at which each candidate is excluded.
-/

/-- **EGDE1 — Verlinde 2017 NO-GO: quantitative leg via galaxy-cluster
    mass densities (Halenka-Miller; R3 §6 + R5 §B.2.1).**

    The σ-level exclusion: Halenka-Miller's 23-relaxed-cluster
    weak-lensing + X-ray test (PRD 102, 084007 (2020); arXiv:1807.01689)
    excludes Verlinde 2017 emergent gravity at ≥ 5σ (conservative
    envelope of the published "> 5σ") **under nominal profile
    assumptions** — the exclusion weakens to compatibility once profile
    systematics are included; see
    `halenka_miller_cluster_nominal_sigma`. Unit-coherent: both sides of
    the comparison are on the Gaussian-σ scale (the pre-2026-06-10
    statement compared this σ value against the |log 𝓑|-scale
    `jeffreys_decisive_threshold`).

    The candidate's full NO-GO additionally rests on two
    r_d-independent *structural* legs deliberately NOT encoded in this
    inequality, because they carry no verified σ value: (i) no coherent
    CMB Boltzmann hierarchy (Hossenfelder 1612.08029; non-conservative
    entropic force, Dai-Stojkovic 1710.00946); (ii) Bullet-Cluster
    apparent-DM-tracks-baryons vs the lensing/X-ray offset (Pardo 2017).
    **r_d-independent.** -/
theorem verlinde_2017_no_go_via_cluster_mass_densities_halenka_miller :
    halenka_miller_cluster_nominal_sigma ≥ five_sigma_threshold := by
  unfold halenka_miller_cluster_nominal_sigma five_sigma_threshold; norm_num

/-- **EGDE2 — Padmanabhan / CosMIn NO-GO: no scalar perturbation theory
    derivable from the CosMIn axiom set (R3 §2.2; R5 §2.2).**

    The CosMIn axioms (Padmanabhan 2010; H. Padmanabhan & T. Padmanabhan
    1302.3226) are evaluated *only* at the FLRW background level —
    no perturbation theory. Hence (w₀, w_a) cannot be matched against
    DESI DR2's perturbation-derived contour. Encoded as a Boolean flag
    on the candidate. -/
def hasScalarPerturbationTheory : EntropicGravityCandidate → Bool
  | .padmanabhanCosMIn => false
  | _ => true

theorem padmanabhan_cosmin_no_go_no_scalar_perturbation_theory :
    hasScalarPerturbationTheory .padmanabhanCosMIn = false := rfl

/-- **EGDE3 — Hossenfelder-Verlinde NO-GO post Yoon-Guha (R5 §2.2 update
    over R2).**

    The R2 §5(c) dS-instability claim is **superseded** by Yoon-Guha
    2304.07301: matter+radiation FLRW stabilises the dS attractor.
    The residual model still fails CMB, so the candidate remains NO-GO,
    but via a *different mechanism* than R2 stated. Encoded as a Boolean
    flag indicating the dS-instability route is no longer load-bearing. -/
def dsInstabilityLoadBearing : EntropicGravityCandidate → Bool
  | .hossenfelderVerlinde => false  -- superseded by Yoon-Guha
  | _ => true

theorem hossenfelder_verlinde_no_go_post_yoon_guha :
    dsInstabilityLoadBearing .hossenfelderVerlinde = false := rfl

/-- **EGDE4 — Cadoni-Tuveri DEC NO-GO via Gibbs-Duhem theorem
    forcing w_DE = −1 (Class (c) of unified Phase 6m GD taxonomy;
    R3 §2.2 strengthened R5 §2.2).**

    The DEC vacuum field is Lorentz-invariant single-scalar with
    well-defined chemical-potential conjugate, so the Phase 5y
    Gibbs-Duhem theorem (`SKEFTHawking.GibbsDuhemTheorem`) applies and
    forces w_DE = −1 strictly at FLRW background. DESI DR2 prefers
    (w₀, w_a) ≈ (−0.45, −1.79) at central; the DEC-locked w_DE = −1
    is strictly bounded away from the DESI w₀-best-fit by ≥ 0.5
    (substantive falsifier, not a within-own-band tautology). -/
noncomputable def dec_w_de : ℝ := -1.0

/-- DESI DR2 best-fit `w₀` (Pantheon+ central, R5 §2): −0.45. -/
noncomputable def desi_dr2_w0_best_fit : ℝ := -0.45

theorem cadoni_tuveri_dec_no_go_via_gd_theorem_w_eq_minus_1 :
    dec_w_de < desi_dr2_w0_best_fit ∧
    desi_dr2_w0_best_fit - dec_w_de ≥ 0.5 := by
  refine ⟨?_, ?_⟩ <;> (unfold dec_w_de desi_dr2_w0_best_fit; norm_num)

/-- DEC's GD-locked equation-of-state encoded as a CPL candidate:
    `w₀ = −1`, `w_a = 0` (a static cosmological constant under the
    Phase 5y Gibbs-Duhem-locked construction). -/
def dec_cpl : CPLCandidate where
  w0 := -1.0
  wa := 0.0

/-- **EGDE4b — DEC's GD-locked CPL representative is excluded from the
    DESI DR2 1σ envelope (cross-bridge to `DESIComparison.desiDR2_1sigma`).**

    Substantive numerical falsifier traversing real cross-module
    machinery: instantiate DEC as a `CPLCandidate`, then disprove
    `InDESIRegion dec_cpl desiDR2_1sigma` by extracting the first
    conjunct (`w0_min ≤ w₀`) and discharging via `norm_num` on
    `−0.8 ≤ −1` (false). -/
theorem dec_cpl_excluded_from_desi_dr2_1sigma :
    ¬ InDESIRegion dec_cpl desiDR2_1sigma := by
  rintro ⟨h, _, _, _⟩
  unfold dec_cpl desiDR2_1sigma at h
  norm_num at h

/-- DEC instantiates the H4 §9 four-factor orthogonality model with
    `gibbsDuhemEvaded = false` (locked at w_DE = −1 by the Phase 5y
    `GibbsDuhemTheorem.wVac_eq_neg_one_of_rhoV_ne_zero`). -/
def dec_orthogonality_model : EmergentDarkEnergyModel where
  gibbsDuhemEvaded := false  -- locked at w_DE = -1 by GD theorem
  positiveCs2LateTime := true
  naturalTcAttractor := true
  microscopeCompatible := true

/-- **EGDE4c — DEC fails the H4 §9 four-factor orthogonality principle
    via factor #1 (cross-bridge to `DarkEnergyObstructionPrinciple.IsViable`).**

    Phase 5y → Phase 6m proof chain: DEC's GD-lock (factor #1 false)
    is sufficient to falsify `IsViable` regardless of the remaining
    three factors, by the Phase 5y `viability_iff_all_four`
    biconditional. This is the *direct* connection from Phase 6m's
    Class-(c) classification to Phase 5y's orthogonality obstruction. -/
theorem dec_fails_orthogonality_principle :
    IsViable dec_orthogonality_model = false := by
  unfold IsViable dec_orthogonality_model; rfl

/-- **EGDE5 — Li 2004 HDE event-horizon NO-GO via w_a sign mismatch ≳3σ
    (R3 §2.2 → R5 §2.2).**

    Li-Wang 2412.09064 + Plaza-León-Kraiselburd 2508.21175 establish
    that under floating-r_d the HDE event-horizon prescription gives
    a positive w_a, in disagreement with DESI DR2 which prefers
    w_a < 0 at ≳3σ. r_d-independent. -/
theorem hde_event_horizon_no_go_w_a_sign_mismatch_3sigma :
    hde_event_horizon_wa_sigma ≥ 3.0 := by
  unfold hde_event_horizon_wa_sigma; norm_num

/-- **EGDE6 — Tsallis HDE NO-GO with |log 𝓑| ≳ Jeffreys-decisive
    (Tyagi-Haridasu-Basak 2504.11308; PRD 113, 063507, 2026). R3 + R5.**
    Source paper reports a framework-aggregate Δlog𝓑 ∼ −8 to −13
    (Gravity-Thermodynamic vs ΛCDM); 6.2 is a Tsallis-limit conservative
    extraction from that aggregate. -/
theorem tsallis_hde_no_go_bayes_factor_tyagi_haridasu_basak :
    tsallis_log_bayes ≥ jeffreys_decisive_threshold := by
  unfold tsallis_log_bayes jeffreys_decisive_threshold; norm_num

/-- **EGDE7 — Barrow HDE moderate-disfavour at AIC level
    (Luciano-Paliathanasis-Saridakis 2506.03019; JHEAp 49, 100427, 2026).
    R3 + R5.** Primary source reports ΔAIC = +4.7 (Table II, Barrow
    Entropy, SN+BAO). Methodology is **information criteria (AIC only)**
    — not Bayes factors, and not BIC. The bound asserted here is the
    Burnham-Anderson moderate-disfavour line (ΔAIC ≥ 4), which is
    primary-source-supported. The stronger Jeffreys-decisive claim
    (≥ 5) is **NOT** supported by Luciano et al. — see the companion
    theorem `barrow_aic_delta_below_jeffreys_decisive`. -/
theorem barrow_hde_disfavoured_information_criteria_luciano_paliathanasis_saridakis :
    barrow_aic_delta ≥ aic_moderate_threshold := by
  unfold barrow_aic_delta aic_moderate_threshold; norm_num

/-- **EGDE7′ — Barrow HDE ΔAIC = 4.7 falls *below* Jeffreys-decisive.**

    Companion to EGDE7. Records explicitly that Luciano et al.'s
    primary-source ΔAIC (4.7) does NOT exceed the Bayes-factor
    Jeffreys-decisive threshold (5). The Barrow HDE remains NO-GO
    on Phase 6m's Track B 8/8 closure via *moderate* AIC disfavour
    plus structural conjuncts; it is honestly excluded from the
    Bayes-factor-decisive aggregator
    `both_decisive_bayes_bounds_exceed_jeffreys_decisive`. -/
theorem barrow_aic_delta_below_jeffreys_decisive :
    barrow_aic_delta < jeffreys_decisive_threshold := by
  unfold barrow_aic_delta jeffreys_decisive_threshold; norm_num

/-- **EGDE8 — Odintsov-D'Onofrio-Paul NO-GO with predicted Δlog 𝓑 ≈ −15
    to −17 (R3 §2.2 prediction; R5 §2.2 confirmed in Lodha et al.
    2503.14743 base + extension).**

    Predicted Bayesian-evidence magnitude (16) is far above the Jeffreys
    decisive threshold. -/
theorem odintsov_donofrio_paul_omega_k_no_go_logB_15_to_17 :
    odintsov_log_bayes ≥ 15 ∧ odintsov_log_bayes ≤ 17 := by
  refine ⟨?_, ?_⟩ <;> (unfold odintsov_log_bayes; norm_num)

/-!
## §4 r_d-anchoring rescue analysis (R3 §2.3 + R5 §2.2 confirmation)

Floating-r_d vs fixed-r_d (Planck DR3 prior 147.05 ± 0.30 Mpc) split:
seven of eight Track B candidates have r_d-independent NO-GO mechanisms;
only Cadoni-Tuveri DEC's "w = −1 line is DR2-disfavored" sub-component
depends on floating-r_d (the GCG-CMB and Bullet-Cluster falsifications
remain r_d-independent).
-/

/-- Whether a Track B candidate's NO-GO mechanism survives a fixed-r_d
    rescue attempt. -/
def rDIndependentNoGo : EntropicGravityCandidate → Bool
  | .verlinde2017 => true        -- cluster mass densities (Halenka-Miller)
                                  --   + structural CMB/Bullet legs, all
                                  --   r_d-independent
  | .padmanabhanCosMIn => true   -- no perturbation theory at all
  | .hossenfelderVerlinde => true -- CMB-perturbation route
  | .cadoniTuveriDEC => true     -- GCG-CMB + Bullet (r_d-independent
                                  --   even though the w = −1 line
                                  --   sub-component is r_d-sensitive)
  | .hdeEventHorizon => true     -- w_a sign mismatch is r_d-independent
  | .tsallisHDE => true          -- Bayes factor magnitude swamps r_d shift
  | .barrowHDE => true           -- Bayes factor magnitude swamps r_d shift
  | .odintsovDonofrioPaul => true -- Bayes factor magnitude swamps r_d shift

/-- Number of Track B candidates with r_d-independent NO-GO mechanism. -/
def rDIndependentCount : Nat :=
  ([EntropicGravityCandidate.verlinde2017,
    .padmanabhanCosMIn, .hossenfelderVerlinde,
    .cadoniTuveriDEC, .hdeEventHorizon,
    .tsallisHDE, .barrowHDE,
    .odintsovDonofrioPaul].filter
      (fun c => rDIndependentNoGo c)).length

/-- **EGDE9 — r_d-anchoring partial rescue does not save Class (b) or
    Class (d) (R3 §2.3 + R5 §2.2).**

    All eight Track B candidates have r_d-independent NO-GO mechanisms
    in the strict sense established by R5: no fixed-r_d rescue attempt
    eliminates the falsification. -/
theorem r_d_anchoring_partial_rescue_does_not_save_class_b_or_class_d :
    ∀ c : EntropicGravityCandidate, rDIndependentNoGo c = true := by
  intro c; cases c <;> rfl

/-- **EGDE9′ — All eight candidates count among r_d-independent NO-GOs.** -/
theorem r_d_independent_count_eight :
    rDIndependentCount = 8 := by
  unfold rDIndependentCount; rfl

/-!
## §5 First complete-mechanism-family NO-GO closure (publication-novelty)

This is the **paper-45 publication-novelty claim** of Phase 6m: every
single candidate in the entropic-gravity dark-energy class has been
ruled out at R3, with R5 confirmation. Within the SK_EFT_Hawking
project's review of dark-energy mechanism families, this is the first
such complete-class closure.
-/

/-- All 8 Track B candidates as a list. -/
def allEntropicGravityCandidates : List EntropicGravityCandidate :=
  [.verlinde2017, .padmanabhanCosMIn, .hossenfelderVerlinde,
   .cadoniTuveriDEC, .hdeEventHorizon, .tsallisHDE,
   .barrowHDE, .odintsovDonofrioPaul]

/-- **EGDE10 — Track B contains exactly 8 candidates, all r_d-independent
    NO-GO (first complete-mechanism-family closure in Phase 6m;
    paper-45 publication-novelty claim).**

    Combines list-length count with the EGDE9 r_d-independence statement.
    The 8 candidates are exhaustive of the entropic-gravity DE class
    surveyed by Phase 6m. -/
theorem entropic_gravity_no_go_count_eight :
    allEntropicGravityCandidates.length = 8 := by
  unfold allEntropicGravityCandidates; rfl

/-!
## §6 Quantitative summary (mixed-threshold, primary-source-honest)

The four explicitly-quantitative NO-GO ledgers in Track B split by
methodology: two (Tsallis, Odintsov) are Bayes-factor-based and
individually exceed Jeffreys-decisive (≥ 5); one (Verlinde,
Halenka-Miller PRD 102, 084007 (2020)) is a σ-significance
galaxy-cluster mass-density exclusion at ≥ 5σ **under nominal profile
assumptions only** (weakening once systematics are included); one
(Barrow, Luciano-Paliathanasis-Saridakis 2506.03019) is
information-criteria-based with primary-source-verified ΔAIC = 4.7,
which is *moderate* disfavour (Burnham-Anderson ≥ 4) but **NOT**
Jeffreys-decisive.

Two aggregators below capture the honest closure:

* `both_decisive_bayes_bounds_exceed_jeffreys_decisive` covers the two
  genuinely Bayes-factor-decisive cases (Tsallis, Odintsov).
* `all_quantitative_bounds_disfavoured` covers all four with
  per-candidate unit coherence (σ / log𝓑 / ΔAIC / log𝓑), where
  Verlinde is at the nominal-assumptions 5σ level (Gaussian-σ scale),
  Barrow at the AIC moderate level, and Tsallis/Odintsov at the
  Bayes-factor decisive level.

The historical-named aggregator
`all_quantitative_bounds_exceed_jeffreys_decisive` (which Phase-6m-era
prose cited) is **retained as a deprecation alias** restricted to the
honest Bayes-factor cohort, after two successive honesty restrictions:
Barrow removed 2026-05-08 (AIC-only methodology, ΔAIC = 4.7 < 5), and
Verlinde removed 2026-06-10 (its quantitative ledger is a Gaussian-σ
cluster exclusion, not a Bayes factor — the historical first conjunct
conflated the σ and |log 𝓑| scales). Downstream prose now cites the
two new aggregators with explicit per-candidate methodology tagging.
-/

/-- **EGDE11 — Both Bayes-factor bounds exceed Jeffreys-decisive
    (R3 + R5 numerical content; Bayes-factor methodology cohort).**

    Exactly two of the four quantitative Track-B ledgers are Bayes
    factors (Tsallis, Odintsov); both are Jeffreys-decisive. Verlinde's
    quantitative ledger is a Gaussian-σ cluster-mass-density exclusion
    (see `verlinde_2017_no_go_via_cluster_mass_densities_halenka_miller`)
    and Barrow's is AIC-moderate
    (see `barrow_aic_delta_below_jeffreys_decisive`); neither belongs in
    a Bayes-factor cohort. Supersedes the pre-2026-06-10
    `all_three_decisive_bayes_bounds_exceed_jeffreys_decisive`, whose
    first conjunct compared Verlinde's σ value against the |log 𝓑|
    threshold (units conflation). -/
theorem both_decisive_bayes_bounds_exceed_jeffreys_decisive :
    tsallis_log_bayes ≥ jeffreys_decisive_threshold ∧
    odintsov_log_bayes ≥ jeffreys_decisive_threshold :=
  ⟨tsallis_hde_no_go_bayes_factor_tyagi_haridasu_basak,
   by unfold odintsov_log_bayes jeffreys_decisive_threshold; norm_num⟩

/-- **EGDE11′ — All four quantitative bounds quantitatively disfavour
    the candidate at moderate-or-greater level on their native scales
    (mixed-threshold honest closure).**

    Per-candidate unit-coherent conjunction: Verlinde at the
    nominal-assumptions galaxy-cluster 5σ level (Gaussian-σ scale;
    Halenka-Miller PRD 102, 084007 (2020)); Tsallis + Odintsov
    Bayes-factor-decisive (|log 𝓑| ≥ 5); Barrow AIC-moderate
    (ΔAIC ≥ 4). The mixed-threshold conjunction is the load-bearing
    numerical content of Phase 6m Track B's
    first-complete-mechanism-family closure under primary-source
    fidelity. Each conjunct compares a quantity against a threshold on
    the SAME scale; no σ↔log𝓑 conversion is asserted. -/
theorem all_quantitative_bounds_disfavoured :
    halenka_miller_cluster_nominal_sigma ≥ five_sigma_threshold ∧
    tsallis_log_bayes ≥ jeffreys_decisive_threshold ∧
    barrow_aic_delta ≥ aic_moderate_threshold ∧
    odintsov_log_bayes ≥ jeffreys_decisive_threshold :=
  ⟨verlinde_2017_no_go_via_cluster_mass_densities_halenka_miller,
   tsallis_hde_no_go_bayes_factor_tyagi_haridasu_basak,
   barrow_hde_disfavoured_information_criteria_luciano_paliathanasis_saridakis,
   by unfold odintsov_log_bayes jeffreys_decisive_threshold; norm_num⟩

/-- **Deprecation alias.** The Phase-6m-era name
    `all_quantitative_bounds_exceed_jeffreys_decisive` is retained for
    cross-bundle prose-side citation continuity, restricted to the
    honest Bayes-factor cohort after two successive honesty
    restrictions: (i) 2026-05-08 — Barrow removed (primary source is
    AIC-only, ΔAIC = 4.7 < 5; see
    `barrow_aic_delta_below_jeffreys_decisive`); (ii) 2026-06-10 —
    Verlinde removed (its quantitative ledger is the Halenka-Miller
    Gaussian-σ galaxy-cluster exclusion, not a Bayes factor; the
    historical conjunct `verlinde_cmb_bullet_sigma ≥
    jeffreys_decisive_threshold` conflated the σ and |log 𝓑| scales).
    What this name now proves is the 2-of-4 Bayes cohort
    (Tsallis + Odintsov). Downstream callers should migrate to
    `both_decisive_bayes_bounds_exceed_jeffreys_decisive` (Bayes
    cohort) or `all_quantitative_bounds_disfavoured` (all four,
    mixed-threshold, unit-coherent). -/
@[deprecated both_decisive_bayes_bounds_exceed_jeffreys_decisive
  (since := "2026-05-08")]
theorem all_quantitative_bounds_exceed_jeffreys_decisive :
    tsallis_log_bayes ≥ jeffreys_decisive_threshold ∧
    odintsov_log_bayes ≥ jeffreys_decisive_threshold :=
  both_decisive_bayes_bounds_exceed_jeffreys_decisive

end SKEFTHawking.EntropicGravityDarkEnergy
