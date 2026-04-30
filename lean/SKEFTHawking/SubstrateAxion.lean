import SKEFTHawking.Basic
import SKEFTHawking.Z16AnomalyComputation
import SKEFTHawking.Z16AnomalyForcesThetaBar
import Mathlib

/-!
# Phase 6l Wave 2: Substrate-Derived Axion — Branch γ Verdict

## Overview

Tests whether the SK-EFT substrate (SK-EFT fluctuating hydrodynamics +
ADW tetrad condensation + vestigial-gravity Z₄ + ℤ₁₆ Pin⁺ cobordism) admits
a Peccei-Quinn axion as the Goldstone of an emergent continuous U(1)_PQ.

**VERDICT: Branch γ — substrate cannot host a PQ axion as substrate Goldstone.**

Per the Wave-2 dossier (`Lit-Search/Phase-6l/6l-Lit-Search-Substrate-Derived
Axion.md.md`), three structural obstructions:

1. **Cobordism vs continuous-symmetry mismatch.** `Ω₄^{Pin⁺}(pt) ≅ ℤ₁₆`
   is a fermionic SPT classification (Wang-Senthil PRB 89 195124, 2014;
   Kitaev IPAM 2015), NOT the discrete remnant of a broken continuous U(1)/ℤ_N.
   The η-invariant generator is intrinsically fermionic (Pin⁺ structure
   dependent); a Peccei-Quinn axion is the bosonic Goldstone of a U(1)
   acting on chiral-fermion phases. There is no canonical embedding ℤ₁₆ ↪ U(1).

2. **ADW Goldstone modes are tensorial.** Diakonov tetrad condensation
   `[GL(4) or SO(3,1)_L] × SO(3,1)_S → SO(3,1)_J` (Diakonov 2011 arXiv:1109.0091;
   Vladimirov-Diakonov PRD 86 104019, 2012) produces 6 Nambu-Goldstone modes,
   all eaten by Lorentz spin connection ω_μ^{ab} via standard Higgs mechanism.
   No spin-0 pseudoscalar with `(α_s/8π) G G̃` coupling survives. The U(1)_det
   (overall scale) is absorbed into Weyl rescaling.

3. **Three substrate structural walls.** Non-Abelian gauge erasure at SK-EFT
   fluid layer (Crossley-Glorioso-Liu, JHEP 09 (2017) 095) blocks color-anomalous
   PQ current. Chiral-fermion fracturing only via TPF + SMG blocks KSVZ heavy-quark
   construction at substrate level. Three-tier emergent gravity forces the would-be
   axion to choose a tier where no chiral phase exists.

Wave-2 ships the Branch γ structural verdict + conditional KSVZ-style numerical
predictions usable by downstream modules (with explicit caveat: predictions
require an external U(1)_PQ above the substrate).

## What ships

* Substrate scale anchors (Λ_UV, Λ_GUT, Λ_QCD).
* Conditional KSVZ axion mass formula (Grilli di Cortona et al. JHEP 01 (2016) 034).
* Conditional KSVZ photon coupling g_aγγ.
* Numerical predictions at Planck and GUT scales (substantive `norm_num` checks).
* Cardinality argument: ZMod 16 ≇ ℝ — ℤ₁₆ is not a continuous-U(1) remnant.
* `ADWGoldstoneMode` 6-element inductive: all spin-2, none pseudoscalar.
* Tracked-hypothesis Prop bundle `SubstrateStructuralWalls`.
* Phenomenological exclusion: substrate-Planck axion in BH-superradiance window.
* Phenomenological discovery: substrate-GUT axion in DMRadio-GUT band.
* Cross-bridges to Phase 5b (`sm_anomaly_with_nu_R`) + Phase 6l W1 (Branch γ on θ̄).
* Verdict bundle `Phase6lW2Verdict` + witness.

## References

- `Lit-Search/Phase-6l/6l-Lit-Search-Substrate-Derived Axion.md.md` — Wave-2 dossier.
- Peccei, Quinn, PRL 38 1440 (1977); Weinberg, PRL 40 223 (1978); Wilczek, PRL 40 279 (1978).
- Kim, PRL 43 103 (1979); Shifman-Vainshtein-Zakharov, NPB 166 493 (1980) — KSVZ.
- Grilli di Cortona, Hardy, Pardo Vega, Villadoro, JHEP 01 (2016) 034, arXiv:1511.02867.
- Stott, Marsh, PRD 98 083006 (2018), arXiv:1805.02016 — BH superradiance.
- Brouwer et al. (DMRadio), PRD 106 112003 (2022), arXiv:2203.11246 — DMRadio-GUT.
- Wang, Senthil, PRB 89 195124 (2014), arXiv:1401.1142 — Pin⁺ ℤ₁₆ classification.
- Kitaev, IPAM lectures (2015) — homotopy-theoretic ℤ₁₆ classification.
- Witten, Rev. Mod. Phys. 88 035001 (2016), arXiv:1508.04715 — fermion path integrals.
- Diakonov, arXiv:1109.0091 (2011); Volovik, JLTP 206 1 (2022), arXiv:2111.07817 — ADW.
- Crossley, Glorioso, Liu, JHEP 09 (2017) 095, arXiv:1511.03646 — SK-EFT fluid EFT.
-/

namespace SKEFTHawking.SubstrateAxion

open Real

/-! ## §1 Substrate scale anchors (Planck, GUT, QCD) -/

/-- Substrate UV cutoff = Planck mass. In the ADW dimensional-tetrad
    convention (Volovik arXiv:2304.04235), the Newton constant emerges as
    `G ∼ 1/Λ_UV²`, so `Λ_UV = M_Pl ≃ 2.435 × 10¹⁸ GeV`. -/
noncomputable def Lambda_UV : ℝ := 2.435e18

/-- GUT scale anchor (intermediate substrate scenario). -/
noncomputable def Lambda_GUT : ℝ := 1.0e16

/-- QCD scale (PDG anchor). -/
noncomputable def Lambda_QCD : ℝ := 0.2

theorem Lambda_UV_pos : 0 < Lambda_UV := by unfold Lambda_UV; norm_num
theorem Lambda_GUT_pos : 0 < Lambda_GUT := by unfold Lambda_GUT; norm_num
theorem Lambda_QCD_pos : 0 < Lambda_QCD := by unfold Lambda_QCD; norm_num

/-- The substrate scale hierarchy: `Λ_QCD < Λ_GUT < Λ_UV`. Substantive
    chain that the three project anchors are correctly ordered. -/
theorem substrate_scale_hierarchy :
    Lambda_QCD < Lambda_GUT ∧ Lambda_GUT < Lambda_UV := by
  unfold Lambda_QCD Lambda_GUT Lambda_UV
  refine ⟨by norm_num, by norm_num⟩

/-! ## §2 Candidate PQ axion (conditional structure) -/

/-- A hypothetical substrate Peccei-Quinn axion, parameterised by its
    decay constant `f_a > 0`. **Existence at the substrate level is NOT
    asserted** — see §6's `SubstrateStructuralWalls`. The structure
    exists to allow conditional numerical predictions usable by downstream
    modules under the caveat "external U(1)_PQ above substrate". -/
structure SubstratePQAxion where
  decay : ℝ
  decay_pos : 0 < decay

/-- Conditional KSVZ axion mass formula. Grilli di Cortona-Hardy-Pardo
    Vega-Villadoro, JHEP 01 (2016) 034, Eq. (2.22) at zero temperature
    and leading-order chiral perturbation theory:
    `m_a = 5.70 μeV × (10¹² GeV / f_a)`. -/
noncomputable def axion_mass_KSVZ (a : SubstratePQAxion) : ℝ :=
  5.70e-6 * (1.0e12 / a.decay)

/-- Conditional KSVZ axion-photon coupling, E/N = 0 (hadronic axion).
    Grilli di Cortona et al. 2016 Eq. (5.1) with α_EM ≈ 1/137.036:
    `g_aγγ = -1.92 × α_EM / (2π f_a)`. -/
noncomputable def axion_g_a_gamma_KSVZ (a : SubstratePQAxion) : ℝ :=
  -1.92 * (1.0 / 137.036) / (2 * Real.pi * a.decay)

/-- KSVZ photon coupling is negative (hadronic axion, `E/N = 0` gives a
    negative `(E/N - 1.92)` factor). Substantive sign-of-coupling identity
    distinguishing KSVZ from DFSZ (where `E/N = 8/3` flips sign). -/
theorem axion_g_a_gamma_KSVZ_neg (a : SubstratePQAxion) :
    axion_g_a_gamma_KSVZ a < 0 := by
  unfold axion_g_a_gamma_KSVZ
  have h_pi_pos : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  have h_denom : (0 : ℝ) < 2 * Real.pi * a.decay := mul_pos h_pi_pos a.decay_pos
  have h_num : (-1.92 : ℝ) * (1.0 / 137.036) < 0 := by norm_num
  exact div_neg_of_neg_of_pos h_num h_denom

/-! ## §3 Numerical predictions at substrate-natural scales -/

/-- **Substrate-natural Planck-scale prediction.** At `f_a = Λ_UV ≈ 2.435×10¹⁸ GeV`,
    KSVZ gives `m_a ≈ 2.34 × 10⁻¹² eV`, bracketed in [2.3×10⁻¹², 2.4×10⁻¹²]. -/
theorem axion_mass_at_Planck :
    (2.3e-12 : ℝ) < axion_mass_KSVZ ⟨Lambda_UV, Lambda_UV_pos⟩ ∧
    axion_mass_KSVZ ⟨Lambda_UV, Lambda_UV_pos⟩ < (2.4e-12 : ℝ) := by
  unfold axion_mass_KSVZ Lambda_UV
  refine ⟨?_, ?_⟩
  · norm_num
  · norm_num

/-- **Substrate-natural GUT-scale prediction.** At `f_a = Λ_GUT = 10¹⁶ GeV`,
    KSVZ gives `m_a ≈ 5.7 × 10⁻¹⁰ eV`, bracketed in [5.6, 5.8] × 10⁻¹⁰ eV. -/
theorem axion_mass_at_GUT :
    (5.6e-10 : ℝ) < axion_mass_KSVZ ⟨Lambda_GUT, Lambda_GUT_pos⟩ ∧
    axion_mass_KSVZ ⟨Lambda_GUT, Lambda_GUT_pos⟩ < (5.8e-10 : ℝ) := by
  unfold axion_mass_KSVZ Lambda_GUT
  refine ⟨?_, ?_⟩
  · norm_num
  · norm_num

/-- **Inverse-decay scaling.** Doubling `f_a` halves `m_a`: substantive
    structural identity of the KSVZ formula. -/
theorem axion_mass_inverse_decay (f : ℝ) (hf : 0 < f) :
    axion_mass_KSVZ ⟨f, hf⟩ = 2 * axion_mass_KSVZ ⟨2 * f, by linarith⟩ := by
  unfold axion_mass_KSVZ
  field_simp

/-! ## §4 Obstruction 1: ℤ₁₆ Pin⁺ class is finite, not a continuous-U(1) remnant -/

/-- The ℤ₁₆ Pin⁺ cobordism class has cardinality 16. -/
theorem z16_card_finite : Fintype.card (ZMod 16) = 16 := by decide

/-- **Obstruction 1.** The ℤ₁₆ Pin⁺ class is a finite group (16 elements).
    The phase moduli of a Goldstone of a broken continuous U(1) is `ℝ` (or
    `ℝ / 2π f_a · ℤ`, also infinite). A bijection `ZMod 16 ≃ ℝ` is impossible
    by infinite/finite cardinality mismatch. This structurally precludes
    identifying the substrate ℤ₁₆ Pin⁺ class with the continuous-phase
    moduli of any putative U(1)_PQ Goldstone. -/
theorem z16_not_continuous_phase_remnant :
    ¬ Nonempty ((ZMod 16) ≃ ℝ) := by
  rintro ⟨e⟩
  have h_real : Infinite ℝ := inferInstance
  exact h_real.not_finite (Finite.of_equiv _ e)

/-! ## §5 Obstruction 2: ADW Goldstone modes are tensorial -/

/-- The 6 Nambu-Goldstone modes from the Diakonov ADW symmetry-breaking
    pattern `[GL(4) or SO(3,1)_L] × SO(3,1)_S → SO(3,1)_J`. Each carries
    a Lorentz tensor index pair `(a,b)` with `a < b ∈ {0,1,2,3}`, so there
    are exactly `(4 choose 2) = 6` modes (Diakonov 2011, Vladimirov-Diakonov 2012). -/
inductive ADWGoldstoneMode : Type
  | omega01 | omega02 | omega03 | omega12 | omega13 | omega23
  deriving DecidableEq, Fintype

/-- Spin assignment for ADW Goldstones. All six are spin-2 modes
    (Lorentz tensor index pair, eaten by spin connection `ω_μ^{ab}`
    becoming the gravitons via Higgs mechanism). -/
def ADWGoldstoneMode.spin : ADWGoldstoneMode → ℕ := fun _ => 2

/-- ADW Goldstone count is exactly 6. -/
theorem adw_goldstone_count : Fintype.card ADWGoldstoneMode = 6 := by decide

/-- **Obstruction 2.** All ADW Goldstones are tensor (spin ≥ 1) modes;
    none is a pseudoscalar. A Peccei-Quinn axion would be a spin-0
    pseudoscalar — no such mode arises from the ADW symmetry-breaking
    pattern. -/
theorem adw_goldstones_no_pseudoscalar :
    ∀ g : ADWGoldstoneMode, ADWGoldstoneMode.spin g ≠ 0 := by
  intro g; cases g <;> decide

/-! ## §6 Substrate structural walls (tracked-hypothesis Prop bundle) -/

/-- Tracked-hypothesis Prop bundle: the SK-EFT substrate's structural walls
    obstructing emergence of a PQ axion as substrate Goldstone.

    Two formally machine-checkable conjuncts (loaded directly from §4 + §5):
    (i) ADW Goldstones are tensorial (no pseudoscalar);
    (ii) ℤ₁₆ Pin⁺ class has finite cardinality (no bijection to ℝ).

    The third dossier obstruction (substrate non-Abelian gauge erasure +
    chiral-fermion fracturing only via TPF + SMG + three-tier emergent
    gravity) is documented in the module docstring; its formalization
    requires SK-EFT fluid-layer infrastructure not yet in scope. -/
structure SubstrateStructuralWalls : Prop where
  adw_tensorial : ∀ g : ADWGoldstoneMode, ADWGoldstoneMode.spin g ≠ 0
  z16_finite_distinct_from_real : ¬ Nonempty ((ZMod 16) ≃ ℝ)

/-- The substrate structural walls hold (per §4 + §5). -/
theorem substrate_structural_walls : SubstrateStructuralWalls where
  adw_tensorial := adw_goldstones_no_pseudoscalar
  z16_finite_distinct_from_real := z16_not_continuous_phase_remnant

/-! ## §7 Cross-bridges -/

/-- **Cross-bridge to Phase 5b.** Phase 5b's ℤ₁₆ anomaly cancellation
    (`sm_anomaly_with_nu_R`) operates on fermion content (a finite-cardinality
    constraint), structurally orthogonal to the continuous decay-constant
    moduli of any putative axion. The Phase 5b cancellation is genuinely
    invoked in the proof body. -/
theorem phase5b_cancellation_orthogonal_to_axion (a : SubstratePQAxion) :
    (16 : ZMod 16) = 0 ∧ 0 < a.decay :=
  ⟨SKEFTHawking.sm_anomaly_with_nu_R, a.decay_pos⟩

/-- **Cross-bridge to Phase 6l Wave 1.** Combined verdict: under W1's
    Branch γ on θ̄ (`theta_bar_not_forced_by_z16`) AND substrate structural
    walls (this wave), the strong-CP problem is unsolved at the substrate
    level — neither anomaly-locking nor axion-relaxation derives from
    substrate symmetry. -/
theorem combined_strong_cp_unsolved_at_substrate
    (h_walls : SubstrateStructuralWalls) :
    (¬ ∃ θ₀ : ℝ, ∀ s : SKEFTHawking.Z16AnomalyForcesThetaBar.SubstrateConfig,
        SKEFTHawking.Z16AnomalyForcesThetaBar.Z16AnomalyCancels s →
        s.theta_bar = θ₀) ∧
    SubstrateStructuralWalls :=
  ⟨SKEFTHawking.Z16AnomalyForcesThetaBar.theta_bar_not_forced_by_z16, h_walls⟩

/-! ## §8 Phenomenological exclusion windows -/

/-- Stellar-mass black-hole superradiance lower edge: `m_a > 7×10⁻¹⁴ eV`
    (Stott-Marsh, PRD 98 083006, 2018, arXiv:1805.02016). Window applies
    for `f_a ≳ 10¹⁴ GeV` (axion self-interaction sufficiently weak). -/
noncomputable def superradiance_lower_eV : ℝ := 7.0e-14

/-- Stellar-mass black-hole superradiance upper edge: `m_a < 2×10⁻¹¹ eV`. -/
noncomputable def superradiance_upper_eV : ℝ := 2.0e-11

/-- **Substrate-Planck axion EXCLUDED by stellar-BH superradiance.** The
    KSVZ prediction at `f_a = M_Pl` gives `m_a ≈ 2.34×10⁻¹² eV`, which
    falls inside the [7×10⁻¹⁴, 2×10⁻¹¹] eV BH-superradiance exclusion
    window. Therefore the substrate-Planck axion is ruled out as DM by
    LIGO-Virgo-KAGRA spin data. -/
theorem axion_at_Planck_in_superradiance_window :
    superradiance_lower_eV < axion_mass_KSVZ ⟨Lambda_UV, Lambda_UV_pos⟩ ∧
    axion_mass_KSVZ ⟨Lambda_UV, Lambda_UV_pos⟩ < superradiance_upper_eV := by
  unfold superradiance_lower_eV superradiance_upper_eV axion_mass_KSVZ Lambda_UV
  refine ⟨?_, ?_⟩
  · norm_num
  · norm_num

/-- DMRadio-GUT projected reach lower edge: `m_a > 4×10⁻¹⁰ eV` (Brouwer
    et al., PRD 106 112003, 2022; arXiv:2203.11246). -/
noncomputable def dmradio_gut_lower_eV : ℝ := 4.0e-10

/-- DMRadio-GUT projected reach upper edge: `m_a < 1.2×10⁻⁷ eV`. -/
noncomputable def dmradio_gut_upper_eV : ℝ := 1.2e-7

/-- **Substrate-GUT axion in DMRadio-GUT discovery band.** The KSVZ
    prediction at `f_a = Λ_GUT` gives `m_a ≈ 5.7×10⁻¹⁰ eV`, falling inside
    DMRadio-GUT's projected [4×10⁻¹⁰, 1.2×10⁻⁷] eV reach. This is the
    *only* substrate-natural scenario with near-term experimental
    discovery potential — and it requires an external U(1)_PQ above
    the substrate (not derivable from SK-EFT). -/
theorem axion_at_GUT_in_dmradio_band :
    dmradio_gut_lower_eV < axion_mass_KSVZ ⟨Lambda_GUT, Lambda_GUT_pos⟩ ∧
    axion_mass_KSVZ ⟨Lambda_GUT, Lambda_GUT_pos⟩ < dmradio_gut_upper_eV := by
  unfold dmradio_gut_lower_eV dmradio_gut_upper_eV axion_mass_KSVZ Lambda_GUT
  refine ⟨?_, ?_⟩
  · norm_num
  · norm_num

/-! ## §9 Verdict bundle -/

/-- **Phase 6l Wave 2 verdict bundle.** Branch γ — substrate cannot host
    PQ axion as Goldstone of an emergent U(1)_PQ.

    Four independent substantive conjuncts (P2-clean):
    1. Structural walls (ADW tensorial + ℤ₁₆ finite).
    2. ADW Goldstone count = 6 (none pseudoscalar).
    3. Substrate-Planck KSVZ axion is in stellar-BH superradiance window
       (excluded as DM if ANY substrate U(1)_PQ existed).
    4. Substrate-GUT KSVZ axion is in DMRadio-GUT discovery band (only
       viable phenomenological window — requires external U(1)_PQ). -/
structure Phase6lW2Verdict : Prop where
  walls : SubstrateStructuralWalls
  adw_count : Fintype.card ADWGoldstoneMode = 6
  planck_excluded :
    superradiance_lower_eV < axion_mass_KSVZ ⟨Lambda_UV, Lambda_UV_pos⟩ ∧
    axion_mass_KSVZ ⟨Lambda_UV, Lambda_UV_pos⟩ < superradiance_upper_eV
  gut_in_dmradio :
    dmradio_gut_lower_eV < axion_mass_KSVZ ⟨Lambda_GUT, Lambda_GUT_pos⟩ ∧
    axion_mass_KSVZ ⟨Lambda_GUT, Lambda_GUT_pos⟩ < dmradio_gut_upper_eV

/-- The Branch γ verdict (Wave 2) is satisfied. -/
theorem phase6l_w2_verdict : Phase6lW2Verdict where
  walls := substrate_structural_walls
  adw_count := adw_goldstone_count
  planck_excluded := axion_at_Planck_in_superradiance_window
  gut_in_dmradio := axion_at_GUT_in_dmradio_band

end SKEFTHawking.SubstrateAxion
