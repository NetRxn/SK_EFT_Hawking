import SKEFTHawking.Basic
import SKEFTHawking.MajoranaRung
import Mathlib

/-!
# Phase 5z Wave 2b: Decoupling-Theorem Bounds for Embedding I vs III

## Overview

Upgrades `WAVE2-OPEN-5` from a comment-marker IR-equivalence claim to a
quantitative tracked-hypothesis bound, following the deep-research return
at `Lit-Search/Phase-5z/Phase 5z, Wave 2a — Decoupling Bounds for
Embedding I vs III.md` (verdict 2026-04-25).

The Appelquist-Carazzone (AC) decoupling theorem (Phys. Rev. D 11, 2856
(1975)) is well-established and provides the schematic bound

  |amp_III(E) − amp_I(E)|  ≤  C · (E / Λ_ADW)^k

for some `k ≥ 1` and dimensionless `C`. Wave 2b's novel content is NOT a
re-derivation of AC but the identification of:

1. The **leading operator dimension** `Δ` for the substrate-vs-fundamental
   distinction. The deep research finds `Δ = 5` (Weinberg-like dim-5
   operator under explicit lepton-number violation, `k = 1`) or `Δ = 6`
   (generic dim-6 four-fermion / kinetic form-factor, `k = 2`).

2. The **natural coefficient** `C ~ N_f / (16π²)` from the SILH
   counting (Giudice-Grojean-Pomarol-Rattazzi JHEP 06 (2007) 045) +
   bilocal-NJL form factor (Hill, Entropy 26 (2024) 146). Substrate-
   specific C value not computed in primary literature for ADW;
   honest flag.

3. Three **failure modes** of AC that apply at *cosmological* scales but
   NOT at `E ~ M_W`: vestigial gravity (Volovik 2024), q-theory
   (Klinkhamer-Volovik 2008-2009), and FRG strong-coupling (Wetterich +
   Reuter-Saueressig). All three are encoded as additional clauses in
   the `DecouplingRegime` predicate; at `E = M_W ~ 80 GeV` and
   `Λ_ADW = 10^14 GeV` they are trivially satisfied.

## Encoding pattern

Following project precedent for tracked-hypothesis Props (see e.g.
`MajoranaRung.H_MR_FromADWSubstrate_BCS_LNV`,
`HiddenSectorMixedCharge.H_MixedChannelZ16Cancels`,
`DarkSectorSynthesis.H_VestigialRelicCarriesZ16Charge`), the AC bound
itself enters as a tracked Prop hypothesis. Substrate-specific
coefficient determination is left to the deep-research-flagged sources;
the Lean module's role is to thread the bound through to falsifiability
witnesses and the `Asymptotics.IsBigO` API.

## References

- Appelquist & Carazzone, Phys. Rev. D 11, 2856 (1975) — AC theorem.
- Ball & Thorne, hep-th/9404156 — Wilsonian-EFT proof.
- Giudice, Grojean, Pomarol, Rattazzi, JHEP 06 (2007) 045 — SILH
  natural coefficients.
- Hill, Entropy 26 (2024) 146 — bilocal NJL bound-state form factor.
- Cirigliano et al., JHEP 12 (2017) 082 + 12 (2018) 097 — SMEFT
  master formula for 0νββ.
- Volovik, JETP Lett. 119 (2024) 330 — vestigial-gravity failure mode.
- Klinkhamer & Volovik, PRD 79 (2009) 063527 — q-theory failure mode.
-/

noncomputable section

open Real

namespace SKEFTHawking.MajoranaRungDecoupling

/-! ## 1. DecouplingRegime predicate

Captures the conjunction of conditions under which the AC theorem applies
to the substrate-vs-fundamental Embedding I vs III amplitude difference:

- Energy `E` is positive and well below the substrate scale.
- The hierarchy `E < Λ_ADW / 10` provides a robust margin (avoids
  threshold-region complications).
- Three failure-mode predicates are excluded:
  (a) Vestigial-gravity regime (Volovik 2024) — applies only at `E ≲ Λ_QCD`.
  (b) Cosmological regime (Klinkhamer-Volovik q-theory) — applies only
      at `E ≲ H_0^{1/4} · Λ_ADW^{3/4}`, far below electroweak scale.
  (c) FRG strong-coupling regime (Wetterich) — applies only when the
      substrate four-fermion coupling exceeds the strong-coupling bound.

At `E = M_W ~ 80 GeV` and `Λ_ADW = 10^14 GeV`, all three (a)-(c) are
trivially satisfied; encoding them as predicates surfaces the regime of
validity to downstream consumers. -/
structure DecouplingRegime (E Λ_ADW : ℝ) : Prop where
  /-- Energy is positive. -/
  posE : 0 < E
  /-- Substrate scale is positive. -/
  posΛ : 0 < Λ_ADW
  /-- Robust hierarchy: `E < Λ_ADW / 10`. -/
  hierarchy : 10 * E < Λ_ADW
  /-- Not in the vestigial-gravity regime (Volovik 2024). The vestigial
  regime applies only at `E ≲ Λ_QCD ≃ 0.2 GeV`; we require `E` strictly
  above QCD confinement. At `E = M_W ≃ 80 GeV`, satisfied numerically.
  Stage-13 strengthened (2026-04-25, BLOCKER 5.3): prior encoding
  `not_vestigial : True` accepted any inhabitant; replaced by an
  explicit hierarchy `0.2 < E` so the field encodes the regime
  exclusion the prose claims. -/
  not_vestigial : (0.2 : ℝ) < E
  /-- Not in the cosmological regime (Klinkhamer-Volovik q-theory).
  Cosmological corrections apply only at `E ≲ H_0 ≃ 1.4·10⁻⁴² GeV` (in
  natural units); we require `E` strictly above the present-day Hubble
  scale. At `E = M_W`, trivially numerically satisfied.
  Stage-13 strengthened (2026-04-25, BLOCKER 5.3). -/
  not_cosmological : (1.4e-42 : ℝ) < E
  /-- Substrate is not in the FRG strong-coupling regime. The
  Wetterich-Reuter-Saueressig analysis applies when the substrate four-
  fermion coupling exceeds the strong-coupling unitarity bound, which
  in this normalization corresponds to `Λ_ADW ≳ M_Pl ≃ 10¹⁹ GeV`. We
  require the substrate scale to be sub-Planckian: `Λ_ADW < 10¹⁹` GeV.
  At `Λ_ADW = 10¹⁴`, trivially numerically satisfied.
  Stage-13 strengthened (2026-04-25, BLOCKER 5.3). -/
  weakly_coupled_matter : Λ_ADW < (1e19 : ℝ)

/-! ## 2. SubstrateData — substrate parameters needed for Wilson coefficient -/

/-- Substrate parameters that determine the natural Wilson-coefficient
estimate for the AC bound. Mirrors the deep-research recommendation:
`N_f`, `G_c` (4-fermion coupling), `Λ_UV`, `Λ_ADW`. -/
structure SubstrateData where
  /-- Substrate scale (lower of the two). -/
  Λ_ADW : ℝ
  /-- UV cutoff (above the substrate scale, may be the same in practice). -/
  Λ_UV : ℝ
  /-- Number of substrate fermion flavors (≥ 1). -/
  N_f : ℕ
  /-- Substrate scale positive. -/
  hΛ_ADW : 0 < Λ_ADW
  /-- UV cutoff is at or above the substrate scale. -/
  hΛ_UV_ge : Λ_ADW ≤ Λ_UV
  /-- At least one substrate flavor. -/
  hN_f : 1 ≤ N_f

/-- Natural Wilson-coefficient estimate per SILH counting + bilocal NJL.
For ADW with `N_f ~ 16` and `Λ_UV ≃ Λ_ADW`, this evaluates to
`~ 0.1` — neither an enhancement nor a suppression.

Honest flag: the exact ADW value is NOT computed in primary literature;
this is the natural transplant from NJL+SILH analog systems. -/
def naturalC (s : SubstrateData) : ℝ :=
  (s.N_f : ℝ) / (16 * Real.pi ^ 2)

theorem naturalC_pos (s : SubstrateData) : 0 < naturalC s := by
  unfold naturalC
  have h_Nf : (0 : ℝ) < s.N_f := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one s.hN_f
  have h_pi_sq : 0 < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  positivity

/-- Natural Wilson coefficient is bounded above by the strong-coupling
unitarity scale `4π` whenever the substrate flavor count satisfies
`N_f ≤ 64 π³ ≈ 1985`. For natural ADW substrates with `N_f ≃ 16` this
is trivially satisfied; the bound is the algebraic statement that the
SILH natural coefficient never exceeds the strong-unitarity scale in
realistic substrates. -/
theorem naturalC_le_4pi (s : SubstrateData) (h_N_f : (s.N_f : ℝ) ≤ 64 * Real.pi ^ 3) :
    naturalC s ≤ 4 * Real.pi := by
  unfold naturalC
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_denom_pos : 0 < 16 * Real.pi ^ 2 := by positivity
  rw [div_le_iff₀ h_denom_pos]
  -- Goal: (s.N_f : ℝ) ≤ 4 * π * (16 * π²) = 64 * π³
  nlinarith [h_N_f, h_pi_pos]

/-! ## 3. The amplitude-difference tracked-hypothesis bounds

Following project precedent, the Appelquist-Carazzone bound itself is a
tracked-hypothesis `Prop` parameterized over a candidate amplitude-
difference function. The hypothesis is non-vacuous (existence proven by
the trivial zero-difference witness); proving the bound holds for a
specific physical Embedding-III amplitude is a follow-up wave (Wave 2c
or paper 21 strengthening pass).

The deep-research material gives the natural form:

  |amp_diff(E)|  ≤  naturalC s · (E / Λ_ADW)^k,    k ∈ {1, 2}

with `k = 1` requiring explicit lepton-number violation
(`MajoranaRung.H_LeptonNumberViolated`) — that selects the dim-5
Weinberg-operator channel — and `k = 2` the generic dim-6 four-fermion /
kinetic-form-factor channel.
-/

/-- **WAVE2-OPEN-5b (k = 2, generic dim-6)**: tracked hypothesis that the
amplitude-difference function `amp_diff : ℝ → ℝ` between Embedding III
(substrate-bound `ν_R`) and Embedding I (fundamental `ν_R`) is bounded
above by the natural Wilson coefficient times `(E / Λ_ADW)²` at every
energy in the decoupling regime.

This is the AC bound applied at dim-6 — applicable when the substrate
preserves U(1)_L and the dim-5 Weinberg channel is symmetry-forbidden. -/
def H_DecouplingBoundDim6
    (amp_diff : ℝ → ℝ) (s : SubstrateData) : Prop :=
  ∀ E : ℝ, DecouplingRegime E s.Λ_ADW →
    |amp_diff E| ≤ naturalC s * (E / s.Λ_ADW) ^ 2

/-- **WAVE2-OPEN-5a (k = 1, dim-5 LNV)**: stronger tracked hypothesis
that, under explicit lepton-number violation, the amplitude difference
is bounded by the natural coefficient times `(E / Λ_ADW)¹`. The dim-5
Weinberg-operator channel saturates the AC bound when LNV is allowed.

Parameterized over the substrate L-violation coefficient `G_LV` (per the
Stage-13 strengthening of `MajoranaRung.H_LeptonNumberViolated` to the
non-trivial predicate `G_LV ≠ 0`). The dim-5 channel is selected when
`G_LV ≠ 0`; absent LNV, `G_LV = 0` falsifies the predicate and the
generic dim-6 bound `H_DecouplingBoundDim6` applies instead. -/
def H_DecouplingBoundDim5_LNV
    (amp_diff : ℝ → ℝ) (s : SubstrateData) (G_LV : ℝ) : Prop :=
  SKEFTHawking.MajoranaRung.H_LeptonNumberViolated G_LV ∧
  ∀ E : ℝ, DecouplingRegime E s.Λ_ADW →
    |amp_diff E| ≤ naturalC s * (E / s.Λ_ADW)

/-! ## 4. Non-vacuity witnesses and refinement chain -/

/-- Non-vacuity witness for `DecouplingRegime`: the canonical electroweak-
scale point `E = M_W ≃ 80 GeV` and substrate scale `Λ_ADW = 10^14 GeV`
satisfies the regime. Concretely we verify:
- the hierarchy `10·M_W < Λ_ADW` (`800 < 10^14`);
- `not_vestigial`: `0.2 < 80` (M_W ≫ Λ_QCD);
- `not_cosmological`: `1.4·10⁻⁴² < 80` (M_W ≫ H_0);
- `weakly_coupled_matter`: `10^14 < 10^19` (Λ_ADW sub-Planckian).

Stage-13 strengthened (2026-04-25): the three failure-mode predicates
are now substantive numerical inequalities rather than `True`
placeholders, and this proof discharges them via `norm_num`. -/
theorem decouplingRegime_at_electroweak_scale :
    DecouplingRegime 80 (10 ^ 14) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

/-- Non-vacuity witness for the dim-6 hypothesis: the trivially-zero
amplitude difference satisfies the bound at every decoupling-regime
energy. This confirms the predicate is logically consistent (existence
without forcing the substrate physics). -/
theorem H_DecouplingBoundDim6_consistent (s : SubstrateData) :
    H_DecouplingBoundDim6 (fun _ => 0) s := by
  intro E h_regime
  simp
  have h_C := naturalC_pos s
  have h_E : 0 < E := h_regime.posE
  have h_Λ : 0 < s.Λ_ADW := s.hΛ_ADW
  positivity

/-- Independence of the dim-5-LNV and dim-6 bounds: at `E < Λ_ADW`, the
ratio `E/Λ_ADW < 1`, so `(E/Λ_ADW)² < E/Λ_ADW`, meaning the dim-6 bound
is *tighter* (smaller upper bound) than the dim-5 bound. The two
hypotheses therefore apply in *different physical regimes*: dim-6 when
the substrate preserves U(1)_L (the dim-5 Weinberg operator is
symmetry-forbidden, generic dim-6 form factor leads); dim-5 when the
substrate violates U(1)_L (the Weinberg operator is allowed and gives
the leading IR correction). The deep research is explicit on this
(§1.1, §2.2): the bounds are NOT in an implication relation. This
lemma surfaces the algebraic ratio fact for downstream consumers. -/
theorem dim6_tighter_than_dim5_in_decoupling_regime
    (s : SubstrateData) {E : ℝ} (h_regime : DecouplingRegime E s.Λ_ADW) :
    (E / s.Λ_ADW) ^ 2 ≤ E / s.Λ_ADW := by
  have h_E_pos : 0 < E := h_regime.posE
  have h_Λ_pos : 0 < s.Λ_ADW := s.hΛ_ADW
  have h_ratio_le : E / s.Λ_ADW ≤ 1 := by
    rw [div_le_one h_Λ_pos]
    linarith [h_regime.hierarchy]
  have h_ratio_pos : 0 < E / s.Λ_ADW := div_pos h_E_pos h_Λ_pos
  rw [sq]
  nlinarith [h_ratio_pos, h_ratio_le]

/-! ## 5. Asymptotics.IsBigO restatement

Compatibility layer with Mathlib's `Asymptotics` library, following the
deep-research recommendation. Under the dim-6 hypothesis, the amplitude
difference is `O(E^2)` along the decoupling-regime principal filter; this
matches the form expected by downstream calculus / asymptotic-analysis
infrastructure.
-/

/-- **Asymptotics restatement**: under the dim-6 hypothesis, the
amplitude difference is `O((E/Λ)²)` on the decoupling-regime principal
filter. Useful for connecting to Mathlib's existing IsBigO API. -/
theorem H_DecouplingBoundDim6_isBigOWith
    (amp_diff : ℝ → ℝ) (s : SubstrateData)
    (h : H_DecouplingBoundDim6 amp_diff s) :
    Asymptotics.IsBigOWith (naturalC s)
      (Filter.principal {E : ℝ | DecouplingRegime E s.Λ_ADW})
      amp_diff (fun E => (E / s.Λ_ADW) ^ 2) := by
  rw [Asymptotics.IsBigOWith_def, Filter.eventually_principal]
  intro E h_regime
  have h_E_pos : 0 < E := h_regime.posE
  have h_Λ_pos : 0 < s.Λ_ADW := s.hΛ_ADW
  have h_ratio_pos : 0 < E / s.Λ_ADW := div_pos h_E_pos h_Λ_pos
  have h_sq_pos : 0 < (E / s.Λ_ADW) ^ 2 := pow_pos h_ratio_pos 2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h_sq_pos]
  exact h E h_regime

/-! ## 6. Wave 2b summary

The Wave 2b decoupling-strengthening infrastructure for Embedding I vs III
is in place at the tracked-hypothesis level: `DecouplingRegime` encodes
substantive numerical exclusions of the three known cosmological-scale
failure modes (vestigial gravity, q-theory, FRG strong-coupling), and
the dim-5/dim-6 AC bounds are parameterized via `H_DecouplingBoundDim5_LNV`
+ `H_DecouplingBoundDim6`. The substrate-specific Wilson coefficient `C`
is not derived in primary literature for ADW; the natural-coefficient
estimate `naturalC s = N_f / (16π²)` from SILH+Hill bilocal-NJL is the
honest stand-in. (Stage-13 cleanup 2026-04-25 removed the
`wave2b_decoupling_summary : True := trivial` placeholder per BLOCKER 5.4
on paper21 review; the file-level docstring above replaces it.)
-/

end SKEFTHawking.MajoranaRungDecoupling
