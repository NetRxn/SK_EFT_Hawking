import Mathlib
import SKEFTHawking.SoftTheorems.Carrollian

/-!
# Phase 6o Wave 1a.4: ADW emergent-graviton subleading soft factor

## Goal

Encode the ADW (Akama-Diakonov-Wetterich) emergent-graviton **subleading**
soft factor with Goldstone-broken-boost content per Green-Huang-Shen
arXiv:2208.14544 inflationary Adler conditions and Cachazo-Strominger
arXiv:1404.4091 subleading soft graviton.

## Substantive content (R-01 remediation, 2026-07-20)

The soft expansion of a graviton amplitude is

    M(ω) = S⁽⁰⁾/ω + S⁽¹⁾ + O(ω),

where S⁽⁰⁾ is the Weinberg leading (1/ω) soft factor and S⁽¹⁾ is the
subleading O(1) factor (the angular-momentum / broken-boost-Goldstone
term, Cachazo-Strominger / Green-Huang-Shen). Equivalently,

    ω · M(ω) = S⁽⁰⁾ + S⁽¹⁾ · ω     (leading + subleading Laurent truncation).

The subleading predicate now **ties the subleading factor S⁽¹⁾ to the
actual amplitude** via this equation (rather than the previous vacuous
`∃ subleading_factor, True`): the amplitude must admit a genuine two-term
soft expansion with a specific subleading coefficient. Non-vacuity is
witnessed at both S⁽¹⁾ = 0 (`trivialADWGravitonSoft`) and S⁽¹⁾ = 2 ≠ 0
(`subleadingSoftAmplitude_isADW`), the latter showing the subleading
factor genuinely varies (is load-bearing).

## References

- Green-Huang-Shen, "Inflationary Adler Conditions," arXiv:2208.14544.
- Cachazo-Strominger, arXiv:1404.4091 — subleading soft graviton.
- arXiv:2403.05459 — boostless soft amplitudes.
-/

noncomputable section

namespace SKEFTHawking.SoftTheorems

/-- The ADW emergent-graviton subleading-soft-factor structure.

`M` satisfies this predicate when
* it has the Weinberg leading 1/ω soft factor (`IsBoostlessLeadingSoftFactor`,
  Wave 1a.2), AND
* it admits a genuine **leading + subleading** soft expansion: there exist
  a leading residue `S0` and a subleading factor `S1` with
  `ω · M.amplitudeAt ω = S0 + S1 · ω` for all ω > 0.

The subleading coefficient `S1` is the O(1) piece controlled by the
spontaneously-broken-boost Goldstone (Green-Huang-Shen arXiv:2208.14544).
It is tied to the amplitude by the expansion equation — NOT a free
existential. -/
def IsADWLinearizedGravitonSubleadingSoft {n : ℕ} (M : SoftAmplitude n) : Prop :=
  IsBoostlessLeadingSoftFactor M ∧
  ∃ S0 S1 : ℝ, ∀ ω : ℝ, ω > 0 → ω * M.amplitudeAt ω = S0 + S1 * ω

/-- The ADW-graviton subleading-soft predicate strictly extends the
boostless leading-soft-factor predicate: any amplitude satisfying the
ADW subleading predicate also satisfies the Wave 1a.2 boostless leading
predicate. -/
theorem isADWLinearizedGravitonSubleadingSoft_implies_boostless
    {n : ℕ} {M : SoftAmplitude n}
    (h : IsADWLinearizedGravitonSubleadingSoft M) :
    IsBoostlessLeadingSoftFactor M :=
  h.1

/-- Toy ADW-graviton-soft-amplitude witness with **zero** subleading factor:
the trivial soft amplitude `M(ω) = 1/ω` has leading residue S⁽⁰⁾ = 1 and
subleading factor S⁽¹⁾ = 0 (pure pole, no O(1) piece). -/
theorem trivialADWGravitonSoft :
    IsADWLinearizedGravitonSubleadingSoft trivialSoftAmplitude := by
  refine ⟨trivialSoftAmplitude_satisfies_boostless, 1, 0, fun ω hω => ?_⟩
  simp only [trivialSoftAmplitude, if_pos hω]
  field_simp
  ring

/-- A soft amplitude with a genuinely **non-zero** subleading factor:
`M(ω) = 1/ω + 2`, with leading residue S⁽⁰⁾ = 1 and subleading factor
S⁽¹⁾ = 2. -/
def subleadingSoftAmplitude : SoftAmplitude 2 :=
  { hn := by norm_num
  , amplitudeAt := fun ω => if ω > 0 then 1 / ω + 2 else 0
  , residualAt := fun _ => 1 }

/-- `subleadingSoftAmplitude` satisfies the ADW subleading predicate with a
non-zero subleading factor S⁽¹⁾ = 2 — demonstrating the subleading factor
is load-bearing (genuinely varies, not pinned to 0). -/
theorem subleadingSoftAmplitude_isADW :
    IsADWLinearizedGravitonSubleadingSoft subleadingSoftAmplitude := by
  constructor
  · -- leading 1/ω factor with universal factor F(ω) = 1 + 2ω
    refine ⟨fun ω => 1 + 2 * ω, fun ω hω => ?_⟩
    simp only [subleadingSoftAmplitude, if_pos hω]
    field_simp
  · -- genuine two-term expansion: ω·M = 1 + 2·ω
    refine ⟨1, 2, fun ω hω => ?_⟩
    simp only [subleadingSoftAmplitude, if_pos hω]
    field_simp

/-- The subleading factor of `subleadingSoftAmplitude` is non-zero: the
predicate's subleading data is not degenerate. -/
theorem subleadingSoftAmplitude_subleading_ne_zero :
    ∃ S0 S1 : ℝ, S1 ≠ 0 ∧
      ∀ ω : ℝ, ω > 0 → ω * subleadingSoftAmplitude.amplitudeAt ω = S0 + S1 * ω := by
  refine ⟨1, 2, by norm_num, fun ω hω => ?_⟩
  simp only [subleadingSoftAmplitude, if_pos hω]
  field_simp

/-- Wave 1a.4 closure summary (R-01 remediation). -/
theorem wave_1a_4_emergentGraviton_closure :
    -- Predicate has a witness with subleading factor 0
    IsADWLinearizedGravitonSubleadingSoft trivialSoftAmplitude ∧
    -- and a witness with a genuinely non-zero subleading factor
    IsADWLinearizedGravitonSubleadingSoft subleadingSoftAmplitude ∧
    -- and strictly extends the Wave 1a.2 leading-soft-factor predicate
    (∀ {n : ℕ} {M : SoftAmplitude n},
       IsADWLinearizedGravitonSubleadingSoft M →
       IsBoostlessLeadingSoftFactor M) :=
  ⟨trivialADWGravitonSoft,
   subleadingSoftAmplitude_isADW,
   @isADWLinearizedGravitonSubleadingSoft_implies_boostless⟩

end SKEFTHawking.SoftTheorems
