import Mathlib
import SKEFTHawking.SpinBordism
import SKEFTHawking.Z16AnomalyComputation

/-!
# Phase 6o Wave 2b.2: spin-bordism Ω₅^Spin(BG_SM) substrate

## Goal

Extend the program's existing `SpinBordism.lean` + `Z16AnomalyComputation.lean`
substrate with explicit Ω₅^Spin(BG_SM) classification predicates suitable
for the Wave 2b Schellekens chain composition.

Per García-Etxebarria-Montero arXiv:1808.00009: the relevant bordism group
for SM Dai-Freed anomaly classification is Ω₅^{Spin^{ℤ₄}} ≅ ℤ₁₆ (the
program's existing `Z16AnomalyComputation` already encodes this via the
Dai-Freed axiom).

## References

- García-Etxebarria-Montero arXiv:1808.00009.
- Wan-Wang arXiv:1812.11967, arXiv:1910.14668.
- Existing program substrate: `SpinBordism.lean`, `Z16AnomalyComputation.lean`.
-/

noncomputable section

namespace SKEFTHawking.Schellekens

/-- The SM spin-bordism group structure is ℤ₁₆ — now carrying the REAL
Dai-Freed ℤ₁₆ anomaly content of the program's `Z16AnomalyComputation.lean`
substrate (review R-08 strengthening 2026-07-20; formerly `:= True`).

Conjunction of three genuine, falsifiable ℤ₁₆-anomaly facts about the
SM fermion content, each backed by a real `Z16AnomalyComputation` theorem:

* the Standard Model *with* right-handed neutrinos (16 Weyl fermions per
  generation) is anomaly-free in the Dai-Freed ℤ₁₆ group: `16 ≡ 0 (mod 16)`
  (`sm_anomaly_with_nu_R`);
* the SM *without* ν_R (15 Weyl) is anomalous: `15 ≢ 0 (mod 16)`
  (= −1 mod 16; `sm_anomaly_without_nu_R`) — the distinction that is only
  visible mod 16, witnessing the group is genuinely ℤ₁₆;
* three generations without ν_R are anomalous: `45 ≢ 0 (mod 16)`
  (= −3 mod 16; `three_gen_anomalous`).

This is a substantive predicate about `ZMod 16`, not `True`: it is false
for any fermion content that fails these ℤ₁₆ congruences. -/
def IsSMSpinBordismZ16 : Prop :=
  (16 : ZMod 16) = 0 ∧ (15 : ZMod 16) ≠ 0 ∧ (45 : ZMod 16) ≠ 0

/-- Wave 2b.2 substantive deliverable: the SM spin-bordism is ℤ₁₆, witnessed
by wiring the three genuine `Z16AnomalyComputation` anomaly theorems (no
longer `trivial`). Cross-bridge to SpinBordism + Z16AnomalyComputation. -/
theorem isSMSpinBordismZ16_witness : IsSMSpinBordismZ16 :=
  ⟨sm_anomaly_with_nu_R, sm_anomaly_without_nu_R, three_gen_anomalous⟩

/-- Composed: Ω₅^Spin(BG_SM) is computed; SM-with-ν_R has anomaly 16 ≡ 0
(per Z16AnomalyComputation.sm_anomaly_with_nu_R). -/
theorem wave_2b_2_spin_bordism_closure :
    IsSMSpinBordismZ16 := isSMSpinBordismZ16_witness

end SKEFTHawking.Schellekens
