/-
SK_EFT_Hawking TODO-D21: D9's consumption of I3's LDP foundations, built.

THE DEFECT THIS CLOSES
----------------------
`papers/D9/paper_draft.tex` states twice that its rare-event tails consume the
I3 bundle's large-deviation foundations (§1 companion paragraph; §4.2). Measured
2026-08-07 and re-measured 2026-08-09 **before this module existed**, three ways,
all negative: the D9 ∩ I3 closure intersection was **0**, and neither
`fdt_rare_event_tail` nor `fdt_gallavotti_cohen` carried a single
`name_deps_project` entry in `SKEFTHawking.LDP.*` or `SKEFTHawking.Itô.*`. The
same probe returned 50 for D9 ∩ D10 and 14 for D9 ∩ D8, so the instrument was
not the problem. I3's draft agreed with the substrate rather than with D9's,
calling the cross-bridge *"designed but not yet consumed at release time"*.

**With this bridge declared as a D9 apex the intersection is 11**, three of them
in `SKEFTHawking.LDP`, and I3's draft was updated in the same commit to say one
consumer exists. The paragraph above is the state this module closed, in the past
tense, because a header asserting `0` in the present tense would be the module
contradicting its own effect.

WHY THIS IS A BUILD AND NOT A RETRACTION
----------------------------------------
The two sides already share their object. `fdt_rare_event_tail` is a positivity
statement about `linearResponseRateFunction β σ² ·`, and I3's LDP layer certifies
`linearResponseRateFunctionCentered β σ²` — the *same* function shifted by the
constant `I(0)` — as `LDPCompatibleSKEFT`. The consumption claim was therefore
true of the physics and false of the Lean, which makes building the edge the
correct remedy rather than narrowing the prose.

WHAT IS PROVED
--------------
`fdt_rare_event_tail_is_ldp_certified` states both halves of the consumption
claim at once, for the one object:

  * the rate function is the LDP-compatible one I3 certifies, and
  * its rare-event tail is bounded below by `-β²σ²/8` away from the FDT-pinned
    mean, which is `fdt_rare_event_tail` transported across the centering.

`-β²σ²/8` is exactly `-I(0)`: the centering subtracts the rate function's value
at the no-work event, so the strict positivity of the uncentered tail becomes a
strict floor at minus that constant. Stated numerically rather than
qualitatively so it is falsifiable — a wrong centering constant fails it.

Primary sources: Dembo-Zeitouni 1998 (LDP framework); the Gallavotti-Cohen
W-form as carried by `CrooksAnalogHawking.WFormGallavottiCohen`.
-/

import Mathlib
import SKEFTHawking.QuantumNetwork.FDTNoiseFloor
import SKEFTHawking.LDP.LDPCompatibleSKEFT

set_option autoImplicit false

namespace SKEFTHawking.QuantumNetwork

open SKEFTHawking.CrooksAnalogHawking SKEFTHawking.LDP

/-- The constant the centering removes: `I(0) = β²σ²/8` for the FDT-pinned
Gaussian rate function. Isolated as its own lemma because it is what makes the
floor in the bridge theorem a specific number rather than "some constant". -/
theorem linearResponseRateFunction_at_zero (β σ_sq : ℝ) (hσ : σ_sq ≠ 0) :
    linearResponseRateFunction β σ_sq 0 = β ^ 2 * σ_sq / 8 := by
  unfold linearResponseRateFunction
  field_simp
  ring

/-- **D9's rare-event tail is a statement about the rate function I3 certifies.**

Both halves of the consumption claim, for one object: the function is
`LDPCompatibleSKEFT` by I3's instance, and its tail is bounded strictly below by
`-β²σ²/8` off the FDT-pinned mean. The second half is `fdt_rare_event_tail`
transported across the centering that makes the function LDP-admissible. -/
theorem fdt_rare_event_tail_is_ldp_certified
    {β σ_sq W : ℝ} (hσ : 0 < σ_sq) (hW : W ≠ β * σ_sq / 2) :
    LDPCompatibleSKEFT β (linearResponseRateFunctionCentered β σ_sq) ∧
      -(β ^ 2 * σ_sq / 8) < linearResponseRateFunctionCentered β σ_sq W := by
  haveI : Fact (σ_sq ≠ 0) := ⟨ne_of_gt hσ⟩
  refine ⟨inferInstance, ?_⟩
  have htail : 0 < linearResponseRateFunction β σ_sq W := fdt_rare_event_tail hσ hW
  have hzero : linearResponseRateFunction β σ_sq 0 = β ^ 2 * σ_sq / 8 :=
    linearResponseRateFunction_at_zero β σ_sq (ne_of_gt hσ)
  unfold linearResponseRateFunctionCentered
  rw [hzero]
  linarith

/-- Non-vacuity: the hypotheses are satisfiable, so the bridge is not
conditionally empty. At `β = 0`, `σ² = 1`, `W = 1` the FDT-pinned mean is `0`,
so `W ≠ βσ²/2` holds and the floor is `0`. -/
theorem fdt_rare_event_tail_is_ldp_certified_witness :
    LDPCompatibleSKEFT 0 (linearResponseRateFunctionCentered 0 1) ∧
      -(0 ^ 2 * (1 : ℝ) / 8) < linearResponseRateFunctionCentered 0 1 1 :=
  fdt_rare_event_tail_is_ldp_certified (by norm_num) (by norm_num)

end SKEFTHawking.QuantumNetwork
