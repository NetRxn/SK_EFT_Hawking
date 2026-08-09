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

/-- **Half one of the consumption claim: the centered rate function is exactly what
I3's LDP layer certifies.**

⚠️ **This is stated ALONE, on purpose.** It used to be the first conjunct of the
bridge theorem below, where it was dead weight: it resolves by `inferInstance`
from `linearResponseRateFunctionCentered_isLDPCompatibleSKEFT`, which needs only
`[Fact (σ_sq ≠ 0)]` and holds for every `β` and every `W` — so it was independent
of both of that theorem's hypotheses, and dropping it changed nothing (CLAUDE.md
preemptive-strengthening rule 1). A fact about the function is not a consequence
of the hypotheses, and bundling the two made one substantive theorem look like
two. Both halves remain D9 apexes; they are now separately checkable. -/
theorem linearResponseRateFunctionCentered_is_ldp_certified
    (β : ℝ) {σ_sq : ℝ} (hσ : 0 < σ_sq) :
    LDPCompatibleSKEFT β (linearResponseRateFunctionCentered β σ_sq) := by
  haveI : Fact (σ_sq ≠ 0) := ⟨ne_of_gt hσ⟩
  infer_instance

/-- **Half two, and the substantive one: D9's rare-event tail, transported.**

Off the FDT-pinned mean the centered rate function is bounded strictly below by
`-β²σ²/8`. This is `fdt_rare_event_tail` carried across the centering that makes
the function LDP-admissible, and unlike the certification above it genuinely
consumes both hypotheses. -/
theorem fdt_rare_event_tail_is_ldp_certified
    {β σ_sq W : ℝ} (hσ : 0 < σ_sq) (hW : W ≠ β * σ_sq / 2) :
    -(β ^ 2 * σ_sq / 8) < linearResponseRateFunctionCentered β σ_sq W := by
  have htail : 0 < linearResponseRateFunction β σ_sq W := fdt_rare_event_tail hσ hW
  have hzero : linearResponseRateFunction β σ_sq 0 = β ^ 2 * σ_sq / 8 :=
    linearResponseRateFunction_at_zero β σ_sq (ne_of_gt hσ)
  unfold linearResponseRateFunctionCentered
  rw [hzero]
  linarith

/-- Non-vacuity, at an operating point where every number in the statement is
NONZERO.

⚠️ The witness was `β = 0, σ² = 1, W = 1`. There the FDT-pinned mean `βσ²/2` is
`0`, the centering constant `β²σ²/8` is `0`, and the floor is `0` — every
quantity the theorem is *about* vanished, and nothing distinguished it from
`0 < I(1)`. At `β = 2, σ² = 1, W = 0` the mean is `1`, so `W ≠ βσ²/2` is a real
side condition, and the floor is `-1/2`: a wrong centering constant breaks it. -/
theorem fdt_rare_event_tail_is_ldp_certified_witness :
    -((2 : ℝ) ^ 2 * (1 : ℝ) / 8) < linearResponseRateFunctionCentered 2 1 0 :=
  fdt_rare_event_tail_is_ldp_certified (by norm_num) (by norm_num)

/-- The certification half at the same nonzero operating point. -/
theorem linearResponseRateFunctionCentered_is_ldp_certified_witness :
    LDPCompatibleSKEFT 2 (linearResponseRateFunctionCentered 2 1) :=
  linearResponseRateFunctionCentered_is_ldp_certified 2 (by norm_num)

end SKEFTHawking.QuantumNetwork
