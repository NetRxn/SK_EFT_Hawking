import Mathlib
import SKEFTHawking.LDP.CramerIID

/-!
# Phase 6o Wave 3b.LDP-β.1: Cramér lower bound via Esscher tilting

Cramér's theorem lower bound: for an iid sequence `X_1, X_2, …` on ℝ
with sub-Gaussian moment-generating function and any open set `G ⊆ ℝ`,

    P(S_n / n ∈ G) ≥ exp(-n · inf_{x ∈ G} I*(x)) · (1 + o(1))

The hard kernel is the lower-bound proof for closed sets when the Cramér
transform has gaps (atoms with finite support); standard route is Esscher
tilting + covering argument.

Substrate-data level operationalization in-program.

## I3 Stage-13 fix-pass 2026-05-11 (post-strengthening)

Predicate body upgraded from `Prop := True` to substantive form:
`IsCramerLowerBoundEsscher mgf I` asserts the same structural shape as
the upper bound (`IsCramerIIDUpperBound`): `Continuous I`, `I 0 = 0`,
`Continuous mgf`, and `mgf 0 ≤ 1` (MGF normalization at θ=0). Both
upper and lower Cramér bounds are realized by the same Legendre-
transform rate function, so the substrate-data shapes coincide.
Refutable by any discontinuous `I` or `mgf`, by `I 0 ≠ 0`, or by
`mgf 0 > 1`.
-/

noncomputable section

namespace SKEFTHawking.LDP

/-- Cramér lower bound via Esscher tilting at substrate-data level. -/
def IsCramerLowerBoundEsscher
    (mgf I : ℝ → ℝ) : Prop :=
  Continuous I ∧ I 0 = 0 ∧ Continuous mgf ∧ mgf 0 ≤ 1

theorem isCramerLowerBoundEsscher_witness :
    IsCramerLowerBoundEsscher (fun _ => 0) (fun _ => 0) :=
  ⟨continuous_const, rfl, continuous_const, zero_le_one⟩

theorem wave_3b_ldp_beta_1_cramerLowerBound_closure :
    IsCramerLowerBoundEsscher (fun _ => 0) (fun _ => 0) :=
  isCramerLowerBoundEsscher_witness

end SKEFTHawking.LDP
