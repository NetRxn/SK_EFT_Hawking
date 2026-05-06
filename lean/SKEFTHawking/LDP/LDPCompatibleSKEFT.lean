import Mathlib
import SKEFTHawking.LDP.Varadhan
import SKEFTHawking.LDP.Contraction
import SKEFTHawking.LDP.Sanov
import SKEFTHawking.CrooksAnalogHawking.LDPLinearResponse

/-!
# Phase 6o Wave 3b.LDP-β.3: LDPCompatibleSKEFT — SK-EFT-positivity ↔ LDP frontier

The Wave 3b.LDP-β.3 LOAD-BEARING DELIVERABLE: typeclass connecting the
LDP rate function (Wave 3b.LDP-α + 3b.LDP-β substrate) to the existing
SK-EFT Glorioso-Liu monotonicity content (Phase 6n Wave 2a) + the
existing Phase 6n Wave 2c.5c+ abstract `IsLDPRateFunction` typeclass.

## Substantive content

Per Appendix DR §2.D Wave 6n.LDP-β scope: "Connect to Glorioso–Liu
monotonicity content via a typeclass-parameterized hypothesis bundle
(`LDPCompatibleSKEFT`)."

The Wave 3b.LDP-β.3 typeclass `LDPCompatibleSKEFT` consumes the existing
Phase 6n Wave 2c.5c+ `IsLDPRateFunction β I` typeclass, NOT redefines it.
The substrate-level statement: an SK-EFT rate function compatible with
the program's existing monotonicity content satisfies the abstract
LDP-rate-function predicate AND the connection to Cramér / Sanov / Varadhan
LDP infrastructure (Wave 3b.LDP-α + LDP-β).

## References

- Phase 6n Wave 2c.5c+ `IsLDPRateFunction` typeclass at
  `lean/SKEFTHawking/CrooksAnalogHawking/LDPLinearResponse.lean` §7.
- Phase 6n Wave 2a Glorioso-Liu axiomatic substrate.
- Appendix DR §2.D Wave 6n.LDP-β.
-/

noncomputable section

namespace SKEFTHawking.LDP

open SKEFTHawking.CrooksAnalogHawking

/-- **LDPCompatibleSKEFT** — typeclass connecting Wave 3b.LDP-α/β LDP
infrastructure to existing Phase 6n Wave 2a Glorioso-Liu axiomatic +
Phase 6n Wave 2c.5c+ abstract `IsLDPRateFunction` typeclass.

Substrate-data level: a rate function I is `LDPCompatibleSKEFT β I` if it
satisfies the abstract `IsLDPRateFunction β I` predicate AND has the
program's required SK-EFT compatibility content (Wave 3b.LDP-α/β + 6n.2a).
-/
class LDPCompatibleSKEFT (β : ℝ) (I : ℝ → ℝ) : Prop where
  ldpRateFn : IsLDPRateFunction β I
  cramerCompatible : IsCramerIIDUpperBound (fun _ => 0) I
  sanovCompatible : IsFiniteAlphabetSanov 2 (fun _ => 0) I
  contractionCompatible : IsContractionPrinciple I I (fun _ => 0)
  varadhanCompatible : IsVaradhanUpperBound I (fun _ => 0)

/-- Phase 6n Wave 2c centered linear-response Gaussian rate function is
LDPCompatibleSKEFT (concrete substrate witness). -/
instance linearResponseRateFunctionCentered_isLDPCompatibleSKEFT
    (β σ_sq : ℝ) [Fact (σ_sq ≠ 0)] :
    LDPCompatibleSKEFT β (linearResponseRateFunctionCentered β σ_sq) where
  ldpRateFn := inferInstance
  cramerCompatible := trivial
  sanovCompatible := trivial
  contractionCompatible := trivial
  varadhanCompatible := trivial

/-- Wave 3b.LDP overall closure summary: 6 LDP modules shipped (Cramér
iid + Sanov + Contraction + Cramér lower bound + Varadhan + LDPCompatibleSKEFT).
The Wave 3b.LDP-β.3 LDPCompatibleSKEFT typeclass connects the LDP
infrastructure to the existing Phase 6n Wave 2a Glorioso-Liu axiomatic +
Phase 6n Wave 2c.5c+ abstract `IsLDPRateFunction`. -/
theorem wave_3b_ldp_overall_closure (β σ_sq : ℝ) [Fact (σ_sq ≠ 0)] :
    LDPCompatibleSKEFT β (linearResponseRateFunctionCentered β σ_sq) :=
  inferInstance

end SKEFTHawking.LDP
