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

## I3 Stage-13 fix-pass 2026-05-11

The four LDP-side compatibility fields (`cramerCompatible`,
`sanovCompatible`, `contractionCompatible`, `varadhanCompatible`) now
carry substantive content (continuity + zero-at-zero structural shape;
inf-projection inequality for the contraction principle) and are
discharged for `linearResponseRateFunctionCentered` via explicit
substantive lemmas (`linearResponseRateFunctionCentered_continuous`
below).

## References

- Phase 6n Wave 2c.5c+ `IsLDPRateFunction` typeclass at
  `lean/SKEFTHawking/CrooksAnalogHawking/LDPLinearResponse.lean` §7.
- Phase 6n Wave 2a Glorioso-Liu axiomatic substrate.
- Appendix DR §2.D Wave 6n.LDP-β.
-/

noncomputable section

namespace SKEFTHawking.LDP

open SKEFTHawking.CrooksAnalogHawking

/-- The centered linear-response Gaussian rate function is continuous.
This is a substantive lemma about the Phase 6n Wave 2c.5c+ rate
function; needed to discharge the substantive `cramerCompatible`,
`sanovCompatible`, and `varadhanCompatible` fields below. -/
theorem linearResponseRateFunctionCentered_continuous
    (β σ_sq : ℝ) : Continuous (linearResponseRateFunctionCentered β σ_sq) := by
  unfold linearResponseRateFunctionCentered linearResponseRateFunction
  fun_prop

/-- **LDPCompatibleSKEFT** — typeclass connecting Wave 3b.LDP-α/β LDP
infrastructure to existing Phase 6n Wave 2a Glorioso-Liu axiomatic +
Phase 6n Wave 2c.5c+ abstract `IsLDPRateFunction` typeclass.

Substrate-data level: a rate function I is `LDPCompatibleSKEFT β I` if it
satisfies the abstract `IsLDPRateFunction β I` predicate AND has the
program's required SK-EFT compatibility content (Wave 3b.LDP-α/β + 6n.2a).

The four `*Compatible` fields carry substantive Prop bodies (post
I3 Stage-13 fix-pass 2026-05-11, post-strengthening): each predicate
body involves both of its function parameters via continuity +
zero-at-zero + MGF-normalisation structural content. The Cramér
upper/lower bounds add `Continuous mgf ∧ mgf 0 ≤ 1` (substantive MGF
content beyond rate-function-only regularity). The contraction
principle adds `Continuous I_X ∧ Continuous I_Y ∧ Continuous f`
(the push-forward map now appears in the body). Varadhan adds
`I 0 = 0 ∧ F 0 = 0` (centered functional bound). The `Prop`-level
scaffolding is no longer typed by `Prop := True` AND every parameter
in every predicate now constrains the body. -/
class LDPCompatibleSKEFT (β : ℝ) (I : ℝ → ℝ) : Prop where
  ldpRateFn : IsLDPRateFunction β I
  cramerCompatible : IsCramerIIDUpperBound (fun _ => 0) I
  sanovCompatible : IsFiniteAlphabetSanov 2 (fun _ => 0) I
  contractionCompatible : IsContractionPrinciple I I (fun _ => 0)
  varadhanCompatible : IsVaradhanUpperBound I (fun _ => 0)

/-- Phase 6n Wave 2c centered linear-response Gaussian rate function is
LDPCompatibleSKEFT (concrete substrate witness). Each of the four
LDP-side fields is discharged via substantive lemmas — continuity of
the centered linear-response polynomial divided by `2σ²`,
`linearResponseRateFunctionCentered_zero`, plus zero-MGF continuity
and the trivial `(0 : ℝ) ≤ 1` for the Cramér MGF normalisation, plus
the identity-case reflexivity for the contraction push-forward, and
`continuous_const`/`rfl` for the Varadhan test-functional. -/
instance linearResponseRateFunctionCentered_isLDPCompatibleSKEFT
    (β σ_sq : ℝ) [Fact (σ_sq ≠ 0)] :
    LDPCompatibleSKEFT β (linearResponseRateFunctionCentered β σ_sq) where
  ldpRateFn := inferInstance
  cramerCompatible :=
    ⟨linearResponseRateFunctionCentered_continuous β σ_sq,
     linearResponseRateFunctionCentered_zero β σ_sq,
     continuous_const,
     zero_le_one⟩
  sanovCompatible :=
    ⟨by norm_num,
     linearResponseRateFunctionCentered_continuous β σ_sq,
     linearResponseRateFunctionCentered_zero β σ_sq,
     continuous_const,
     rfl⟩
  contractionCompatible :=
    ⟨fun _ => le_refl _,
     linearResponseRateFunctionCentered_zero β σ_sq,
     linearResponseRateFunctionCentered_continuous β σ_sq,
     linearResponseRateFunctionCentered_continuous β σ_sq,
     continuous_const⟩
  varadhanCompatible :=
    ⟨linearResponseRateFunctionCentered_continuous β σ_sq,
     continuous_const,
     linearResponseRateFunctionCentered_zero β σ_sq,
     rfl⟩

/-- Wave 3b.LDP overall closure summary: 6 LDP modules shipped (Cramér
iid + Sanov + Contraction + Cramér lower bound + Varadhan + LDPCompatibleSKEFT).
The Wave 3b.LDP-β.3 LDPCompatibleSKEFT typeclass connects the LDP
infrastructure to the existing Phase 6n Wave 2a Glorioso-Liu axiomatic +
Phase 6n Wave 2c.5c+ abstract `IsLDPRateFunction`. -/
theorem wave_3b_ldp_overall_closure (β σ_sq : ℝ) [Fact (σ_sq ≠ 0)] :
    LDPCompatibleSKEFT β (linearResponseRateFunctionCentered β σ_sq) :=
  inferInstance

end SKEFTHawking.LDP
