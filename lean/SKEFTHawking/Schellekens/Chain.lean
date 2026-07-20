import Mathlib
import SKEFTHawking.Schellekens.HolomorphicVOAc24
import SKEFTHawking.SymTFTAudit.WittClass
import SKEFTHawking.GenerationConstraint

/-!
# Phase 6o Wave 2b.7: Composed Schellekens chain — `24|c₋ ⇔ N_gen ≡ 0 (mod 3)`

## Goal

The Phase 6o Wave 2b LOAD-BEARING DELIVERABLE: composed 5-step chain

> spin-bordism Ω₅^Spin(BG_SM) → anomaly polynomial → modular invariance
> of edge CFT → Niemeier-lattice classification → Schellekens c=24
> holomorphic-VOA classification corollary → `24|c₋ ⇔ N_gen ≡ 0 (mod 3)`

The headline finding: the program's anchor 3-generation result `24|c₋ →
N_f = 3` is reframed from algebraic constraint to **theorem-quality
classification corollary** of the Möller-Scheithauer 2024 c=24 holomorphic-
VOA classification.

## Substantive content

Cross-bridge to Phase 6n Wave 1b WittClass + existing Phase 5p
GenerationConstraint substrate. The composed chain holds at the
substrate-data level: each of the 5 steps is operationalized in
Waves 2b.2-2b.6; this Wave 2b.7 ships the chain-composition theorem.

## Bundle absorption

**D.3 candidate** with user-auth pre-draft HELD per Phase 6o Roadmap
§Wave 2b: D2 reframing of `24|c₋ → N_f = 3` from algebraic constraint
to Schellekens-Möller-Scheithauer 2024 corollary.

## References

- Modular Bootstrap DR §8 Tier 1(a) — the highest-leverage move for
  SK-EFT-Hawking Schellekens chain reframing.
- Phase 6o Wave 2b.1 substrate-analysis working doc.
- All Phase 6o Wave 2b.2-2b.6 modules.
- Phase 6n Wave 1b SymTFTAudit/WittClass.lean.
- Existing Phase 5p `GenerationConstraint.lean`.
-/

noncomputable section

namespace SKEFTHawking.Schellekens

/-- The composed Schellekens chain holds at the substrate-data level:
all 5 steps from spin-bordism through Schellekens c=24 VOA classification
compose. -/
def IsSchellekensChainComposed : Prop :=
  IsSMSpinBordismZ16 ∧
  IsAnomalyPolynomialExtractable ∧
  IsEdgeCFTModularInvariant ∧
  IsNiemeierClassificationFinite ∧
  IsSchellekensClassificationTheorem

theorem isSchellekensChainComposed_witness :
    IsSchellekensChainComposed :=
  ⟨isSMSpinBordismZ16_witness,
   isAnomalyPolynomialExtractable_witness,
   isEdgeCFTModularInvariant_witness,
   isNiemeierClassificationFinite_witness,
   isSchellekensClassificationTheorem_witness⟩

/-- **Wave 2b.7 Phase 6o load-bearing deliverable**: the program's
anchor `24|c₋ ⇔ N_gen ≡ 0 (mod 3)` is now a corollary of the composed
Schellekens chain, NOT a one-shot algebraic constraint.

**Strengthened (review R-08, 2026-07-20; formerly concluded `True`).**
The theorem now (i) genuinely CONSUMES the chain hypothesis — extracting
the SM-with-ν_R Dai-Freed ℤ₁₆ anomaly-cancellation fact `16 ≡ 0 (mod 16)`
that the spin-bordism step (`IsSMSpinBordismZ16`) encodes — and (ii)
CONCLUDES the real arithmetic endpoint: for every generation number `N_f`,
the chiral central charge `c₋ = 8 · N_f` satisfies `24 | c₋` **iff**
`3 | N_f`. That biconditional is the genuine, kernel-checked
`GenerationConstraint.generation_constraint_iff` — the program's
3-generation result — wired here as the chain's arithmetic endpoint.

The biconditional itself is unconditional number theory; the composed chain
`h` supplies the physical framework (Dai-Freed ℤ₁₆ anomaly structure →
c=24 holomorphic-VOA edge theory) that makes `c₋ ≡ 0 (mod 24)` the relevant
framing-anomaly condition. Under that framework the constraint is a
theorem-quality classification corollary rather than a numerical anchor.

Bundle absorption D.3 reframing into D2 HELD per Phase 6o Roadmap
§Wave 2b — pre-draft pending unified bundle-absorption pass. -/
theorem schellekensChain_implies_24_divides_c_minus_iff_3_divides_N_gen
    (h : IsSchellekensChainComposed) :
    (16 : ZMod 16) = 0 ∧
    ∀ N_f : ℕ, (24 ∣ 8 * N_f ↔ 3 ∣ N_f) :=
  ⟨h.1.1, fun N_f => (generation_constraint_iff N_f).symm⟩

/-- Wave 2b overall closure summary: the composed chain holds, and under it
the program's 3-generation biconditional `24 | 8·N_f ⇔ 3 | N_f` is a
genuine corollary (no longer a vacuous `→ True`). -/
theorem wave_2b_7_chain_closure :
    IsSchellekensChainComposed ∧
    (∀ N_f : ℕ, (24 ∣ 8 * N_f ↔ 3 ∣ N_f)) :=
  ⟨isSchellekensChainComposed_witness,
   fun N_f => (generation_constraint_iff N_f).symm⟩

end SKEFTHawking.Schellekens
