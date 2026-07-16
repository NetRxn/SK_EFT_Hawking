/-
# Phase 5q.H close-out — the S²×S² Gram pin, reduced to its TWO named geometric residuals

`PinPlusKTSpinSigmaStock.SphereProdGramPin` — the lumped hypothesis `interMatrix
sphereProdIntFundClassHonest sphereProdHDataComputed.intH2Basis = sphereProdFormDatum` (`II(S²×S²) =
H`) that gates the S²×S² witness's `s2s2_hyp` — is stated on the COMPUTED (UCT-flip) `H²`-basis. The
`SphereProdCrossInt` module already assembled the full 2×2 Gram matrix on the GEOMETRIC factor-pullback
family `![α, β]` (`crossFamily_gram_eq_hyp`), isolating it to ONE hypothesis: the Eilenberg–Zilber cross
value `⟨α ∪ β, [S²×S²]⟩ = 1`. This module closes the last gap between the two, exhibiting that the lumped
pin is EXACTLY the conjunction of its two genuinely-deep, named geometric residuals:

* `hcross` — the **Eilenberg–Zilber / Künneth cross value** `⟨α ∪ β, [M]⟩ = 1`. Genuinely unbuilt: the
  pinned Mathlib (`5e932f97`, v4.29.1) has no Künneth theorem / EZ cross product for singular
  (co)homology, and this project's cup/cap layer was built from scratch on the `TopCat.toSSet` cochain
  model precisely because that layer is absent (a multi-hundred-line combinatorial build; project-recorded
  as "OFF critical path, deferred" — the σ÷16 Rokhlin leg is independently discharged via the S⁴ witness);
* the **basis identification** between the computed UCT basis and the geometric factor-dual family — a
  SEPARATE geometric statement (`SphereProdHData` docstring: the computed basis discharges *existence*, not
  the geometric factor-dual identity; `deltaGen`'s factor-projections are not forced without normalization).

## What this ships (honest reduction — no grind, no new gap)

* `sphereProdGramPin_of_cross_of_basisId` — the lumped `SphereProdGramPin` from the LITERAL basis-ID
  (`computed basis = ![α, β]`) plus `hcross`. Plugs straight into the existing Stock consumers
  (`sphereProd_s2s2_hyp_of_gram`, `..._evenUnimodular_of_gram`).
* `sphereProd_s2s2_hyp_of_cross_of_congr` — the CORRECTLY-STRENGTHENED `s2s2_hyp` (`∃ N hyperbolic,
  IntCongr (interMatrix) N`) from the ROBUST basis-ID (a unimodular change-of-basis `IntCongr` between the
  computed and geometric Gram matrices — not literal equality) plus `hcross`. Since `s2s2_hyp` only needs
  congruence, this is the honest minimal shape: the S²×S² hyperbolic pin bottoms out at exactly the EZ
  cross value + a change-of-basis congruence, both disclosed geometric facts.

Neither theorem discharges the EZ cross value or the basis geometry — they REDUCE the lumped pin to those
two named atoms, matching the substrate recon and the project's recorded deferred status. Preemptive-
strengthening: the hypotheses are load-bearing named residuals (drop `hcross` → the off-diagonal is
unpinned; drop the basis-ID → the computed-basis Gram is unrelated to `![α, β]`), not tautologies.

Dimension discipline: `SphereProdT = S² × S²`, closed spin 4-manifold; integral cohomology degree 2; the
intersection form on `H²`. Fence `synthetic-grade-ker-bot-nogo`: the reduction carries genuine disclosed
Künneth geometry, no fabricated grade; the S²×S² product is a genuine closed manifold, not a pair-class route.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusKTSpinSigmaStock

namespace SKEFTHawking.SphereProdGramPinReduce

open SKEFTHawking SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SphereProdHFourInt (sphereProdIntFundClassHonest)
open SKEFTHawking.SphereWitnessTowerInt
  (SphereProdT sphereProdBasis2Computed sphereProdIntH2Basis sphereProdHDataComputed)
open SKEFTHawking.SphereProdCrossInt (alphaOf betaOf crossFamily crossFamily_gram_eq_hyp)
open SKEFTHawking.SpinSigmaRoute (sphereProdFormDatum sphereProdFormDatum_hyp_pin)
open SKEFTHawking.PinPlusKTSpinSigmaStock (SphereProdGramPin)

/-! ## §1. The lumped Gram pin from the LITERAL basis-ID + the EZ cross value -/

/-- **`SphereProdGramPin` from its two named residuals (literal basis-ID).** Given (i) the literal
identification of the computed UCT `H²`-basis with the geometric factor-pullback family `![α, β]`
(`hbasisId`) and (ii) the Eilenberg–Zilber cross value `⟨α ∪ β, [M]⟩ = 1` (`hcross`), the lumped Stock
hypothesis `SphereProdGramPin` (`interMatrix fc B = sphereProdFormDatum`) holds. Assembles the two DONE
diagonal zeros + symmetry + the disclosed cross value (all via `crossFamily_gram_eq_hyp`) and transports
along the basis-ID. This plugs into the existing `sphereProd_s2s2_hyp_of_gram` /
`sphereProd_s2s2_evenUnimodular_of_gram`, exhibiting the lumped pin as exactly these two atoms. -/
theorem sphereProdGramPin_of_cross_of_basisId (x : Cohomology (Sph 2) 2)
    (hbasisId : ∀ i, sphereProdBasis2Computed i = crossFamily x i)
    (hcross : interFormInt sphereProdIntFundClassHonest (alphaOf x) (betaOf x) = 1) :
    SphereProdGramPin := by
  show interMatrix sphereProdIntFundClassHonest sphereProdHDataComputed.intH2Basis = sphereProdFormDatum
  rw [← crossFamily_gram_eq_hyp x hcross]
  ext i j
  show interFormInt sphereProdIntFundClassHonest (sphereProdBasis2Computed i) (sphereProdBasis2Computed j)
    = interFormInt sphereProdIntFundClassHonest (crossFamily x i) (crossFamily x j)
  rw [hbasisId i, hbasisId j]

/-! ## §2. The correctly-strengthened `s2s2_hyp` from a ROBUST (congruence) basis-ID + the EZ cross value -/

/-- **The S²×S² hyperbolic pin `s2s2_hyp`, reduced to the EZ cross value + a change-of-basis
congruence.** `s2s2_hyp` (`∃ N, IsHyperbolicForm N ∧ IntCongr (interMatrix fc B) N`) needs only
CONGRUENCE, so the robust honest shape takes the basis-ID as a unimodular `IntCongr` between the computed
Gram matrix and the geometric family's Gram matrix (`hcong`), NOT literal equality. With `hcross`, the
family Gram is `sphereProdFormDatum = Hyp` (`crossFamily_gram_eq_hyp`), which is hyperbolic-standard
(`sphereProdFormDatum_hyp_pin`); transitivity of `IntCongr` closes it. This is the minimal honest
residual of the second σ-witness: the EZ cross value + a change-of-basis congruence, both disclosed. -/
theorem sphereProd_s2s2_hyp_of_cross_of_congr (x : Cohomology (Sph 2) 2)
    (hcong : IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis)
      (Matrix.of fun i j => interFormInt sphereProdIntFundClassHonest (crossFamily x i) (crossFamily x j)))
    (hcross : interFormInt sphereProdIntFundClassHonest (alphaOf x) (betaOf x) = 1) :
    ∃ N, IsHyperbolicForm N ∧
      IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis) N := by
  have heq := crossFamily_gram_eq_hyp x hcross
  obtain ⟨N, hN, hpin⟩ := sphereProdFormDatum_hyp_pin
  exact ⟨N, hN, hcong.trans (heq.symm ▸ hpin)⟩

end SKEFTHawking.SphereProdGramPinReduce
