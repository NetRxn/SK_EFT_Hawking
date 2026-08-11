/-
SK_EFT_Hawking TODO-D35: the AGP recursion, derived rather than instantiated.

WHY THIS MODULE EXISTS
----------------------
`Chernoff.lean` defines `pairFailureBound n ε := C(n,2) * ε^2` and its own
docstring says the probabilistic content is deferred:

    "This is provable from union bound + independence ... At the Lean level, we
     abstract this as a real-valued upper-bound function ... The concrete
     MeasureTheory instantiation is deferred."

`Concatenation.lean` then *defines* `agpLevelSequence A ε₀ (L+1) = A * (εL L)^2`,
so the whole chain up to `AGP/Threshold.lean` proves statements about a sequence
that is DEFINED to satisfy the recursion. Nothing connected an actual failure
probability to `A * ε^2`.

Measured 2026-08-09 via `bundle_closure.compute_closure` — the canonical
resolver, not a hand-rolled walk: `agp_threshold_steane`'s dependency closure
walks 22 declarations, 21 of them author-written, and reaches none of
`ExRec`, `Malignant`, `NoiseModel`, `NoiseModelMT` or `Chernoff`. (The 27 this
comment carried until 2026-08-09 was, AS MEASURED THEN, the closure of a
DIFFERENTLY NAMED theorem —
`FaultTolerance.agp_threshold_steane_bound` in `Counting.lean`. The qualitative
half — that neither reaches those five modules — holds for both.) What was machine-checked was the CONSEQUENCE of the
AGP recursion, not its derivation.

WHAT IS PROVED HERE
-------------------
The union bound over malignant pairs, as a statement about a genuine probability
measure:

  `measure_malignant_union_le` :
      μ (⋃ p ∈ F, fail p.1 ∩ fail p.2) ≤ F.card * ε^2

given that each malignant pair's joint failure has probability at most `ε^2`.
`malignant_pair_indep_le` supplies that hypothesis from independence plus a
per-location rate bound, which is the local stochastic noise model's content.

Composing the two gives `exRecFailure_le_agpRecursionStep`: an ex-Rec whose
malignant-pair set has cardinality `A`, under local stochastic noise at rate
`ε`, fails with probability at most `A * ε^2`. That is Eq. (agp-recursion) of
AGP 2006 §4 as a derived bound rather than a definition.

SCOPE, stated because it is the boundary of the result
------------------------------------------------------
This derives the recursion's INEQUALITY from the ex-Rec's malignant-pair set and
pairwise independence. It does NOT derive the malignant-pair COUNT for the Steane
CNOT ex-Rec: `A_CNOT = 35235` remains pinned to AGP 2006 §8.3 eq. (36) in
`Counting.lean`, which is a combinatorial enumeration over a concrete circuit and
a separate undertaking.

Primary source: Aliferis-Gottesman-Preskill 2006, arXiv:quant-ph/0504218 §4.
-/

import Mathlib
import SKEFTHawking.FaultTolerance.Chernoff
import SKEFTHawking.FaultTolerance.ExRec

set_option autoImplicit false

namespace SKEFTHawking.FaultTolerance

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*}

/-! ## 1. A malignant pair's joint failure probability

Under local stochastic noise each location fails with probability at most `ε`,
and distinct locations fail independently. A pair therefore fails jointly with
probability at most `ε^2`.
-/

/-- **A pair of independent locations, each failing with probability at most `ε`,
fails jointly with probability at most `ε ^ 2`.**

This is the local-stochastic-noise input to the AGP recursion, and the only
place independence is used. -/
theorem malignant_pair_indep_le
    {μ : Measure Ω} {s t : Set Ω} {ε : ENNReal}
    (hindep : IndepSet s t μ) (hs : μ s ≤ ε) (ht : μ t ≤ ε) :
    μ (s ∩ t) ≤ ε ^ 2 := by
  rw [hindep.measure_inter_eq_mul, sq]
  exact mul_le_mul' hs ht

/-! ## 2. The union bound over the malignant-pair set

An extended rectangle is bad exactly when some malignant pair fails jointly, so
its failure event is the union over the malignant-pair set. The union bound
turns the per-pair estimate into `|F| * ε ^ 2`.
-/

/-- **The AGP union bound.** If every pair in the malignant set `F` fails jointly
with probability at most `ε ^ 2`, the ex-Rec fails with probability at most
`F.card * ε ^ 2`.

No independence is needed *here*: independence is what supplies the hypothesis,
and it is isolated in `malignant_pair_indep_le` so the two ingredients stay
separable. -/
theorem measure_malignant_union_le
    {μ : Measure Ω} (fail : ι → Set Ω) (F : Finset (ι × ι)) {ε : ENNReal}
    (hpair : ∀ p ∈ F, μ (fail p.1 ∩ fail p.2) ≤ ε ^ 2) :
    μ (⋃ p ∈ F, fail p.1 ∩ fail p.2) ≤ (F.card : ENNReal) * ε ^ 2 := by
  calc μ (⋃ p ∈ F, fail p.1 ∩ fail p.2)
      ≤ ∑ p ∈ F, μ (fail p.1 ∩ fail p.2) := measure_biUnion_finset_le F _
    _ ≤ ∑ _p ∈ F, ε ^ 2 := Finset.sum_le_sum hpair
    _ = (F.card : ENNReal) * ε ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## 3. The recursion step, derived

Composing §1 and §2: under local stochastic noise at rate `ε`, an ex-Rec whose
malignant-pair set has cardinality `A` is bad with probability at most
`A * ε ^ 2`. This is the AGP level recursion of Eq. (agp-recursion).
-/

/-- **The AGP recursion step, derived from the ex-Rec structure.**

Given a malignant-pair set `F`, a per-location failure bound `ε`, and pairwise
independence within each malignant pair, the ex-Rec's failure probability is at
most `F.card * ε ^ 2`.

This is the statement `Chernoff.agpRecursionStep` names and `Concatenation.lean`
previously assumed by definition. -/
theorem exRecFailure_le_agpRecursionStep
    {μ : Measure Ω} (fail : ι → Set Ω) (F : Finset (ι × ι)) {ε : ENNReal}
    (hrate : ∀ i, μ (fail i) ≤ ε)
    (hindep : ∀ p ∈ F, IndepSet (fail p.1) (fail p.2) μ) :
    μ (⋃ p ∈ F, fail p.1 ∩ fail p.2) ≤ (F.card : ENNReal) * ε ^ 2 :=
  measure_malignant_union_le fail F
    (fun p hp => malignant_pair_indep_le (hindep p hp) (hrate p.1) (hrate p.2))

/-- **The same bound from SUB-multiplicativity, which is all the proof uses.**

⚠️ `IndepSet` is an EQUALITY — `μ (s ∩ t) = μ s * μ t` — and the union bound needs
only `≤`. Demanding exact independence excludes every negatively-correlated noise
model, and those are precisely the models the AGP bound is supposed to cover:
local stochastic noise gives sub-multiplicativity in general, not independence.

`malignant_pair_indep_le` remains the adapter for the genuinely independent case,
so nothing that had independence loses anything; this is strictly more general. -/
theorem exRecFailure_le_agpRecursionStep_of_submul
    {μ : Measure Ω} (fail : ι → Set Ω) (F : Finset (ι × ι)) {ε : ENNReal}
    (hrate : ∀ i, μ (fail i) ≤ ε)
    (hsubmul : ∀ p ∈ F, μ (fail p.1 ∩ fail p.2) ≤ μ (fail p.1) * μ (fail p.2)) :
    μ (⋃ p ∈ F, fail p.1 ∩ fail p.2) ≤ (F.card : ENNReal) * ε ^ 2 :=
  measure_malignant_union_le fail F (fun p hp =>
    (hsubmul p hp).trans (by rw [sq]; exact mul_le_mul' (hrate p.1) (hrate p.2)))

/-- Independence implies the sub-multiplicativity the bound actually needs, so the
general form above subsumes the independent case. -/
theorem submul_of_indepSet
    {μ : Measure Ω} {s t : Set Ω} (h : IndepSet s t μ) :
    μ (s ∩ t) ≤ μ s * μ t :=
  le_of_eq h.measure_inter_eq_mul

/-! ## 4. Consistency with the counting bound

The malignant-pair count refines the naive "any two locations" count: `F` is a
subset of the pairs available, so the derived bound is at least as tight as
`pairFailureBound`. This connects the derived statement to the abstract one
`Chernoff.lean` ships. -/

/-- **Monotone in the CARD**, which is the form a caller with `card ≤ A` needs.

⚠️ `agp_bound_mono_malignant_set` below is monotone in the SET (`F ⊆ G`), and
`ConcatenatedComposition`'s proof has `(malignant L j).card ≤ A` with no ambient
`G` — so its comment named a lemma that was a different statement and re-derived
this one inline. Backing a docstring cross-reference with an actual call is rule 3
of the preemptive-strengthening discipline; this is the lemma that makes the call
possible. -/
theorem agp_bound_mono_card {n m : ℕ} (ε : ENNReal) (h : n ≤ m) :
    (n : ENNReal) * ε ^ 2 ≤ (m : ENNReal) * ε ^ 2 := by
  have hnm : (n : ENNReal) ≤ (m : ENNReal) := by exact_mod_cast h
  gcongr

/-- The derived bound is monotone in the malignant-pair set: a refinement that
counts fewer pairs gives a tighter bound. Now DERIVED from the card form, so the
two cannot drift. -/
theorem agp_bound_mono_malignant_set
    (F G : Finset (ι × ι)) (ε : ENNReal) (hFG : F ⊆ G) :
    (F.card : ENNReal) * ε ^ 2 ≤ (G.card : ENNReal) * ε ^ 2 :=
  agp_bound_mono_card ε (Finset.card_le_card hFG)

/-! ## 5. The bridge to `ExRec.exRecFailureBound`

`ExRec.lean` defines

    `exRecFailureBound A ε := A * ε ^ 2`

and its docstring calls it *"the leading-order Chernoff-like bound from union
bound on malignant pairs"*. Until now nothing proved that any probability
satisfies it: `ExRec` carries a location COUNT, `MalignantPairAttestation`
carries a malignant-pair COUNT, and neither mentions a measure. The whole layer
was combinatorial bookkeeping, which is why the threshold theorem's closure did
not reach it.

The theorem below supplies the missing content: given a probability model whose
malignant-pair set has cardinality `att.A`, the ex-Rec's failure probability
really is at most `exRecFailureBound att.A ε`.
-/

open scoped ENNReal

/-- **`exRecFailureBound` is a bound on an actual probability.**

For a probability measure `μ`, a malignant-pair set `F` with `F.card = att.A`,
a per-location failure bound `ε`, and independence within each malignant pair,
the probability that the ex-Rec is bad is at most `exRecFailureBound att.A ε`.

This is the statement `ExRec.lean`'s docstring asserts and does not prove, and
it is what makes the AGP recursion a derived inequality rather than a
definition. -/
theorem exRecFailureProb_le_exRecFailureBound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {R : ExRec} (att : MalignantPairAttestation R)
    (fail : ι → Set Ω) (F : Finset (ι × ι)) (hcard : F.card = att.A)
    {ε : NNReal}
    (hrate : ∀ i, μ (fail i) ≤ (ε : ENNReal))
    (hindep : ∀ p ∈ F, IndepSet (fail p.1) (fail p.2) μ) :
    (μ (⋃ p ∈ F, fail p.1 ∩ fail p.2)).toReal
      ≤ exRecFailureBound att.A (ε : ℝ) := by
  have hle : μ (⋃ p ∈ F, fail p.1 ∩ fail p.2) ≤ (F.card : ENNReal) * (ε : ENNReal) ^ 2 :=
    exRecFailure_le_agpRecursionStep fail F hrate hindep
  have hfin : (F.card : ENNReal) * (ε : ENNReal) ^ 2 ≠ ⊤ := by
    simp [ENNReal.mul_eq_top]
  have := ENNReal.toReal_le_toReal (measure_ne_top μ _) hfin |>.mpr hle
  refine this.trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.coe_toReal, hcard]
  rfl

end SKEFTHawking.FaultTolerance
