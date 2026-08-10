/-
SK_EFT_Hawking TODO-D35, second half: the levels, composed.

WHAT WAS STILL OPEN
-------------------
`MalignantUnionBound.lean` closed the SINGLE-level step: an ex-Rec whose
malignant-pair set has cardinality `A`, under local stochastic noise at rate `ε`,
fails with probability at most `A · ε²`. What it did not do is compose levels, so
`Concatenation.agpLevelSequence` remained *defined* by `ε_{L+1} = A · ε_L²`
rather than derived, and `DoubleExp.agp_double_exp_bound` — which already takes
the recursion as a HYPOTHESIS rather than a definition — had that hypothesis
discharged only for the sequence that satisfies it by construction.

WHAT IS PROVED HERE
-------------------
A level-`(L+1)` extended rectangle is modelled by the only structural fact the
bound needs: **it fails only when some malignant pair of its level-`L`
constituents both fail.** That is `hstruct` below, an inclusion of events, and it
is the AGP concatenation picture stated in the language of the measure space.

From it, `levelFailure_le_agpSeq` derives by induction on `L`:

    μ (fail L i) ≤ agpSeq A ε₀ L        for every level-`L` rectangle `i`

and `agpSeq_coe_eq_agpLevelSequence` identifies `agpSeq` with `Concatenation`'s
`agpLevelSequence`, so the real-valued chain up to `AGP/Threshold.lean` now
describes a genuine failure probability rather than an abstract sequence.
`concatenated_failure_double_exp` and `steane_concatenated_failure_below_threshold`
are the two consequences a reader of D6 §7 actually wants.

SCOPE — read before quoting this
--------------------------------
Two things remain pinned, and both are deliberate:

* **`A` is a hypothesis, not a derivation.** `hcard` says each level's
  malignant-pair set has cardinality `A`; for the Steane CNOT ex-Rec
  `A_CNOT = 35235` is still pinned to AGP 2006 §8.3 eq. (36) in `Counting.lean`.
  Deriving it is a combinatorial enumeration over a concrete circuit.
* **`hstruct` and `hindep` are modelling assumptions, stated as hypotheses so a
  reader can see exactly what the derivation rests on.** They are the AGP noise
  model's content, not consequences of it proved here.

⚠️ `agp_threshold_steane` itself is a statement about real numbers and cannot
"consume" a measure. What closes the gap is that the *probabilistic* capstone
below reaches both this module and that one in a single dependency closure.

Primary source: Aliferis-Gottesman-Preskill 2006, arXiv:quant-ph/0504218 §4, §8.3.
-/

import Mathlib
import SKEFTHawking.FaultTolerance.MalignantUnionBound
import SKEFTHawking.FaultTolerance.Concatenation
import SKEFTHawking.FaultTolerance.AGP.Threshold

set_option autoImplicit false

namespace SKEFTHawking.FaultTolerance

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## 1. The level sequence over `ℝ≥0`

`Concatenation.agpLevelSequence` lives in `ℝ`, where the induction below would
carry a nonnegativity side condition at every step, and the measure lives in
`ℝ≥0∞`, where it would carry a finiteness one. `ℝ≥0` has neither: it coerces
into `ℝ≥0∞` as a semiring and into `ℝ` as the sequence the threshold theorem
already reasons about, so it is the type that lets one induction serve both.
-/

/-- The AGP level sequence, valued in `ℝ≥0`. Same recursion as
`agpLevelSequence`; `agpSeq_coe_eq_agpLevelSequence` identifies them. -/
def agpSeq (A ε₀ : NNReal) : ℕ → NNReal
  | 0 => ε₀
  | L + 1 => A * (agpSeq A ε₀ L) ^ 2

@[simp] theorem agpSeq_zero (A ε₀ : NNReal) : agpSeq A ε₀ 0 = ε₀ := rfl

@[simp] theorem agpSeq_succ (A ε₀ : NNReal) (L : ℕ) :
    agpSeq A ε₀ (L + 1) = A * (agpSeq A ε₀ L) ^ 2 := rfl

/-- The two sequences are the same sequence. This is the bridge that lets the
probabilistic bound below be read against `AGP/Threshold.lean`'s conclusions. -/
theorem agpSeq_coe_eq_agpLevelSequence (A ε₀ : NNReal) (L : ℕ) :
    ((agpSeq A ε₀ L : ℝ)) = agpLevelSequence (A : ℝ) (ε₀ : ℝ) L := by
  induction L with
  | zero => simp [agpLevelSequence_zero]
  | succ L ih => rw [agpSeq_succ, agpLevelSequence_succ, ← ih]; push_cast; ring

/-! ## 2. The concatenation hypothesis, and the induction

`hstruct` is the whole model: a level-`(L+1)` rectangle's failure event is
contained in the union, over malignant pairs of its level-`L` constituents, of
the events where both constituents fail. Everything else is the single-level
bound applied at each level with the previous level's rate.
-/

/-- **The composed bound.** Every level-`L` extended rectangle fails with
probability at most `agpSeq A ε₀ L`, derived level by level from the single-level
union bound rather than assumed.

The hypotheses are exactly the AGP model: a base-level rate (`hbase`), a constant
malignant-pair count bound (`hcard`), the concatenation structure (`hstruct`), and
sub-multiplicativity of constituent failures (`hsubmul`).

⚠️ Both `hcard` and `hsubmul` are deliberately the WEAKEST forms the proof uses.
`hcard` was `= A` where only `≤ A` is needed and the bound is monotone in the
card; `hsubmul` was full `IndepSet`, an equality, where only `μ (s ∩ t) ≤ μ s * μ t`
is needed. Independence excludes negatively-correlated noise, and equality on the
card excludes any ex-Rec whose malignant set is a proper subset of the available
pairs — that is, all of them. `submul_of_indepSet` converts an independent model,
so nothing that had the stronger hypotheses loses anything. -/
theorem levelFailure_le_agpSeq
    {μ : Measure Ω} {Loc : ℕ → Type*}
    (fail : ∀ L, Loc L → Set Ω)
    (malignant : ∀ L, Loc (L + 1) → Finset (Loc L × Loc L))
    (A : ℕ) (ε₀ : NNReal)
    (hbase : ∀ i, μ (fail 0 i) ≤ (ε₀ : ENNReal))
    (hcard : ∀ L j, (malignant L j).card ≤ A)
    (hstruct : ∀ L j,
      fail (L + 1) j ⊆ ⋃ p ∈ malignant L j, fail L p.1 ∩ fail L p.2)
    (hsubmul : ∀ L j, ∀ p ∈ malignant L j,
      μ (fail L p.1 ∩ fail L p.2) ≤ μ (fail L p.1) * μ (fail L p.2)) :
    ∀ L, ∀ i, μ (fail L i) ≤ ((agpSeq (A : NNReal) ε₀ L : NNReal) : ENNReal) := by
  intro L
  induction L with
  | zero => simpa using hbase
  | succ L ih =>
    intro j
    refine le_trans (measure_mono (hstruct L j)) ?_
    refine le_trans
      (exRecFailure_le_agpRecursionStep_of_submul (μ := μ) (fail L) (malignant L j)
        (ε := ((agpSeq (A : NNReal) ε₀ L : NNReal) : ENNReal)) ih (hsubmul L j)) ?_
    -- ⚠️ `hcard` is `≤`, not `=`, and the bound is MONOTONE in the card, which is
    -- exactly what `agp_bound_mono_card` states — and it is CALLED here rather than
    -- re-derived inline, because a comment naming a lemma it does not invoke is the
    -- rot rule 3 of the preemptive-strengthening discipline exists to stop. (Its
    -- sibling `agp_bound_mono_malignant_set` is monotone in the SET, which is a
    -- different statement and does not apply at this call site.) A real ex-Rec's
    -- malignant set is a SUBSET of the pairs available, so `≤ A` is what it can
    -- supply; demanding equality made the hypothesis unsatisfiable for the models
    -- the theorem is about.
    refine le_trans (agp_bound_mono_card _ (hcard L j)) ?_
    rw [agpSeq_succ]
    push_cast
    exact le_rfl

/-! ## 3. What the composition buys

The two statements a reader of D6 §7 wants, now about a probability rather than
about a sequence: double-exponential suppression, and — below the Steane
threshold — a failure probability driven to zero.
-/

/-- **Double-exponential suppression of a genuine failure probability.**
`A · P[level-L rectangle fails] ≤ (A ε₀)^{2^L}`. -/
theorem concatenated_failure_double_exp
    {μ : Measure Ω} {Loc : ℕ → Type*}
    (fail : ∀ L, Loc L → Set Ω)
    (malignant : ∀ L, Loc (L + 1) → Finset (Loc L × Loc L))
    (A : ℕ) (ε₀ : NNReal)
    (hbase : ∀ i, μ (fail 0 i) ≤ (ε₀ : ENNReal))
    (hcard : ∀ L j, (malignant L j).card ≤ A)
    (hstruct : ∀ L j,
      fail (L + 1) j ⊆ ⋃ p ∈ malignant L j, fail L p.1 ∩ fail L p.2)
    (hsubmul : ∀ L j, ∀ p ∈ malignant L j,
      μ (fail L p.1 ∩ fail L p.2) ≤ μ (fail L p.1) * μ (fail L p.2)) :
    ∀ L, ∀ i, (A : ℝ) * (μ (fail L i)).toReal ≤ ((A : ℝ) * (ε₀ : ℝ)) ^ (2 ^ L) := by
  intro L i
  have hbound := levelFailure_le_agpSeq fail malignant A ε₀ hbase hcard hstruct hsubmul L i
  have htoReal : (μ (fail L i)).toReal ≤ (agpSeq (A : NNReal) ε₀ L : ℝ) :=
    ENNReal.toReal_le_coe_of_le_coe hbound
  have hcast : (((A : NNReal)) : ℝ) = (A : ℝ) := by push_cast; ring
  rw [agpSeq_coe_eq_agpLevelSequence, hcast] at htoReal
  calc (A : ℝ) * (μ (fail L i)).toReal
      ≤ (A : ℝ) * agpLevelSequence (A : ℝ) (ε₀ : ℝ) L :=
        mul_le_mul_of_nonneg_left htoReal (by positivity)
    _ ≤ ((A : ℝ) * (ε₀ : ℝ)) ^ (2 ^ L) :=
        agpLevelSequence_double_exp_bound (A : ℝ) (ε₀ : ℝ)
          (by positivity) (by positivity) L

/-- **Below the Steane threshold, the composed failure probability is suppressed
to zero.** This is the statement whose dependency closure reaches BOTH the
measure-theoretic union bound of `MalignantUnionBound.lean` AND the real-valued
threshold chain of `AGP/Threshold.lean` — which is what "the recursion is
machine-checked from the ex-Rec structure" means. -/
theorem steane_concatenated_failure_below_threshold
    {μ : Measure Ω} {Loc : ℕ → Type*}
    (fail : ∀ L, Loc L → Set Ω)
    (malignant : ∀ L, Loc (L + 1) → Finset (Loc L × Loc L))
    (ε₀ : NNReal)
    (hbase : ∀ i, μ (fail 0 i) ≤ (ε₀ : ENNReal))
    (hcard : ∀ L j, (malignant L j).card ≤ steaneMalignancyCounts.A_CNOT)
    (hstruct : ∀ L j,
      fail (L + 1) j ⊆ ⋃ p ∈ malignant L j, fail L p.1 ∩ fail L p.2)
    (hsubmul : ∀ L j, ∀ p ∈ malignant L j,
      μ (fail L p.1 ∩ fail L p.2) ≤ μ (fail L p.1) * μ (fail L p.2))
    (hbelow : (ε₀ : ℝ) < AGP.steaneAGPThreshold) :
    ∀ L, 1 ≤ L → ∀ i,
      (steaneMalignancyCounts.A_CNOT : ℝ) * (μ (fail L i)).toReal < 1 := by
  intro L hL i
  have hbound := levelFailure_le_agpSeq fail malignant
    steaneMalignancyCounts.A_CNOT ε₀ hbase hcard hstruct hsubmul L i
  have htoReal :
      (μ (fail L i)).toReal
        ≤ (agpSeq ((steaneMalignancyCounts.A_CNOT : ℕ) : NNReal) ε₀ L : ℝ) :=
    ENNReal.toReal_le_coe_of_le_coe hbound
  have hcast : ((((steaneMalignancyCounts.A_CNOT : ℕ)) : NNReal) : ℝ)
      = (steaneMalignancyCounts.A_CNOT : ℝ) := by push_cast; ring
  rw [agpSeq_coe_eq_agpLevelSequence, hcast] at htoReal
  calc (steaneMalignancyCounts.A_CNOT : ℝ) * (μ (fail L i)).toReal
      ≤ (steaneMalignancyCounts.A_CNOT : ℝ)
          * agpLevelSequence (steaneMalignancyCounts.A_CNOT : ℝ) (ε₀ : ℝ) L :=
        mul_le_mul_of_nonneg_left htoReal (by positivity)
    _ < 1 := AGP.agp_threshold_steane_strict (ε₀ : ℝ) (by positivity) hbelow L hL

/-! ## 4. Non-vacuity

Both results above are conditional on four hypotheses, and a conditional theorem
whose hypotheses cannot all hold at once proves nothing. The witness below
exhibits a measure space and a level structure satisfying every one of them, for
an arbitrary `A` and an arbitrary base rate.

⚠️ **What this does and does not show.** It shows the hypothesis set is
*satisfiable*, which is what rules out vacuity. It does NOT exhibit a model in
which the bound is tight — that needs a genuine independent product space over
the circuit's locations, and building one is the same construction as deriving
`A_CNOT` itself.
-/

/-- **The hypothesis set is satisfiable**, in the shape the theorems now take
(`hcard` as `≤`, `hsubmul` rather than full independence) PLUS off-diagonality,
which is strictly more than any of them requires — so neither
`levelFailure_le_agpSeq` nor its corollaries is conditionally empty.

⚠️ **THE MALIGNANT PAIRS ARE OFF-DIAGONAL, and that is not cosmetic.** This
witness used `fun i => (i, i)`. A diagonal pair is not a pair of two distinct
locations at all — AGP's malignant set counts pairs of *different* locations —
and under the old `IndepSet` hypothesis it was worse than wrong: `IndepSet s s μ`
forces `μ s = (μ s)²`, i.e. `μ s ∈ {0, 1}`, so a diagonal malignant set could
never be satisfied by any nondegenerate failure event. The witness proved the
hypotheses non-empty only in the corner where the theorem says nothing.

⚠️ **What this still does NOT show, stated rather than implied.** `fail ≡ ∅`
makes every probability `0`, so `hbase` is satisfied without being exercised: the
witness rules out vacuity, it does not exhibit a model in which the bound is
approached. A model with a strictly positive base rate needs a genuine
independent product space over the circuit's locations — the same construction as
deriving `A_CNOT` itself, which `MalignantUnionBound.lean`'s scope note already
records as a separate undertaking. Building it is open work, not a closed gap. -/
theorem levelFailure_hypotheses_satisfiable
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℕ) (ε₀ : NNReal) :
    ∃ (Loc : ℕ → Type) (fail : ∀ L, Loc L → Set Ω)
      (malignant : ∀ L, Loc (L + 1) → Finset (Loc L × Loc L)),
      (∀ i, μ (fail 0 i) ≤ (ε₀ : ENNReal)) ∧
      (∀ L j, (malignant L j).card ≤ A) ∧
      (∀ L j, fail (L + 1) j ⊆ ⋃ p ∈ malignant L j, fail L p.1 ∩ fail L p.2) ∧
      (∀ L j, ∀ p ∈ malignant L j, p.1 ≠ p.2) ∧
      (∀ L j, ∀ p ∈ malignant L j,
        μ (fail L p.1 ∩ fail L p.2) ≤ μ (fail L p.1) * μ (fail L p.2)) := by
  -- `Fin A × Bool` gives every level at least two DISTINCT locations to pair, so
  -- the malignant set is off-diagonal for every `A ≥ 1` — and vacuously so at
  -- `A = 0`, where the type is empty and the malignant set is too.
  refine ⟨fun _ => Fin A × Bool, fun _ _ => (∅ : Set Ω),
          fun _ _ => (Finset.univ : Finset (Fin A)).map
            ⟨fun i => ((i, false), (i, true)), ?_⟩,
          ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    simpa using congrArg (fun q => q.1.1) h
  · intro i; simp
  · intro L j; simp
  · intro L j; simp
  · intro L j p hp
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
      true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    simp
  · intro L j p _
    simp

end SKEFTHawking.FaultTolerance
