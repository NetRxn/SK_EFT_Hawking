/-
Phase 5q Wave 5: Ext → Bordism Bridge with Decomposed Hypotheses

## ⚠⚠ VACUITY DISCLOSURE — READ FIRST (added 2026-07-21, atlas-integrity repair;
## H4 REMEDIATED 2026-07-21, same day — see below)

**`H1_ko_cohomology`, `H2_change_of_rings` and `H3_ass_collapses` are each literally `:= True`.**
They are PROSE MARKERS carrying **zero formal content**, not propositions.

**`H4_abp_splitting` is no longer one of them.** It was rebuilt (not renamed, not narrowed) into the
genuine Prop `Nonempty SpinBordismData` — the actual degree-4 ABP output: an abelian group with
`≃+ ℤ`, a signature homomorphism, and the K3 normalisation `σ = -16` (`SpinBordism.lean:46`).  It is
**non-vacuous and load-bearing**: `rokhlin_from_H4` below consumes it to derive `16 ∣ σ` through the
already-proved `SpinBordism.rokhlin_from_bordism`.  H4 remains *undischarged* (nothing in-tree
constructs a `SpinBordismData` — Thom-spectrum theory, ADR-003), which is the honest disclosed-Prop
status, not vacuity.

Consequently, for the three that remain:

* **`generation_constraint_chain` is NOT conditional on them.** Its `(h1 … h4)` binders are
  decorative — the proof body `clear`s all four and closes by `omega` from `h_mod : 24 ∣ 8 * N_f`
  alone. (This stays true of `h4` too: the *arithmetic* step genuinely does not need it, even now
  that H4 has content.  H4's real consumer is `rokhlin_from_H4`.)  H1–H3 can each be supplied with
  `trivial`; this is made kernel-visible by `extBordismBridge_hypotheses_are_vacuous` below.
* **This module PROVES none of the spectrum / cohomology / change-of-rings / ASS-collapse /
  ABP-splitting statements described in the docstrings below.** It now *states* one of them (H4);
  it discharges none. For H1–H3 the docstrings state real mathematics that the Lean declarations
  beneath them do not carry at all.
* **They are NOT "tracked in `HYPOTHESIS_REGISTRY`."** Verified 2026-07-21: no entry for any of
  H1–H4 exists in `HYPOTHESIS_REGISTRY` (`src/core/constants.py`), and their names do not match the
  `tracked_hypothesis_ledger` gate's detection pattern, so they were never ledger-enforced either.
  The claim to the contrary appeared in this docstring and in §3 below; both are corrected. Now
  that H4 carries a real type it is *eligible* for the ledger; H1–H3 are not (a `True` marker has
  nothing to track — registering them would require first giving them real types).
* **Do NOT cite this module as a decomposition of the spin-bordism input into "four focused
  hypotheses, each independently verifiable" or as "replacing one monolithic claim with strictly
  smaller inputs."** As of this remediation the count is **one** genuine disclosed hypothesis (H4)
  plus three `True` markers — not four focused hypotheses, and not a replacement of
  `SpinBordismData` by anything smaller (H4 *is* `Nonempty SpinBordismData`). The genuine,
  machine-checked content of this Phase-5q lane remains the A(1)-Ext computation itself
  (`A1Ext.lean`) and the final arithmetic step.
* **Do NOT copy the "H1–H3 `True`-marker pattern" as a template.** Where a Prop must be disclosed,
  state it — cf. `PinPlusExtBound.DeltaTruncationCap` (a genuine Prop, `16 • [ℝP⁴] = 0`) and now
  `H4_abp_splitting` itself, which is the corrected in-module exemplar.

Discharging H1/H3 for real needs Thom-spectrum / stable-homotopy infrastructure that is
Mathlib-absent (ADR-003, trigger-gated); the same is true of *discharging* H4, though H4 is at
least now honestly stated. H2 is algebraic and has a partial in-tree treatment in
`ChangeOfRings.lean` — though note `ChangeOfRings.h2_discharged_TODO : True := trivial` is itself a
placeholder of the same kind. The honest reading of this module is "the algebraic core is
machine-checked; H4 is a real, undischarged, disclosed Prop; H1–H3 are *named in prose*, not
formalized."

---

Connects the machine-checked Ext computation (A1Ext.lean) to the spin
bordism isomorphism Ω^Spin_4 ≅ ℤ via four topological steps named in prose
(see the vacuity disclosure above — they are `True`, not hypotheses).

The intended decomposition — the mathematics the four markers *stand for*, none of it
formalized here — is the chain of explicit steps:

  Ext^n_{A(1)}(F₂, F₂) computed         [MACHINE-CHECKED: A1Ext.lean]
       ↓ (H1: ko cohomology)
  H*(ko; F₂) ≅ A ⊗_{A(1)} F₂            [HYPOTHESIS: topological]
       ↓ (H2: change of rings)
  Ext_A(H*(ko), F₂) ≅ Ext_{A(1)}(F₂,F₂) [HYPOTHESIS: algebraic, potentially provable]
       ↓ (H3: ASS collapses at E₂)
  π_n(ko) determined from E₂ page        [HYPOTHESIS: topological]
       ↓ (H4: ABP splitting)
  Ω^Spin_4 ≅ π₄(ko) ≅ ℤ                 [HYPOTHESIS: topological]
       ↓ (Rokhlin, already proved)
  16 | σ(M) for all spin 4-manifolds     [PROVED in SpinBordism.lean]
       ↓ (Wang chain, already proved)
  3 | N_f (generation constraint)        [PROVED in GenerationConstraint.lean]

Each hypothesis is statable without importing topology:
  H1 is about a specific spectrum's mod-2 cohomology
  H2 is a standard adjunction (Shapiro's lemma)
  H3 is comparison with Bott periodicity
  H4 is the Anderson-Brown-Peterson splitting theorem (1967)

HYPOTHESIS TRACKING (corrected 2026-07-21):
  NONE of the four is tracked in HYPOTHESIS_REGISTRY (constants.py) — verified by direct lookup.
  The previous text here claimed all four were. They are `True`-valued prose markers, so there is
  nothing for the ledger to track; registering them would require first giving them real types.
  The eliminability / circularity notes below remain accurate as MATHEMATICAL commentary
  (H2 = algebraic/potentially provable, H1/H3/H4 = topological; ABP historically tangled with
  Rokhlin) — they describe the intended statements, not anything proved in this file.

References:
  A1Ring.lean, A1Resolution.lean, A1Ext.lean — machine-checked Ext computation
  SpinBordism.lean — Rokhlin from bordism data
  GenerationConstraint.lean — 3 | N_f from 24 | 8N_f
  Deep research: Lit-Search/Phase-5q/The minimal free resolution...
-/

import Mathlib
import SKEFTHawking.A1Ext
import SKEFTHawking.SpinBordism

namespace SKEFTHawking

/-! ## 1. Decomposed Topological Hypotheses

Each hypothesis is entered as a Prop parameter to theorems, not as
a global axiom. This keeps the module axiom-free and allows downstream
theorems to state their dependencies explicitly. -/

/--
**Hypothesis H1 (ko cohomology):** The connective real K-theory spectrum ko
has mod-2 cohomology that is free over A(1).

Formally: H*(ko; F₂) ≅ A ⊗_{A(1)} F₂ as a module over the Steenrod algebra A.

This is a topological fact proved by Stong (1963) and Adams (1974, Ch. 16).
It says that the Steenrod algebra acts on ko's cohomology in a specific way
determined by the subalgebra A(1).

⚠ **NOT FORMALIZED: this definition is `True`.** The statement above is the intended mathematics;
the Lean body carries none of it. See the module's VACUITY DISCLOSURE.

Eliminability: TOPOLOGICAL — requires spectrum theory not in Lean/Mathlib.
Reference: Adams, "Stable Homotopy and Generalised Homology" (1974), Ch. 16. -/
def H1_ko_cohomology : Prop :=
  True  -- ⚠ VACUOUS: prose marker only; see extBordismBridge_hypotheses_are_vacuous

/--
**Hypothesis H2 (change of rings):** The Hom-tensor adjunction gives
  Ext_A(A ⊗_{A(1)} F₂, F₂) ≅ Ext_{A(1)}(F₂, F₂)

This is purely ALGEBRAIC — it's Shapiro's lemma / the change-of-rings
isomorphism. It follows from the fact that A is free as a right A(1)-module
(Milnor-Moore: connected Hopf algebras over a field are free over sub-Hopf algebras).

Eliminability: ALGEBRAIC — potentially provable in Lean given enough
homological algebra infrastructure (Shapiro's lemma + A/A(1) freeness).
⚠ **NOT FORMALIZED: this definition is `True`.** The statement above is the intended mathematics;
the Lean body carries none of it. `ChangeOfRings.lean` is often cited as discharging H2, but its
`h2_discharged_TODO : True := trivial` is a placeholder of the same kind; what that module does
prove is dimension bookkeeping, not the change-of-rings isomorphism. See the VACUITY DISCLOSURE.

Currently absent from Mathlib; see Phase 5r roadmap.
Reference: Weibel, "An Introduction to Homological Algebra" (1994), Thm 6.10.7. -/
def H2_change_of_rings : Prop :=
  True  -- ⚠ VACUOUS: prose marker only; see extBordismBridge_hypotheses_are_vacuous

/--
**Hypothesis H3 (Adams spectral sequence collapse):** For the spectrum ko,
the Adams spectral sequence collapses at E₂ — there are no differentials.

This follows from comparison with the known homotopy groups π_*(ko)
computed via Bott periodicity: ℤ, ℤ/2, ℤ/2, 0, ℤ, 0, 0, 0, ℤ, ...
(period 8). Since the E₂ page matches these groups, there is no room
for differentials.

⚠ **NOT FORMALIZED: this definition is `True`.** The statement above is the intended mathematics;
the Lean body carries none of it. See the module's VACUITY DISCLOSURE.

Eliminability: TOPOLOGICAL — requires ASS construction + Bott periodicity.
Reference: Ravenel, "Complex Cobordism" (2003), Ch. 3. -/
def H3_ass_collapses : Prop :=
  True  -- ⚠ VACUOUS: prose marker only; see extBordismBridge_hypotheses_are_vacuous

/--
**Hypothesis H4 (Anderson-Brown-Peterson splitting):** At the prime 2,
the Thom spectrum MSpin splits as a wedge of suspensions of ko and
Eilenberg-MacLane spectra. In degrees < 8, this gives:
  π_n(MSpin)₍₂₎ ≅ π_n(ko)₍₂₎

Combined with the absence of odd torsion (MSpin → MSO is an equivalence
after inverting 2), this yields Ω^Spin_n ≅ π_n(ko) for n < 8.

Eliminability: TOPOLOGICAL — requires Thom spectrum theory.
Reference: Anderson-Brown-Peterson, Ann. Math. 86, 256 (1967).

CIRCULARITY NOTE: The ABP computation historically used Rokhlin-equivalent
facts. We document this clearly — the derivation is logically valid
(the hypothesis IMPLIES Rokhlin, so there's no circularity in the
formal proof) but the historical provenance is tangled.

✅ **FORMALIZED (2026-07-21).** This hypothesis is no longer a `True` marker.  It is now the
genuine, non-vacuous Prop `Nonempty SpinBordismData` — i.e. the assertion that the degree-4
output of ABP actually exists as data: an abelian group `Bordism`, an isomorphism
`isoZ : Bordism ≃+ ℤ` (this is `Ω^Spin_4 ≅ ℤ`), a signature homomorphism, and the K3 normalisation
`σ(isoZ.symm 1) = -16` (`SpinBordism.lean:46`).  That is exactly the content H4 is invoked for
downstream, and it is what the whole ABP step is *for*.

Because the Prop is now real, the circularity note above regains its force: the hypothesis does
now imply Rokhlin, and `rokhlin_from_H4` below is that implication, discharged through the
already-proved `SpinBordism.rokhlin_from_bordism`.  H4 remains **undischarged** (nothing in-tree
constructs a `SpinBordismData`; that needs Thom-spectrum theory, ADR-003) — but it is now an
honest disclosed Prop in the sense of `PinPlusExtBound.DeltaTruncationCap`, not a vacuity. -/
def H4_abp_splitting : Prop :=
  Nonempty SpinBordismData

/-! ## 2. The Bridge Theorem

Given the machine-checked Ext computation AND the four hypotheses,
we can derive the generation constraint.

The logical chain:
  Ext computation (A1Ext.lean)    — MACHINE-CHECKED
  + H1 (ko cohomology)           — HYPOTHESIS
  + H2 (change of rings)         — HYPOTHESIS (algebraic)
  + H3 (ASS collapses)           — HYPOTHESIS
  ⟹ π₄(ko) ≅ ℤ                  — follows from infinite h₀-tower in stem 4

  + H4 (ABP splitting)           — HYPOTHESIS
  ⟹ Ω^Spin_4 ≅ ℤ                — follows from ABP in degree 4

  + K3 has σ = -16               — HYPOTHESIS (concrete existence)
  ⟹ 16 | σ (Rokhlin)            — PROVED in SpinBordism.lean

  + c₋ = 8N_f (SM content)       — PROVED in WangBridge.lean
  + 24 | c₋ (modular invariance) — PROVED in ModularInvarianceConstraint.lean
  ⟹ 3 | N_f                     — PROVED in GenerationConstraint.lean
-/

/-- The Ext computation provides the algebraic input to the bordism chain.
    Ext^4_{A(1)}(F₂, F₂) has dimension 3, with an infinite h₀-tower in stem 4.
    This is MACHINE-CHECKED in A1Ext.lean (zero sorry). -/
theorem ext_algebraic_input :
    -- Chain complex verified (d² = 0 at all levels)
    A1.d1 * A1.d2 = 0 ∧ A1.d2 * A1.d3 = 0 ∧ A1.d3 * A1.d4 = 0 ∧ A1.d4 * A1.d5 = 0
    -- Minimality verified (differentials in augmentation ideal)
    ∧ (∀ j : Fin 16, A1.d1 0 j = 0) :=
  ⟨A1.d1_d2_zero, A1.d2_d3_zero, A1.d3_d4_zero, A1.d4_d5_zero, A1.d1_minimal⟩

/-- **⚠ NOT conditional on H1–H4** (docstring corrected 2026-07-21; the previous text claimed it was).
`H1_ko_cohomology`, `H2_change_of_rings`, `H3_ass_collapses` are each `:= True`
(`extBordismBridge_hypotheses_are_vacuous`); `H4_abp_splitting` is real but **unused here**. All
four binders are decorative for *this* theorem: the proof body below `clear`s all four and closes by
`omega` from `h_mod : 24 ∣ 8 * N_f` alone. What this theorem actually proves is the ARITHMETIC step
`24 ∣ 8 * N_f → 3 ∣ N_f` — which is real, and is the honest content to cite.

The intended reading — Ω^Spin_4 ≅ ℤ from the Ext computation given H1–H4, hence Rokhlin, hence
(with the Wang bridge + modular invariance) 3 ∣ N_f — is documented mathematics, NOT what the
binders enforce here. The binders are retained so the intended chain stays visible at the call site
and so this declaration's API does not change; they must not be presented as tracked hypotheses.
For the one step of that chain that IS now machine-backed, see `rokhlin_from_H4`.
See the module's VACUITY DISCLOSURE. -/
theorem generation_constraint_chain
    (h1 : H1_ko_cohomology)
    (h2 : H2_change_of_rings)
    (h3 : H3_ass_collapses)
    (h4 : H4_abp_splitting)
    (N_f : ℕ)
    (h_mod : 24 ∣ (8 * N_f : ℤ))  -- from modular invariance + c₋ = 8N_f
    : 3 ∣ N_f := by
  -- The hypotheses h1-h4 document the logical chain:
  -- H1+H2+H3 give π₄(ko) ≅ ℤ from the Ext data (A1Ext.lean).
  -- H4 gives Ω^Spin_4 ≅ π₄(ko) ≅ ℤ.
  -- Rokhlin (SpinBordism.lean) gives 16 | σ.
  -- The final arithmetic step (24 | 8N_f → 3 | N_f) is self-contained:
  clear h1 h2 h3 h4  -- topological hypotheses used upstream, not in arithmetic
  omega

/-- **⚠ H1, H2, H3 ARE STILL FREE — kernel-visible.** Each of `H1_ko_cohomology`,
`H2_change_of_rings`, `H3_ass_collapses` is definitionally `True`, so this conjunction is provable
outright by `trivial`. No consumer gains any content by supplying them.

This theorem exists so the remaining vacuity is **machine-checked and impossible to miss**, rather
than a docstring caveat a reader can skip: if any of H1–H3 is ever given a real type, this proof
stops compiling, which is precisely the alarm one wants.

**The alarm has already fired once, and correctly.** This statement formerly included
`H4_abp_splitting`.  H4 was upgraded on 2026-07-21 from `True` to the genuine
`Nonempty SpinBordismData`, so it is no longer provable here and has been dropped from the
conjunction — the conjunction shrank because the *substrate grew*, which is the intended
direction.  H4's real content and its real consumer are `H4_abp_splitting` and `rokhlin_from_H4`.

It asserts vacuity of H1–H3; it does **not** assert that the underlying mathematics is false — H1
and H3 are true theorems of algebraic topology (Adams; Bott) and H2 is a standard change-of-rings
isomorphism. They are simply not formalized here. -/
theorem extBordismBridge_hypotheses_are_vacuous :
    H1_ko_cohomology ∧ H2_change_of_rings ∧ H3_ass_collapses :=
  ⟨trivial, trivial, trivial⟩

/-- **H4 has real content — kernel-checked.** Supplying `H4_abp_splitting` now genuinely buys
Rokhlin's theorem: the degree-4 ABP output `SpinBordismData` determines a group in which every
element's signature is divisible by 16, via the already-proved `SpinBordism.rokhlin_from_bordism`.

This is the P6 discipline applied to the module's own chain diagram: the docstring step
"H4 ⟹ Ω^Spin_4 ≅ ℤ ⟹ 16 ∣ σ" is now **backed by an actual Lean call**, not merely asserted in
prose.  Contrast `generation_constraint_chain`, whose `h4` binder is still not used in its body —
the final arithmetic step genuinely does not need it. -/
theorem rokhlin_from_H4 (h4 : H4_abp_splitting) :
    ∃ D : SpinBordismData, ∀ M : D.Bordism, 16 ∣ D.signature M := by
  obtain ⟨D⟩ := h4
  exact ⟨D, rokhlin_from_bordism D⟩

/-- Hypothesis inventory for the generation constraint.
    ⚠ **This theorem is a numeral tautology** (`6 = 6 ∧ 3 = 3 ∧ 0 = 0`, closed by `rfl`): it records
    counts in its comments, but asserts nothing about the module and would still hold if every count
    were wrong. Read the comments as documentation, never as a verified inventory.
    ⚠ The "H2 DISCHARGED" note is also unreliable — see `H2_change_of_rings`'s docstring.
    Machine-checked: Ext computation, chain complex, minimality, change-of-rings, Wang chain, generation.
    Hypotheses: 3 topological inputs (H1, H3, H4). H2 DISCHARGED (ChangeOfRings.lean). -/
theorem hypothesis_inventory :
    -- Number of machine-checked components
    (6 : ℕ) = 6  -- d²=0 + minimality + Ext dims + change-of-rings + Wang chain + generation
    -- Number of topological hypotheses (H2 discharged)
    ∧ (3 : ℕ) = 3  -- H1, H3, H4
    -- Of which algebraically eliminable
    ∧ (0 : ℕ) = 0  -- H2 was the algebraic one; now discharged
    := ⟨rfl, rfl, rfl⟩

/-! ## 3. Comparison: Before and After

BEFORE (SpinBordism.lean alone):
  N_f ≡ 0 mod 3, conditional on ONE opaque hypothesis:
    SpinBordismData (packages Ω^Spin_4 ≅ ℤ + σ(K3) = -16)

AFTER (with A1Ext.lean + ExtBordismBridge.lean) — ⚠ CORRECTED 2026-07-21, H4 REMEDIATED same day:
  N_f ≡ 0 mod 3, with:
    - Machine-checked: Ext computation (resolution, d²=0, minimality, dimensions). REAL.
    - 1 GENUINE disclosed hypothesis:
      H4: ABP splitting in low degrees (Anderson-Brown-Peterson 1967)
          := Nonempty SpinBordismData — a real, non-vacuous Prop; consumed by `rokhlin_from_H4`
          to derive 16 ∣ σ. Undischarged (needs Thom spectra, ADR-003), but honestly stated.
          Eligible for HYPOTHESIS_REGISTRY; not yet entered there.
    - 3 topological steps NAMED IN PROSE (H1-H3). ⚠ Each is `:= True` — NOT formalized, NOT
      independently verifiable in Lean, NOT tracked in HYPOTHESIS_REGISTRY:
      H1: ko cohomology (Adams 1974)
      H2: change of rings (Shapiro's lemma — ALGEBRAIC, potentially provable)
      H3: ASS collapses for ko (Bott periodicity comparison)

The honest improvement: the algebraic core (WHY 16) is machine-checked; H4 is a real disclosed
Prop with a real consumer; H1-H3 are NAMED and referenced only. This is still NOT a decomposition
"into minimal, transparent pieces", and it does NOT replace the opaque `SpinBordismData` with
"strictly smaller inputs" — H4 *is* `Nonempty SpinBordismData`, the same input, now honestly typed;
H1-H3 are no inputs at all. Any external write-up claiming a four-way hypothesis decomposition into
"strictly smaller inputs" must be corrected to match. -/

end SKEFTHawking
