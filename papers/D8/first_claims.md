# D8 — First-Claim Ledger

**Bundle:** D8 — Kernel-Verified Universal Quantum Gate Compilation.
**Gate:** READINESS_GATES Gate 10 (FirstClaimVerification).
**Created:** 2026-05-31, from the Stage-13 adversarial-review prior-art search (finding class 5).

The current draft has one hedged priority claim, repeated in three places.
The numbered May 31 entries are the historical Stage-13 ledger.

## Current priority readback, 2026-11-07

- **Draft pin.** `3bfc51622b6b246ce31662403888cd06a93f6dc8`. The
  abstract, introduction and general-dimension theorem discussion repeat
  the quantitative Solovay–Kitaev priority claim. The other three May
  ledger headings describe earlier draft wording.
- **Comparator.** A proof assistant checks a quantitative synthesis theorem
  for every finite dimension \(d\ge 2\), with a density hypothesis and a
  compatible free-group length. One compilation function supplies a word
  meeting both the operator-norm error and polylogarithmic reduced-word
  length bounds. A comparable prior result may use a different norm,
  exponent or proof assistant. Executable extraction is outside this
  comparator. The formal anchor is
  `solovayKitaev_dawson_nielsen_quantitative_generic_sud_strict_constructive_tight`
  in `GenericSUdQuantitative.lean`. The alphabet interface includes
  decidable equality, a free-group word-carrier equality, density and
  the word-length predicate.
- **Mathematical comparators.** Dawson and Nielsen give the algorithm and
  discuss general dimension. Bouland and Giurgică-Tiron give a quantitative
  inverse-free construction. Ennes and Maria study variable-dimension
  online synthesis. These are mathematical algorithm results in the
  cited preprints. [Dawson–Nielsen](https://arxiv.org/abs/quant-ph/0505030v2),
  [Bouland–Giurgică-Tiron](https://arxiv.org/abs/2112.02040v1),
  [Ennes–Maria](https://arxiv.org/abs/2607.19874v1).
- **Proof-assistant comparators.** VOQC checks circuit optimization against
  SQIR semantics. Qbricks verifies parametric circuit-building programs.
  QEDIA's published examples include approximate Hamiltonian simulation,
  a program-verification obligation distinct from a general dense-alphabet
  word-approximation theorem. MerLean's evaluation covers formalizations
  of three other quantum research papers. [VOQC](https://arxiv.org/abs/1912.02250v3),
  [Qbricks](https://arxiv.org/abs/2003.05841v2),
  [QEDIA, §6](https://arxiv.org/html/2610.17708v1#S6),
  [MerLean](https://arxiv.org/abs/2602.16554v1).
- **Search boundary.** Searched the indexed web and GitHub for
  Solovay–Kitaev with formalization, machine-checked, mechanized, Lean,
  Rocq/Coq and Isabelle. Reviewed the primary comparator pages above and
  QEDIA's example list. No result meeting the comparator surfaced in
  that bounded search. The current hedged wording remains for independent
  Stage-13 review. This record supplies no exhaustive priority claim or
  completed G10 disposition.

---

## Claim 1 — "first machine-checked development of universal quantum gate compilation as a *theory*"

- **Location:** `paper_draft.tex` abstract (line ~27).
- **Phrasing:** "We report what is, to our knowledge, the first machine-checked development of universal quantum gate compilation as a theory rather than a single algorithm."
- **Search performed (Stage 13, 2026-05-31):** prior verified-quantum-computation in proof assistants — VOQC/SQIR (Coq, inQWIRE; arXiv:1912.02250); the verified-quantum-programs landscape survey (Lewis–Soudjani–Zuliani 2021, arXiv:2110.01320) covering Why3/Qbricks, Isabelle, etc.
- **Finding:** VOQC and the surveyed frameworks target **exact** circuit semantics / optimization / program correctness; none develops **quantitative approximation** theory (density of a discrete alphabet, error-vs-length trade-off, Solovay–Kitaev). The VOQC repository was inspected and confirmed to contain no Solovay–Kitaev / approximation / density / synthesis-to-precision content.
- **Verdict:** HOLDS under its precise reading (approximation theory vs exact optimization). The draft now cites VOQC + the survey and draws the optimization-vs-approximation distinction explicitly (§1). Hedged.

## Claim 2 — "first kernel-verified quantitative Solovay–Kitaev at arbitrary dimension SU(d) in any proof assistant"

- **Location:** abstract; §3 ("The lift to arbitrary dimension").
- **Phrasing:** "To our knowledge this is the first kernel-verified quantitative Solovay–Kitaev at arbitrary dimension in any proof assistant."
- **Search performed:** Mathlib (no Solovay–Kitaev); the proof-assistant verified-QC landscape (above). The project's own Phase 6t/6u did quantitative SK at SU(2) (Fibonacci, Clifford+T); Phase 6y is the SU(d) lift.
- **Finding:** No prior proof-assistant formalization of quantitative Solovay–Kitaev at general dimension found. The closest prior is the project's own SU(2) work, which this generalizes.
- **Verdict:** HOLDS. Hedged.

## Claim 3 — "first unconditional machine-checked Toffoli-count lower bound"

- **Location:** §6 ("A verified resource lower bound").
- **Phrasing:** "A fully machine-checked unconditional resource lower bound for a fault-tolerant gate is, to our knowledge, the first of its kind."
- **Search performed:** Mukhopadhyay 2024 (arXiv:2401.08950) is the mathematical source (not a formalization). No proof-assistant formalization of a Toffoli/T-count resource lower bound found.
- **Finding:** The bound `channelSde2_le_toffoliCost` was independently confirmed (Stage 13, Gate 5) to be genuinely unconditional — hC/hCCZ discharged, not smuggled as hypotheses. Minimality (Mukhopadhyay Conjecture 4.8) is explicitly out of scope.
- **Verdict:** HOLDS. Hedged.

## Claim 4 — "first T-free, CCZ-essential density in SU(8)"

- **Location:** §5 ("Two density mechanisms for SU(8)"); companion to Claim 2.
- **Search performed:** prior proof-assistant density results; the project's own Phase 6y (T-based) vs Phase 6z (T-free, CCZ-essential, `cliffordCCZLiteral_dense`).
- **Finding:** No prior machine-checked T-free CCZ-essential SU(8) density found; the converse `cliffordOnly_not_dense` (Clifford-alone finite) establishes essentiality.
- **Verdict:** HOLDS. Hedged.

---

*Searches performed by the Stage-13 adversarial reviewer (fresh-context Opus) on 2026-05-31; recorded here as Gate-10 ledger evidence. Re-verify if competing formalizations appear before submission.*
