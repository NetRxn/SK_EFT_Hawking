# D8 — First-Claim Ledger

**Bundle:** D8 — Kernel-Verified Universal Quantum Gate Compilation.
**Gate:** READINESS_GATES Gate 10 (NarrativeGrounding / first-claim).
**Created:** 2026-05-31, from the Stage-13 adversarial-review prior-art search (finding class 5).

Each "first" claim in the D8 draft, its location, the prior-art search performed, and the verdict. All claims are phrased with "to our knowledge" hedging in the draft.

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
