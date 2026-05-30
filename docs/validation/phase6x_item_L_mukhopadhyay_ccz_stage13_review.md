# Phase 6x Item L — Mukhopadhyay exact Clifford+CCZ (increments 1–2) — Stage 13 review

**Date:** 2026-05-30  **Verdict:** ✅ **GREEN** (0 findings at any severity)
**Reviewer:** fresh-context adversarial agent (read-only), per Wave Execution Pipeline Stage 13.

## Scope reviewed

`lean/SKEFTHawking/FKLW/MukhopadhyayCCZ.lean` (commit `5072aef`) — the public math layer for
Mukhopadhyay 2024 (arXiv:2401.08950) exact Clifford+CCZ synthesis on 3 qubits (SU(8)), increments
1–2 (the MVP foundation): `zsign`/`pauliZ`, `mukGen_Z`, the grounding `mukGen_Z_eq_CCZ`, the
`CliffordCCZGate` ADT, `gateMatrix`/`interp`, `interp_append`, `interp_ccz`, `IsExactlyCliffordCCZ`,
`mukGen_Z_isExactlyCliffordCCZ`, `interp_ccz_ccz`.

## Findings: NONE

1. **`mukGen_Z_eq_CCZ` is mathematically TRUE and honestly proven.** The reviewer independently
   recomputed the generating-element formula `(3/4)+(1/4)(z₀+z₁+z₂−z₀z₁−z₁z₂−z₂z₀+z₀z₁z₂)` over all 8
   basis indices with `zₐ = (−1)^{bit a}`: `+1` on indices 0–6, `−1` at index 7 — exactly the CCZ
   diagonal (Mukhopadhyay Eq. 12 at the canonical Z-Paulis). The `zsign`/`Nat.testBit` convention is
   consistent and relabeling-invariant; `diagonal_mul_diagonal` collapses the products correctly; the
   proof genuinely establishes the 8-entry diagonal equality (not a vacuous `rfl`).
2. **Non-vacuous MVP.** `interp_ccz` honestly chains `gateMatrix ccz = CCZ_mat` ∘ `mul_one` ∘
   `mukGen_Z_eq_CCZ` (not circular); `interp_append` is a correct `mul_assoc` induction;
   `interp_ccz_ccz` is genuinely `CCZ²=I` via `CCZ_mat_sq_eq_one`; `mukGen_Z_isExactlyCliffordCCZ` is
   a real `⟨[ccz], interp_ccz⟩` witness.
3. **Gate ADT grounding.** `gateMatrix (.clifford g)` (`g : Fin 9`) indexes the nine real shipped
   literal Clifford generators (`H_q{1,2,3}, S_q{1,2,3}, CNOT_{12,13,23}`) via `cliffordCCZLiteralGenMap`;
   the `Fin 9 → Fin 10` `omega` bound is sound and the CCZ slot (index 9) is correctly unreachable
   from `.clifford`.
4. **Axiom hygiene.** All theorems close over exactly `{propext, Classical.choice, Quot.sound}` — no
   `native_decide`/`Lean.ofReduceBool`, no `sorryAx`, no new axiom; no `sorry`/`maxHeartbeats`/
   `axiom`/`opaque`/`unsafe` in source. Invariants #10 and #15 respected.
5. **Honest-scope framing.** Docstrings correctly frame this as an MVP foundation;
   `mukGen_Z_isExactlyCliffordCCZ` proves only the canonical-generator witness, never general
   synthesis. The general `G_{P,Q,R}` via Clifford conjugation, the Fact-3.9 channel-representation
   test, and full `synth_CCZ_correct` (Thm 3.2 + meet-in-the-middle) are explicitly documented as
   not-yet-shipped continuations.
6. **Compile gate.** `lean_diagnostic_messages` returns zero items.
7. **No private leaks.** Case-insensitive scan for the private-repo identifiers returns none.

## Disposition

GREEN — ship as-is. The Item-L MVP foundation (generating-element grounding + gate ADT + `interp` +
composition soundness + canonical-generator exact synthesis + the order-2 relation) is sound,
kernel-pure, and honestly scoped. Build clean (8987 jobs); counts 9787 theorems / 0 axioms / 0 sorry
/ 738 modules; `axiom_closure_allowlist` + `counts_fresh` + `graph_integrity` PASS.

**Remaining for full Item L** (documented continuations, not part of this review): general `G_{P,Q,R}`
via Clifford conjugation; the channel-representation exact-implementability test; full
`synth_CCZ_correct` for an arbitrary exactly-representable `U` (Thm 3.2 decomposition + the
meet-in-the-middle search). These are a fresh multi-session construction.
