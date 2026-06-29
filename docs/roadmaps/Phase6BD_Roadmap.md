# Phase 6BD — Fermionic-Simulation Substrate (Jordan–Wigner / Trotter) — DEPRIORITIZED

**Status: PLANNED (authorized 2026-06-29) — DEPRIORITIZED, do not schedule standalone.** Jordan–Wigner transform, Fock space, and a non-commuting Trotter–Suzuki error bound. Distinct phase in the `6B*` chemistry series, but the **lowest priority** of the family.

> **⚠️ NOVELTY REFUTED.** QBlue (Rocq, arXiv:2509.18583, 2025) already machine-checked Trotter + Jordan–Wigner. Any result here is **"first in Lean" only, NOT first in any proof assistant** — state this in every module header and claim **no** first-in-prover headline. This phase exists only as a *feature consumed by the verified-compilation arc (the D8 family)* when a downstream resource estimate needs it. Schedule **only** if a D8 consumer pulls it.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. Wave sizing ≈ one `/goal` (≤ ~5M tokens).

**Bundle target:** **D8** (existing — verified-compilation arc), *not* D10 — JW/Trotter resource content is a compilation-substrate feature. Absorb via `LATE_PHASE6_ABSORPTION_PROTOCOL` if scheduled.

---

## Wave 1 — Jordan–Wigner + Fock space
- **Goal:** the JW string map between fermionic modes and qubit operators; fermionic CCR on the PhysLib ladder/CCR substrate. **Verdict: reachable** (first in Lean; cite QBlue prior art).
- **Why:** the standard fermion-to-qubit encoding any simulation resource estimate needs.
- **Bricks:** PhysLib ladder/CCR; `PauliMatrices`.
- **Gate:** `jordanWigner_anticommutation` kernel-pure; QBlue prior-art disclosed in header.

## Wave 2 — Trotter error bound
- **Goal:** the non-commuting Trotter–Suzuki bound `‖e^{(A+B)t} − (e^{At/n}e^{Bt/n})ⁿ‖ ≤ …` via the project's `MatrixBCH` (Mathlib `Matrix.exp` is commuting-case only). **Verdict: reachable.**
- **Why:** the resource/error primitive for digital quantum simulation.
- **Bricks:** `MatrixBCH`; W1.
- **Gate:** `trotter_suzuki_error_bound` kernel-pure; no first-in-prover claim.

## Sequencing
Schedule only on a D8-consumer pull. W1 → W2. Independent of all other 6B*/6C* phases.

## Closure
If scheduled: `lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; QBlue prior-art disclosure; absorb into D8 via the late-absorption protocol; roadmap status updated.
