# Phase 6BD — Fermionic-Simulation Substrate (Jordan–Wigner / Trotter) — DEPRIORITIZED

**Status: PLANNED (authorized 2026-06-29) — DEPRIORITIZED, do not schedule standalone.** Jordan–Wigner transform, Fock space, and a non-commuting Trotter–Suzuki error bound. Distinct phase in the `6B*` chemistry series, but the **lowest priority** of the family.

> **⚠️ NOVELTY REFUTED.** QBlue (Rocq, arXiv:2509.18583, 2025) already machine-checked Trotter + Jordan–Wigner. Any result here is **"first in Lean" only, NOT first in any proof assistant** — state this in every module header and claim **no** first-in-prover headline. This phase exists only as a *feature consumed by the verified-compilation arc (the D8 family)* when a downstream resource estimate needs it. Schedule **only** if a D8 consumer pulls it.

**Substrate (verified 2026-06-29 — PhysLib source read + lean MCP):**
- **Reuse (exists):** PhysLib `QFT/PerturbationTheory/CreateAnnihilate.lean` + `FieldSpecification/{CrAnFieldOp,NormalOrder}.lean` + `FieldOpFreeAlgebra/` (a real create–annihilate + normal-ordering field-operator algebra) and `PhyslibAlpha/QuantumMechanics/QuantumHarmonicOscillator.lean` (ladder operators); project `PauliMatrices.lean`; project `MatrixBCH.lean` — `BCHOrder2Bound`, `norm_exp_smul_le_exp_norm`, `norm_exp_smul_sub_one_le`, `exp_neg_commutator_first_order_diff` (the non-commuting Trotter substrate; Mathlib `Matrix.exp` is commuting-case only).
- **Absent → build:** `JordanWigner` — 0 in PhysLib and the project (first in Lean; QBlue did it in Rocq).
- **New content:** the JW string map (PhysLib create–annihilate → project Pauli strings); Trotter–Suzuki bound via `MatrixBCH.norm_exp_*`.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop: if `CLAUDE.md` or the mandatory references were missed in a context-recovery or a sub-agent handoff, this is the floor — do not start proving without it.)*
>
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` (the **14-stage law** — no skipping/reordering; each stage gates the next) → `SK_EFT_Hawking_Inventory_Index.md`. Paper-shaped output also reads `docs/PAPER_STRATEGY.md` + `docs/BUNDLE_LIFT_PROCEDURE.md` + `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` (D8 absorption).
> 2. **Read this roadmap end-to-end** before claiming a wave. The **Substrate** block and each wave's **Bricks** name the *exact* PhysLib/project declarations (verified 2026-06-29) — read those sources **directly**; never delegate depth-reading of substrate or `Lit-Search/Phase-*` files to a sub-agent.
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`): `lean_file_outline` → statement + `sorry` → `lean_goal` → `lean_multi_attempt` (4–6 tactics) → write winner → repeat → `lake build` to finalize. Not write→`lake build`→parse-error.
> 4. **Pipeline disciplines (hard gates):** (a) **Stage 1 — bundle assignment mandatory (Invariant #14):** target is the **existing D8** (verified-compilation arc), **not** D10 — absorb via `LATE_PHASE6_ABSORPTION_PROTOCOL`. (b) **Stage 3 — preemptive-strengthening checklist before EVERY theorem** (drop-conjunct P2 · `norm_num` numerical content · cross-module bridge P6 · trivial-discharge P3/P4/P5 · defining-the-conclusion) + ruthless post-wave audit. (c) **Kernel-purity** `{propext, Classical.choice, Quot.sound}`, zero `sorry`/`native_decide` regression (`lean_verify`); **no new project-local `axiom` without explicit user sign-off (Invariant #15)**. (d) **No `set_option maxHeartbeats` in a proof body (Invariant #10)** — decompose into `have` sub-lemmas.
> 5. **This phase:** **DEPRIORITIZED — do not schedule standalone.** Novelty is **refuted** (QBlue, Rocq, arXiv:2509.18583) → first-in-Lean only; claim **no** first-in-prover headline; state QBlue prior art in every module header. Schedule **only** on a D8-consumer pull.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. Wave sizing ≈ one `/goal` (≤ ~5M tokens).

**Bundle target:** **D8** (existing — verified-compilation arc), *not* D10 — JW/Trotter resource content is a compilation-substrate feature. Absorb via `LATE_PHASE6_ABSORPTION_PROTOCOL` if scheduled.

---

## Wave 1 — Jordan–Wigner + Fock space
- **Goal:** the JW string map between fermionic modes and qubit operators; fermionic CCR on the PhysLib ladder/CCR substrate. **Verdict: reachable** (first in Lean; cite QBlue prior art).
- **Why:** the standard fermion-to-qubit encoding any simulation resource estimate needs.
- **Bricks:** PhysLib ladder/CCR; `PauliMatrices`.
- **Done (AC / `/goal` condition):**
  - [ ] `JordanWigner.lean` builds clean — 0 sorry, kernel-pure (`lean_verify`), no new project-local axiom
  - [ ] `jordanWigner_anticommutation` proven; QBlue prior-art disclosed in the module header; **no** first-in-prover claim

## Wave 2 — Trotter error bound
- **Goal:** the non-commuting Trotter–Suzuki bound `‖e^{(A+B)t} − (e^{At/n}e^{Bt/n})ⁿ‖ ≤ …` via the project's `MatrixBCH` (Mathlib `Matrix.exp` is commuting-case only). **Verdict: reachable.**
- **Why:** the resource/error primitive for digital quantum simulation.
- **Bricks:** `MatrixBCH`; W1.
- **Done (AC / `/goal` condition):**
  - [ ] `TrotterError.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `trotter_suzuki_error_bound` proven via `MatrixBCH.norm_exp_*`; no first-in-prover claim

## Sequencing
Schedule only on a D8-consumer pull. W1 → W2. Independent of all other 6B*/6C* phases.

## Phase Definition of Done (`/goal` exit — every wave AC above green, then:)
If scheduled: `lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; QBlue prior-art disclosure; absorb into D8 via the late-absorption protocol; roadmap status updated.
