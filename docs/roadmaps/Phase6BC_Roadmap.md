# Phase 6BC — Open-System Dynamics (Lindblad / GKSL)

**Status: PLANNED (authorized 2026-06-29).** The verified Lindblad / Gorini–Kossakowski–Sudarshan (GKSL) master equation for open-system molecular dynamics. PhysLib ships the full CPTP/Choi/Kraus channel layer — the **static half is done**; the new content is the *generator* and the Markovian semigroup. Distinct phase in the `6B*` chemistry series.

**Substrate (verified 2026-06-29 — PhysLib source read + lean MCP):**
- **Reuse (exists):** PhysLib `QuantumInfo/Finite/CPTPMap/CPTP.lean` — `CPTPMap`, `choi_PSD_of_CPTP`, `Tr_of_choi_of_CPTP`, `CPTP_of_choi_PSD_Tr` (construct from PSD + unit trace), `CPTPMap.compose`; `…/MatrixMap.lean` — `choi_matrix`, `choi_equiv` (the Choi iso), `of_kraus`, `exists_kraus`. PhysLib `…/HermitianMat/LogExp.lean` — `HermitianMat.exp`/`.log`/`exp_pos` + `…/CFC.lean` (CFC) for the **Hermitian** Hamiltonian/Gibbs parts. Project `QuantumCrooks/ReservoirCoupled.lean` — `IsLindbladDetailedBalance` (predicate) + a 2-state Lindblad data structure + `HasLindbladDetailedBalanceWitness` (existing detailed-balance toehold to consume). Project `QuantumNetwork/*` diamond-norm / trace-distance.
- **Absent → build:** the GKSL generator object, CP-of-the-generated-map, the semigroup law — 0 `Lindblad`/`GKSL` generator content in PhysLib; the project has only the *predicate* above.
- **New content:** the generator `ℒ`; CP via PhysLib Choi; structure theorem; the semigroup `e^{tℒ}`.
- **Correction (was a planning miss):** the Markovian semigroup `e^{tℒ}` is the exponential of the **non-Hermitian Liouvillian** superoperator — use Mathlib `Matrix.exp` on the vectorized `ℒ` (or project `MatrixBCH`), **not** `HermitianMat.exp` (which only applies to Hermitian operators like `H`, `ρ`).

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop: if `CLAUDE.md` or the mandatory references were missed in a context-recovery or a sub-agent handoff, this is the floor — do not start proving without it.)*
>
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` (the **14-stage law** — no skipping/reordering; each stage gates the next) → `SK_EFT_Hawking_Inventory_Index.md`. Paper-shaped output also reads `docs/PAPER_STRATEGY.md` + `docs/BUNDLE_LIFT_PROCEDURE.md`.
> 2. **Read this roadmap end-to-end** before claiming a wave. The **Substrate** block and each wave's **Bricks** name the *exact* PhysLib/project declarations (verified 2026-06-29) — read those sources **directly**; never delegate depth-reading of substrate or `Lit-Search/Phase-*` files to a sub-agent.
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`): `lean_file_outline` → statement + `sorry` → `lean_goal` → `lean_multi_attempt` (4–6 tactics) → write winner → repeat → `lake build` to finalize. Not write→`lake build`→parse-error.
> 4. **Pipeline disciplines (hard gates):** (a) **Stage 1 — bundle assignment mandatory (Invariant #14):** target candidate **D10** (pending roster auth) — record it; do **not** create a `papers/` bundle or edit `_VALID_BUNDLE_TARGETS` without the user's roster sign-off. (b) **Stage 3 — preemptive-strengthening checklist before EVERY theorem** (drop-conjunct P2 · `norm_num` numerical content · cross-module bridge P6 · trivial-discharge P3/P4/P5 · defining-the-conclusion) + ruthless post-wave audit. (c) **Kernel-purity** `{propext, Classical.choice, Quot.sound}`, zero `sorry`/`native_decide` regression (`lean_verify`); **no new project-local `axiom` without explicit user sign-off (Invariant #15)** — DR "ship as axiom" is advisory; use a disclosed tracked-Prop. (d) **No `set_option maxHeartbeats` in a proof body (Invariant #10)** — decompose into `have` sub-lemmas.
> 5. **This phase:** the Markovian semigroup `e^{tℒ}` is the exponential of the **non-Hermitian** Liouvillian → Mathlib `Matrix.exp`, **not** `HermitianMat.exp`. Consume the existing `IsLindbladDetailedBalance` toehold (don't re-derive it).

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. **Two-layer honesty:** the generator/semigroup *formulas* are Lean-verified; the physical-channel identification (which bath, which jump operators) stays literature-cited in the module header. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics.

**Bundle target:** **D10** (authorized 2026-06-29; §open-systems), shared with 6BA/6BB. Roster-expansion mechanics at first content-lift.

---

## Wave 1 — GKSL generator + complete positivity
- **Goal:** `ℒ(ρ) = −i[H,ρ] + Σ_k (L_k ρ L_k† − ½{L_k†L_k, ρ})`; complete positivity of the generated map via PhysLib Choi (`choi_PSD_iff_CP_map`). **Verdict: reachable** — generator over the existing CPTP layer.
- **Why:** the central object of open-system dynamics; CP is the physical-consistency condition.
- **Bricks:** PhysLib CPTP/Choi; `HermitianMat` CFC.
- **Done (AC / `/goal` condition):**
  - [ ] `LindbladGenerator.lean` builds clean — 0 sorry, kernel-pure (`lean_verify`), no new project-local axiom
  - [ ] GKSL generator `ℒ` defined; `lindblad_generator_CP` (complete positivity via PhysLib Choi) proven

## Wave 2 — structure theorem (trace preservation + canonical form)
- **Goal:** `Tr ℒ(ρ) = 0` (trace preservation); the canonical Hamiltonian-vs-dissipator decomposition; gauge freedom of the jump operators. **Verdict: reachable.**
- **Why:** the structural backbone (the "GKSL form") downstream constructions cite.
- **Bricks:** W1; Mathlib trace + Hermitian structure.
- **Done (AC / `/goal` condition):**
  - [ ] `GKSLStructure.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `gksl_trace_preserving` (`Tr ℒ(ρ)=0`) + `gksl_canonical_form` (Hamiltonian/dissipator split) proven

## Wave 3 — Markovian semigroup + contractivity
- **Goal:** `Λ_t = e^{tℒ}` via Mathlib `Matrix.exp` on the vectorized (non-Hermitian) Liouvillian; the semigroup law `Λ_t ∘ Λ_s = Λ_{t+s}`; trace-distance monotonicity (data-processing under the dynamical map). **Verdict: reachable.**
- **Why:** Markovianity + contractivity are the dynamical guarantees a certificate would invoke.
- **Bricks:** W1/W2; Mathlib `Matrix.exp` (the Liouvillian is **non-Hermitian** — *not* `HermitianMat.exp`); project diamond-norm/trace-distance.
- **Done (AC / `/goal` condition):**
  - [ ] `LindbladSemigroup.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `lindblad_semigroup` (`Λ_t∘Λ_s=Λ_{t+s}` via Mathlib `Matrix.exp`) + `traceDist_lindblad_monotone` (data-processing) proven

## Wave 4 — concrete certified model
- **Goal:** a damped two-level / vibrational-relaxation model instantiating the generator, with a **certified exponential decay envelope** (rational-enclosure corollary, no floating-point). **Verdict: reachable.**
- **Why:** a worked, falsifiable instance that grounds the abstract substrate.
- **Bricks:** W1–W3; `expNeg_enclosure`.
- **Done (AC / `/goal` condition):**
  - [ ] `DampedTwoLevel.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `dampedTwoLevel_decay_envelope` with a `norm_num`-backed bound proven; two-layer-honesty note in the module header

## Sequencing
W1 (generator) → W2 (structure) → W3 (semigroup) → W4 (model). Independent of 6BA/6BB/6BD; the fastest chemistry phase (PhysLib does the most here).

## Phase Definition of Done (`/goal` exit — every wave AC above green, then:)
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; D10 §open-systems row staged for first-lift; roadmap status updated.
