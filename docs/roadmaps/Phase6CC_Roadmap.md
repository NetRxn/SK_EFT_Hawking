# Phase 6CC — SPT Classification via Cobordism (Pin⁺ Reframe) — CONDITIONAL, consumes existing arc

**Status: PLANNED (authorized 2026-06-29) — CONDITIONAL, coordinate with `5q.G`.** The topological-superconductor symmetry-protected-topological (SPT) classification in **condensed-matter language**, as a *reframe/application* of the project's existing Pin⁺ ℤ/16 bordism arc. Distinct phase in the `6C*` materials series.

> **⚠️ SCOPING — READ BEFORE ANY WORK.** This phase **consumes** `KitaevSixteenFold`, `RokhlinClassification`, `ArfInvariant`, `BrownInvariant`, `SPTStacking`, `Omega5FiniteIso`, `BordismGroup` — it does **NOT** re-derive them and **NOT** fork or race the **active, separate `5q.G` unconditional-geometric-Pin⁺ `/goal`** (read `Phase5qG_GenuineUnconditional_Roadmap.md` + `Phase5qB_LabNotebook.md` first; coordinate). The finite ℤ/16 cardinality is unconditional; the *geometric full-carrier identification is OPEN (5q.G)*. Per the standing rule a **conditional (disclosed-landmark) discharge is an acceptable temporary posture** for this materials reframe — ship it kernel-clean while 5q.G proceeds.
>
> **⚠️ PHYSICS FIX (mandatory):** an external proposal mis-stated Kitaev's sixteen-fold way as "1D class-BDI." It is **2D class-D**. Every condensed-matter statement here uses 2D class-D.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop: if `CLAUDE.md` or the mandatory references were missed in a context-recovery or a sub-agent handoff, this is the floor — do not start proving without it.)*
>
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` (the **14-stage law** — no skipping/reordering; each stage gates the next) → `SK_EFT_Hawking_Inventory_Index.md`. **Also (mandatory for this phase):** `roadmaps/Phase5qG_GenuineUnconditional_Roadmap.md` + `Phase5qB_LabNotebook.md` (the active unconditional-Pin⁺ `/goal` this phase must coordinate with). Paper-shaped output also reads `docs/PAPER_STRATEGY.md` + `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`.
> 2. **Read this roadmap end-to-end** before claiming a wave. The **Substrate** block names the *exact* existing decls this phase **consumes** (verified 2026-06-29) — read those sources **directly**; never delegate depth-reading of substrate or `Lit-Search/Phase-*` files to a sub-agent.
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`): `lean_file_outline` → statement + `sorry` → `lean_goal` → `lean_multi_attempt` (4–6 tactics) → write winner → repeat → `lake build` to finalize.
> 4. **Pipeline disciplines (hard gates):** (a) **Stage 1 — bundle assignment mandatory (Invariant #14):** target **D2** (existing — owns the 16-convergence) **or** **D11** (authorized 2026-06-29) — decide at first-lift; the `papers/` + `_VALID_BUNDLE_TARGETS` scaffolding is created at first content-lift, not before. (b) **Stage 3 — preemptive-strengthening checklist before EVERY theorem** + ruthless post-wave audit. (c) **Kernel-purity** `{propext, Classical.choice, Quot.sound}`; **no new project-local `axiom` without explicit user sign-off (Invariant #15)** — the conditional content uses the *existing* disclosed Kirby–Taylor tracked Prop, NOT a new axiom. (d) **No `set_option maxHeartbeats` in a proof body (Invariant #10)**.
> 5. **This phase:** **CONDITIONAL reframe** — *consume* the existing Pin⁺ ℤ/16 arc (`KitaevSixteenFold.kitaevClass`, `SPTStacking.SPTPhase.stack` — group laws already proven, so W2 is a thin wrapper) + the disclosed Kirby–Taylor landmark. **Coordinate with the active `5q.G` `/goal`; do NOT fork or race it.** Kitaev = **2D class-D** (not 1D class-BDI). See the SCOPING + PHYSICS-FIX callouts above.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; **no new project-local axioms (#15)** — the conditional content uses the existing KEEP tracked Prop "Kirby–Taylor Pin⁺ bordism geometric ISO" (Deferred-Targets register item 15) as the disclosed landmark, **not** a new axiom; no `native_decide`; no `maxHeartbeats` (#10); never push. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics (dual condensed-matter publication).

**Bundle target:** **D2** (existing — anomaly/SM; already owns the 16-convergence, Rokhlin's 16, Kitaev DIII) as a condensed-matter-reframe section — **or** D11; decided at Stage 1 (first-lift). Absorb via `LATE_PHASE6_ABSORPTION_PROTOCOL`.

**Substrate (verified 2026-06-29 — lean MCP + source read):**
- **Consume (exists, proven):** project `KitaevSixteenFold.lean` — `kitaevClass : ℤ → ZMod 16`, `kitaevCentralCharge`, `kitaevCentralCharge_period16`, `kitaev_integral_charge_iff_even`, `kitaev_eight_bosonic_phases`; `SPTStacking.lean` — `SPTPhase.stack` with `stack_assoc` + `stack_trivial_left/right` + `stack_inverse_left/right` (**the ℤ/16 group structure is already proven** — so W2 is a thin materials-language wrapper, not a new derivation); `RokhlinClassification`, `Omega5FiniteIso`, `BordismGroup`.
- **Disclosed landmark (not an axiom):** the existing KEEP tracked Prop "Kirby–Taylor Pin⁺ bordism geometric ISO" (Deferred-Targets item 15) — the geometric full-carrier identification the active 5q.G `/goal` discharges unconditionally.
- **New content:** the **2D class-D** condensed-matter interpretation layer over the above (conditional on the landmark). No new mathematics beyond the reframe + the conditional geometric ID.

---

## Wave 1 — topological-superconductor SPT classification *(CONDITIONAL)*
- **Goal:** the **2D class-D** sixteen-fold classification of topological superconductors in materials language, CONDITIONAL on the disclosed `H_PinPlusBordismLandmark`; cites the existing arc and adds the condensed-matter interpretation layer. **Verdict: reachable (conditional)** — interpretation over already-proven structure.
- **Why:** restates a marquee program result in the language of the condensed-matter audience; broadens reach at near-zero marginal cost.
- **Bricks:** `KitaevSixteenFold`, `RokhlinClassification`, `Omega5FiniteIso`; the existing landmark tracked Prop.
- **Done (AC / `/goal` condition):**
  - [ ] `TopSuperconductorSPT.lean` builds clean — 0 sorry, kernel-pure, **no new axiom** (uses the *existing* disclosed `H_PinPlusBordismLandmark`, not a new one)
  - [ ] `topSuperconductor_sixteenfold_classification` (conditional, **2D class-D**) proven, consuming `KitaevSixteenFold.kitaevClass`; landmark disclosed; 5q.G coordination confirmed before start

## Wave 2 — SPT stacking / group structure
- **Goal:** the stacking law / ℤ/16 group structure in materials language, on the existing `SPTStacking`. **Verdict: reachable.**
- **Why:** completes the classification as a group (stacking = addition mod 16).
- **Bricks:** W1; `SPTStacking`/`SPTClassification`.
- **Done (AC / `/goal` condition):**
  - [ ] `SPTStackingMaterials.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `spt_stacking_z16` (materials-language wrapper on the already-proven `SPTStacking.SPTPhase.stack` group) proven

## Sequencing
Coordinate with `5q.G` **before** starting (gate G-6CC.0). W1 (classification) → W2 (stacking). Independent of 6CA/6CB/6CD/6CE. The smallest materials phase (reframe, not new derivation).

## Phase Definition of Done (`/goal` exit — every wave AC above green, then:)
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; explicit cross-ref to D2 + to the active 5q.G unconditional work; bundle row staged for first-lift; roadmap status updated.
