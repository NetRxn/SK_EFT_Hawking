# Phase 6CE — Effective-Medium Homogenization (Maxwell–Garnett)

**Status: PLANNED (authorized 2026-06-29).** A certified quasi-static effective-medium theory via the **algebraic Maxwell–Garnett** mixing formula, plus certified effective-parameter bounds. Clean whitespace (no two-scale / Maxwell–Garnett in any prover). Distinct phase in the `6C*` materials series.

**Substrate (verified 2026-06-29 — PhysLib source read + lean MCP):**
- **Reuse (exists):** Mathlib field arithmetic; project `QuantumNetwork/NumericalBounds.expNeg_enclosure` (rational two-sided enclosure); Mathlib `FunctionalSpaces.SobolevInequality` (GNS *inequalities* only).
- **Absent → build:** `MaxwellGarnett` 0 in PhysLib + project; two-scale / periodic homogenization absent — Mathlib has Sobolev *inequalities*, not two-scale convergence, and PhysLib `Optics/Basic.lean` is an **explicit placeholder** (its own docstring reads *"This directory is currently a place holder"*; only `Optics/Polarization` exists, unrelated; no `OpticalMedium` / effective-medium type).
- **New content:** the algebraic quasi-static Clausius–Mossotti / Maxwell–Garnett `ε_eff`; Hashin–Shtrikman two-sided enclosure; elastic analog.

> **⚠️ GUARDRAIL — algebraic path ONLY.** Do **not** attempt full two-scale / periodic-homogenization convergence (the documented substrate-stall above). Use only the algebraic derivation — finite-dim algebra + `expNeg_enclosure`.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop: if `CLAUDE.md` or the mandatory references were missed in a context-recovery or a sub-agent handoff, this is the floor — do not start proving without it.)*
>
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` (the **14-stage law** — no skipping/reordering; each stage gates the next) → `SK_EFT_Hawking_Inventory_Index.md`. Paper-shaped output also reads `docs/PAPER_STRATEGY.md` + `docs/BUNDLE_LIFT_PROCEDURE.md`.
> 2. **Read this roadmap end-to-end** before claiming a wave. The **Substrate** block and each wave's **Bricks** name the *exact* PhysLib/project declarations (verified 2026-06-29) — read those sources **directly**; never delegate depth-reading of substrate or `Lit-Search/Phase-*` files to a sub-agent.
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`): `lean_file_outline` → statement + `sorry` → `lean_goal` → `lean_multi_attempt` (4–6 tactics) → write winner → repeat → `lake build` to finalize. Not write→`lake build`→parse-error.
> 4. **Pipeline disciplines (hard gates):** (a) **Stage 1 — bundle assignment mandatory (Invariant #14):** target **D11** (authorized 2026-06-29 in `PAPER_STRATEGY`) — record it; the `papers/D11/` + `_VALID_BUNDLE_TARGETS` scaffolding is created at **first content-lift** (`BUNDLE_LIFT_PROCEDURE` step 2), not before. (b) **Stage 3 — preemptive-strengthening checklist before EVERY theorem** (drop-conjunct P2 · `norm_num` numerical content · cross-module bridge P6 · trivial-discharge P3/P4/P5 · defining-the-conclusion) + ruthless post-wave audit. (c) **Kernel-purity** `{propext, Classical.choice, Quot.sound}`, zero `sorry`/`native_decide` regression (`lean_verify`); **no new project-local `axiom` without explicit user sign-off (Invariant #15)**. (d) **No `set_option maxHeartbeats` in a proof body (Invariant #10)** — decompose into `have` sub-lemmas.
> 5. **This phase:** **algebraic Maxwell–Garnett ONLY** — full two-scale / periodic homogenization is a documented substrate-stall (PhysLib `Optics` is an explicit placeholder; Mathlib has no two-scale). Do **not** attempt it. See the GUARDRAIL above.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. **Two-layer honesty:** the mixing *formula* + bounds are Lean-verified; the physical-composite identification (dilute limit, sphere geometry) stays literature-cited in the module header. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics.

**Bundle target:** **D11** (authorized 2026-06-29; §homogenization), shared with 6CA/6CB/6CD. Roster-expansion mechanics at first content-lift.

---

## Wave 1 — Maxwell–Garnett formula
- **Goal:** the quasi-static effective permittivity `ε_eff(ε_h, ε_i, f)` (host `ε_h`, inclusion `ε_i`, fill fraction `f`); the Clausius–Mossotti derivation in the dilute limit. **Verdict: reachable** — algebraic identity + a clean limit.
- **Why:** the canonical macroscale effective-parameter formula metamaterial design relies on.
- **Bricks:** finite-dim algebra; Mathlib field arithmetic.
- **Done (AC / `/goal` condition):**
  - [ ] `MaxwellGarnett.lean` builds clean — 0 sorry, kernel-pure (`lean_verify`), no new project-local axiom
  - [ ] `maxwellGarnett_eps_eff` + the `f → 0` host-recovery limit proven (algebraic path only — no two-scale)

## Wave 2 — certified effective-parameter bounds
- **Goal:** a **Hashin–Shtrikman**-style two-sided enclosure on `ε_eff`; an interval-arithmetic certificate (rational brackets). **Verdict: reachable.**
- **Why:** turns the formula into a certificate-grade bound (the design-relevant guarantee).
- **Bricks:** W1; `expNeg_enclosure`-style interval arithmetic.
- **Done (AC / `/goal` condition):**
  - [ ] `EffectiveMediumBounds.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `effectiveMedium_hashinShtrikman_enclosure` (`norm_num`-backed two-sided bound) proven

## Wave 3 — elastic / acoustic effective moduli
- **Goal:** the effective bulk/shear moduli of a composite via the same algebraic mixing + enclosure (the elastic analog of W1/W2). **Verdict: reachable.**
- **Why:** extends the certificate from electromagnetic to mechanical metamaterials (ties to 6CB's acoustic substrate).
- **Bricks:** W1/W2; elastic-modulus mixing rules.
- **Done (AC / `/goal` condition):**
  - [ ] `EffectiveModuli.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `effectiveModuli_enclosure` (elastic bulk/shear analog) proven

## Sequencing
W1 (formula) → W2 (bounds) → W3 (elastic analog). Independent of 6CA–6CD. Algebraic path throughout — two-scale stays out of scope.

## Phase Definition of Done (`/goal` exit — every wave AC above green, then:)
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; algebraic-path-only + two-scale-out-of-scope documented; D11 §homogenization row staged for first-lift; roadmap status updated.
