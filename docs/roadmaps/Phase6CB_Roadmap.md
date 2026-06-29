# Phase 6CB — Acoustic / Phononic Band Structure & Gaps

**Status: PLANNED (authorized 2026-06-29).** Bloch–Floquet band theory for a periodic acoustic/elastic medium and a **certified band-gap existence theorem** for a concrete phononic crystal. Clean whitespace (no Bloch/Floquet for acoustics in any prover). Distinct phase in the `6C*` materials series.

**Substrate (verified 2026-06-29 — PhysLib source read + lean MCP):**
- **Reuse (exists):** PhysLib `CondensedMatter/TightBindingChain/Basic.lean` — the band-model template (`hamiltonian_energyEigenstate` TISE, `BrillouinZone`, `energyEigenvalue`, `energyEigenstate_orthogonal`); Mathlib `Analysis.InnerProductSpace.Rayleigh` — `LinearMap.IsSymmetric.hasEigenvalue_iSup/iInf_of_finiteDimensional` (**extremal** eigenvalue only); project `QuantumNetwork/NumericalBounds.expNeg_enclosure` (rational enclosure).
- **Absent → build:** `Floquet` (0 in PhysLib); the acoustic Bloch operator; the **band-gap** theorem. **Key nuance (verified):** the PhysLib TB model is a *single* `E₀−2t·cos(ka)` band with **no gap** — a gap requires a **≥2-band (diatomic / two-sublattice) acoustic chain** (gap between acoustic & optical branches). The **k-th-eigenvalue Courant–Fischer** is also new (Mathlib has only extremal Rayleigh).
- **New content:** the diatomic mass-spring acoustic Bloch operator (≥2 bands); band-gap existence via min-max + the new Courant–Fischer; certified gap enclosure.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop: if `CLAUDE.md` or the mandatory references were missed in a context-recovery or a sub-agent handoff, this is the floor — do not start proving without it.)*
>
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` (the **14-stage law** — no skipping/reordering; each stage gates the next) → `SK_EFT_Hawking_Inventory_Index.md`. Paper-shaped output also reads `docs/PAPER_STRATEGY.md` + `docs/BUNDLE_LIFT_PROCEDURE.md`.
> 2. **Read this roadmap end-to-end** before claiming a wave. The **Substrate** block and each wave's **Bricks** name the *exact* PhysLib/project declarations (verified 2026-06-29) — read those sources **directly**; never delegate depth-reading of substrate or `Lit-Search/Phase-*` files to a sub-agent.
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`): `lean_file_outline` → statement + `sorry` → `lean_goal` → `lean_multi_attempt` (4–6 tactics) → write winner → repeat → `lake build` to finalize. Not write→`lake build`→parse-error.
> 4. **Pipeline disciplines (hard gates):** (a) **Stage 1 — bundle assignment mandatory (Invariant #14):** target candidate **D11** (pending roster auth) — record it; do **not** create a `papers/` bundle or edit `_VALID_BUNDLE_TARGETS` without the user's roster sign-off. (b) **Stage 3 — preemptive-strengthening checklist before EVERY theorem** (drop-conjunct P2 · `norm_num` numerical content · cross-module bridge P6 · trivial-discharge P3/P4/P5 · defining-the-conclusion) + ruthless post-wave audit. (c) **Kernel-purity** `{propext, Classical.choice, Quot.sound}`, zero `sorry`/`native_decide` regression (`lean_verify`); **no new project-local `axiom` without explicit user sign-off (Invariant #15)** — DR "ship as axiom" is advisory; use a disclosed tracked-Prop. (d) **No `set_option maxHeartbeats` in a proof body (Invariant #10)** — decompose into `have` sub-lemmas.
> 5. **This phase:** the band **gap requires a ≥2-band diatomic (two-sublattice) chain** — the PhysLib TB model is a *single gapless* `E₀−2t·cos` band (do not expect a gap from it). The k-th-eigenvalue Courant–Fischer is the new piece (Mathlib has only extremal Rayleigh).

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. **Two-layer honesty:** the band/gap *theorems* are Lean-verified; the physical-crystal identification stays literature-cited in the module header. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics (dual acoustics publication + flagship scope).

**Bundle target:** **D11** (authorized 2026-06-29; §phononic), shared with 6CA/6CD/6CE. A Stage-1 option (decide at first-lift): evaluate a standalone "first verified phononic band gap" headline letter. Roster-expansion mechanics at first content-lift.

---

## Wave 1 — acoustic Bloch operator
- **Goal:** a periodic acoustic/elastic operator (mass-spring / Helmholtz lattice); Bloch–Floquet spectrum + Brillouin zone (PBC), porting the TB template. **Verdict: reachable** — structural port of a proven model.
- **Why:** the spectral object whose gaps the phase certifies.
- **Bricks:** PhysLib `TightBindingChain`; Mathlib self-adjoint spectral theory.
- **Done (AC / `/goal` condition):**
  - [ ] `AcousticBlochOperator.lean` builds clean — 0 sorry, kernel-pure (`lean_verify`), no new project-local axiom
  - [ ] diatomic (≥2-band) acoustic Bloch operator; `acousticBloch_spectrum` (real, bounded-below) proven

## Wave 2 — band-gap existence
- **Goal:** min-max (Rayleigh) + k-th-eigenvalue **Courant–Fischer**; a spectral gap `[ω₋, ω₊]` proven for a concrete **diatomic (two-sublattice)** crystal — the gap opens between the acoustic and optical branches (no eigenvalue in the open interval). **Verdict: reachable-moderate.**
- **Why:** the headline result — a *proven* phononic band gap.
- **Bricks:** W1; Mathlib `Rayleigh`; new Courant–Fischer.
- **Done (AC / `/goal` condition):**
  - [ ] `PhononicBandGap.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `phononic_band_gap_exists` (gap between acoustic & optical branches) + falsifier (`∃ mode in (ω₋,ω₊) ⇒ ⊥`) proven

## Wave 3 — certified gap enclosure
- **Goal:** interval-arithmetic bounds on the gap edges (`expNeg_enclosure`-style); a rational enclosure usable with no floating-point. **Verdict: reachable.**
- **Why:** turns the existence theorem into a certificate-grade numerical bound.
- **Bricks:** W2; `expNeg_enclosure`.
- **Done (AC / `/goal` condition):**
  - [ ] `BandGapEnclosure.lean` builds clean — 0 sorry, kernel-pure, no new axiom
  - [ ] `band_gap_rational_enclosure` (`norm_num`-backed, no floating-point) proven

## Sequencing
W1 (operator) → W2 (gap existence) → W3 (enclosure). Independent of 6CA/6CC/6CD/6CE; one of the two fast materials phases (with 6CD).

## Phase Definition of Done (`/goal` exit — every wave AC above green, then:)
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; D11 §phononic row staged for first-lift; roadmap status updated.
