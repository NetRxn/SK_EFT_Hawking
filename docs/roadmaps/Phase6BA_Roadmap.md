# Phase 6BA — Verified Quantum Transport (NEGF / Landauer–Büttiker)

**Status: PLANNED (authorized 2026-06-29).** First machine-checked non-equilibrium Green's-function (NEGF) steady-state transport: retarded/advanced Green's functions, the Landauer–Büttiker / Meir–Wingreen conductance, and a certified conductance-quantization bound. No Landauer/NEGF transport exists in any proof assistant (clean whitespace). One of the public substrate-breadth phases scoped 2026-06-29 (companion chemistry phases 6BB–6BD; materials phases 6CA–6CE); the PhysLib operator/resolvent substrate makes the new transport layer MODERATE, not greenfield-expensive. Distinct double-letter phase in the `6B*` (computational-chemistry) series, independent of the unrelated `6A`/`6b`.

> **⚠️ CHECK PhysLib + project substrate FIRST.** Build on `DKMBootstrap/` (broadening-matrix / spectral-function infra, Phase 6q), Mathlib resolvent + `InnerProductSpace.LinearPMap`; the new content is the transport object itself. Verify by `lean_leansearch`/`loogle` before deriving any operator lemma from scratch.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` in proof bodies (#10); preemptive-strengthening checklist before each statement; decompose-before-asserting-walls; never push. **Two-layer honesty:** the transport *formulas* are Lean-verified; the device/material identification stays literature-cited in the module header. Wave sizing ≈ one `/goal` (≤ ~5M tokens) — a chunking heuristic, not a time estimate (PM/time estimates remain banned). Frame purely as physics (dual publication + flagship scope).

**Bundle target:** **D10** (authorized 2026-06-29) — "Kernel-Verified Foundations of Computational Quantum Chemistry & Open-System Dynamics" *(provisional)*, shared with 6BB/6BC. Roster-expansion mechanics (`PAPER_STRATEGY` roster, `_VALID_BUNDLE_TARGETS`, `papers/D10/` scaffold) execute at **first content-lift** per `BUNDLE_LIFT_PROCEDURE` — not at planning time (avoids standing up an empty bundle).

---

## Wave 1 — NEGF Green's-function substrate
- **Goal:** `G^{R/A}(E) = (E − H ± iη)⁻¹`; self-energy `Σ`; spectral function `A = i(G^R − G^A)`; sum rule `∫ A dE/2π = 1`. **Verdict: reachable** — resolvent on existing operator substrate.
- **Why:** the load-bearing object every transport quantity is built from.
- **Bricks:** Mathlib resolvent; `DKMBootstrap/` broadening matrix; `InnerProductSpace.LinearPMap`.
- **Gate:** `negf_spectral_sum_rule` (or equivalent) kernel-pure; `A ⪰ 0`.

## Wave 2 — Landauer–Büttiker conductance
- **Goal:** transmission `T(E) = Tr[Γ_L G^R Γ_R G^A]` (Caroli/Meir–Wingreen); `G = (2e²/h)∫ T(E)(−∂f/∂E) dE`. **Verdict: reachable** — trace formula over W1.
- **Why:** the headline observable.
- **Bricks:** W1 Green's functions; broadening matrices `Γ`; Mathlib `Matrix.trace`.
- **Gate:** `landauer_conductance_def` + linear-response limit, kernel-pure.

## Wave 3 — certified transport bound
- **Goal:** steady-state current; conductance-**quantization theorem** `G = n·G₀` for n open channels + falsifier (`G > n·G₀ ⇒ ⊥`); resolvent-bound envelope. **Verdict: reachable.**
- **Why:** the falsifiable, certificate-grade result.
- **Bricks:** W1+W2; `expNeg_enclosure`-style enclosure.
- **Gate:** `conductance_quantization` + the `norm_num`-backed falsifier, kernel-pure.

## Sequencing
W1 (substrate) → W2 (conductance) → W3 (certified bound). W1 unblocks all. 6BA is independent of 6BB/6BC/6BD.

## Closure
`lake build` + `lake build SKEFTHawking.ExtractDeps` clean; `validate.py` green; counts + Inventory refreshed; root `SKEFTHawking.lean` imports; Stage-13-style strengthening review of new statements; D10 §transport row staged for first-lift; roadmap status updated.
