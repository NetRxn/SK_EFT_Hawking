# Phase 6BA — Verified Quantum Transport (NEGF / Landauer–Büttiker)

**Status: PLANNED (authorized 2026-06-29).** First machine-checked non-equilibrium Green's-function (NEGF) steady-state transport: retarded/advanced Green's functions, the Landauer–Büttiker / Meir–Wingreen conductance, and a certified conductance-quantization bound. No NEGF Green's-function / Landauer-*conductance* transport exists in any proof assistant. One of the public substrate-breadth phases scoped 2026-06-29 (companion chemistry phases 6BB–6BD; materials phases 6CA–6CE); the PhysLib unbounded-operator resolvent makes the new transport layer MODERATE, not greenfield-expensive. Distinct double-letter phase in the `6B*` (computational-chemistry) series, independent of the unrelated `6A`/`6b`.

**Substrate (verified 2026-06-29 — PhysLib source read + lean MCP `loogle`/`leansearch`):**
- **Reuse (exists):** PhysLib `…/Operators/SpectralTheory/Basic.lean` — `resolvent (T : H →ₗ.[ℂ] H) (z) := (T - z • 1).inverse` (unbounded-operator resolvent on Mathlib `LinearPMap`) + `defectNumber`/numerical-range API; project `GrapheneNoiseFormula.lean` — `hawkingNoisePSD`, `johnsonNyquistPSD`, `snrPerBin` (the existing Keldysh + Landauer–Büttiker *noise* spectrum the conductance result ties into); project `QuantumNetwork/NumericalBounds.lean` `expNeg_enclosure` (rational enclosure).
- **Absent → build (confirmed):** NEGF Green's functions + Landauer *conductance* — 0 hits in Mathlib, PhysLib, and the project (the project's only Landauer–Büttiker content is the noise PSD above, **not** the Green's-function conductance).
- **New content:** `G^{R/A}`, spectral function `A`, transmission `T(E)=Tr[Γ G^R Γ G^A]`, conductance — on PhysLib `resolvent` + Mathlib finite-dim `Matrix`.
- **Correction (was a planning miss):** `DKMBootstrap/` is **not** a brick — it is an SK-EFT SDP transport *bootstrap* (`IsDKMSpectralFunction` predicate, `horizon_transport_uniqueness_graphene_witness_one_half`, `sharpened_no_go_super_factorial`) with **no** NEGF broadening/Green's-function machinery; at most a thematic SK-EFT transport cross-bridge, not load-bearing here.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` in proof bodies (#10); preemptive-strengthening checklist before each statement; decompose-before-asserting-walls; never push. **Two-layer honesty:** the transport *formulas* are Lean-verified; the device/material identification stays literature-cited in the module header. Wave sizing ≈ one `/goal` (≤ ~5M tokens) — a chunking heuristic, not a time estimate (PM/time estimates remain banned). Frame purely as physics (dual publication + flagship scope).

**Bundle target:** **D10** (authorized 2026-06-29) — "Kernel-Verified Foundations of Computational Quantum Chemistry & Open-System Dynamics" *(provisional)*, shared with 6BB/6BC. Roster-expansion mechanics (`PAPER_STRATEGY` roster, `_VALID_BUNDLE_TARGETS`, `papers/D10/` scaffold) execute at **first content-lift** per `BUNDLE_LIFT_PROCEDURE` — not at planning time (avoids standing up an empty bundle).

---

## Wave 1 — NEGF Green's-function substrate
- **Goal:** `G^{R/A}(E) = (E − H ± iη)⁻¹`; self-energy `Σ`; spectral function `A = i(G^R − G^A)`; sum rule `∫ A dE/2π = 1`. **Verdict: reachable** — resolvent on existing operator substrate.
- **Why:** the load-bearing object every transport quantity is built from.
- **Bricks:** PhysLib `SpectralTheory.Basic.resolvent` (on `H →ₗ.[ℂ] H`); Mathlib `LinearPMap`; finite-dim `Matrix`. (Broadening matrices `Γ` are defined here — new, not from DKMBootstrap.)
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
