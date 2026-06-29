# Phase 6CE — Effective-Medium Homogenization (Maxwell–Garnett)

**Status: PLANNED (authorized 2026-06-29).** A certified quasi-static effective-medium theory via the **algebraic Maxwell–Garnett** mixing formula, plus certified effective-parameter bounds. Clean whitespace (no two-scale / Maxwell–Garnett in any prover). Distinct phase in the `6C*` materials series.

**Substrate (verified 2026-06-29 — PhysLib source read + lean MCP):**
- **Reuse (exists):** Mathlib field arithmetic; project `QuantumNetwork/NumericalBounds.expNeg_enclosure` (rational two-sided enclosure); Mathlib `FunctionalSpaces.SobolevInequality` (GNS *inequalities* only).
- **Absent → build:** `MaxwellGarnett` 0 in PhysLib + project; two-scale / periodic homogenization absent — Mathlib has Sobolev *inequalities*, not two-scale convergence, and PhysLib `Optics/Basic.lean` is an **explicit placeholder** (its own docstring reads *"This directory is currently a place holder"*; only `Optics/Polarization` exists, unrelated; no `OpticalMedium` / effective-medium type).
- **New content:** the algebraic quasi-static Clausius–Mossotti / Maxwell–Garnett `ε_eff`; Hashin–Shtrikman two-sided enclosure; elastic analog.

> **⚠️ GUARDRAIL — algebraic path ONLY.** Do **not** attempt full two-scale / periodic-homogenization convergence (the documented substrate-stall above). Use only the algebraic derivation — finite-dim algebra + `expNeg_enclosure`.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening checklist; never push. **Two-layer honesty:** the mixing *formula* + bounds are Lean-verified; the physical-composite identification (dilute limit, sphere geometry) stays literature-cited in the module header. Wave sizing ≈ one `/goal` (≤ ~5M tokens). Frame purely as physics.

**Bundle target:** **D11** (authorized 2026-06-29; §homogenization), shared with 6CA/6CB/6CD. Roster-expansion mechanics at first content-lift.

---

## Wave 1 — Maxwell–Garnett formula
- **Goal:** the quasi-static effective permittivity `ε_eff(ε_h, ε_i, f)` (host `ε_h`, inclusion `ε_i`, fill fraction `f`); the Clausius–Mossotti derivation in the dilute limit. **Verdict: reachable** — algebraic identity + a clean limit.
- **Why:** the canonical macroscale effective-parameter formula metamaterial design relies on.
- **Bricks:** finite-dim algebra; Mathlib field arithmetic.
- **Gate:** `maxwellGarnett_eps_eff` + the `f → 0` host-recovery limit, kernel-pure.

## Wave 2 — certified effective-parameter bounds
- **Goal:** a **Hashin–Shtrikman**-style two-sided enclosure on `ε_eff`; an interval-arithmetic certificate (rational brackets). **Verdict: reachable.**
- **Why:** turns the formula into a certificate-grade bound (the design-relevant guarantee).
- **Bricks:** W1; `expNeg_enclosure`-style interval arithmetic.
- **Gate:** `effectiveMedium_hashinShtrikman_enclosure` (`norm_num`-backed) kernel-pure.

## Wave 3 — elastic / acoustic effective moduli
- **Goal:** the effective bulk/shear moduli of a composite via the same algebraic mixing + enclosure (the elastic analog of W1/W2). **Verdict: reachable.**
- **Why:** extends the certificate from electromagnetic to mechanical metamaterials (ties to 6CB's acoustic substrate).
- **Bricks:** W1/W2; elastic-modulus mixing rules.
- **Gate:** `effectiveModuli_enclosure` kernel-pure.

## Sequencing
W1 (formula) → W2 (bounds) → W3 (elastic analog). Independent of 6CA–6CD. Algebraic path throughout — two-scale stays out of scope.

## Closure
`lake build` + ExtractDeps clean; `validate.py` green; counts + Inventory refreshed; root imports; strengthening review; algebraic-path-only + two-scale-out-of-scope documented; D11 §homogenization row staged for first-lift; roadmap status updated.
