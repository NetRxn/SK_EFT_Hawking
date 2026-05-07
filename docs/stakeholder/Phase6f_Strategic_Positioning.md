# Strategic Positioning: Phase 6f — The Classical-GR Substrate Layer

## How Phase 6f Built the Language Phase 6g (and Everything Past) Speaks

**Date:** 2026-05-07
**Context:** This memo positions Phase 6f within the broader research program. Phase 6f is CLOSED.

---

## Phase 6f's Strategic Value

Phase 6f delivers a *substrate*, not a result. Its value is unlocking downstream work:

- **Phase 6g** (singularity / area / no-hair theorems) needs Riemann, Ricci, Einstein tensor, energy conditions, and exact solutions as Lean objects. Phase 6f provides them.
- **Phase 6e** (nonlinear effective action) was structurally complete at the heat-kernel-coefficient level but referenced these objects abstractly; Phase 6f makes the references load-bearing.
- **Phase 6a** (linearized EFE / FLRW / GW170817 / BH entropy / BCH four laws) shipped before Phase 6f and used local definitions; Phase 6f's exact-solutions catalog provides a unified cross-reference.
- **The I1 methodology paper** consumes Phase 6f's first-formalization claims as worked evidence that machine-checked theoretical physics produces upstream-grade infrastructure.

Strategically, Phase 6f is the *enabling* phase. Without it, Phase 6g could not have shipped algebraically. With it, Phase 6g lands six waves in days at the abstract-relation scope.

---

## Two Strategic Pillars

### Pillar 1: First Algebraic-GR Backbone in Any Proof Assistant

The Phase 6f deep-research audit confirms: no proof assistant (Coq, Isabelle/AFP, HOL Light, HOL4, Mizar, Agda, pre-Phase-6f Lean 4) had Riemann curvature, Einstein tensor, Bianchi identities, energy conditions, exact GR solutions, or ADM as machine-checked objects. Phase 6f closes that gap entirely.

Audience: the formal-mathematics community (Mathlib working groups, the Lean theorem-proving community at large), mathematical-relativity theorists who care about rigor of GR foundations, and the Bonn / Steinitz / Macbeth differential-geometry-formalization track in Mathlib.

Community partner: the Bonn `CovariantDerivative` track (Massot / Rothgang / Macbeth 2025) — Phase 6f W8 builds *on top of* their landed Mathlib infrastructure with Mathlib upstream conventions, with future PR submissions deferred per the project's "build locally first" policy.

### Pillar 2: Mathlib-Upstream-PR-Shape Infrastructure

W7 catch-up + W8 multi-session build produce Mathlib-style root-namespace lemmas: `IsCovariantDerivativeOn.neg`, `IsCovariantDerivativeOn.sub`, `mlieBracket_neg_right_apply`, `mlieBracket_cyclic_jacobi_apply`, plus the bundle-level Levi-Civita uniqueness via the Koszul argument. These are upstream-quality contributions in latent form.

Audience: the Mathlib probability / differential-geometry working groups; the formal-verification community (CPP, ITP, FSCD).

Community partner: future Mathlib PR cycles when user authorizes upstream submission. The project's policy is "develop in own repo first; submit at end of relevant wave closure" — the W8 work is now closure-eligible.

---

## Bridge Map — How Phase 6f Connects to the Rest

| Bridge | Phase | Status | Cross-bridge to Phase 6f |
|---|---|---|---|
| Algebraic Riemann + Einstein tensor + Λ-vacuum biconditional | 6f W1+W2 | shipped | Substrate for everything downstream |
| Energy conditions (NEC/WEC/DEC/SEC) + counterexample witnesses | 6f W3 | shipped | Phase 6g's Penrose / Hawking–Penrose / area theorems consume directly |
| Exact solutions (Minkowski / dS / AdS / Schwarzschild / FLRW) | 6f W4 | shipped | Phase 6g Wave 4 (Schwarzschild area) + Wave 6 (Kerr) build on this |
| ADM 3+1 decomposition | 6f W5 | shipped | Phase 6g W5 (Cauchy problem structural-Prop scope) |
| Tetrad / vierbein formalism | 6f W6 | shipped | Phase 6e Einstein–Cartan torsion (W6) cross-bridge |
| Lorentzian metric typeclass + Levi-Civita uniqueness | 6f W7+W8 | shipped | Phase 6g W2 curve-theoretic Penrose unblocked |
| Bonn `CovariantDerivative` API (Mathlib) | external | landed | W8 builds on top |

---

## Publication Strategy

Phase 6f produces *no per-wave PRL splash papers*. The content lifts as:

- **D3 §22.5** — algebraic-GR backbone shared substrate for §17–§22 (Phase 6e content) plus §23–§27 (Phase 6g content).
- **I1 sidebar primary** — paper44 (Riemannian connection + Lorentzian metric + Levi-Civita uniqueness, ~5pp) lifts here as the worked methodology case study for Mathlib-PR-quality infrastructure produced as a byproduct of physics formalization.
- **F flagship §6 + §9** — summary mention.

The strategic point: Phase 6f is a substrate phase, and the bundle architecture is correct in not awarding it a standalone deep paper. The I1 methodology paper is the right vehicle.

---

## What Phase 6f Unblocks

- **Phase 6g** ships immediately after Phase 6f closure (the actual ship sequence: W1 through W6 of Phase 6g all shipped at the algebraic-relation scope on a single day, 2026-04-29, leveraging the Phase 6f substrate).
- **Phase 6e cross-references** load-bearing — heat-kernel theorems can now invoke `EinsteinTensor` and `Curvature` directly rather than via local definitions.
- **Phase 6m Track C** Sakharov-criterion cross-bridges use the tetrad formalism directly.
- **Mathlib upstream PR cycle** is a future option when user authorizes; build is to upstream conventions.
- **D3 §22.5** + I1 paper44 lift into the bundle architecture cleanly.

---

## Phase 6f Closure Summary

**Phase 6f is CLOSED.** All six algebraic-precedent waves shipped (W1 W2 W3 W4 W5 W6) plus the W7 catch-up modules (`LorentzianMetric.lean`, `RiemannianConnection.lean`) and the W8 multi-session bundle-level build (`RiemannCoordinate`, `RiemannDifferentialBianchi`, `BundleRiemannAux`, `BundleRiemann`, `LeviCivita`).

**Total Phase 6f numbers:**
- ~80+ substantive Lean theorems / 0 sorry / 0 new axioms across ~13 modules.
- 1 standalone paper (paper44) lifting as I1 sidebar primary + D3 §22.5 supplement.
- ~12 distinct first-formalization-in-any-proof-assistant claims documented.
- Mathlib upstream-PR candidates parked for future user-authorized submission.

The "first algebraic-GR backbone in any proof assistant" claim is the one-line pitch. The longer story is that Phase 6f is the language Phase 6g speaks.

---

## Program Maturity Assessment after Phase 6f

The project's Lean library now possesses the standard algebraic and global-analytic machinery a relativist needs to write a theorem statement. This is the precondition for shipping Phase 6g (singularity / area / no-hair) at speed and for the I1 methodology paper having concrete case studies of upstream-grade infrastructure produced as a byproduct of theoretical-physics formalization.
