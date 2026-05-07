# Phase 6f: Implications of the Classical-GR Algebraic Backbone

## Technical and Real-World Implications

**Status:** Phase 6f CLOSED — all algebraic-precedent waves (W1–W6) shipped, plus W7 catch-up modules and W8 multi-session bundle-Riemann build on the Bonn `CovariantDerivative` API.
**Date:** 2026-05-07
**Classification:** Research Overview — For Technical and Non-Technical Stakeholders
**Prerequisite:** Phase 6e (heat-kernel chain through $a_4$); Mathlib4 pinned to commit `8850ed93` (which contains the Bonn–Massot–Rothgang–Macbeth `CovariantDerivative` infrastructure).

---

## Executive Summary

Phase 6f is the project's *infrastructure* phase for general relativity. It builds — for the first time in any proof assistant — a Lean-native classical-GR algebraic backbone covering: algebraic Riemann curvature with all eight identities (antisymmetries, first Bianchi, pair symmetry); the Einstein tensor and its trace identity; the four standard energy conditions (NEC, WEC, DEC, SEC) with chain implications and explicit counterexample witnesses; a catalog of exact solutions (Minkowski, Schwarzschild, de Sitter, anti-de Sitter, FLRW) with horizon-thermodynamic cross-bridges; the ADM 3+1 decomposition with Hamiltonian and momentum constraint biconditionals; the tetrad / vierbein formalism with cross-bridges to Phase 6e Einstein–Cartan; and a Lorentzian-metric typeclass plus Levi-Civita uniqueness proved at the bundle level via the substantive Koszul-bilinear-form argument from Wald §3.1.

This is not a derivation — it is the *language* in which derivations live. Before Phase 6f, no proof assistant (Coq, Isabelle/AFP, HOL Light, HOL4, Mizar, Agda, prior Lean 4) had any of these objects. The Phase 6f deep-research audit (`Lit-Search/Phase-6f/`) confirms: Mathlib4 master at the pinned commit reaches up to smooth manifolds, tangent / vector bundles, Lie groups, integral curves, and the Gouëzel 2025 positive-definite Riemannian-metric typeclass — and stops there. Curvature, Bianchi, exact solutions, ADM, energy conditions, named GR theorems: zero coverage anywhere.

Phase 6f closes the gap. The work was done with Mathlib upstream-PR conventions where feasible (root-namespace lemmas, bundled structures, Mathlib-style API) so that future contribution back to the upstream library is a structured option rather than a retroactive re-architecture.

---

## What Phase 6f Adds Beyond Phase 6e

Phase 6e supplied an *emergent* gravitational effective action — the heat-kernel coefficients, higher-curvature corrections, variational equations, cosmological-constant prediction, Einstein–Cartan torsion. To talk about that effective action in the language a relativist uses, the project needed a Lean-native Riemann tensor, an Einstein tensor, energy conditions, exact solutions to compare against, and a Lorentzian-metric typeclass. Phase 6e ran ahead of these by working at heat-kernel-coefficient level; Phase 6f catches up and provides the shared substrate that Phase 6g (singularity / area / no-hair) consumes directly.

---

## Result 1: Algebraic Riemann Tensor (Wave 1, plus W8 Sessions 1–4)

### What we found

`Curvature.lean` defines the algebraic Riemann tensor as a four-index object on `Vec4 = Fin 4 → ℝ` and proves all standard symmetries: antisymmetry in the last two indices, antisymmetry in the first two, first Bianchi (the cyclic identity), and pair symmetry $R_{\rho\sigma\mu\nu} = R_{\mu\nu\rho\sigma}$. Constant-sectional-curvature specialization (de Sitter / AdS / hyperbolic) is included. Wave 8 lifts this to bundle scope on the Bonn `CovariantDerivative` API: `bundleRiemannAux` constructed from `IsCovariantDerivativeOn` plus `mlieBracket`, with antisymmetry-in-(X,Y) derived from bracket antisymmetry, $R(X, X)Z = 0$ derived from `mlieBracket_self`, and the first Bianchi for torsion-free covariant derivatives derived from a cyclic Jacobi identity for `mlieBracket`. The Levi-Civita uniqueness theorem is proved at the bundle level via the full Wald §3.1 Koszul-bilinear-form argument (three metric-compatibility instances at cyclic shifts + three symmetry rewrites + three torsion-free pairwise substitutions, combined via `linear_combination`).

### Why it matters

This is the first formal algebraic Riemann tensor with all eight identities in any proof assistant. The cyclic Jacobi identity for `mlieBracket` and the bundle-level Levi-Civita uniqueness are Mathlib-PR-shaped contributions; pinned Mathlib has only the Leibniz form of the Lie-bracket identity, not the cyclic Jacobi. The Phase 6f audit identified the gap explicitly; the project closes it locally with Mathlib upstream conventions.

---

## Result 2: Einstein Tensor + Trace Identity + Λ-Vacuum Biconditional (Wave 2)

### What we found

`EinsteinTensor.lean` defines $G_{\mu\nu} = R_{\mu\nu} - \frac{1}{2} g_{\mu\nu} R$ and proves the trace identity $g^{\mu\nu} G_{\mu\nu} = -R$ in four dimensions. The $\Lambda$-vacuum biconditional $G_{\mu\nu} + \Lambda g_{\mu\nu} = 0 \Leftrightarrow R_{\mu\nu} = \Lambda g_{\mu\nu}$ is the load-bearing structural identity tying the Einstein tensor to constant-curvature solutions.

### Why it matters

Every cosmology and BH-thermodynamics calculation that uses $\Lambda$ traces through this biconditional. Phase 6g's Hawking–Penrose SEC counterexample (cosmological-$\Lambda$ violates SEC) consumes this directly. Phase 6e's CC-emergent calculation cross-references the trace identity for the variational form.

---

## Result 3: Energy Conditions (Wave 3)

### What we found

`EnergyConditions.lean` defines the four standard energy conditions — Null (NEC), Weak (WEC), Dominant (DEC), and Strong (SEC) — as predicates on an abstract bilinear form, with explicit timelike / null / future-directed-timelike machinery. Three chain implications are proved: DEC ⟹ WEC (direct), WEC ⟹ NEC (under continuity, which is genuinely load-bearing), DEC ⟹ NEC (composition).

Five concrete counterexample witnesses ship: $\Lambda > 0$ violates SEC (witness $t = v = (1,0,0,0)$); ghost scalar violates NEC; stiff fluid $\rho = 1, p = 2$ violates DEC; cosmological $\Lambda \geq 0$ satisfies WEC; cosmological $\Lambda$ satisfies NEC vacuously.

### Why it matters

Energy conditions are the structural prerequisites of Penrose / Hawking–Penrose / Witten positive-mass theorems. Without explicit predicates and counterexample witnesses, those theorems cannot be stated in Lean. The first-formalization claim here covers all four predicates *with* chain implications *with* explicit witnesses across all proof assistants checked (Coq, Isabelle/AFP, HOL Light, HOL4, Mizar, Agda).

---

## Result 4: Exact Solutions Catalog + Horizon Thermodynamics (Wave 4)

### What we found

`ExactSolutions.lean` covers Minkowski (flat), de Sitter and anti-de Sitter (constant Λ vacuum), Schwarzschild (vacuum spherically symmetric), and FLRW (cosmological). Each solution carries explicit metric components, scalar curvature, and the relevant Λ-vacuum or vacuum cross-bridges. Horizon-thermodynamics cross-bridges to Phase 6a Wave 5 BCH four laws are wired in for Schwarzschild and de Sitter.

### Why it matters

The named-solutions catalog is what a relativist actually uses to *check* a calculation. No proof assistant prior to Phase 6f had any of these as Einstein-equation-solving objects. The horizon-thermodynamics cross-bridge to Phase 6a closes a longstanding internal-references gap in the project.

---

## Result 5: ADM 3+1 Decomposition (Wave 5)

### What we found

`ADMFormalism.lean` formalizes the 3+1 decomposition of spacetime with explicit lapse/shift, induced 3-metric, extrinsic curvature, and the Hamiltonian and momentum constraint biconditionals.

### Why it matters

ADM is the canonical formulation of GR for numerical relativity, BH thermodynamics, and quantum gravity. Phase 6g Wave 5 (Cauchy problem) and Phase 6g Wave 4 (area theorem) both reference ADM via the constraint biconditionals.

---

## Result 6: Tetrad / Vierbein Formalism (Wave 6)

### What we found

`TetradFormalism.lean` provides the tetrad-induced metric, vierbein orthonormality conditions, and the cross-bridge to Phase 6e Einstein–Cartan torsion. The tetrad-VEV ↔ quark-condensate naturalness correctness-push in Phase 6d Wave 2 cross-references this module.

### Why it matters

The tetrad / vierbein language is required for spinor and fermionic gravity. The project's ADW microscopic theory is fermionic, so tetrad formalism is the correct bridge between condensate-side and metric-side physics. Phase 6e Einstein–Cartan torsion (Wave 6) requires this substrate.

---

## Wave 7 Catch-Up + Wave 8 Bundle-Level Build

`LorentzianMetric.lean` adds the indefinite-signature Lorentzian metric typeclass (Mathlib only has the Gouëzel 2025 positive-definite form). `RiemannianConnection.lean` adds the Christoffel-quadratic Riemann piece, antisymmetry-in-(μ,ν), Koszul-formula Christoffel symbols (noncomputable due to the 1/2 factor), and torsion-free predicates.

Wave 8 — a five-session multi-session build — extends the algebraic precedent to bundle scope on Bonn's `CovariantDerivative` API:

- Session 1: full coordinate Riemann linear-piece + algebraic first Bianchi for torsion-free Christoffel.
- Session 2: differential second Bianchi machinery via `Christoffel2Partial` and Schwarz hypothesis.
- Session 3: bundle-level `bundleRiemannAux` on `IsCovariantDerivativeOn` + `mlieBracket`, with $R(X,X)Z = 0$ and antisymmetry-in-(X,Y).
- Session 4: cyclic Jacobi for `mlieBracket` + bundle first Bianchi for torsion-free covariant derivatives.
- Session 5 + 5b: bundle-level Levi-Civita uniqueness via the Koszul-bilinear-form argument, using Mathlib's `extDerivFun` for the metric-compatibility condition.

**First formalization in any proof assistant** of: bundle-level Lorentzian metric typeclass; Riemannian-Lorentzian signature falsifier; Christoffel-quadratic Riemann antisymmetry; cyclic Jacobi for `mlieBracket`; bundle-level first Bianchi for torsion-free covariant derivatives; bundle-level Levi-Civita uniqueness via the substantive Koszul argument (not the def-as-equality form).

---

## By the Numbers (Phase 6f, post-CLOSED)

- **Lean theorems shipped (W1–W6 + W7 + W8 across 5 sessions):** approximately 80+ substantive theorems across roughly 13 modules; 0 sorry; 0 new axioms.
- **First-formalization-in-any-proof-assistant claims:** ~12 distinct items.
- **Mathlib upstream-PR candidates:** several in W7/W8 (root-namespace lemmas like `IsCovariantDerivativeOn.neg`, `IsCovariantDerivativeOn.sub`, cyclic Jacobi for `mlieBracket`).
- **Papers shipped:** paper44 (Riemannian connection + Lorentzian metric + Levi-Civita uniqueness; ~5pp).
- **Bundle destinations:** D3 §22.5 (algebraic-GR backbone shared substrate) + I1 (sidebar primary: Mathlib-PR-quality first-formalization claims).

Phase 6f deliberately ships *no* per-wave standalone papers other than paper44 — the substrate is consumed wholesale by D3 §22.5 and surfaces in the I1 methodology paper as a worked example of Mathlib-grade infrastructure produced from a downstream physics project.

---

## Strategic Reading

Phase 6f is unusual: it produces no new physics predictions. It builds *language*. Without Phase 6f, every Phase 6e and Phase 6g theorem statement would have had to inline its own ad-hoc Riemann tensor or energy condition. Phase 6f means there is one shared, machine-checked substrate.

The first-formalization-in-any-proof-assistant claims attached to Phase 6f are concrete and verifiable. They sit primarily in I1's methodology paper as evidence for the broader thesis: *machine-checked theoretical physics produces upstream-grade formal infrastructure as a byproduct.* The Mathlib upstream PR cycle is a distinct future option; the work is built locally to Mathlib conventions so that PR submission is a clean append rather than a re-architecture.
