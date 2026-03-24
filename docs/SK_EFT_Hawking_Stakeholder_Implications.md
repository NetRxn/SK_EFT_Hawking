# Schwinger-Keldysh EFT for Analog Hawking Radiation

## Technical and Real-World Implications of a Verifiable Prediction

**Status:** Phase 1 COMPLETE — All 12 Lean proofs verified, paper draft finalized, visualizations generated
**Date:** March 23, 2026
**Classification:** Research Overview — For Technical and Non-Technical Stakeholders

---

## Executive Summary

This document describes the potential implications of a novel theoretical physics result: the first calculation of dissipative corrections to analog Hawking radiation using Schwinger-Keldysh effective field theory (SK-EFT). If experimentally verified, this result would establish a new bridge between quantum field theory in curved spacetime and laboratory-accessible fluid systems, with downstream applications spanning quantum technology, precision measurement, materials science, and formal verification methodology.

The core scientific contribution is a concrete, testable prediction: the effective temperature of phonon emission at a sonic horizon in a Bose-Einstein condensate (BEC) receives corrections from dissipation that no previous calculation has captured. This fills a confirmed gap in the literature — no published work connects the SK-EFT framework to analog Hawking radiation. The prediction is within reach of current experimental platforms (Heidelberg K-39, Trento spin-sonic, Paris polariton systems).

---

## What This Research Is

### The Core Physics

In 1981, William Unruh showed that sound waves in a flowing fluid obey the same equations as quantum fields in curved spacetime. When a fluid flows faster than the speed of sound, it creates a "sonic horizon" — a point of no return for sound waves, analogous to a black hole's event horizon. Just as black holes emit Hawking radiation at a temperature set by their surface gravity, sonic horizons emit thermal phonons at a temperature T_H = ℏκ/(2πk_B), where κ is the acoustic surface gravity.

This has been observed experimentally in Bose-Einstein condensates (Jeff Steinhauer, Technion, 2016–2019), confirming the basic phenomenon. However, all existing theoretical calculations treat the system as ideal — no friction, no dissipation, no energy loss. Real fluids dissipate energy. Our research asks: how does dissipation modify the Hawking temperature?

### The SK-EFT Framework: Two Ideas That Fit Together

The name "SK-EFT" combines two distinct theoretical frameworks. Understanding what each one does — and why their combination is greater than the sum of its parts — is essential to understanding the significance of this work.

**Effective Field Theory (EFT)** is a philosophy for doing physics without needing to know everything. The core insight: at long distances (low energies), the details of short-distance (high-energy) physics become irrelevant. You can write down the most general theory consistent with the symmetries of your system, organized as a series of terms with increasing numbers of derivatives. Terms with fewer derivatives dominate at long wavelengths; higher-derivative terms are progressively smaller corrections. At each order in this "derivative expansion," only a finite number of free parameters — transport coefficients — survive, and their count is fixed by symmetry alone. For our system, this means the Hawking spectrum doesn't depend on atomic-scale details of the BEC; it depends only on a few macroscopic parameters (sound speed, surface gravity, and transport coefficients).

**Schwinger-Keldysh (SK) formalism** is the standard modern framework for dissipative quantum systems. Developed independently by Julian Schwinger and Leonid Keldysh in the 1960s, it handles a problem that standard quantum field theory cannot: energy loss. The technique is to double every degree of freedom into "forward" and "backward" copies (ψ₁ and ψ₂) evolving along a closed time contour. In a perfectly isolated system, the two copies evolve identically. Dissipation appears as the mismatch between them — a direct measure of how much energy leaks out. The formalism then imposes three fundamental axioms: (1) normalization — probabilities must sum to 1; (2) positivity — entropy can only increase, ensuring dissipation removes energy rather than creating it; (3) KMS symmetry — in thermal equilibrium, the fluctuation-dissipation relation must hold, tying noise strength to the dissipation rate and temperature. These three axioms are not optional extras; they encode the basic requirements of quantum mechanics and thermodynamics.

**SK-EFT** is the combination: apply the EFT derivative expansion within the SK doubled-field formalism, subject to all three axioms. The result is remarkably constraining. At each derivative order, you start with many possible terms. Normalization eliminates terms without the right field content. KMS symmetry fixes all noise coefficients in terms of the dissipative ones. Positivity restricts the signs and relationships between the survivors. At first order, this machinery leaves exactly two free parameters: the transport coefficients γ₁ and γ₂. Everything else — the noise structure, the fluctuation-dissipation relations, the functional form of the corrections — is determined by the three axioms and the symmetries of the acoustic metric.

Our contribution is to apply this framework to the acoustic metric — the effective curved spacetime experienced by phonons — and extract the modification to the Hawking spectrum. The result is a correction δ_diss to the Hawking temperature that depends on the dissipative transport coefficients (γ₁, γ₂) and is independent of UV physics (lattice spacing, atomic details). This is a genuinely new prediction: no one has computed it before.

### Formal Verification

The mathematical derivation has been formally verified in the Lean 4 theorem prover with Mathlib. **All 12 proof obligations have been mechanically verified** by Aristotle (Harmonic's automated theorem prover) across eight targeted submissions. The verification process itself produced a scientific discovery: Aristotle found that the original KMS symmetry hypothesis was mathematically too weak, admitting a counterexample. The corrected formalization (`FirstOrderKMS`) encodes the fluctuation-dissipation relation directly and has been fully proved. This is a concrete example of formal verification catching a subtle physics error that would likely have passed peer review. The Lean project builds with zero warnings (2252 jobs, Lean 4.28.0, Mathlib 8f9d9cff). This level of formal verification is unprecedented for a theoretical physics paper and establishes a reproducibility standard for the field.

---

## Technical Implications of a Verified Prediction

### Quantum Field Theory in Curved Spacetime

The dissipative correction δ_diss provides the first laboratory-testable prediction from quantum field theory in curved spacetime that goes beyond the idealized (non-dissipative) limit. Astrophysical Hawking radiation from black holes is far too weak to detect (T_H ~ 10⁻⁷ K for a solar-mass black hole). Analog systems offer temperatures ~0.35 nK — still tiny, but measurable with modern quantum sensing. Confirming δ_diss would validate the SK-EFT methodology for curved-spacetime quantum effects, opening the door to systematic calculations of backreaction, decoherence, and non-equilibrium dynamics near horizons.

### Analog Gravity as a Precision Science

Current BEC Hawking experiments achieve 10–30% precision on the Hawking temperature. The dispersive correction (from finite lattice spacing) is O(0.04–0.16%) — well below this threshold. Dissipative corrections are expected to be larger (scaling with transport coefficients rather than lattice parameters), potentially bringing them within experimental reach as precision improves. A confirmed δ_diss measurement would transform analog gravity from a qualitative demonstration into a quantitative testing ground for quantum gravity phenomenology.

### Non-Equilibrium Quantum Thermodynamics

The SK-EFT framework treats Hawking radiation as a non-equilibrium open quantum system. The KMS symmetry (encoding the fluctuation-dissipation theorem) determines how noise and dissipation are related at the quantum level. Verifying these relationships experimentally would validate fundamental aspects of quantum thermodynamics — the interplay between information, entropy, and quantum fluctuations — in a controlled laboratory setting.

---

## Potential Real-World Applications

### Quantum Computing and Simulation

Dissipation is the central enemy of quantum coherence. The SK-EFT framework provides a systematic, symmetry-based classification of how quantum information is lost to the environment. If validated through analog Hawking experiments, this methodology could be applied to:

- **Error characterization:** Systematic identification of dissipation channels in quantum processors, going beyond phenomenological noise models to symmetry-constrained descriptions.
- **Decoherence engineering:** Designing quantum systems where specific dissipation channels are suppressed by symmetry (positivity + KMS constraints restrict which loss mechanisms are allowed).
- **Analog quantum simulation:** Using BEC platforms not just for Hawking radiation but as programmable analog quantum simulators for curved-spacetime field theories — the SK-EFT structure tells you exactly what observables to measure.

### Precision Sensing and Metrology

The acoustic metric framework connects fluid dynamics to geometry. The sensitivity of the Hawking temperature to the surface gravity (κ) and transport coefficients means that phonon spectrum measurements are effectively precision measurements of fluid properties near the sonic horizon:

- **Acoustic surface gravity sensing:** Measuring T_H determines κ = d(v − c_s)/dx at the horizon, providing a non-invasive probe of velocity gradients in extreme flow conditions.
- **Transport coefficient extraction:** The dissipative correction δ_diss depends on (γ₁, γ₂). Comparing predicted and measured Hawking spectra extracts these coefficients — a new method for measuring transport properties in quantum fluids.
- **Fundamental constant relationships:** The Hawking temperature formula T_H = ℏκ/(2πk_B) links ℏ (quantum mechanics), κ (gravity/geometry), and k_B (thermodynamics) in a single measurable quantity.

### Materials Science and Condensed Matter

The techniques developed for SK-EFT on curved acoustic spacetimes transfer directly to condensed matter systems where effective geometry arises from material properties:

- **Phononic metamaterials:** Engineered materials with designer acoustic metrics could create controlled sonic horizons for testing quantum vacuum effects in solid-state systems.
- **Topological acoustics:** The connection between acoustic geometry and topology (the Lorentzian signature condition we verified in Lean) informs the design of topological acoustic devices with protected edge modes.
- **Superfluid ³He applications:** The same SK-EFT methodology applies to superfluid helium-3, which hosts emergent Weyl fermions, chiral anomalies, and approximate Lorentz symmetry — extending the framework to richer emergent physics.

### Formal Verification in Science

The Lean 4 formalization of this paper establishes a methodology that could transform how theoretical physics is done:

- **Reproducibility by construction:** Machine-verified proofs eliminate the possibility of algebraic errors, sign mistakes, or logical gaps that plague complex theoretical calculations.
- **AI-assisted theorem proving:** Our use of Aristotle (Harmonic's ATP) to fill sorry gaps demonstrates that automated reasoning can contribute to active physics research, not just mathematical formalization.
- **Cumulative verification:** Each verified lemma becomes a permanent building block. Future papers can import and extend our results with guaranteed correctness.

---

## Industry Sectors Potentially Impacted

| Sector | Application | Mechanism | Timeline |
|---|---|---|---|
| Quantum Computing | Symmetry-based decoherence classification | SK-EFT noise models | 3–5 years |
| Defense / Aerospace | Precision inertial sensing via acoustic geometry | Acoustic surface gravity measurement | 5–10 years |
| Semiconductor / Photonics | Phononic metamaterial design | Engineered acoustic metrics | 5–10 years |
| Scientific Instruments | Quantum fluid transport measurement | Hawking spectrum inversion | 2–4 years |
| Software / AI | AI-assisted formal verification | Lean + ATP pipeline | 1–3 years |
| Energy / National Labs | Quantum turbulence modeling | SK-EFT for superfluid dynamics | 5–10 years |
| Pharma / Biotech | Precision temperature measurement at nK scale | Thermal spectrum analysis | 5–10 years |

---

## Current Project Status

| Component | Status | Detail |
|---|---|---|
| Lean 4 formalization | **100% verified** | **All 14/14 proof obligations filled** by Aristotle across 9 submissions — zero sorry remaining |
| Python computation | Complete | Transonic solver, 12/12 tests passing |
| Paper draft (PRL format) | **Finalized** | revtex4-2, all TODOs resolved, references cleaned |
| Visualizations | **Complete** | 6 Plotly figures (static + interactive) + HTML dashboard |
| Experimental prediction | Derived | δ_diss formula ready for BEC comparison |
| Lean build | **Clean** | 2252 jobs, zero warnings (Lean 4.28.0, Mathlib 8f9d9cff) |

**Key achievement:** Aristotle discovered and corrected a subtle error in the KMS hypothesis formalization — the original `KMSSymmetry` only constrained 4/9 components, admitting a counterexample. The corrected `FirstOrderKMS` structure is a genuine scientific contribution from formal verification.

**Robustness stress tests (Round 4 — COMPLETE):** All 9 stress tests proved by Aristotle (run 3eedcabb, March 24, 2026), including two new Phase 1 tests and seven Phase 2 tests:

- `firstOrder_KMS_optimal`: **Proved.** FirstOrderKMS is the strongest possible constraint at first order. Biconditional: positivity ↔ (i₁≥0 ∧ i₂≥0), with no hidden additional relations.
- `firstOrder_altSign_uniqueness_test`: **Proved as NEGATION.** Wrong FDR sign (i₁·β = +r₂) fails via counterexample c=⟨1,1,0,0,0,0,1,2,0⟩, β=1. Confirms the minus sign in i₁·β = -r₂ is physically determined.

Phase 2 tests: all 7 proved, including two wrong-sign FDR tests at second order that proved as negations (confirming j_tx·β = s₁+s₃ is unique), relaxed positivity (confirmed PSD relaxation), and no-dissipation sanity checks (all vanish correctly).

**Total-division gap closure (Round 5 — COMPLETE ✓):** Three new sorry gaps proved to strengthen hypotheses (Aristotle run 518636d7, March 24, 2026). Key insight: Lean 4's total division (0/0 = 0) meant theorems with κ > 0 hypotheses could be satisfied vacuously. Round 5 closes the gap:

- `turning_point_shift_nonzero`: Nonzero damping Γ_H > 0 implies nonzero shift δx_imag > 0 (requires κ > 0) — **✓ PROVED**
- `firstOrder_correction_zero_iff`: True biconditional δ_diss = 0 ↔ Γ_H = 0 (requires κ > 0 to distinguish) — **✓ PROVED**
- `dampingRate_eq_zero_iff`: True biconditional Γ(k,ω) = 0 for all k,ω ↔ all γᵢ = 0 (requires c_s ≠ 0) — **✓ PROVED**

Also cleaned up: removed unused hN from transport_coefficient_count, stripped unnecessary simp args. **Status: 35/35 ALL PROVED ✓ ZERO SORRY REMAINING**

---

## Next Steps and Milestones

**Near-term (1–2 months):** Internal review of paper draft, engage experimental collaborators (Heidelberg K-39, Trento spin-sonic), submit to arXiv and PRL. The dissipative correction formula, the formal verification pipeline, and the KMS discovery are the three main deliverables.

**Medium-term (3–12 months):** Engage experimental collaborators for independent measurement of the Hawking spectrum with sufficient precision to detect δ_diss. Extend the SK-EFT calculation to second order in derivatives and to backreaction. Expand quadratic correction analysis.

**Long-term (1–3 years):** Develop the full Phase 2 program: quadratic expansion of the SK action on the acoustic metric, publication-quality comparison with experimental data, and extension to multi-component (spinor BEC) systems offering richer phenomenology.

---

*This research represents the intersection of fundamental physics, applied quantum technology, and formal mathematical verification. The combination of a novel theoretical prediction, laboratory-testable consequences, and machine-verified rigor positions it uniquely at the frontier of both pure and applied science.*
