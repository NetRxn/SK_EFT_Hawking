# SK-EFT Hawking Paper: Educational Companion Guide

## Executive Summary

This project computes a fundamental correction to Hawking radiation—one of physics' most profound predictions—in table-top laboratory experiments using cold atoms. Specifically, we calculate how friction in the fluid affects the temperature of "analog Hawking radiation" in Bose-Einstein condensates (BECs). This work combines rigorous mathematical proof-checking with numerical computation to produce experimentally testable predictions.

---

## 1. What Is This Project About?

### The Central Idea: Sound Waves Mimic Black Holes

Imagine you're on a riverbank watching water rush past. If the water flows faster than the speed of waves on that water, something remarkable happens: waves can no longer propagate downstream. They get trapped. This is a surprisingly accurate analog for what happens near a black hole's event horizon—except with light instead of water waves.

In a Bose-Einstein condensate (an exotic state of matter where atoms behave as a single quantum entity), you can create exactly this situation with sound waves. Researchers engineer a flowing condensate so the fluid moves faster than the speed of sound at one location. This creates an "acoustic horizon"—a boundary from which sound particles (phonons) cannot escape, just like light cannot escape beyond a black hole's event horizon.

Here's the profound part: Stephen Hawking predicted in 1974 that black holes are not actually black. They leak radiation because near the event horizon, quantum fluctuations spontaneously create pairs of particles. One particle falls in; the other escapes, carrying away energy. This effect, called Hawking radiation, has never been directly observed at actual black holes (because it's incredibly faint). But in the laboratory, the same quantum mechanism can occur in flowing fluids, producing detectable "analog Hawking radiation." The condensate experiment is a way to test one of the deepest predictions in physics using equipment that fits on an optical table.

### Why This Matters

Hawking radiation is more than an exotic prediction—it fundamentally connects quantum mechanics, gravity, and thermodynamics. By studying it in the lab using quantum fluids, we can:

- **Test the physics** without waiting for a real black hole
- **Understand dissipation** (energy loss) in quantum systems, which real systems always have
- **Develop new mathematical tools** that apply across physics—from black holes to condensed matter

### The Temperature Scale

The Hawking temperature in current BEC experiments is astonishingly cold: approximately **0.35 nanokelvin**—that's a billionth of a degree above absolute zero. Detecting a correction this small is extraordinarily challenging, but it's precisely the kind of fundamental test that advances our understanding.

---

## 2. What's New Here?

### The Missing Piece: Dissipation

All previous theoretical calculations of Hawking radiation in condensate systems have made a simplifying assumption: the fluid is perfectly frictionless. In reality, every fluid loses energy through dissipation (internal friction, viscosity, and other loss mechanisms). For real BECs, dissipation is small but non-zero.

The question we answer is: **How much does dissipation change the Hawking temperature?**

This is not a trivial correction. Previous work established the basic physics of analog Hawking radiation. But to make precision predictions—especially for next-generation experiments designed to measure these tiny effects—we need to understand every source of correction. Our work fills this gap.

### The Mathematical Machinery: What is SK-EFT?

The name "SK-EFT" combines two powerful frameworks in theoretical physics. Understanding each one — and why they fit together — is key to understanding this project.

#### Part 1: Effective Field Theory (EFT) — Ignoring What Doesn't Matter

Effective Field Theory is a philosophy as much as a technique. The core idea: you don't need to know everything about a system to make precise predictions about the things you care about.

Consider water waves on the ocean. To predict how a 10-meter wave behaves, you don't need to track every water molecule. The atomic details are irrelevant at the scale of ocean waves — what matters is the water's density, its surface tension, and the depth of the ocean. EFT formalizes this intuition into a systematic mathematical framework.

In an EFT, you write down the most general theory consistent with the symmetries of your system, organized by a "derivative expansion" — terms with fewer derivatives (smoother, longer-wavelength physics) come first, and terms with more derivatives (sharper, shorter-wavelength physics) are progressively smaller corrections. The beauty is that this works without knowing the microscopic theory at all. You parameterize your ignorance with a finite number of "transport coefficients" at each order, and symmetry constrains how many there can be.

For our BEC system: the microscopic theory involves billions of interacting rubidium (or potassium, or sodium) atoms obeying the Gross-Pitaevskii equation. The EFT description replaces all that complexity with a handful of parameters — the speed of sound, the surface gravity, and the transport coefficients γ₁, γ₂ — that capture everything the Hawking spectrum cares about. This is why the prediction is robust: it doesn't depend on atomic-scale details.

#### Part 2: Schwinger-Keldysh (SK) Formalism — Handling Dissipation Quantum-Mechanically

Standard quantum field theory is built for isolated systems in perfect equilibrium. It describes particles being created and destroyed without any energy leaking out. But real systems lose energy — to friction, viscosity, radiation, coupling to the environment. Standard methods can't handle this.

The Schwinger-Keldysh formalism (developed independently by Julian Schwinger and Leonid Keldysh in the 1960s) solves this problem with an elegant trick: double every degree of freedom. Instead of one quantum field ψ, you work with two copies: ψ₁ (evolving "forward" in time) and ψ₂ (evolving "backward"). The key insight is that dissipation shows up as a mismatch between these two copies. In a perfectly isolated system, the forward and backward evolutions are identical. When energy leaks out, they differ — and that difference encodes exactly how much energy is lost and where it goes.

To make this concrete, think of double-entry bookkeeping. A business tracks money flowing in (revenue) and money flowing out (expenses) in parallel ledgers. Any discrepancy between the two reveals where money was gained or lost. The SK formalism does the same thing for quantum energy flow: the "forward" and "backward" field copies are two ledgers, and dissipation appears as the discrepancy between them.

The SK formalism then imposes three fundamental axioms that any physically sensible dissipative theory must satisfy:

1. **Normalization:** Probabilities must add up to 1. This eliminates unphysical terms in the action.
2. **Positivity:** Entropy can only increase (the second law of thermodynamics at the quantum level). This ensures dissipation always removes energy from the system, never adds it.
3. **KMS Symmetry:** In thermal equilibrium, the fluctuation-dissipation relation must hold — the strength of random noise is exactly determined by the dissipation rate and the temperature. This is the quantum version of Einstein's 1905 insight that Brownian motion and viscosity are two sides of the same coin.

#### Part 3: SK-EFT — The Combination

SK-EFT combines these two frameworks: use the EFT philosophy (write down the most general theory organized by derivatives) within the SK formalism (double the fields and impose the three axioms). The result is remarkably constraining.

At each derivative order N, you start with many possible terms in the action. The SK axioms then eliminate most of them. Normalization kills terms without the right field content. KMS symmetry (the fluctuation-dissipation relation) fixes all the noise coefficients in terms of the dissipative ones. Positivity constrains the signs and relationships between what remains. The end result is that at first order, only two free parameters survive: the transport coefficients γ₁ and γ₂. Everything else is determined by symmetry.

This is the power of SK-EFT: it turns a problem with potentially infinite complexity (how does dissipation affect a quantum field on a curved background?) into one with a finite, small number of free parameters at each order. And those parameters have clear physical meaning — they measure the strength of specific types of friction in the quantum fluid.

### What We Computed

We applied SK-EFT to acoustic Hawking radiation and computed the **dissipative correction to the Hawking temperature**:

**δ_diss** ≈ 0.001% to 0.1% for current experiments

This tells us: friction changes the Hawking temperature by somewhere between one-hundredth and one-tenth of a percent. It's tiny, but measurable with the right experimental setup.

We also established the hierarchy of corrections:

| Correction | Size | Source | Status |
|------------|------|--------|--------|
| **δ_disp** | ~0.1% | Quantum dispersion (kinetic energy variations) | Previously known |
| **δ_diss** | 0.001% – 0.1% | Dissipation (energy loss) | **This work** |

### Why This Matters for Experiments

Current BEC experiments can measure the Hawking temperature to about 10–30% accuracy. At that precision, our δ_diss correction is too small to see. However, proposed "spin-sonic" experiments could amplify the effect by a factor of 100×, potentially pushing δ_diss into the measurable range. Our calculation provides the theoretical prediction these experiments need to succeed.

---

## 3. The Technical Architecture

This project follows a two-pillar approach: **mathematical proof** and **numerical computation**.

### Pillar 1: Lean 4 Formalization (Mathematical Proofs)

We formalize the mathematics in **Lean 4**, a proof assistant—a programming language where mathematical theorems are statements you write, and proofs are programs that construct those statements. It's like spell-check for mathematics: the computer verifies that every logical step is sound.

**Why this matters:** Quantum field theory papers involve hundreds of equations and approximations. It's easy to make errors. By formalizing key results in Lean, we ensure correctness and create a machine-readable record of the logic.

**The three structures we formalize:**

1. **Acoustic Metric** (Structure A)
   - Defines the geometry of sound propagation in a flowing fluid
   - Captures the key property: at the acoustic horizon, the "speed" coordinate matches the flow speed
   - Lean guarantees this geometry is mathematically well-formed

2. **SK Doubling Constraints** (Structure B)
   - Encodes the Schwinger-Keldysh formalism: how to consistently "double" quantum fields and impose dissipation constraints
   - Ensures energy conservation despite dissipation terms
   - Lean verifies these constraints are logically consistent

3. **Hawking Universality** (Structure C)
   - Proves that the Hawking temperature depends only on the acoustic horizon's geometry (surface gravity), not on microscopic details
   - This universality is profound: it means the temperature formula is robust across different physical systems

**Current status:** The Lean project compiles successfully. **All 12 "sorry" gaps have been filled by Aristotle** (an AI theorem prover) across eight targeted submissions. The filled proofs span all three priority levels: priority-1 algebraic results (acoustic metric determinant, inverse, Lorentzian signature, SK positivity), priority-2 structural results (phonon EOM construction, candidate term counting), and priority-3 analytic results (d'Alembertian operator, FDR from KMS symmetry, dispersive correction bound, dissipative correction existence, combined Hawking universality, and SK first-order uniqueness).

**Key discovery:** During the uniqueness proof, Aristotle found that our original KMS hypothesis was too weak — it only constrained 4 of 9 field components, admitting a counterexample. This led to a corrected formalization (`FirstOrderKMS`) encoding the fluctuation-dissipation relation directly, which is a concrete example of formal verification catching a subtle physics error.

### Pillar 2: Python Computation (Numerical Results)

While Lean proves theorems formally, Python computes actual numbers for real atoms in real labs.

**The transonic background solver** numerically solves the fluid equations to find the flow configuration that creates an acoustic horizon. It uses parameters for three real BEC experiments:

- **Steinhauer's Technion experiment** (Rb-87 atoms)
- **Heidelberg experiment** (K-39 atoms)
- **Trento experiment** (Na-23 atoms)

The solver produces physically correct results: stable transonic flows with well-defined acoustic horizons.

**The tests:** All 12 Python tests verify:
- Correct computation of surface gravity (the key parameter for Hawking temperature)
- Proper boundary condition handling at the horizon
- Physical consistency across different atom species and parameters
- Correct Hawking temperature calculations using measured lab values

### Integration: Aristotle (Automated Theorem Proving)

We use **Aristotle**, an AI-powered theorem prover, to automatically fill the simpler "sorry" gaps in our Lean formalization. This accelerates proof development and reduces manual work.

### Diagram: Project Architecture

```
┌─────────────────────────────────────────────────────────────┐
│         SK-EFT Hawking Radiation Computation                │
└─────────────────────────────────────────────────────────────┘
                              │
                ┌─────────────┴──────────────┐
                │                            │
        ┌───────▼────────┐          ┌──────▼─────────┐
        │  LEAN FORMAL   │          │  PYTHON NUMER  │
        │  VERIFICATION  │          │   COMPUTATION  │
        └───────┬────────┘          └──────┬─────────┘
                │                          │
        ┌───────▼────────────────────────┐ │
        │ • Acoustic Metric Structure    │ │
        │   (horizon geometry)           │ │
        │                                │ │
        │ • SK Doubling Constraints      │ │
        │   (dissipation mechanics)      │ │
        │                                │ │
        │ • Hawking Universality Proof   │ │
        │   (temperature robustness)     │ │
        │                                │ │
        │ → ALL 12 sorry gaps filled!      │ │
        │ → Aristotle: all priorities done  │ │
        └────────────────────────────────┘ │
                                           │
        ┌──────────────────────────────────┘
        │
        │ ┌──────────────────────────────┐
        │ │ Transonic Background Solver  │
        │ └──────────────────────────────┘
        │
        │ Experimental Parameters:
        │ • Rb-87 (Steinhauer/Technion)
        │ • K-39 (Heidelberg)
        │ • Na-23 (Trento)
        │
        ├─ Acoustic horizon detection ✓
        ├─ Surface gravity calculation ✓
        ├─ Hawking temperature T_H ✓
        ├─ Dissipation correction δ_diss ✓
        └─ Physical validation (12 tests) ✓
```

---

## 4. Key Results So Far

### Formal Verification Progress

| Metric | Status |
|--------|--------|
| Lean project compilation | ✓ Success |
| Structures defined | 3 (A, B, C) |
| Sorry gaps identified | 12 total — **all 12 filled!** |
| Sorry gaps by priority | 0×P1 (all filled!), 0×P2 (all filled!), 0×P3 (all filled!) |
| Aristotle integration | ✓ Priority-1 and Priority-2 batches complete |

The Lean codebase is stable and ready for proof development.

### Numerical Computation Progress

| Component | Status | Details |
|-----------|--------|---------|
| Transonic solver | ✓ Working | Produces physically correct horizons |
| Test suite | ✓ All 12 pass | Validates surface gravity, boundary conditions |
| Steinhauer params | ✓ Implemented | Rb-87, published experimental values |
| Heidelberg params | ✓ Implemented | K-39, optimized configurations |
| Trento params | ✓ Implemented | Na-23, enhanced dissipation regime |
| Hawking temperature | ✓ Calculated | ~0.35 nK for current experiments |
| Dissipation correction | ✓ Estimated | δ_diss: 10⁻⁵ to 10⁻³ |

All numerical computations pass validation and produce physically sensible results.

### The Dissipation Correction Estimates

For the three experimental systems:

- **Steinhauer (Rb-87):** δ_diss ≈ 10⁻⁴ (0.01%)
- **Heidelberg (K-39):** δ_diss ≈ 10⁻⁴ to 10⁻³ (0.01% to 0.1%)
- **Trento (Na-23):** δ_diss ≈ 10⁻⁵ to 10⁻³ (0.001% to 0.1%, depending on geometry)

These values bracket the range of current experimental systems and suggest which setups might best probe dissipative effects.

---

## 5. What the Numbers Mean: The Correction Hierarchy

### The Baseline: Hawking Temperature

In current BEC experiments, the predicted Hawking temperature is approximately:

**T_H ≈ 0.35 nanokelvin = 0.35 × 10⁻⁹ K**

This is fantastically small—about a billion times colder than the coolest laboratory temperatures. For context, the cosmic microwave background (the afterglow of the Big Bang) is 2.7 K. We're talking about something 8 orders of magnitude colder.

### Corrections Build Up

When we account for all quantum and dissipative effects, the actual measured temperature isn't exactly T_H. Instead:

**T_measured = T_H × (1 + δ_disp + δ_diss + ...)**

Breaking this down:

#### δ_disp: Quantum Dispersion Correction (~0.1%)

In quantum fluids, particles don't all travel at the same speed; there's a spread in velocities called dispersion. This modifies the Hawking temperature slightly.

- **Size:** ~0.1%
- **Status:** Well-established from prior work
- **Physical origin:** Quantum kinetic energy distributions

#### δ_diss: Dissipation Correction (~0.001% to 0.1%)

Energy loss through friction and viscosity. This is what we compute.

- **Size:** Varies from 10⁻⁵ to 10⁻³ depending on the system
- **Status:** Novel result from this work
- **Physical origin:** Dissipative processes in the fluid (viscosity, etc.)

### Why Experiments Currently Can't See δ_diss

Current BEC experiments measure Hawking temperature to **~10–30% accuracy**. Our δ_diss correction is 0.001% to 0.1%—much smaller than the experimental uncertainty.

**Example:** Suppose T_H = 0.35 nK and δ_diss = 10⁻⁴ (0.01%).
- The corrected temperature is T_measured ≈ 0.35 × (1 + 0.0001) ≈ 0.350035 nK
- Change: 0.035 pK (picokelvins—thousandths of a nanokelvin)
- Experimental precision: ±3.5 to ±105 pK
- **Result:** The correction is drowned out by measurement noise.

### Future Experiments: Enhanced Sensitivity

Next-generation "spin-sonic" experiments exploit quantum properties of atomic spins to amplify dissipative effects. Early designs suggest dissipative corrections could be enhanced by factors of 100–1000×.

If δ_diss is amplified to **100× its current value**:
- New effective correction: δ_diss^eff ≈ 0.1% to 10%
- This enters the measurable regime (comparable to or better than current experimental precision)
- Our prediction becomes testable

---

## 6. Project Status and Next Steps

### Current Status (as of March 23, 2026)

**Lean formalization:** Three core structures compiled and building successfully with zero warnings. **All 12 sorry gaps filled** by Aristotle across eight targeted submissions covering all priority levels. The final submission discovered and corrected a subtle error in the KMS hypothesis formalization. Build: 2252 jobs, all pass (Lean 4.28.0, Mathlib 8f9d9cff).

**Python computation:** Fully functional. All 12 tests passing. Numerical results physically validated. Publication-quality interactive visualizations generated (6 Plotly figures + interactive HTML dashboard).

**Paper draft:** PRL-format LaTeX complete. All TODO items resolved. References cleaned up. Formal verification section documents the KMS discovery. Ready for internal review.

**Integration:** Aristotle pipeline operational with automated extract → diff → integrate workflow. OUT_OF_BUDGET resume infrastructure in place for future submissions.

**Robustness stress tests (Round 4 — COMPLETE):** All 9 stress tests proved by Aristotle (run 3eedcabb, March 24, 2026). Two Phase 1 tests and seven Phase 2 tests confirmed optimal framework:
- `firstOrder_KMS_optimal`: Proved. FirstOrderKMS is optimal (positivity ↔ i₁≥0 ∧ i₂≥0).
- `firstOrder_altSign_uniqueness_test`: Proved as negation. Wrong FDR sign fails via counterexample c=⟨1,1,0,0,0,0,1,2,0⟩, β=1, confirming i₁·β = -r₂ is unique.
- Phase 2 tests: all 7 proved, including two FDR sign tests (proved as negations confirming j_tx·β = s₁+s₃ is unique), relaxed positivity (PSD bound verified), and no-dissipation sanity checks.

**Total-division gap closure (Round 5 — COMPLETE ✓):** Three new sorry gaps closed by Aristotle (run 518636d7, March 24, 2026). These theorems close the gap between "proof is valid" and "proof exercises all the physics." Key insight: Lean 4's total division (0/0 = 0) meant theorems with κ > 0 hypotheses could be satisfied vacuously when unused. Round 5 adds theorems where κ > 0 is genuinely load-bearing:
- `turning_point_shift_nonzero`: Nonzero damping Γ_H > 0 implies nonzero shift δx_imag > 0 — **✓ PROVED**
- `firstOrder_correction_zero_iff`: True biconditional δ_diss = 0 ↔ Γ_H = 0 (requires κ > 0 to distinguish) — **✓ PROVED**
- `dampingRate_eq_zero_iff`: Γ(k,ω) = 0 for all k,ω ↔ all γᵢ = 0 (requires c_s ≠ 0) — **✓ PROVED**
Status: 35/35 ALL PROVED; current tally: 32 proved + 3 Round 5 = 35 total ✓ ZERO SORRY REMAINING

### Phase 1: Foundation — COMPLETE ✓

- [x] Run `lake build` locally — builds successfully (2252 jobs, zero warnings)
- [x] Submit all 12 sorry gaps to Aristotle — all 12 filled across 8 targeted submissions
- [x] Review and integrate Aristotle outputs into main Lean library
- [x] Draft paper (PRL format) and companion documentation
- [x] Finalize Python results; generate publication-quality plots (Plotly)
- [x] Clean up unused variable warnings from Aristotle proofs
- [x] Resolve all paper draft TODO items

### Phase 2: Refinement and Submission (Next 4–8 weeks)

- [ ] Expand the SK action around the transonic background to quadratic order
- [ ] Compute the quadratic correction to Hawking temperature
- [ ] Derive analytic expressions for δ_diss in different regimes
- [ ] Validate quadratic expansion against numerical solver
- [ ] Internal review of paper draft
- [ ] Engage experimental collaborators (Heidelberg K-39, Trento Na-23)
- [ ] Target journal: *Physical Review Letters* or *Physical Review A*

### Phase 3: Extensions (Months 3–6)

- [ ] Second-order SK-EFT corrections (beyond leading order)
- [ ] Backreaction calculation (how radiation modifies the horizon)
- [ ] Connection to superfluid ³He-A experiments (Weyl fermion analogs)
- [ ] Supplementary material: Lean code documentation, full numerical tables

### Milestones

| Milestone | Target Date | Status |
|-----------|-------------|--------|
| Phase 1 complete | March 23, 2026 | **COMPLETE** ✓ |
| Internal review | April 15, 2026 | In progress |
| Experimental engagement | May 1, 2026 | Planned |
| Journal submission | June 15, 2026 | Target |

---

## 7. Glossary

### Core Physics Terms

**Acoustic Horizon**
A location in a flowing fluid where the flow speed equals the sound speed. By analogy, it's like the event horizon of a black hole, but for sound waves instead of light. Waves created inside the horizon cannot escape.

**Analog Gravity / Analog Black Hole**
A physical system in the lab (usually a flowing fluid) that mimics the mathematical structure of gravity and black holes. The system doesn't actually have curved spacetime—it's a mathematical analogy—but the equations are identical, allowing us to test gravitational predictions without needing a real black hole.

**Bose-Einstein Condensate (BEC)**
A state of matter where atoms cooled to near absolute zero (nanokelvin temperatures) all occupy the same quantum state. At these temperatures, quantum mechanics dominates, and you can literally have millions of atoms acting as a single quantum entity. BECs are the cleanest laboratory platforms for testing analog gravity.

**Hawking Radiation**
Radiation spontaneously emitted by black holes (or analog black holes) due to quantum fluctuations near the event horizon. It has a specific temperature determined by the black hole's gravity (or acoustic horizon's "surface gravity"). Hawking's prediction in 1974 was shocking because it showed black holes aren't perfectly black.

**Phonon**
A quantum of sound—the particle-like excitation corresponding to a sound wave. In a quantum fluid, sound is quantized just like light is quantized into photons.

**Surface Gravity**
In general relativity, the strength of gravity at the surface of an object (e.g., Earth's surface gravity is 9.8 m/s²). At a black hole's event horizon, surface gravity determines Hawking temperature. In an acoustic horizon, the analogous quantity is the "rate at which flow speed increases" near the horizon, and it plays the same role in determining Hawking temperature for phonons.

### Theoretical Framework Terms

**EFT (Effective Field Theory)**
A systematic approach to physics that separates "high-energy" (short-distance, microscopic) phenomena from "low-energy" (long-distance, macroscopic) phenomena. Rather than solving the full microscopic theory, you write down the most general theory consistent with the system's symmetries, organized as a "derivative expansion" — terms with fewer derivatives capture smoother, longer-wavelength physics and come first; terms with more derivatives are progressively smaller corrections. The unknown microscopic details are absorbed into a finite number of free parameters (transport coefficients) at each order. EFT is powerful because it leads to universal predictions: many microscopically different systems behave identically at long distances, and the number of free parameters is fixed by symmetry, not by the complexity of the underlying theory. (See Section 2 for a full explanation with examples.)

**Schwinger-Keldysh (SK) Formalism**
A quantum field theory framework developed by Julian Schwinger and Leonid Keldysh in the 1960s for computing dissipative and non-equilibrium effects. The key technique: double every degree of freedom into "forward" (ψ₁) and "backward" (ψ₂) copies evolving along a closed time contour. In an isolated system, these copies evolve identically; dissipation appears as the mismatch between them. The formalism imposes three axioms — normalization (probabilities sum to 1), positivity (entropy increases), and KMS symmetry (fluctuation-dissipation relation in thermal equilibrium) — that severely constrain the allowed form of the dissipative action. This is the standard modern framework for open quantum systems and non-equilibrium quantum field theory. (See Section 2 for a detailed walkthrough.)

**SK-EFT (Schwinger-Keldysh Effective Field Theory)**
The combination of the SK formalism with the EFT derivative expansion. You write down the most general dissipative action consistent with all symmetries, organized order-by-order in derivatives, with the SK axioms eliminating most possible terms at each order. The result is a systematic, symmetry-constrained description of dissipation in quantum systems with a small, finite number of free transport coefficients at each derivative order. This is the framework we apply to the acoustic metric to compute dissipative corrections to Hawking radiation. (See Section 2 for the full story of why these two frameworks fit together.)

### Technical/Project Terms

**Sorry Gaps**
In Lean, a "sorry" is a proof placeholder—you write "sorry" to tell the system "I'm claiming this is true, but I haven't proven it yet." The Lean compiler accepts "sorry" to let you keep writing and move forward, but marks it as an incomplete proof. These gaps are opportunities for improvement and debugging.

**Lean 4**
A modern proof assistant—a programming language where theorems are types and proofs are programs. It's particularly powerful for mathematics because it has a large library (Mathlib) of formalized mathematics, and it's increasingly used by mathematicians to verify complex proofs and eliminate ambiguity.

**Aristotle**
An AI theorem prover integrated with the Lean ecosystem. It can automatically prove certain categories of theorems, especially routine algebraic manipulations and routine applications of existing lemmas. Aristotle accelerates proof development by automating the mechanical steps.

**Transonic Flow**
A flow regime where the speed varies from subsonic (slower than sound speed) to supersonic (faster than sound speed), passing through sonic (exactly sound speed) in between. In our case, the transonic profile creates an acoustic horizon at the sonic point.

**Dissipation**
Energy loss due to friction, viscosity, and other dissipative processes. In quantum systems, dissipation leads to decoherence—quantum states lose their quantum properties and become more classical. Dissipation is always present in real experiments; it's unavoidable and must be accounted for in precision predictions.

**Healing Length**
In a BEC, the characteristic length scale over which quantum properties (like the condensate order parameter) vary. Shorter healing lengths mean sharper variations in density; longer healing lengths mean smoother, more gradual transitions. It's analogous to how far into a conductor electric fields penetrate (the London penetration depth).

**Dispersion / Dispersive Corrections**
The spread in wave speeds depending on wavelength (in water, long waves travel faster than short waves; this is dispersion). Quantum dispersive effects modify the Hawking temperature; we account for these in our correction δ_disp.

**UV (Ultraviolet) / IR (Infrared)**
Borrowed from the electromagnetic spectrum as shorthand for energy/distance scales. UV means short-distance, high-energy physics (the atomic scale in a BEC, or the Planck scale in gravity). IR means long-distance, low-energy physics (the macroscopic fluid behavior). EFT is built on the principle that IR physics is insensitive to UV details — which is exactly why Hawking radiation is universal: the thermal spectrum doesn't care about atomic-scale (UV) physics, only the horizon geometry.

**Trans-Planckian**
Refers to physics at energy scales above the Planck energy (~10¹⁹ GeV in gravity) or, in the analog context, at wavelengths shorter than the healing length ξ where the continuum fluid description breaks down. The "trans-Planckian problem" of Hawking radiation asks whether the thermal spectrum survives when short-distance physics deviates from the simple free-field assumption. Analog experiments directly test this because the "trans-Planckian" (sub-healing-length) physics is known.

**WKB (Wentzel-Kramers-Brillouin) Approximation**
A semiclassical method for solving wave equations when the wavelength varies slowly compared to the background. The wave is written as an amplitude times a rapidly oscillating phase, and the equation is solved order-by-order in the ratio (wavelength / background scale). In our context, WKB is used to track phonon modes as they propagate through the varying flow near the acoustic horizon.

**KMS (Kubo-Martin-Schwinger) Symmetry**
A fundamental property of thermal equilibrium states in quantum field theory. KMS symmetry constrains the relationship between correlation functions at different times, effectively encoding the fluctuation-dissipation theorem at the level of the path integral. In our SK-EFT framework, imposing KMS symmetry on the doubled action forces the noise (imaginary) coefficients to be determined by the dissipative (real) coefficients divided by the inverse temperature β, leaving only two free transport coefficients (γ₁, γ₂).

**FDR (Fluctuation-Dissipation Relation)**
A deep result in statistical mechanics: in thermal equilibrium, the strength of random fluctuations (noise) is exactly determined by the rate of energy dissipation and the temperature. In our formalism, FDR is a consequence of KMS symmetry — it forces the noise kernel of the SK action to equal (γ/β) × (field)², eliminating independent noise parameters.

**D'Alembertian (□)**
The wave operator in spacetime, generalizing the Laplacian (∇²) from space to spacetime: □ = ∂_t² − c_s²∇². On a curved acoustic background (where the sound speed and flow velocity vary in space), the d'Alembertian acquires additional terms encoding the geometry. The phonon equation of motion is □_g π = 0, where g is the acoustic metric.

**Bogoliubov Coefficients**
The amplitudes (α_k, β_k) relating "ingoing" vacuum modes to "outgoing" particle modes when a quantum field propagates through a time-dependent or spatially varying background. The modulus squared |β_k|² gives the particle production rate. In Hawking radiation, the Bogoliubov transformation between the vacuum state at early times and the state seen by a late-time observer produces a thermal spectrum with temperature T_H.

---

## Further Reading and Resources

### Landmark Papers (for context)

- **Hawking (1974):** "Black hole explosions?" — The original prediction
- **Unruh (1981):** "Experimental black hole evaporation?" — Proposing lab analogs
- **Steinhauer et al. (2014–2019):** Series on analog Hawking radiation in BEC

### Key Concepts

This project sits at the intersection of:

1. **Quantum field theory** (Schwinger-Keldysh formalism)
2. **Condensed matter physics** (BECs, acoustic phenomena)
3. **Analog gravity** (mapping quantum fluids to black hole physics)
4. **Computational mathematics** (numerical solutions, formal verification)

Understanding any one of these areas deeply will enrich your appreciation of the project.

### Questions?

For technical questions about the Lean formalization, see `/SK_EFT_Hawking_Paper/lean/README.md`.

For details on the numerical solver, see `/SK_EFT_Hawking_Paper/src/README.md`.

For the full technical paper (in progress), stay tuned to the project repository.

---

*This companion guide is part of the SK-EFT Hawking Paper project documentation. It aims to make the physics and methodology accessible to stakeholders and collaborators without requiring a PhD in theoretical physics. Last updated: March 23, 2026.*
