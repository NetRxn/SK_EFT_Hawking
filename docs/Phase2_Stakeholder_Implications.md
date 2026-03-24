# Phase 2: Second-Order SK-EFT for Analog Hawking Radiation

## Technical and Real-World Implications of Frequency-Dependent Corrections

**Status:** Phase 2 VERIFICATION COMPLETE — All 22/22 Lean proofs verified, zero sorry remaining
**Date:** March 24, 2026
**Classification:** Research Overview — For Technical and Non-Technical Stakeholders
**Prerequisite:** Phase 1 Stakeholder Implications document (March 23, 2026)

---

## Executive Summary

Phase 1 established the first calculation of dissipative corrections to analog Hawking radiation, finding a constant temperature shift δ_diss = O(Γ_H/κ). Phase 2 extends this to the next order in the derivative expansion and discovers qualitatively new physics: **frequency-dependent corrections** to the Hawking spectrum that produce a non-Planckian spectral distortion. This is the difference between "the thermometer reads slightly differently" (Phase 1) and "the color of the glow changes with frequency" (Phase 2).

The key advance is not just a more precise number but a **new observable**: the spectral shape. A constant temperature shift requires measuring an absolute temperature — extremely hard at nanokelvin scales. A spectral distortion requires measuring the relative intensity at different frequencies — potentially much easier and more robust against systematic errors.

---

## The Framework: What is SK-EFT?

"SK-EFT" stands for Schwinger-Keldysh Effective Field Theory — the theoretical framework underlying both Phase 1 and Phase 2. It combines two ideas that together give us a systematic, symmetry-constrained way to compute dissipative corrections to Hawking radiation.

**Effective Field Theory (EFT)** is the principle that you can make precise predictions at long distances without knowing short-distance details. The theory is organized as a "derivative expansion": terms with fewer derivatives (smoother physics) dominate, while higher-derivative terms are progressively smaller corrections. At each order, only a finite number of free parameters — transport coefficients — survive, and their count is fixed by symmetry. This is why the Hawking spectrum depends on just a handful of numbers, not on the full quantum many-body physics of billions of atoms.

**Schwinger-Keldysh (SK) formalism** handles what standard quantum field theory cannot: dissipation. Every real system loses energy to its environment, and the SK framework accounts for this by doubling every degree of freedom into "forward" and "backward" copies. Dissipation shows up as the mismatch between these copies. Three fundamental axioms constrain the theory: normalization (probabilities sum to 1), positivity (entropy can only increase), and KMS symmetry (in thermal equilibrium, the fluctuation-dissipation relation ties noise to dissipation and temperature).

**The combination (SK-EFT)** is remarkably powerful. You write down all possible terms at each derivative order, then the three SK axioms eliminate most of them. At first order (Phase 1), only 2 free parameters survive. At second order (Phase 2), only 2 new parameters appear — and positivity further reduces them to effectively 1 independent parameter. The framework converts a potentially infinite-dimensional problem into one with a small, well-defined parameter space at each order, all constrained by fundamental physics.

For a more detailed explanation with analogies and examples, see the Phase 1 and Phase 2 Educational Companion Guides.

---

## What Phase 2 Adds Beyond Phase 1

### Phase 1 (Complete): The Thermometer Shifts

Phase 1 found that friction in the quantum fluid shifts the effective Hawking temperature by a constant amount. Two transport coefficients (γ₁, γ₂) parameterize the shift. The correction is small (0.001% to 0.1%) and doesn't depend on the frequency of the emitted phonons. All mathematical structures were formally verified in Lean 4 with zero remaining proof gaps.

### Phase 2 (In Progress): The Spectrum Distorts

Phase 2 asks: what happens at the next order? The answer reveals four results with distinct physical and experimental significance:

**1. Two new transport coefficients, but only with background flow.**
At second derivative order, exactly 2 new transport coefficients appear — but both require the spatial symmetry x → -x to be broken. In a BEC with transonic background flow (which breaks this symmetry), both coefficients are active. In a homogeneous system, they vanish. This means the second-order corrections are a direct probe of the flow profile, not just the dissipation strength.

**2. Frequency-dependent spectral distortion.**
The new correction scales as ω³ — it grows with the frequency of the emitted phonons. At low frequencies, the Hawking spectrum looks thermal (Planckian). At higher frequencies, the second-order correction kicks in, producing a characteristic deviation from the thermal shape. This spectral distortion is qualitatively distinguishable from a simple temperature change.

**3. Unitarity constrains the parameters.**
The positivity axiom of the SK framework (encoding quantum unitarity) forces a non-trivial algebraic relation between the two new coefficients: γ_{2,1} + γ_{2,2} = 0. This reduces the effective number of new free parameters from 2 to 1 and demonstrates that the allowed space of dissipative theories is smaller than naive counting suggests.

**4. General counting formula verified.**
The number of transport coefficients at each EFT order follows the formula count(N) = ⌊(N+1)/2⌋ + 1. This has been verified computationally and is being formally proved in Lean 4. It tells us the rate at which the theory's complexity grows — important for deciding how many orders are needed for a given experimental precision.

---

## Why Frequency Dependence Matters

### For Fundamental Physics

A constant correction to the Hawking temperature doesn't change the spectrum's shape — it's still a perfect blackbody, just at a slightly different temperature. This makes it hard to distinguish from other systematic effects (calibration errors, trap imperfections, etc.).

A frequency-dependent correction is fundamentally different. It predicts that the spectrum is no longer a perfect blackbody. Specifically:

- At low frequencies (ω ≪ Λ): the spectrum is approximately Planckian
- At higher frequencies (ω ~ Λ): the spectrum develops a characteristic ω³ deviation

This non-Planckian deviation is a **smoking gun** for second-order dissipative effects. It cannot be mimicked by a simple temperature change, calibration drift, or most common systematic errors. It is a new kind of observable for analog Hawking experiments.

### For Experiments

Detecting a spectral distortion is operationally different from detecting a temperature shift:

- **Temperature shift** (Phase 1): requires absolute temperature measurement at nanokelvin precision. Currently limited to ~10-30% accuracy.
- **Spectral distortion** (Phase 2): requires measuring the ratio of phonon counts at two different frequencies. Ratio measurements can cancel many systematic errors and may achieve higher relative precision.

This means Phase 2's prediction could potentially be tested even before Phase 1's — if the experimental setup is designed to measure spectral ratios rather than absolute temperatures.

---

## The Parity Story: A Hidden Variable in Hawking Physics

One of Phase 2's most striking results is the role of spatial parity. All previous analyses of Hawking radiation (both analog and gravitational) have focused on corrections that preserve spatial symmetry. Phase 2 reveals that:

- **All** second-order dissipative corrections require broken spatial parity
- The background flow in a sonic black hole is precisely what breaks this parity
- A parity-preserving experiment would see **zero** second-order dissipative corrections

This opens a new experimental knob: by engineering flow profiles with varying degrees of asymmetry, experimentalists can control the magnitude of the second-order correction. A symmetric flow profile serves as a control (zero correction); an asymmetric profile reveals the new physics.

---

## Formal Verification: Stress-Testing the Theory

### What's Being Verified

Phase 2 extends the Lean 4 formalization with two new modules and 7 new proof obligations:

- **Counting lemmas** (4 gaps, priority 1): ✓ **ALL PROVED** by Aristotle (run d61290fd). The general formula was proved via bijection with `Finset.range`; the three specific counts used `native_decide`.
- **Strong uniqueness** (1 gap, priority 2): ✓ **PROVED** by Aristotle (run c4d73ca8). Constructive proof builds CombinedDissipativeCoeffs with γ₁=-c.r2, γ₂=c.r1+c.r2, γ_{2,1}=c.s1, γ_{2,2}=c.s3. **No counterexample found** — the second-order KMS framework is validated.
- **Positivity constraint** (1 gap, priority 2): ✓ **PROVED** by Aristotle (run c4d73ca8). Proof by contradiction: constructs field configuration making Im < 0 if γ_{2,1}+γ_{2,2} ≠ 0.
- **Turning point shift** (1 gap, priority 3): ✓ **PROVED** by Aristotle (run c4d73ca8). Pure witness construction.

**All 7 Phase 2 sorry gaps are now proved. Combined with Phase 1 (15/15), the project has 22/22 proofs verified with zero sorry remaining.**

### The Stress Test Passed

In Phase 1, Aristotle discovered that the original KMS formulation was mathematically too weak — it admitted a counterexample that satisfied all stated constraints but didn't correspond to any physical theory. This was a genuine scientific discovery from formal verification.

Phase 2 deliberately exposed the second-order KMS condition to the same stress test. **Aristotle found no counterexample.** The proof of `fullSecondOrder_uniqueness` confirms that the conjectured second-order FDR relation (j_tx · β = s₁ + s₃) is correct — any SK action satisfying the full second-order KMS condition is uniquely determined by exactly 4 transport coefficients. This is a significant validation of the theoretical framework.

### Bulletproofing Suite (Round 4) — ✓ COMPLETE

With 22/22 core proofs complete, we subjected the framework to *robustness testing* — deliberately modifying axioms to test whether results are fragile or resilient. Nine new stress tests (Aristotle run 3eedcabb, March 24, 2026) proved all expected results.

### Total-Division Gap Closure (Round 5) — COMPLETE ✓

**Key insight:** Lean 4's total division (0/0 = 0) meant that theorems with $\kappa > 0$ hypotheses could be vacuously satisfied when those hypotheses were unused. Round 5 closes this gap with three new theorems where $\kappa > 0$ (and $c_s \neq 0$) are genuinely load-bearing (Aristotle run 518636d7, March 24, 2026):

1. **turning_point_shift_nonzero**: Nonzero damping $\Gamma_H > 0$ implies nonzero shift. Requires $\kappa > 0$ to avoid 0/0 in shift formula. — **✓ PROVED**
2. **firstOrder_correction_zero_iff**: True biconditional $\delta_{\text{diss}} = 0 \iff \Gamma_H = 0$. Requires $\kappa > 0$ to distinguish cases (with total division, both sides are 0 when $\kappa = 0$). — **✓ PROVED**
3. **dampingRate_eq_zero_iff**: True biconditional $\Gamma(k, \omega) = 0$ for all $k, \omega \iff$ all $\gamma_i = 0$. Requires $c_s \neq 0$ to avoid spurious identities. — **✓ PROVED**

Also cleaned up: removed unused hN from transport_coefficient_count, stripped unnecessary simp arguments. **Status: 35/35 ALL PROVED ✓ ZERO SORRY REMAINING**

**FDR sign sensitivity.** We flipped the sign of the FDR (replacing s₁ + s₃ with s₁ - s₃) and tested uniqueness. Aristotle proved both wrong-sign tests as *negations* — proving ¬(∀...) via explicit counterexamples. This is the desired outcome: it confirms the FDR sign is physically meaningful and uniquely determined by the SK framework, not arbitrary. Tests `altFDR_uniqueness_test` and `firstOrder_altSign_uniqueness_test` both proved.

**Relaxed positivity.** Dropping the i₃=0 constraint introduces a fifth parameter γ_x. Test `relaxed_positivity_weakens` verified that the strict bound (γ_{2,1} + γ_{2,2} = 0) relaxes to the predicted inequality (γ_{2,1}+γ_{2,2})² ≤ 4γ₂γ_x β, confirming the PSD condition on the extended quadratic form.

**KMS optimality.** Test `firstOrder_KMS_optimal` proved the biconditional: positivity under FirstOrderKMS ↔ (i₁≥0 ∧ i₂≥0), with no hidden relations. Our first-order constraint is optimal.

**No-dissipation limit.** Three tests verified all corrections vanish when dissipation is zero: `no_dissipation_zero_damping`, `turning_point_no_shift`, `firstOrder_correction_zero_iff_no_dissipation`.

**Third-order extension.** Test `thirdOrder_count` extended the counting formula: count(3) = 3 (proved by native_decide).

**Status: 9/9 stress tests proved. Combined Phase 1+2+Round 4: 31 total proofs, zero sorry.**

---

## Updated Project Status

| Component | Phase 1 | Phase 2 | Round 4 |
|---|---|---|---|
| Lean formalization | **14/14** (100%) ✓ | **7/7** (100%) ✓ | **9/9** (100%) ✓ |
| Core proofs | Aristotle runs across 9 submissions | Aristotle runs d61290fd + c4d73ca8 | Aristotle run 3eedcabb |
| Robustness stress tests | 2 (FDR optimal, alt-sign) | 7 planned | **9 all proved** ✓ |
| Python computation | 12/12 tests ✓ | Complete (enumeration + WKB) | N/A (proof-verified) |
| Paper draft | **Finalized** (PRL format) | In progress (PRD format) | Integrated |
| Counting formula | N/A | **4/4 proved** ✓ | Extended: count(3)=3 ✓ |
| Strong uniqueness | **Proved** (first-order) | **Proved** (second-order) ✓ | Stress-tested ✓ |
| FDR sign determination | Not applicable | (Intended for Round 4) | **Confirmed via negation** ✓ |
| Positivity constraint | Trivial at first order | **γ_{2,1}+γ_{2,2}=0 proved** ✓ | Relaxation law **proved** ✓ |
| Spectral distortion | Not applicable | Framework complete | Impact on damping validated |
| Lean build | 2252 jobs | 2254 jobs | Builds clean with all proofs |

---

## Potential Applications Beyond Phase 1

### Precision Spectroscopy of Quantum Vacua

The frequency-dependent correction opens the possibility of "spectroscopy" of the quantum vacuum near sonic horizons. Rather than measuring a single number (the Hawking temperature), experiments could map out the full spectral function — providing much richer information about the dissipative structure of the quantum fluid.

### Constraining Unknown UV Physics

The counting formula count(N) = ⌊(N+1)/2⌋ + 1 tells us how many independent parameters are needed at each order to describe all possible dissipative effects. Combined with the positivity constraints, this dramatically restricts the space of allowed UV completions. Any microscopic theory (Bogoliubov, kinetic theory, etc.) must produce transport coefficients satisfying these constraints — providing a systematic way to test proposed UV theories against the symmetry structure.

### Template for Higher-Order EFT

The methodology developed here — systematic monomial enumeration, algebraic KMS analysis, positivity constraints, and formal verification — is a template that applies to any SK-EFT through any order. The infrastructure is reusable for third-order analysis, for different spatial dimensions, and for different symmetry groups (e.g., spinor BECs with SU(2) symmetry).

---

## Next Steps

**Immediate (this week):**
- ~~Submit counting lemmas to Aristotle (Round 1)~~ ✓ COMPLETE — all 4 proved (run d61290fd)
- ~~Submit stress tests + WKB to Aristotle (Round 2+3)~~ ✓ COMPLETE — all 3 proved (run c4d73ca8)
- ~~Verify `lake build` with integrated Aristotle proofs~~ ✓ COMPLETE — clean build
- Submit robustness stress tests to Aristotle (Round 4) — **IN PROGRESS** (9 gaps, results pending)

**Near-term (2-4 weeks):**
- Finalize numerical estimates for spectral distortion at experimental parameters
- Complete Phase 2 paper draft
- Generate publication-quality visualizations of spectral distortion

**Medium-term (1-3 months):**
- Internal review of combined Phase 1 + Phase 2 papers
- Engage experimental collaborators with spectral distortion prediction
- Begin Phase 3 planning (backreaction + ³He-A extension)

---

*This document extends the Phase 1 Stakeholder Implications to cover the second-order SK-EFT analysis. It emphasizes the qualitatively new physics (frequency dependence, parity, spectral distortion) that distinguishes Phase 2 from a simple refinement of Phase 1. Last updated: March 24, 2026.*
