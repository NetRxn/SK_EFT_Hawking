# Strategic Positioning: SK-EFT Hawking Paper within the Fluid-Based Physics Program

## How the Current Work Fits the Bigger Picture

**Date:** March 23, 2026
**Context:** This memo connects the SK-EFT analog Hawking paper (**Phase 1 COMPLETE** as of March 23, 2026 — all 14 Lean proofs verified, paper draft finalized, interactive visualizations generated) to the broader fluid-based approach to fundamental physics, as assessed in the Consolidated Critical Review v3, the Feasibility Study, and the full Tier 1/Tier 2 literature search.

---

## The Three-Layer Architecture at a Glance

The broader research program proposes a hybrid three-layer model for emergent physics:

| Layer | Content | Role |
|---|---|---|
| **Layer 1 (UV)** | Quantum order: string-nets, Fermi-point topology, fracton phases | Source of gauge fields, chirality, fermionic statistics |
| **Layer 2 (Mesoscopic)** | Fluid dynamics: Navier-Stokes, superfluid hydrodynamics, fracton hydro | Coarse-grained description; acoustic geometry; transport |
| **Layer 3 (IR)** | Effective field theory: Standard Model + GR as emergent low-energy theory | Observable physics; experimental predictions |

The SK-EFT Hawking paper sits at the **Layer 2 → Layer 3 bridge** — the exact interface where fluid dynamics produces emergent spacetime geometry and where dissipative EFT connects to observable quantum effects. This is the only layer transition that is already complete in the formal sense: the Schwinger-Keldysh framework (Crossley-Glorioso-Liu) provides the rigorous infrastructure, and the acoustic metric (Unruh-Visser) provides the geometric target.

---

## Why This Paper Is Tier 0

The Consolidated Critical Review v3 identifies the SK-EFT dissipative correction to analog Hawking radiation as "the single most impactful paper the program can produce." The reasoning:

**It fills a confirmed literature gap.** No published work connects Schwinger-Keldysh dissipative EFT to analog Hawking radiation. Dispersive corrections (Coutant-Parentani) are computed; backreaction (Balbinot et al. 2025) is computed; dissipative corrections from the SK framework are not. This is a genuine gap, not an incremental extension.

**It produces a concrete experimental prediction.** The correction δ_diss to the Hawking temperature depends on the SK transport coefficients (γ₁, γ₂) and is measurable in BEC experiments. The dispersive correction is O(0.04–0.16%), below current 10–30% experimental precision. The dissipative correction scales differently and may be larger — potentially within reach as Heidelberg (K-39 Feshbach) and Trento (spin-sonic) platforms improve precision.

**It bridges two major theoretical frameworks.** SK-EFT is the modern language for dissipative quantum systems, used across heavy-ion physics, condensed matter, and cosmology. Analog gravity is a mature experimental program with confirmed Hawking radiation. Connecting them creates a new intersection that neither community has explored.

**It is formally verified.** The Lean 4 + Mathlib + Aristotle pipeline has produced the first theoretical physics paper with **100% machine-verified** mathematical content (14/14 proofs, zero warnings). During verification, Aristotle discovered and corrected a subtle error in the KMS hypothesis formalization — a concrete demonstration that formal verification catches bugs that would pass peer review.

**It requires no new physics.** Everything needed — Son's superfluid EFT, SK doubling, the acoustic metric, BEC platforms — already exists. The contribution is the calculation itself and the prediction it yields.

---

## How the Paper Relates to the Three Structural Walls

The broader program faces three fundamental obstructions. The SK-EFT paper's relationship to each:

### Wall 1: Non-Abelian Gauge Structure

**Status:** Structurally impossible at the fluid layer (universal gauge erasure theorem).

**SK-EFT paper's role:** Neutral. The paper operates entirely within the Abelian/phonon sector, which is exactly where the acoustic metric is valid. The Cuomo et al. result constrains the SK-EFT approach to irrotational/phonon-only sectors (vortex-sector EFT fails due to UV/IR mixing), and our paper respects this boundary. We do not claim to address non-Abelian physics.

**Strategic value:** By succeeding cleanly in the Abelian sector, the paper demonstrates what the fluid layer *can* do — produce testable quantum-gravity phenomenology within its domain of validity — without overreaching into what it cannot.

### Wall 2: Dynamical Einstein Gravity

**Status:** Three-level hierarchy (vestigial → tetrad → UV-complete), with the ADW mechanism as the strongest route.

**SK-EFT paper's role:** Indirect but foundational. The acoustic metric is kinematic (no dynamical Einstein equations), and the paper does not claim to produce gravity. However, the SK-EFT methodology we develop is the same formalism needed for the gravity program: SK-EFT for superfluid ³He-A (which hosts emergent Weyl fermions and approximate Lorentz symmetry) would be the natural next step. The Selch-Zubkov (2025) computation of emergent vierbein in ³He-A with nonzero torsion and Nieh-Yan anomaly is directly addressable with our pipeline.

**Strategic value:** The paper builds the computational and formal-verification infrastructure (SK doubling, KMS constraints, Lean formalization) that the gravity program will need. It is a proof-of-concept for the harder calculation.

### Wall 3: Chiral Fermions

**Status:** Fracturing (TPF disentangler, SMG at 16 Weyl) but structurally intact.

**SK-EFT paper's role:** Tangential. Chirality is a Layer 1 problem; our paper operates at Layer 2→3. However, the two-component spin-sonic horizons (Berti et al. 2025) accessible in spinor BECs offer a path toward probing spin-dependent Hawking effects, which could eventually connect to chirality questions in analog systems.

---

## The Paper as a Keystone in the Research Roadmap

The Consolidated Critical Review v3 organizes the research program into tiers. Here is where the SK-EFT paper fits and what it enables:

### Tier 0 (This Paper) — Immediate

- SK-EFT dissipative correction to analog Hawking radiation
- Lean 4 formal verification with Aristotle ATP
- Experimental prediction for BEC platforms

### What This Paper Enables at Tier 1 (6–18 months)

**BEC replication and precision measurement (§5.4 of the Critical Review).** Our prediction gives the Heidelberg and Trento groups a specific target: measure the Hawking spectrum precisely enough to detect or constrain δ_diss. The K-39 Feshbach tunability allows varying surface gravity independently — precisely the experimental knob needed to test the κ-dependence of our correction.

**Extension to backreaction (Balbinot et al. 2025).** Acoustic black holes cool and approach extremality (opposite of Schwarzschild). Our SK-EFT framework provides the natural language for computing the interplay between dissipative corrections and backreaction — a second paper waiting to be written.

**Second-order SK-EFT.** The first-order calculation (this paper) determines the leading dissipative correction. The second-order calculation would access thermal noise correlators and the full fluctuation-dissipation structure, providing a richer experimental signature.

### What This Paper Enables at Tier 2 (18–36 months)

**SK-EFT for superfluid ³He-A.** The same doubling procedure and KMS constraints apply to p-wave superfluids with emergent Weyl fermions. This is where the program connects to the gravity wall: the acoustic metric in ³He-A is a rank-(1,1) tensor (not scalar), potentially producing spin-2 emergent gravitons via the ADW mechanism.

**Fracton hydrodynamics SK-EFT (Glorioso et al. JHEP 2023).** The fracton SK-EFT preserves dramatically more UV information than standard Navier-Stokes. Our Lean verification infrastructure could formalize this extension, building toward a verified fracton-hydro → emergent-geometry pipeline.

**Non-Abelian gauge erasure as a formal result (§5.2 of the Critical Review).** The universal structural theorem that non-Abelian gauge DOF cannot survive hydrodynamization is itself publishable. Our formal verification methodology (Lean + Aristotle) could provide the first machine-verified proof of a structural theorem in higher-form symmetry hydrodynamics.

---

## Strategic Positioning: What to Claim and What Not to Claim

Drawing from the Critical Review's careful delineation:

### This paper claims:

- The first calculation of dissipative corrections to analog Hawking radiation from first-principles SK-EFT
- A concrete experimental prediction (δ_diss) testable in current BEC platforms
- The first **100% formally verified** (Lean 4 + Aristotle, 14/14 proofs, zero warnings) theoretical physics paper at this level of complexity
- A scientific discovery from formal verification: the original KMS hypothesis was mathematically too weak, caught by Aristotle's counterexample
- A demonstration that the Layer 2→3 bridge (fluid dynamics → emergent quantum gravity phenomenology) is operational and produces new physics

### This paper does not claim:

- That dynamical Einstein gravity emerges from the acoustic metric (it does not — the metric is kinematic)
- That non-Abelian gauge structure can be accessed through this fluid-layer calculation (it cannot)
- That Steinhauer's BEC Hawking result has been independently replicated (it has not)
- That the broader fluid-based physics program "works" in full — the three structural walls remain

### The honest framing:

The SK-EFT Hawking paper is the strongest card the program has. It demonstrates that the fluid-based approach produces genuine, testable, new predictions within its domain of validity (Abelian/phonon sector, kinematic geometry). It does not solve the program's hardest problems (non-Abelian gauge, dynamical gravity, chirality), but it builds the computational and formal infrastructure needed to attack them, and it establishes credibility by delivering a concrete result in a space where no one else has worked.

---

## The Bigger Picture: A Hybrid Program

The fluid-based approach to fundamental physics is not a single theory but a research program organized around a structural insight: the same mathematics (EFT, symmetry breaking, topological order) that describes emergent physics in condensed matter also describes the Standard Model and general relativity. The three-layer hybrid architecture is the honest attempt to map which parts of this correspondence are rigorous, which are plausible, and which face structural obstructions.

The SK-EFT paper is the program's first **completed** end-to-end deliverable: a new theoretical prediction, formally verified (100%, with a scientific discovery from the verification process itself), experimentally testable, filling a confirmed literature gap, at the layer transition where the program is strongest. Phase 1 is complete — all 14 Lean proofs verified, paper draft finalized, publication-quality interactive visualizations generated. It is the proof that the approach works where it should work — and the foundation for pushing into the harder territory beyond.

### What would change the picture

Six developments from the Critical Review, any of which would shift the broader assessment:

1. **TPF 4+1D gapped interface proven** — breaches the chirality wall
2. **Independent BEC Hawking replication** — transforms analog gravity into established experimental physics
3. **ADW mean-field gap equation solved with emergent fermions** — validates or falsifies the gravity route
4. **SMG demonstrated with chiral gauge coupling** — closes the vector-like → chiral gap
5. **Monte Carlo η/s for emergent SU(2) from Walker-Wang** — tests gauge erasure universality
6. **Resolution of the Wallstrom objection** — completes the Madelung ↔ Schrödinger correspondence

Our paper contributes most directly to item 2: by providing a specific dissipative correction prediction, we give experimentalists a sharper target than "measure the Hawking temperature." We turn a qualitative replication question into a quantitative precision measurement.

---

*This memo synthesizes the Consolidated Critical Review v3, the Feasibility Study, and the Tier 1/Tier 2 literature search (13 research documents across hep-th, gr-qc, cond-mat, quant-ph, and hep-lat). It reflects the program's state as of March 2026.*
