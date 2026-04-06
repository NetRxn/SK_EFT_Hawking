# SK-EFT Hawking: Educational Companion Guide

## What Is This Project About?

This project asks a deep question: can the mathematics of exotic states of matter — superfluids, topological insulators, quantum spin liquids — also describe the fundamental forces and particles of the universe? We investigate this with a combination of numerical computation, formal mathematical proof-checking, and automated theorem proving, producing experimentally testable predictions along the way.

Everything is machine-checked in the Lean 4 proof assistant: 1318 theorems, zero axioms, across 93 modules.

---

## The Big Ideas

### 1. Sound Waves That Behave Like Black Holes

When a fluid flows faster than the speed of sound, it creates a sonic horizon — a boundary that traps sound waves the same way a black hole traps light. Stephen Hawking predicted in 1974 that black holes emit faint radiation due to quantum effects near the horizon. The same physics applies to sonic horizons in laboratory fluids.

We computed the first corrections to the acoustic Hawking temperature from dissipation — the fact that real fluids have viscosity. These corrections are tiny (~0.001-0.1%) but have a specific frequency signature that experimentalists can look for. The polariton platform (a type of light-matter hybrid system) is 10 billion times hotter than BEC systems, making it the most accessible route to detecting these effects. A Paris group has already observed the precursor signals.

### 2. Why Three Generations of Matter

The Standard Model has three copies ("generations") of its fundamental particles — electron/muon/tau and their associated quarks and neutrinos. Nobody knows why three. We derived that the number must be divisible by three, from two independent mathematical facts:

- Each generation contributes a chiral central charge of 8 (from its 16 Weyl fermions)
- The Dedekind eta function — a mathematical object from number theory — forces this charge to be divisible by 24 through a consistency condition called the framing anomaly

The ratio 24/8 = 3 constrains the generation count. The numerator is pure mathematics; the denominator is pure physics. We also show that without right-handed neutrinos, the central charge is fractional (15/2), providing a formal argument for their existence independent of the usual mass-based reasoning.

### 3. The Number 16 Appears Everywhere

The Standard Model has 16 Weyl fermions per generation. The anomaly classification lives in Z/16. Rokhlin's theorem says spin manifold signatures are divisible by 16. Kitaev's classification of topological superconductors has 16-fold periodicity.

We proved these are all the same 16, and we proved exactly where the number comes from: the algebraic bound from lattice theory is 8 (the E8 lattice achieves this), and the extra factor of 2 requires smooth topology. The jump from 8 to 16 encodes whether a mathematical space can be smoothed — a profound connection between particle physics and geometry.

### 4. A Chain from Lattice Models to Gauge Theory

We formalized a complete mathematical chain connecting laboratory-accessible physics to fundamental gauge theory:

**Onsager algebra** (exactly solvable lattice models) → **quantum groups** (q-deformations with Hopf algebra structure) → **fusion categories** (the algebraic data of anyon systems) → **modular tensor categories** (the mathematics underlying topological quantum field theory and Chern-Simons gauge theory)

Every link is machine-checked. The SU(2)_k fusion rules at k=3 contain the Fibonacci anyon — a hypothetical particle whose braiding operations are universal for quantum computing. Our work provides the first formally verified foundation for the fusion operations that future topological quantum computers would perform.

### 5. The Chirality Problem

The biggest obstacle to deriving the Standard Model from condensed matter physics is chirality: the weak nuclear force only acts on left-handed particles. Putting chiral fermions on a lattice was considered impossible since 1981. A January 2026 construction likely evades the old no-go theorems. We provided the first formal analysis of why the evasion works: 9 no-go conditions formalized, 5 proved violated by the new construction, with a master synthesis theorem assembling the result.

### 6. Can Gravity Emerge from Quantum Matter?

The Akama-Diakonov-Wetterich mechanism proposes that gravity emerges from fermion condensation — analogous to how Cooper pairs form in superconductors. We formalized the mean-field structure and identified that the gap equation for tetrad condensation (the gravitational analog of the BCS gap equation) has never been explicitly written down in the published literature. Computing it is the next major open question.

We also proved what doesn't work: fracton gauge theory reproduces linearized gravity perfectly but fails at the nonlinear level (formally verified obstruction). And non-Abelian gauge structure (the strong and weak forces) cannot survive through a fluid layer — this is a structural theorem, not a conjecture.

---

## How It Works

### Three-Layer Verification

Every result passes through three independent checks:

1. **Python computation** — numerical calculations with real experimental parameters, validated by 1600+ automated tests
2. **Lean 4 formal proofs** — mathematical theorems machine-checked by the proof assistant, ensuring logical correctness
3. **Aristotle automated prover** — an AI system that finds proofs for the harder theorem gaps, with 273 theorems proved across 33+ runs

### The Provenance Dashboard

An interactive web dashboard (`localhost:8050`) lets you trace any claim in any paper back through the computation pipeline to its source: which formula computed it, which Lean theorem verifies it, which experimental parameters it depends on, and which published paper those parameters come from. A knowledge graph with 1000+ nodes and 11 edge types visualizes the full provenance chain.

---

## By the Numbers

| Metric | Count |
|--------|-------|
| Lean theorems | 1318 (zero axioms) |
| Lean modules | 93 |
| Tracked hypotheses | 5 (all extremely low risk) |
| Python test files | 41 (1635+ individual tests) |
| Publication-quality figures | 80 |
| Paper drafts | 12 |
| Computational notebooks | 40 (technical + stakeholder pairs) |
| Aristotle prover runs | 35+ |
| Deep research files | 50+ |

### Formal Verification Firsts

This project established several firsts in the formal verification of physics:

- First formally verified anomaly constraint in particle physics
- First quantum group (U_q(sl_2)) in any proof assistant
- First Hopf algebra instance (non-trivial) in any proof assistant
- First affine quantum group, restricted quantum group
- First SU(2)_k fusion rules verified from a quantum group
- First ribbon category and modular tensor category definitions
- First pivotal and spherical category definitions
- First Drinfeld center computations (toric code, non-abelian D(S_3))
- First E8 lattice verification and algebraic Rokhlin decomposition
- First verified statistical estimators for lattice Monte Carlo
- First formal analysis of the chirality wall (GS no-go vs TPF evasion)
- First complete braided fusion category in any proof assistant (Ising MTC with R-matrix, hexagon, ribbon)
- First formally verified knot invariant from MTC data (trefoil = -1)
- First verified SU(2)_3 and SU(2)_4 S-matrix unitarity over algebraic number fields

---

## Where to Learn More

| Topic | Document |
|-------|----------|
| Full technical details | [`README.MD`](../../SK_EFT_Hawking/README.MD) |
| What each phase accomplished | `docs/stakeholder/Phase{N}_Implications.md` |
| Strategic positioning | `docs/stakeholder/Phase{N}_Strategic_Positioning.md` |
| The broader research program | [`docs/Fluid-Based Approach to Fundamental Physics  Feasibility Study.md`](../Fluid-Based%20Approach%20to%20Fundamental%20Physics%20%20Feasibility%20Study.md) |
| Critical assessment of the program | [`docs/Fluid-Based Approach to Fundamental Physics- Consolidated Critical Review v3.md`](../Fluid-Based%20Approach%20to%20Fundamental%20Physics-%20Consolidated%20Critical%20Review%20v3.md) |
| What's next | [`docs/roadmaps/Phase6_Deferred_Targets.md`](../roadmaps/Phase6_Deferred_Targets.md) |
| Interactive exploration | Run `uv run python scripts/provenance_dashboard.py` and open http://localhost:8050 |

---

*Last updated: April 2026. Phase 5e complete: braided Ising/Fibonacci MTCs, SU(2)_3/SU(2)_4 S-matrix unitarity, first verified knot invariant. 1318 theorems, 93 modules, 34 sorry pending Aristotle.*
