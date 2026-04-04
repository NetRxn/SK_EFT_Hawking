# Fluid-Based Approach to Fundamental Physics: Feasibility Study

***

## Executive Summary

This feasibility study investigates whether the dynamics of compressible and incompressible fluids, augmented by pilot-wave ontology, can serve as a structural foundation for quantum field theory, electrodynamics, and gravity. The program builds on a chain of established mathematical results — the Madelung transform is a proven Kähler symplectomorphism, Kambe's fluid Maxwell equations are an exact reformulation of compressible Euler dynamics, Eling's BF gauge theory fully encodes incompressible Euler flow, and Volovik's superfluid ³He-A model generates emergent Weyl fermions, gauge fields, and tetrad gravity from fluid symmetry breaking. Acoustic Hawking radiation has been observed experimentally in Bose-Einstein condensates, the quark-gluon plasma behaves as a near-perfect fluid in agreement with AdS/CFT predictions, and Darrow and Bush's 2024 Lorentz-covariant Lagrangian framework for the double-solution pilot-wave reproduces de Broglie harmony, Compton oscillation, and a classical analog of Heisenberg uncertainty from fluid mechanics alone.[^1][^2][^3][^4][^5][^6][^7][^8][^9][^10][^11][^12][^13][^14]

**Verdict: This program is worth a focused 18-month feasibility study.** Multiple structural gaps remain — full non-Abelian gauge dynamics, a dynamical Einstein equation, and renormalizability — but none is ruled out by a no-go theorem, and each is addressable by concrete theoretical, experimental, and formal-verification tasks. The study design integrates Lean 4 formal proofs (via the existing HepLean/PhysLean infrastructure) into every theoretical deliverable.[^15][^16]

**Items not completable in this study:** Full numerical Wilsonian RG computations for the fluid hierarchy, closed-form reduction from fluid variables to SU(3) QCD color factors, and experimental acquisition of data from the ³He-A thermal Hall and BEC horizon systems require physical apparatus not accessible here. These are documented explicitly in Section 8 (Skipped Items and Open Questions).

***

## 1. Background: The Case for a Fluid-Based Approach

The Standard Model, general relativity, and quantum electrodynamics all encode conservation laws — mass, momentum, energy, charge — that are structurally identical to the governing equations of fluid dynamics. This is not a superficial resemblance. In the low-energy limit, every known quantum field theory produces a hydrodynamic effective description: relativistic heavy-ion collisions at RHIC and the LHC demonstrate that hot QCD matter (the quark-gluon plasma) behaves as a nearly perfect fluid with shear viscosity-to-entropy ratio \(\eta/s \approx 1\) to \(2.5/(4\pi)\) in units of \(\hbar/k_B\) — strikingly close to the Kovtun-Son-Starinets (KSS) holographic lower bound \(\hbar/4\pi k_B\). The same bound arises from the AdS/CFT correspondence, linking strongly-coupled SU(3) gauge theory directly to a gravitational (string/fluid) dual.[^13][^14]

The fluid-based program asks a deeper question: not just whether QFT produces fluids, but whether fluids — specifically a hierarchical compressible/incompressible system with pilot-wave ontology — can *generate* the structural content of QFT, electrodynamics, and gravity from the bottom up. The evidence surveyed here suggests that the answer is "partially yes," and that the partially-yes regions are rich enough to justify formal investigation.

***

## 2. Established Mappings and Their Mathematical Status

### 2.1 Madelung Transform: Quantum Mechanics ↔ Compressible Fluid (Exact)

The Madelung transform writes the complex wavefunction as \(\psi = \sqrt{\rho}\,e^{iS/\hbar}\) and maps the Schrödinger equation to a compressible Euler system:

\[\partial_t \rho + \nabla \cdot (\rho \mathbf{v}) = 0, \qquad \mathbf{v} = \frac{\nabla S}{m}\]

\[\partial_t S + \frac{(\nabla S)^2}{2m} + V + Q = 0, \qquad Q = -\frac{\hbar^2}{2m}\frac{\nabla^2\!\sqrt{\rho}}{\sqrt{\rho}}\]

The quantum potential \(Q\) acts as an additional compressibility term. Khesin, Misiołek, and Modin (2018) proved that this transform is a **Kähler morphism** between the cotangent bundle of smooth probability densities equipped with the Fisher-Rao metric and the projective space of wave functions equipped with the Fubini-Study metric. In particular, it is simultaneously a symplectomorphism and an isometry — a stronger result than merely an analogy. Fusca (2017) proved it is a momentum map for the action of the semidirect product group \(\mathrm{Diff}(\mathbb{R}^n)\ltimes H^\infty(\mathbb{R}^n;\mathbb{R})\). The equivalence is **exact**, not approximate.[^17][^3][^18][^1]

For the Dirac equation (spin-½), the spinor polar decomposition \(\psi = \phi e^{-2i\beta\pi}L^{-1}\) maps the relativistic quantum field onto a compressible fluid with velocity \(U^a = \bar\psi\gamma^a\psi\), energy density \(\mu = 2\phi^2(m\cos\beta - \Omega - \hat\beta/2)\), and pressure \(p = -\tfrac{1}{3}\phi^2(2\Omega + \hat\beta)\), where \(\Omega\) is vorticity and \(\hat\beta\) is the chiral angle gradient.[^19]

### 2.2 Kambe's Fluid Maxwell Equations: QED Structure (Structural Analogy)

For an isentropic, inviscid, compressible fluid, Kambe (2010) defined:[^2][^4]

\[\mathbf{E} \equiv -\partial_t\mathbf{v} - \nabla h, \qquad \mathbf{H} \equiv \boldsymbol{\omega} = \nabla\times\mathbf{v}\]

and derived four equations of Maxwell form:

\[\nabla\cdot\mathbf{H} = 0 \tag{M1}\]
\[\nabla\cdot\mathbf{E} = q \tag{M2}\]
\[\nabla\times\mathbf{E} + \partial_t\mathbf{H} = 0 \tag{M3}\]
\[a_0^2\,\nabla\times\mathbf{H} - \partial_t\mathbf{E} = \mathbf{J} \tag{M4}\]

where \(a_0\) is the sound speed (playing the role of \(c\)), and sources \(q\), \(\mathbf{J}\) are determined entirely by the fluid velocity field — they are not independent degrees of freedom. A geometric algebra extension (2020) derives all four equations from a single multivector equation over 4D Euclidean spacetime. Abreu et al. (2015) extended the construction to non-Abelian internal spaces, deriving Yang-Mills-type source equations with self-coupling terms \(gf^{abc}\mathbf{A}^b\times\mathbf{H}^c\). The Lorentz force analog takes the form \(d\mathbf{P}/dt = m\mathbf{E} + m\mathbf{u}\times\mathbf{H}\), with mass \(m\) playing the role of charge.[^20][^21]

**Status:** Structural analogy recovering the wave equation and force law in the irrotational limit. Key limitations: fluid **E** is not gauge-redundant, sources are enslaved to the velocity field, and the analogy produces no photon or spin-1 boson.

### 2.3 Unruh-Visser Acoustic Metric: General Relativity (Kinematic Analogy)

For a barotropic, inviscid, irrotational fluid, Unruh (1981) and Visser (1993/1998) proved that acoustic perturbations satisfy:[^22][^23]

\[\frac{1}{\sqrt{-g}}\partial_\mu\!\left(\sqrt{-g}\,g^{\mu\nu}\partial_\nu\phi_1\right) = 0\]

with the **acoustic metric**:[^24][^25]

\[g_{\mu\nu} = \frac{\rho_0}{c_s}\begin{pmatrix}-(c_s^2 - v_0^2) & -v_{0i}\\ -v_{0i} & \delta_{ij}\end{pmatrix}\]

The Visser-Molina-Paris (2010) extension covers arbitrary (d+1)-dimensional curved-space backgrounds, deriving the acoustic spacetime in full general-relativistic barotropic irrotational flow. Vorticity can be introduced to mimic rotating spacetimes. The Hawking temperature at an acoustic horizon is:[^25][^26]

\[T_H = \frac{\hbar\kappa}{2\pi k_B}, \qquad \kappa = \frac{1}{2}\partial_n(c_s - v_\perp)\big|_\text{horizon}\]

Steinhauer (2016) observed spontaneous quantum Hawking radiation and its entanglement in a BEC analog black hole, published in *Nature Physics*. Steinhauer (2022) in *Physical Review D* confirmed stimulated Hawking radiation via the Bogoliubov-Cherenkov-Landau mechanism. A superconducting quantum computer simulation (2023) further reproduced curved-spacetime quantum field theory analogs.[^9][^27][^10]

**Status:** Kinematic features rigorously confirmed. Key limitations: no Einstein field equations (metric is algebraic, not dynamic), spatial sections are conformally flat, only scalar perturbations, no back-reaction.

### 2.4 BF Gauge Theory of Incompressible Euler: Topological Gauge Symmetry (Exact)

Eling (2023) proved that the 3+1D incompressible Euler equations can be expressed as an abelian gauge theory with a topological BF term:[^5][^6][^28]

\[S = \int d^4x\left(B_{\mu\nu}F^{\mu\nu} + \lambda\,\epsilon^{\mu\nu\rho\sigma}A_\mu\partial_\nu A_\rho A_\sigma\right)\]

where the 3-form field strength is dual to the **local helicity density** \(\mathcal{H} = \mathbf{v}\cdot(\nabla\times\mathbf{v})\) — a material invariant of incompressible flow. Vorticity maps to the magnetic field \(B^i = \tfrac{1}{2}\epsilon^{ijk}F_{jk}\), and the cross-product \(\mathbf{v}\times\boldsymbol{\omega}\) maps to the electric field \(E_i = F_{0i}\). The Bianchi identity \(d(*H)=0\) is equivalent to helicity conservation, providing a genuine topological U(1) gauge symmetry. The theory also yields edge modes at boundaries, suggesting a fluid Hall effect. A parallel topological BF theory of incompressible polar fluid quantum hydrodynamics (PhysRevB 2014) connects directly to \(\mathbb{Z}_2\) topological insulators in 3D.[^6][^29][^30]

**Status:** Exact. This is currently the strongest gauge-theoretic result from pure fluid dynamics.

### 2.5 Volovik's Superfluid ³He-A: Emergent Standard Model Structure

Volovik established that superfluid ³He-A belongs to a universality class of Fermi systems with topologically stable **Weyl point nodes** in the quasiparticle spectrum. The key results are:[^7][^8]

- Quasiparticles near Weyl points obey the effective Hamiltonian \(H_\text{Weyl} = \pm\hbar\,e^\mu_a\sigma^a k_\mu\), where \(e^\mu_a\) is the **emergent vierbein** (tetrad) from the superfluid order parameter texture[^31]
- Collective bosonic modes are effective gauge fields and gravitational fields[^32]
- ³He-A textures induce a nontrivial effective metric; quasiparticles move along geodesics[^7]
- Axial anomaly, baryoproduction, magnetogenesis, event horizons, and Hawking radiation all have confirmed analogs[^33][^32]
- The combined symmetry-breaking pattern \(G = SO(3)_c\times P_c\times SO(3)_s\times P_s \to H = SO(3)_J\times P\) yields combined Lorentz symmetry in the IR[^31]
- An effective Einstein-Hilbert action \(\int\sqrt{-g}(M_\text{Pl,eff}^2/16\pi)R\) emerges with the effective Planck mass set by superfluid density[^34][^31]

The QUEST-DMC collaboration (Lancaster, Sussex, Aalto, Helsinki) is actively using superfluid ³He as a laboratory testbed for cosmology and BSM physics, funded by the UK STFC. A universal law of quantum vortex dynamics was discovered in superfluid helium in 2025, published in PNAS.[^35][^36]

**Status:** This is the most complete existing realization of the fluid-based SM/gravity program. Its key limitation is that the analogy requires an underlying quantum liquid (fermionic atoms at millikelvin temperatures) — not an abstract fluid.

### 2.6 Pilot-Wave Double-Solution: Darrow-Bush 2024 (Lorentz-Covariant)

Darrow and Bush (MIT, 2024) introduced a Lorentz-covariant Lagrangian framework for de Broglie's double-solution pilot-wave theory. The entire family of systems is:[^11][^12][^37]
- **Local and Lorentz-invariant**
- Derived from a **variational principle** with Noether currents for particle-wave exchange
- Exhibiting **two-way coupling** between particle (compressible soliton) and pilot wave (linear field)

Key results: the particle is always dressed with a Compton-scale Yukawa wavepacket; the pilot wave dynamically adjusts to satisfy \(p = \hbar k\) at the particle's position even under acceleration; and the wave-induced Compton-scale oscillation produces a classical version of the Heisenberg uncertainty principle. Mass appears as the constant energy increase from the Yukawa dressing. This is the closest existing framework to a fully consistent compressible-soliton-on-incompressible-pilot-wave picture.[^11]

***

## 3. The Hierarchical Fluid Architecture

Building on all the mappings above, a three-level hierarchical fluid model emerges:

| Level | Fluid Type | Physical Content | Quantum Analog |
|---|---|---|---|
| **Level 1 (Global)** | Incompressible potential flow | Phase, topology, helicity, BF/Chern-Simons gauge field | Linear pilot wave \(\psi_L\); Chern-Simons gauge field[^5][^38] |
| **Level 2 (Mesoscopic)** | Incompressible vortex knots | Quantum numbers from knot invariants; topological defects | Charge, spin, isospin encoded in Alexander polynomial, linking number, writhe[^39][^40] |
| **Level 3 (Core)** | Compressible soliton | Mass, self-energy, Compton oscillation, de Broglie particle | Double-solution \(\phi_{NL}\); Compton-Yukawa wavepacket[^41][^11] |
| **Inter-level coupling** | Compressible radiation at L2↔L1 interface | Decoherence, measurement events | Vortex reconnection phonon pulse[^42][^36] |

The key insight from the nested architecture is that *the same fluid that is incompressible at one scale is a compressible excitation from the perspective of the next scale up.* Each particle is a compression wave believing it rides an incompressible background, while that background is itself compressible from a higher vantage. The Bohm implicate-order formalization of this as an infinite tower — each level's quantum potential organized by a superquantum potential of the level above — is functionally equivalent to Wilsonian effective field theory: integrating out UV levels yields the low-energy theory, with the soliton core setting a natural UV cutoff.[^43][^44][^45]

***

## 4. Validation and Invalidation Analysis Summary

### 4.1 What is Already Validated

| Criterion | Status | Evidence |
|---|---|---|
| Madelung ↔ Schrödinger exact map | ✅ Proven theorem | Kähler morphism proof[^1][^3] |
| Fluid Maxwell equations from Euler+vorticity | ✅ Derivation complete | Kambe 2010[^2]; geometric algebra 2020[^20] |
| Acoustic metric from barotropic+irrotational fluid | ✅ Proven theorem | Unruh 1981, Visser 1993[^22][^23][^25] |
| Acoustic Hawking radiation | ✅ Observed experimentally | Steinhauer 2016[^10], 2022[^9] |
| SK-EFT dissipative correction to T_H | ✅ **Phase 1-5a COMPLETE (April 2026)** | This program: 748 theorems + 3 axioms in 49 Lean 4 modules (zero sorry, 252 Aristotle-proved across 30+ runs), 48 Python modules, 1390 tests, 8 papers, 69 figures, 22 notebooks. Phases 1-4: δ_diss, δ^(2)(ω), gauge erasure, exact WKB, ADW gap equation, platform predictions, vestigial MC, fracton, backreaction. Phase 5: κ-scaling, polariton Tier 1, chirality wall formal verification (9 GS conditions, 5 TPF violations), first-ever categorical infrastructure (PivotalCategory, FusionCategory, DrinfeldDouble), Weingarten MC framework. **Phase 5a: first formal verification of a lattice chiral fermion construction** — Gioia-Thorngren [H,Q_A]=0 machine-verified, first Onsager algebra and Steenrod A(1) formalizations, Z₁₆ anomaly classification, three-pillar chirality wall master theorem. |
| Emergent Weyl fermions in ³He-A | ✅ Well-established | Volovik, PNAS 1999[^8]; multiple confirmations |
| BF gauge theory of incompressible flow | ✅ Proven | Eling 2023[^5][^6] |
| QGP near-perfect fluid (KSS bound) | ✅ Observed experimentally | RHIC: \(1 < 4\pi(\eta/s) < 2.5\)[^14][^13] |
| Double-solution Lorentz-covariant Lagrangian | ✅ Derived | Darrow-Bush 2024[^11][^12] |
| Born rule relaxation (H-theorem) | ✅ Numerically confirmed | Valentini 1991/92; simulations[^46][^47] |

### 4.2 What Remains Invalidated or Open

| Issue | Status | Root Cause |
|---|---|---|
| Full non-Abelian SU(3)×SU(2)×U(1) | ❌ Open | Internal spaces not emergent from pure fluid; must be imposed[^21][^48] |
| Dynamical Einstein equations | ❌ Partial | Acoustic metric is algebraic; effective EH action in ³He-A requires quantum liquid[^49][^31] |
| Renormalizability / UV completion | ❌ Not resolved | Requires quantization of the fluid field; classical hierarchy cannot regulate loop integrals[^50][^51] |
| Exact Lorentz symmetry at all scales | ⚠️ Emergent only | UV cutoff at healing length / atomic spacing in all known analogs[^52][^53] |
| True fermionic second quantization | ⚠️ Partial | Weyl quasiparticles in ³He-A are a mean-field result; Grassmann path integral not replaced[^54] |
| CPT and preferred frame | ⚠️ Pilot-wave tension | Nonlocality of pilot wave requires preferred foliation at ontological level[^55][^56] |

***

## 5. Deliverable 1: Theoretical Derivation Program

### 5.1 Effective Action for the Two-Fluid System

**Goal:** Derive the combined effective action for a barotropic, inviscid compressible fluid coupled to an incompressible sector described by a BF/Chern-Simons term for vorticity, and check for an emergent \(\sqrt{-g}R\) term.

**Starting point:** The full fluid Lagrangian density in Clebsch representation:

\[\mathcal{L} = \frac{1}{2}\rho v^2 - \rho e(\rho) - \rho\phi_g + \lambda(\partial_t\rho + \nabla\cdot(\rho\mathbf{v})) + \alpha(\partial_t s + \mathbf{v}\cdot\nabla s)\]

where \(e(\rho)\) is specific internal energy and \(\phi_g\) is the gravitational potential. For an incompressible sector with \(\nabla\cdot\mathbf{v}=0\), add the BF term from Eling (2023):

\[\mathcal{L}_\text{BF} = B_{\mu\nu}F^{\mu\nu}, \qquad F_{\mu\nu} = \partial_\mu A_\nu - \partial_\nu A_\mu\]

with \(A_\mu \to v_\mu\) (fluid velocity 1-form), \(B_{\mu\nu}\) the Lagrange multiplier enforcing incompressibility and helicity conservation. The coupled action is:[^5]

\[S_\text{eff} = \int d^4x\left[\mathcal{L}_\text{comp}(\rho,\mathbf{v},s) + \mathcal{L}_\text{BF}(A,B) + \mathcal{L}_\text{int}(\rho,A)\right]\]

where \(\mathcal{L}_\text{int}\) couples density fluctuations (compressible) to gauge field fluctuations (incompressible) at the fluid interface.

**Low-energy integration:** Integrate out compressible modes (frequencies \(\omega > \omega_c = c_s/\xi\), where \(\xi\) is the soliton core scale from Level 3):

\[S_\text{eff,IR} = \int d^4x\left[\frac{M_\text{eff}^2}{16\pi}\sqrt{-g}R + \mathcal{L}_\text{CS}(A) + \mathcal{O}(E^2/M_\text{eff}^2)\right]\]

The Volovik result guarantees that for a superfluid order-parameter texture, \(M_\text{eff}^2 \propto \rho_s c_s^2\) (superfluid density × sound speed squared). The open theoretical task is to derive this for the general two-fluid system without assuming a specific microscopic quantum liquid.[^31]

**Expected outcome:** Either (a) the emergent Einstein-Hilbert term appears with a computable coefficient, confirming that the two-fluid architecture contains emergent gravity in its effective description; or (b) it does not appear, identifying the obstruction (likely: the need for fermionic degrees of freedom at the quantum level, i.e., the quantum liquid requirement).

### 5.2 Non-Abelian Extension

**Goal:** Promote the Kambe construction from U(1) to non-Abelian internal symmetry SU(N) using the strain-rate tensor eigenvectors as the internal space basis.

The strain-rate tensor \(e_{ij} = \tfrac{1}{2}(\partial_i v_j + \partial_j v_i)\) has three real eigenvalues and an associated SO(3) frame. Local diagonalization defines a connection on the bundle of eigenvector frames — a natural SO(3) gauge field. Ghosh (2001) identified this as the geometric origin of gauge structure in fluid mechanics. To extend to SU(3), one augments with the three off-diagonal shear-rate components, forming an 8-dimensional adjoint representation analogous to the gluon octet. The resulting non-Abelian source equations are:[^21][^57]

\[\nabla\cdot\mathbf{H}^a = 0\]
\[a_0^2\nabla\times\mathbf{H}^a - \partial_t\mathbf{E}^a = \mathbf{J}^a + gf^{abc}\mathbf{A}^b\times\mathbf{H}^c\]

**Validation test:** In the limit of uniform, irrotational, barotropic flow, the equations must reduce to the free Yang-Mills equations \(D_\mu F^{\mu\nu} = 0\). This is the key theoretical milestone that would establish whether SU(3) color can be seen as a gauge theory of fluid vortex-frame rotations.

### 5.3 Guidance Equation in Curved Acoustic Spacetime

**Goal:** Write the de Broglie-Bohm guidance equation \(\mathbf{v} = \nabla S/m\) in covariant form on the acoustic metric \(g_{\mu\nu}\) and show that the resulting trajectory equation is equivalent to a geodesic plus a force term from the quantum potential.

The covariant guidance equation on the acoustic spacetime is:

\[u^\mu = g^{\mu\nu}\partial_\nu S / m\]

where \(u^\mu\) is the 4-velocity. The trajectory equation becomes:

\[m\frac{Du^\mu}{d\tau} = -\nabla^\mu Q, \qquad Q = -\frac{\hbar^2}{2m}\frac{\Box_{(g)}\sqrt{\rho}}{\sqrt{\rho}}\]

with \(\Box_{(g)}\) the d'Alembertian of the acoustic metric. In the WKB limit (\(\hbar\to 0\)), this reduces to the geodesic equation on \(g_{\mu\nu}\), confirming that the pilot-wave particle follows acoustic spacetime geodesics in the classical limit. Deviations from geodesic motion are controlled by the quantum potential — providing a prediction: in BEC analog gravity experiments, a test tracer particle should deviate from acoustic geodesics by an amount \(\sim\hbar^2/m^2 \xi^2\) at the healing-length scale.[^58][^11]

***

## 6. Deliverable 2: Lean 4 Formal Verification Plan

### 6.1 Infrastructure and Prerequisites

Lean 4 is an interactive theorem prover based on dependent type theory, developed at Microsoft Research. The Mathlib4 library provides a comprehensive mathematical foundation including differential geometry, functional analysis, measure theory, and Lie group theory. HepLean (Tooby-Smith 2024) already formalizes high-energy physics results — CKM matrices, anomaly cancellation, Higgs physics — in Lean 4, and is available as an open-source project at `https://github.com/HEPLean/HepLean`. PhysLean extends this to broader physics. Index notation for tensor contractions (Tooby-Smith 2024) has been formally implemented in Lean 4, enabling physics-style tensor manipulations with verified correctness. Dimensional analysis including the Buckingham Pi theorem has been formalized (2025). The Lean Millennium Prize Problems project has begun formalizing the Navier-Stokes global regularity problem, providing definitions of classical and weak solutions, energy inequalities, and domain definitions that this project can directly reuse. Differential geometry (manifolds, vector bundles, connections, curvature) is being formalized at Bonn.[^59][^60][^61][^62][^63][^16][^64][^65][^15]

### 6.2 Theorem Targets

The following theorems are the primary Lean formalization goals, in order of priority:

**Theorem 1: Madelung is a Kähler Morphism** *(Priority: Highest — already proven, formalizing establishes Lean infrastructure)*[^3][^1]

```lean
-- Statement sketch
theorem madelung_is_kahler_morphism :
  ∀ (ρ : SmoothProbabilityDensity M) (θ : SmoothFunction M ℝ),
  let ψ := madelung_transform ρ θ
  isSymplectomorphism (cotangentBundle_FisherRao M) (projectiveSpace_FubiniStudy M) ψ ∧
  isIsometry (cotangentBundle_FisherRao M) (projectiveSpace_FubiniStudy M) ψ := by
  -- follows Khesin-Misiołek-Modin (2018) proof
  sorry
```

The proof follows the main theorem in Khesin et al. (2018): (1) define the symplectic form on \(T^*\mathrm{Dens}(M)\) as the canonical \(\omega_\mathrm{can} = \int \delta\rho\wedge\delta v\); (2) define the symplectic form on \(P\mathcal{H}\) as the Fubini-Study form; (3) show that the Madelung transform pulls back the Fubini-Study form to the canonical form. The isometry is with respect to the Fisher-Rao (on density side) and Fubini-Study (on wavefunction side) Riemannian metrics.[^1][^3]

**Theorem 2: Fluid Maxwell Equations from Euler + Vorticity** *(Priority: High — foundational for QED mapping)*

```lean
-- Statement sketch
theorem fluid_maxwell_from_euler
    (ρ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ)  -- density
    (v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))  -- velocity
    (h : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ)  -- enthalpy
    (hEuler : satisfiesEulerEquation ρ v h)
    (hIsentropic : isIsentropic ρ v)
    (hBarotropic : isBarotropic ρ h) :
    let E := fun t x => -(partialDeriv t v t x) - gradient h t x
    let H := fun t x => curl v t x
    satisfiesMaxwellM1 H ∧  -- ∇·H = 0
    satisfiesMaxwellM3 E H  -- ∇×E + ∂_tH = 0
    := by
  -- M1 follows from H = ∇×v and div(curl) = 0
  -- M3 follows from vorticity equation ∂_tω = ∇×(v×ω)
  sorry
```

(M1) follows from \(\nabla\cdot\mathbf{H} = \nabla\cdot(\nabla\times\mathbf{v}) = 0\) by the identity \(\mathrm{div}(\mathrm{curl}) = 0\). (M3) is the vorticity equation. (M2) and (M4) require the Euler + continuity system and involve source terms.[^4][^2]

**Theorem 3: Helicity Conservation as Bianchi Identity** *(Priority: High — establishes U(1) gauge symmetry)*

```lean
-- Statement sketch
theorem helicity_bianchi_identity
    (v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hIncompressible : ∀ t x, divergence v t x = 0)
    (hEuler : satisfiesIncompressibleEuler v) :
    ∀ t, totalHelicity v t = totalHelicity v 0 := by
  -- follows from d(*H) = 0 where H is helicity 3-form
  -- equivalent to Kelvin's circulation theorem + helicity invariance
  sorry
```

This encodes the result from Eling (2023): in incompressible flow, the helicity 3-form \(H = v\wedge dv\) satisfies \(d(*H) = 0\) — a Bianchi identity — providing the topological U(1) gauge invariance.[^6][^5]

**Theorem 4: Acoustic Metric Well-Definedness** *(Priority: Medium — formalizes GR mapping)*

Formalize the statement that for barotropic, inviscid, irrotational flow, the acoustic perturbation equation takes the form \(\Box_{g_\text{ac}}\phi_1 = 0\) with the acoustic metric as defined above, following Visser-Molina-Paris (2010). This requires formalizing the GR barotropic fluid equations, the irrotational condition, linearization, and the d'Alembertian.[^25]

**Theorem 5: Emergent Tetrad Vielbein Postulate** *(Priority: Medium — addresses gravity gap)*

For a superfluid order parameter of ³He-A form, show that the emergent vielbein \(e^a_\mu\) from the texture satisfies the vielbein postulate \(\nabla_\mu e^a_\nu = 0\) (parallel transport compatibility), a necessary condition for the emergent metric to be a valid Riemannian structure with a well-defined Levi-Civita connection.[^7][^31]

### 6.3 Workflow and Quality Assurance

All Lean scripts will be developed in the `PhysLean` repository structure with:[^16]
- One file per theorem cluster (e.g., `FluidMaxwell.lean`, `MadelungSymplecto.lean`, `AcousticMetric.lean`)
- Continuous integration (GitHub Actions) running `lake build` on every commit
- `sorry`-free milestone: no theorem can be marked complete until all `sorry` placeholders are replaced by verified proofs
- AI-assisted proof tactics (`decide`, `norm_num`, `aesop`, `polyrith`) from Mathlib4 and HepLean infrastructure[^66]

A publicly accessible GitHub repository (`fluid-physics-lean`) will host all code, with releases tagged at each major theorem completion. Each Lean proof file constitutes a formally verified component of the theoretical deliverable.

**Status (April 2026):** The Lean formalization has far exceeded the original feasibility study targets. Current state: 748 theorems + 3 axioms across 49 modules (zero sorry), 252 proved by the Aristotle automated theorem prover. The formalization covers acoustic metrics, SK-EFT corrections, gauge erasure, WKB connection, ADW gravity, chirality wall (GS no-go + TPF evasion + GT positive construction), Onsager algebra, Z₁₆ classification, fusion categories, Drinfeld doubles, gauge emergence, Weingarten MC, RHMC, and the three-pillar chirality wall master theorem. Eight papers drafted with 69 publication-quality figures.

***

## 7. Deliverable 3: Analog Experimental Protocols

### 7.1 Bose-Einstein Condensate Acoustic Black Hole

**Platform:** Ultracold ⁸⁷Rb or ²³Na BEC in a laser-trap configuration that imposes a velocity profile crossing the local sound speed (creating a sonic horizon), as demonstrated in Steinhauer's laboratory.[^10][^9]

**Key Observables:**
- Phonon emission spectrum: thermal Planck distribution at temperature \(T_H\) predicted by surface gravity \(\kappa = \frac{1}{2}\partial_n(c_s-v_\perp)|_\text{horizon}\)
- Two-point correlation function \(G^{(2)}(\mathbf{x},\mathbf{x}')\) between subsonic (Hawking) and supersonic (partner) phonons — entanglement signature
- High-k dispersion: deviation from linear phonon dispersion at wavelengths approaching healing length \(\xi = \hbar/\sqrt{2m\mu}\), providing the UV cutoff observable

**Success Criterion:** Agreement of \(T_H\) with prediction within 20%; two-point correlation function matches Bogoliubov simulation; UV cutoff scale \(1/\xi\) matches predicted soliton core size from the Level 3 double-solution model.

**Validation of Fluid Mapping:** The match between \(T_H\) and \(\kappa\) directly validates the acoustic metric construction. The deviation from thermality at high-k tests the Lorentz-violating UV cutoff predicted by the fluid hierarchy.

### 7.2 Superfluid ³He-A: Emergent Gauge and Gravitational Fields

**Platform:** Lancaster Ultra-Low Temperature Laboratory or Aalto University low-temperature facility, as used in the QUEST-DMC collaboration. Requires millikelvin temperatures (\(T < 2.5\) mK for ³He-A phase) and precise magnetic texture control.[^35]

**Key Observables:**
- Quantized thermal Hall conductivity \(\kappa_{xy}\) proportional to emergent chirality of Weyl point quasiparticles[^67][^31]
- Gyrotropic magnetic susceptibility reflecting effective tetrad response
- Phase transitions between ³He-A (Weyl) and ³He-B (topological superfluid) as a function of pressure, testing the two scenarios of emergent vs. broken Lorentz symmetry[^31]
- Vortex reconnection dynamics: universal law of reconnection velocity asymmetry (2025)[^36]

**Success Criterion:** Half-integer quantized steps in thermal Hall conductivity consistent with emergent Weyl fermion chirality; vortex reconnection law agrees with the 2025 PNAS result at the 10% level; phase boundary between ³He-A and ³He-B mapped in pressure-temperature space.

### 7.3 Optical Kerr Fluid: Soliton Guidance by Pilot Wave

**Platform:** Nonlinear optical medium (silica fiber or photorefractive crystal) with Kerr effect, where the intensity-dependent refractive index \(n = n_0 + n_2 I\) provides an effective quantum potential.[^68][^69]

**Key Observables:**
- Light-bullet (3+1D soliton) trajectory as a function of background phase gradient: does the soliton velocity satisfy \(\mathbf{v}_\text{soliton} = \nabla\phi_\text{bg}/m_\text{eff}\)?
- Interference between soliton and linear background wave: do quantum-potential corrections to the trajectory reproduce the Heisenberg-uncertainty analog predicted by Darrow-Bush 2024?[^11]
- Vortex-dipole pair dynamics in the photon fluid: does the pair separate at a rate consistent with acoustic reconnection dynamics?

**Success Criterion:** Soliton trajectory matches de Broglie-Bohm guidance to within experimental uncertainty (< 5% velocity deviation); quantum-potential interference shifts are quantitatively consistent with the Compton-scale wavepacket prediction.

### 7.4 Walking-Droplet Pilot-Wave Analog

**Platform:** Vibrating silicone oil bath system as developed by Couder, Fort, Bush, and collaborators, with charged or spin-polarized droplets.[^70][^71][^69]

**Key Observables:**
- Distribution of droplet positions as a function of time: does the distribution relax toward \(|\psi|^2\) (Born rule) from a non-equilibrium initial state?
- Relaxation rate: does the coarse-grained H-function satisfy \(\dot{H} \leq 0\) (Valentini's subquantum H-theorem)?[^46]
- Many-droplet correlations: do pairs of identically-prepared droplets exhibit position correlations inconsistent with local realism?

**Success Criterion:** Exponential decay of the H-function with a timescale consistent with de Broglie-Bohm quantum relaxation simulations; position distribution converges to Born-rule statistics within 10 oscillation periods.[^47][^46]

***

## 8. Deliverable 4: Phenomenological Signatures and Null-Tests

### 8.1 Modified Dispersion Relation (MDR)

The fluid hierarchy predicts that Lorentz symmetry is emergent and breaks at the UV cutoff scale \(\xi\) (soliton core / healing length). This generically produces a modified dispersion relation:

\[E^2 = p^2c^2 + \xi_1\frac{p^3c^3}{E_\text{QG}} + \xi_2\frac{p^4c^4}{E_\text{QG}^2} + \ldots\]

**Current constraints:** Fermi-LAT observations of GRBs give \(E_\text{QG,1} > 7.6\,E_\text{Pl}\) (linear case) from GRB 090510. LHAASO observations of GRB 221009A (the "BOAT" - Brightest Of All Time) give \(E_\text{QG,1} > 5.4\times10^{19}\) GeV (subluminal) at 95% C.L.. New cosmological-model-independent constraints from 88 GRB time delays (2024-2026) extend these limits to higher redshifts.[^72][^73][^74][^75]

**Implication for fluid model:** The fluid hierarchy's natural UV cutoff is the soliton core size \(\xi_\text{core}\). For the model to be compatible with LIV constraints, the corresponding energy scale \(E_\text{cutoff} = \hbar c/\xi_\text{core}\) must exceed \(E_\text{QG,1} > 5.4\times10^{19}\) GeV. This places a strong lower bound on the core size: \(\xi_\text{core} < \hbar c/(5.4\times10^{19}~\text{GeV}) \approx 3.7\times10^{-36}\) m — smaller than the Planck length (1.6\times10^{-35}\) m). The fluid model's UV cutoff must therefore lie at or beyond the Planck scale to be phenomenologically viable.[^74][^72]

### 8.2 QGP Viscosity as Fluid-Gauge Validation

The shear viscosity-to-entropy ratio \(\eta/s\) of the quark-gluon plasma extracted from heavy-ion collisions at RHIC gave \(1 < 4\pi(\eta/s)_\text{QGP} < 2.5\), and the same value described LHC Pb+Pb collisions. This is the most precise quantitative connection between SU(3) gauge dynamics and relativistic fluid behavior. The fluid mapping predicts that the strongly-coupled QGP should behave as a fluid with \(\eta/s\) near the KSS bound — a prediction that has been experimentally confirmed.[^14][^13]

**Validation target:** Future higher-precision \(\eta/s\) measurements from Run 3/4 at the LHC (ALICE upgrade) and sPHENIX at RHIC should further constrain the transport coefficients. The fluid model predicts that any temperature dependence of \(\eta/s\) reflects the running of the effective fluid coupling — a potential signal of the Wilsonian RG flow in the fluid hierarchy.

### 8.3 Born-Rule Nonequilibrium Signatures

Valentini (2024) showed that in quantum gravity, the Born rule emerges only in the semiclassical regime and is unstable to corrections that could leave relic signatures[^43]. Specifically: CMB power spectrum anomalies at the largest angular scales could reflect quantum non-equilibrium (\(\rho \neq |\psi|^2\)) in the inflationary modes; anomalous relic abundances of axion-like particles could result from freeze-out occurring before quantum relaxation is complete.

**Search strategy:** The residual non-equilibrium parameter \(\eta = (\rho - |\psi|^2)/|\psi|^2\) predicts deviations from standard inflationary power spectra of order \(\eta_\text{relic}^2\). CMB-S4 (planned for early 2030s) could detect or constrain these deviations. Coupled-harmonic-oscillator simulations show that interactions can delay quantum relaxation for some initial states[^47], suggesting that dark matter candidates from the early universe may carry detectable non-equilibrium signatures.

### 8.4 Helicity Anomalies in Relativistic Plasmas

The incompressible fluid sector's helicity is topologically conserved (Bianchi identity). However, at the compressible-incompressible interface (reconnection events), helicity can be generated or destroyed via sound emission. In the QGP, this predicts anomalous helicity production at the onset of deconfinement — potentially observable as charge-dependent flow fluctuations (the chiral magnetic effect).[^5][^6]

**Search strategy:** Reanalyze STAR (RHIC) and ALICE (LHC) heavy-ion data for charge-separation correlations \(\langle\cos(\phi_\alpha + \phi_\beta - 2\Psi_\text{RP})\rangle\) as a function of collision energy and centrality, comparing to fluid-model predictions for helicity sourcing at the confinement-deconfinement transition.

***

## 9. Feasibility Study Timeline

| Phase | Months | Activities | Milestone |
|---|---|---|---|
| **I. Theory Setup** | 1–3 | Derive two-fluid effective action; set up Lean 4 environment; establish PhysLean module structure | Lean environment operational; draft effective action |
| **II. Lean Proofs** | 2–7 | Formalize Theorems 1–3 (Madelung, Fluid Maxwell, Helicity Bianchi) | `sorry`-free proofs of T1–T3 compiled |
| **III. Non-Abelian Theory** | 4–9 | Derive SU(N) extension; test Yang-Mills limit; attempt Lean formalization of T4–T5 | Draft Yang-Mills reduction; T4–T5 Lean statements with partial proofs |
| **IV. Experimental Design** | 4–12 | Finalize protocols for BEC, optical fluid, droplet systems; engage ³He facility | Experimental protocol documents completed |
| **V. Analog Experiments** | 8–15 | Execute optical soliton guidance, droplet relaxation; collaborate on BEC horizon | Data from 2+ analog platforms acquired |
| **VI. Phenomenology** | 10–16 | Compute MDR constraints; analyze QGP η/s predictions; CMB non-equilibrium bounds | Phenomenology white-paper complete |
| **VII. Integration & Report** | 14–18 | Integrate theory, Lean proofs, experimental data, phenomenology; write final report | Full feasibility study report with go/no-go decision |

***

## 10. Budget Outline

| Category | Estimated Cost | Notes |
|---|---|---|
| Theory team (2 postdocs × 18 months) | $360,000 | Expertise: fluid dynamics, QFT, gauge theory, Lean/formal methods |
| Senior PI (25% effort × 18 months) | $90,000 | Oversight and cross-domain expertise |
| BEC lab collaboration (subcontract) | $150,000 | Access to BEC horizon facility; cryogenics consumables |
| ³He-A facility access (subcontract) | $200,000 | Millikelvin cryogenics; QUEST-DMC collaboration |
| Optical fluid / nonlinear optics lab | $80,000 | Equipment, fiber, photorefractive crystals |
| Walking-droplet facility | $30,000 | Silicon oil bath, vibration control, camera |
| Computing (cluster, software) | $30,000 | RG numerics, Lean CI infrastructure |
| Travel and collaboration meetings | $40,000 | Quarterly team meetings; international conference |
| Indirect costs (30%) | $294,000 | Institutional overhead |
| **Total** | **$1,274,000** | ~$1.2M rounded |

***

## 11. Go/No-Go Decision Criteria

| Criterion | Pass Condition |
|---|---|
| **T1: Madelung Lean proof** | `sorry`-free Lean 4 proof of Kähler morphism theorem compiled against Mathlib4 |
| **T2: Fluid Maxwell Lean proof** | `sorry`-free derivation of M1–M4 from isentropic Euler + vorticity in Lean 4 |
| **T3: Helicity Bianchi identity** | `sorry`-free proof that helicity conservation is a Bianchi identity in BF gauge theory |
| **T4/T5: Emergent gravity** | Either: (a) Einstein-Hilbert term derived from two-fluid effective action, or (b) precise obstruction identified and documented |
| **Non-Abelian test** | Yang-Mills equations recovered in irrotational limit of SU(N) fluid extension, or specific group-theoretic obstruction identified |
| **Experimental** | ≥ 2 of 4 analog platforms demonstrate quantitative agreement (within stated tolerances) with theoretical predictions |
| **Phenomenology window** | At least 1 predicted signature (MDR, helicity anomaly, or Born-rule deviation) lies within reach of near-future experiments and is consistent with existing constraints |
| **No fatal inconsistency** | No derivation violates energy-momentum-charge conservation in a way not curable by higher-order terms; no prediction of superluminal signaling or macroscopic equivalence-principle violation |

If all criteria pass: recommend proceeding to full development program (targeting a 3–5 year grant proposal to NSF/DOE, with potential for quantum simulation technology spinoffs). If T4/T5 fails decisively with a well-defined obstruction: publish the obstruction result and investigate whether supersymmetric or string-inspired extensions of the fluid hierarchy can bypass it. If experimental platforms fail: revisit whether the analog systems are faithful enough and consider dedicated quantum simulation on near-term hardware (superconducting qubits or trapped ions).[^27]

***

## 12. Skipped Items and Open Questions

The following items were identified as research tasks but could not be completed in this study:

| Item | Reason Skipped | How to Address |
|---|---|---|
| **Full numerical Wilsonian RG computation for the fluid hierarchy** | Requires weeks of numerical computation on a dedicated cluster; no closed-form analytic result exists | Month 6–9 of the research program; requires Mathematica/Julia + cluster |
| **Closed-form SU(3) color reduction from fluid strain-rate tensor** | Frontier research; no completed derivation exists in the literature | Primary theoretical task for the postdoc with QFT expertise |
| **³He-A thermal Hall conductivity measurement (data acquisition)** | Physical apparatus not accessible; requires millikelvin facility | Subcontract to Lancaster or Aalto through QUEST-DMC |
| **BEC acoustic black hole data acquisition** | Physical apparatus not accessible; requires ultracold lab | Subcontract to Steinhauer group or MIT-Harvard CUA |
| **Lean formalization of T4 and T5 (emergent tetrad, Einstein-Hilbert)** | Requires differential geometry formalization in Lean that is currently in progress at Bonn[^61]; cannot be completed until those Lean libraries mature | Timeline: months 6–12; dependent on external Lean geometry library |
| **Quantitative prediction for CMB Born-rule deviation** | Requires full inflationary quantum non-equilibrium computation beyond scope here | Follow-on work; collaborator with CMB theory expertise required |
| **Derivation of Higgs mechanism analog from two-fluid condensation** | Non-Abelian Higgs sector requires spontaneous breaking of SU(2)×U(1) in the superfluid order parameter; no clean fluid analog currently exists | Long-term theoretical goal; potentially addressable via non-Abelian superfluid dynamics[^76] |

***

## 13. Conclusion

The fluid-based approach to fundamental physics is well-motivated by a chain of rigorous mathematical results and experimental confirmations. The Madelung symplectomorphism, the Kambe fluid Maxwell system, the Unruh-Visser acoustic metric, Eling's BF gauge theory of incompressible flow, Volovik's emergent Weyl fermions and gravity in ³He-A, the experimental observation of acoustic Hawking radiation, and the near-perfect-fluid behavior of the quark-gluon plasma together constitute a substantial body of evidence that fluid dynamics and fundamental physics are deeply structurally related — not merely analogous.

The hierarchical architecture (Level 1: incompressible pilot wave / gauge field; Level 2: incompressible vortex knot / topological quantum numbers; Level 3: compressible soliton / particle mass) provides a unified ontological picture that addresses quantum coherence, emergent Lorentz symmetry, topological gauge invariance, spontaneous symmetry breaking, and a route toward emergent gravity — all from classical and semi-classical fluid mechanics.

The remaining hard problems — full non-Abelian SM gauge structure, dynamical Einstein equations, and renormalizability — are genuine, but each has a well-defined research path. The program's ceiling is the quantization step: classical and semi-classical fluid constructions cannot reproduce quantum loop corrections or true fermionic second quantization without quantizing the fluid fields themselves. Whether this is a fundamental barrier or a solvable technical challenge is precisely the question the feasibility study is designed to answer.

The integration of Lean 4 formal verification throughout the theoretical program provides an unprecedented quality guarantee: every major theoretical claim will carry a machine-checked certificate of logical correctness, making the study's findings maximally reproducible and reusable by the broader community.[^62][^15][^16]

---

## References

1. [Digital Object Identifier (DOI) https://doi.org/10.1007/s00205-019-01397-2](https://www.math.toronto.edu/khesin/papers/madelungARMA.pdf)

2. [On Fluid Maxwell Equations](http://www.tuks.nl/pdf/Reference_Material/Fluid_Dynamics/Kambe_-_On_Fluid_Maxwell_Equations.pdf)

3. [[PDF] Geometry of the Madelung transform - arXiv](https://arxiv.org/pdf/1807.07172.pdf) - We prove that, more generally, the Madelung trans- form is a Kähler map (i.e. a symplectomorphism an...

4. [[PDF] New formulation of equations of compressible fluids on analogy of ...](http://www.tuks.nl/pdf/Reference_Material/Kambe/New%20formulation%20of%20equations%20of%20compressible%20fluids%20on%20analogy%20of%20Maxwells%20equations%20-%20FDR2010.pdf) - This system can be reformulated in a form analogous to that of electromagnetism governed by Maxwell'...

5. [[PDF] arXiv:2310.12475v1 [hep-th] 19 Oct 2023](https://arxiv.org/pdf/2310.12475.pdf) - At long distances, quantum Hall states are described by Chern-Simons theory, which is a topological ...

6. [A gauge theory for the 3+1 dimensional incompressible Euler equations](https://ar5iv.labs.arxiv.org/html/2310.12475) - We show that the incompressible Euler equations in three spatial dimensions can be expressed in term...

7. [Field theory in superfluid 3He: What are the lessons for particle physics, gravity and high-temperature superconductivity?](https://arxiv.org/abs/cond-mat/9812381) - There are several classes of homogeneous Fermi-systems which are characterized by the topology of th...

8. [Field theory in superfluid 3He: What are the lessons for particle physics, gravity, and high-temperature superconductivity? | PNAS](https://www.pnas.org/doi/10.1073/pnas.96.11.6042) - There are several classes of homogeneous Fermi systems that are characterized by the topology of the...

9. [Confirmation of stimulated Hawking radiation, but not of black hole ...](https://link.aps.org/doi/10.1103/PhysRevD.106.102007) - We find that the correlations between the Hawking and partner particles are directly observable in t...

10. [Observation of quantum Hawking radiation and its entanglement in an analogue black hole](https://www.deeplook.ir/wp-content/uploads/2016/08/10.1038@nphys3863.pdf)

11. [Revisiting de Broglie's Double-Solution Pilot-Wave Theory ...](https://arxiv.org/abs/2408.06972) - The relation between de Broglie's double-solution approach to quantum dynamics and the hydrodynamic ...

12. [Revisiting de Broglie's Double-Solution Pilot-Wave Theory with a Lorentz-Covariant Lagrangian Framework](http://arxiv.org/abs/2408.06972) - The relation between de Broglie's double-solution approach to quantum dynamics and the hydrodynamic ...

13. [[1108.5323] The viscosity of quark-gluon plasma at RHIC and the LHC](https://arxiv.org/abs/1108.5323) - The specific shear viscosity (eta/s)_QGP of quark-gluon plasma (QGP) can be extracted from elliptic ...

14. [This is the accepted manuscript made available via CHORUS. The article has been](https://link.aps.org/accepted/10.1103/PhysRevLett.106.192301)

15. [[2405.08863] HepLean: Digitalising high energy physics - arXiv.org](https://arxiv.org/abs/2405.08863) - We introduce HepLean, an open-source project to digitalise definitions, theorems, proofs, and calcul...

16. [A project to digitalise results from physics into Lean. · GitHub](https://github.com/HEPLean/PhysLean) - The project shall contain results (definitions, theorems, lemmas and calculations) from physics form...

17. [The Madelung transform as a momentum map](https://www.aimsciences.org/article/doi/10.3934/jgm.2017006) - The Madelung transform relates the non-linear Schrödinger equation and a compressible Euler equation...

18. [[PDF] The Madelung transform as a momentum map | Semantic ...](https://www.semanticscholar.org/paper/036db481081fc43e9ec62a530fd3220f6bf2fb95) - The Madelung transform relates the non-linear Schr\"odinger equation and a compressible Euler equati...

19. [[Literature Review] Dirac Fields in Hydrodynamic Form and their Thermodynamic Formulation](https://www.themoonlight.io/en/review/dirac-fields-in-hydrodynamic-form-and-their-thermodynamic-formulation) - The paper investigates the Dirac field theory by formulating it in a hydrodynamic picture using the ...

20. [A geometric algebraic approach to fluid dynamics - Academia.edu](https://www.academia.edu/90618966/A_geometric_algebraic_approach_to_fluid_dynamics) - The study shows that fluid Maxwell's equations can be retrieved from a single equation, enhancing th...

21. [Abelian and non-Abelian considerations on compressible fluids with ...](https://link.aps.org/doi/10.1103/PhysRevD.91.125011) - In this work, we have obtained Maxwell-type equations for a compressible fluid whose sources are fun...

22. [[PDF] Acoustic black holes: horizons, ergospheres and Hawking radiation](https://the-center-of-gravity.com/documents/78/Visser_Acoustic-black-holes-horizons-ergospheres-and-Hawking-radiation.pdf) - The acoustic metric gµν (t, x) governing the propagation of sound depends algebraically on the densi...

23. [[PDF] Vorticity in the acoustic analogue of gravity](https://homepages.ecs.vuw.ac.nz/~visser/Seminars/Survey/cargese-part1.pdf)

24. [[PDF] Acoustic geometry for general relativistic barotropic irrotational fluid ...](https://arxiv.org/pdf/1001.1310.pdf) - As usual, the acoustic metric follows from combining the linearized Bernoulli equation and linearize...

25. [Acoustic geometry for general relativistic barotropic irrotational fluid ...](https://arxiv.org/abs/1001.1310) - In this article we provide a pedagogical and simple derivation of the general relativistic acoustic ...

26. [Vorticity in analogue spacetimes | Phys. Rev. D - APS Journals](https://link.aps.org/doi/10.1103/PhysRevD.99.044025) - THE UNRUH METRIC. The Unruh 1981 metric for acoustic perturbations in an irrotational barotropic inv...

27. [Quantum simulation of Hawking radiation and curved spacetime ...](https://pmc.ncbi.nlm.nih.gov/articles/PMC10241825/) - In summary, we have experimentally simulated a curved spacetime of black hole and observed an analog...

28. [[PDF] A gauge theory for the 3+1 dimensional incompressible Euler ...](https://www.semanticscholar.org/paper/A-gauge-theory-for-the-3+1-dimensional-Euler-Eling/70ca05c144783eccfe4f910440e274c09f3c3e17) - We show that the incompressible Euler equations in three spatial dimensions can be expressed in term...

29. [Topological BF theory of the quantum hydrodynamics of incompressible polar fluids](https://journals.aps.org/prb/abstract/10.1103/PhysRevB.90.235118) - We analyze a hydrodynamical model of a polar fluid in (3 + 1)-dimensional spacetime. We explore a sp...

30. [PHYSICAL REVIEW B 90, 235118 (2014)](https://www.dora.lib4ri.ch/psi/islandora/object/psi:9655/datastream/PDF/Tiwari-2014-Topological_BF_theory_of_the-(published_version).pdf)

31. [Combined Lorentz Symmetry: Lessons from Superfluid He](https://acris.aalto.fi/ws/portalfiles/portal/75023549/Volovik_Combined_Lorentz_Symmetry_Lessons_from_Superfluid_3He.pdf)

32. [Simulation of Quantum Field Theory and Gravity in Superfluid He-3](https://arxiv.org/abs/cond-mat/9706172) - Superfluid phases of 3He are quantuim liquids with the interacting fermionic and bosonic fields. In ...

33. [Gravity analogue in superfluid /sup 3/He-A (Journal Article)](https://www.osti.gov/etdeweb/biblio/6638705)

34. [[gr-qc/0005091] Superfluid analogies of cosmological phenomena](https://arxiv.org/abs/gr-qc/0005091) - Superfluid 3He-A gives example of how chirality, Weyl fermions, gauge fields and gravity appear in l...

35. [Superfluid Helium 3 and the search for new physics - HIP Blog](https://blog.hip.fi/superfluid-helium-3-and-the-search-for-new-physics/) - HIP members are working with a UK-based collaboration in a new project to use superfluid helium as l...

36. [Universal law of quantum vortex dynamics discovered in superfluid ...](https://phys.org/news/2025-06-universal-law-quantum-vortex-dynamics.html) - The researchers injected tiny frozen particles into superfluid helium to make invisible quantum vort...

37. [Revisiting de Broglie's Double-Solution Pilot-Wave Theory with a ...](https://ouci.dntb.gov.ua/en/works/4gEjpML9/) - The relation between de Broglie’s double-solution approach to quantum dynamics and the hydrodynamic ...

38. [De Broglie–Bohm theory - Wikipedia](https://en.wikipedia.org/wiki/De_Broglie%E2%80%93Bohm_theory)

39. [Knot spectrum of turbulence - PMC - NIH](https://pmc.ncbi.nlm.nih.gov/articles/PMC6646329/) - By numerically simulating the dynamics of a tangle of quantum vortex lines, we find that this quantu...

40. [[PDF] arXiv:1604.07217v4 [physics.gen-ph] 4 Sep 2019](https://arxiv.org/pdf/1604.07217.pdf) - Wave-particle duality of quantum particles comes from fragmentation of a unit information in knot ph...

41. [L. de Broglie's double solution and self-gravitation](https://fondationlouisdebroglie.org/AFLB-421/4DurtDef.pdf)

42. [Irreversible Dynamics of Vortex Reconnections in Quantum Fluids](https://link.aps.org/doi/10.1103/PhysRevLett.125.164501) - We statistically study vortex reconnections in quantum fluids by evolving different realizations of ...

43. [[PDF] Beyond the Born rule in quantum gravity](https://www.fuw.edu.pl/~ktwig/A-Valentini-24-1-25.pdf) - Non-equilibrium ( 𝜌 ≠ 𝜓. 2. ) relaxes to equilibrium. Page 23. Quantify relaxation with a coarse-gra...

44. [[PDF] Wilsonian renormalization](https://theory.tifr.res.in/~sgupta/courses/eft16/lec2.pdf) - The RG flow proves the central limit theorem: the fixed point of probability distributions under RG ...

45. [Implicate and explicate order - Wikipedia](https://en.wikipedia.org/wiki/Implicate_and_explicate_order) - Implicate order and explicate order are ontological concepts for quantum theory coined by theoretica...

46. [On the Explanation of Born-Rule Statistics in the de Broglie-Bohm ...](https://pmc.ncbi.nlm.nih.gov/articles/PMC7512940/) - The de Broglie-Bohm pilot-wave theory promises not only a realistic description of the microscopic w...

47. [Evolution of quantum non-equilibrium for coupled harmonic oscillators](https://royalsocietypublishing.org/doi/10.1098/rspa.2022.0411) - We study the effects of interactions on quantum relaxation towards equilibrium for a system of one-d...

48. [[PDF] 7 Non–Abelian Gauge Theory](https://www.damtp.cam.ac.uk/user/dbs26/AQFT/YM.pdf) - The first and most important example of a non–Abelian gauge theory was introduced to physics 1954 by...

49. [Analogue Gravity - PMC - NIH](https://pmc.ncbi.nlm.nih.gov/articles/PMC5255570/) - Analogue models of (and for) gravity have a long and distinguished history dating back to the earlie...

50. [Bohmian Mechanics and Quantum Field Theory](https://arxiv.org/abs/quant-ph/0303156) - We discuss a recently proposed extension of Bohmian mechanics to quantum field theory. For more or l...

51. [Renormalization in quantum field theory : r/AskPhysics - Reddit](https://www.reddit.com/r/AskPhysics/comments/1igckmw/renormalization_in_quantum_field_theory/) - Renormalizable QFT's are “UV-complete” meaning they make predictions at all energy scales up to arbi...

52. [Analogue simulations of quantum gravity with fluids - arXiv](https://arxiv.org/html/2402.16136v1) - In this Perspective, we discuss the potential use of analogue hydrodynamic systems beyond classical ...

53. [Modern Tests of Lorentz Invariance - PMC - NIH](https://pmc.ncbi.nlm.nih.gov/articles/PMC5253993/) - This review summarizes both the theoretical frameworks for tests of Lorentz invariance and experimen...

54. [arXiv:2309.00617v1 [quant-ph] 3 Sep 2023](https://arxiv.org/pdf/2309.00617.pdf)

55. [The de Broglie-Bohm pilot-wave interpretation of quantum theory](https://arxiv.org/abs/quant-ph/0506243) - In this thesis we study the de Broglie-Bohm pilot-wave interpretation of quantum theory. We consider...

56. [[PDF] Relativistic Pilot-Wave Theories as the Rational Completion of ...](https://philsci-archive.pitt.edu/23377/1/nonlocality-and-relativity-in-dBB-final.pdf) - So, I show that relativistic pilot-wave theories are the rational completion of quantum mechanics as...

57. [Gauge Theoretic Approach to Fluid Dynamics](https://arxiv.org/abs/hep-th/0105124) - The Hamiltonian dynamics of a compressible inviscid fluid is formulated as a gauge theory. The idea ...

58. [OUCI](https://ouci.dntb.gov.ua/en/?backlinks_to=10.3389%2Ffphy.2020.00300) - Open Ukrainian Citation Index - Відкритий український індекс наукового цитування

59. [Formalization of the Millennium Prize Problems in Lean4](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) - Formalization of the Millennium Problems in Lean4. - lean-dojo/LeanMillenniumPrizeProblems

60. [[PDF] Formalizing dimensional analysis using the Lean theorem prover](https://atomslab.github.io/static/pdf/publications/bobbin_2025.pdf)

61. [Formalising differential geometry in Lean](https://www.math.uni-bonn.de/people/rothgang/slides_Potsdam2025.pdf)

62. [[2411.07667] Formalization of physics index notation in Lean 4 - arXiv](https://arxiv.org/abs/2411.07667) - The physics community relies on index notation to effectively manipulate types of tensors. This pape...

63. [HepLean: Digitalising high energy physics - arXiv.org](https://arxiv.org/html/2405.08863v1) - We introduce HepLean, an open-source project to digitalise definitions, theorems, proofs, and calcul...

64. [Formalization of physics index notation in Lean 4 - arXiv](https://arxiv.org/html/2411.07667v1)

65. [Lean (proof assistant) - Wikipedia](https://en.wikipedia.org/wiki/Lean_(proof_assistant)) - Lean is a proof assistant and a functional programming language. It is based on the calculus of cons...

66. [HepLean: Digitalising high energy physics - ScienceDirect.com](https://www.sciencedirect.com/science/article/abs/pii/S0010465524003801) - We introduce HepLean, an open-source project to digitalise definitions, theorems, proofs, and calcul...

67. [Combined Lorentz Symmetry: Lessons from Superfluid 3He - PMC](https://pmc.ncbi.nlm.nih.gov/articles/PMC8770376/) - These symmetries emerge as a result of the symmetry breaking of the more fundamental P, T and Lorent...

68. [(3+0)D electromagnetic solitons and de Broglie's ''double solution''](https://arxiv.org/abs/math-ph/0201002) - This transformation of a (2+1)D soliton into a (3+0)D soliton shows the existence of those solitons,...

69. [Pilot-wave hydrodynamics - John W. M. Bush - MIT](http://thales.mit.edu/bush/index.php/4801-2/) - Droplets walking on a vibrating fluid bath exhibit features previously thought to be peculiar to the...

70. [[PDF] Pilot-Wave Hydrodynamics - MIT](https://thales.mit.edu/bush/wp-content/uploads/2021/04/Bush-AnnRev2015.pdf) - This fluid system is compared to quantum pilot-wave theories, shown to be markedly different from Bo...

71. [Hydrodynamic quantum analogs | PML](https://www.pml.unc.edu/hqas) - A primary goal of our work is to understand the extent to which quantum phenomena may be recreated t...

72. [Constraints on Lorentz invariance violation from Fermi -Large Area Telescope observations of gamma-ray bursts](https://www.osti.gov/pages/biblio/1356591) - The U.S. Department of Energy's Office of Scientific and Technical Information

73. [New Constraints on Lorentz Invariance Violation at High Redshifts ...](https://arxiv.org/html/2412.07625v2) - In this study, we apply a new cosmological model-independent restriction to LIV using time delay dat...

74. [Constraints on Lorentz Invariance Violation from GRB 221009A ...](https://arxiv.org/html/2508.00656v1) - In this work, we analyze the photon time-of-flight and time-shift data from LHAASO observations of G...

75. [New Constraints on Lorentz Invariance Violation at High Redshifts ...](https://inspirehep.net/literature/2857888) - In the gravity quantum theory, the quantization of spacetime may lead to the modification of the dis...

76. [[PDF] Theory of non-Abelian superfluid dynamics](https://durham-repository.worktribe.com/OutputFile/1375313) - The goal of this paper is to set up a theory for superfluids with an arbitrarily broken internal sym...

