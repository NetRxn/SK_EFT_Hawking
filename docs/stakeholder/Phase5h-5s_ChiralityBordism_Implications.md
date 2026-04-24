# Phase 5h/5j/5n/5q/5r/5s: Chirality Wall 3+1D + Bordism Discharge — Implications

*Last updated: 2026-04-24-1515.*

**Classification:** Research overview — for technical and non-technical stakeholders.
**Prerequisites:** `Phase5a_Implications.md` (1+1D chirality-wall three-pillar formalization), `Phase5b_Implications.md` (modular generation constraint).

---

## What We Achieved

This arc extends two previously established chains rather than opening a new headline programme. It carries the **chirality-wall** three-pillar analysis from the 1+1D setting handled in Phase 5a into 3+1D and into the first 2+1D gapping witness; and it discharges the **algebraic core** of the spin-bordism step in the Phase 5b modular generation constraint, replacing one opaque topological hypothesis with a machine-checked Ext computation plus three clean, independently verifiable textbook inputs. The work strengthens two existing results — it does not replace them.

---

## Key Results

1. **Phase 5h — 3+1D gapping obstruction** (`SPTClassification.lean` + `GaugingStep.lean`, 34 theorems in `GaugingStep.lean` plus the SPT module).
   SPT type infrastructure (`SPTPhaseData`, `FreeFermionSPT`, `CommutingProjectorSPT`, `InterfaceData`), non-on-site symmetry structure with GT Model 1 (non-compact U(1)) and Model 2 (Onsager), SMG phase data (BCH and HW instances), the Golterman–Shamir propagator-zero obstruction, and a comprehensive `ChiralityWall3DStatus` summary. The `gapped_interface_axiom` is the project's single remaining load-bearing axiom, registered in `AXIOM_METADATA` with eliminability tier "hard"; conditional theorems (`anomaly_free_implies_chiral_gauge`, `sm_three_gen_gapped_interface`, `no_gap_implies_anomalous`) derive from it and the rigorous contrapositive direction is proved without it.

2. **Phase 5j — Emergent gauge groups from Fermi points** (`FermiPointTopology.lean`, 33 theorems).
   First Volovik–Zubkov Fermi-point → emergent-gauge-group formalization. Explicit `RigorLevel` tracking (`theorem` / `heuristic` / `speculative`, with decidable equality) per step of the emergence chain: |N|=1 → U(1) (through step 2) at theorem level, |N|=2 → SU(2) through step 2 with subsequent steps flagged heuristic/speculative, and |N|=3 → SU(3) proved *more speculative than SU(2)*. Mechanism A (single |N|=2 node, yields anisotropic Hořava fermions, **not** SU(N)) is formally distinguished from Mechanism B (correlated |N|=1 nodes), correcting a literature conflation. Bridge theorems connect to `EmergentGravityBounds`, `GaugingStep`, and `SPTClassification`.

3. **Phase 5n — Anomaly inflow + Villain + disentangler + stacking** (`KMatrixAnomaly.lean`, `VillainHamiltonian.lean`, `TPFDisentangler.lean`, `SPTStacking.lean`).
   First Villain Hamiltonian formalization in any proof assistant. Wave 1 machine-checks the 1+1D 3450-model gappability master theorem: K-matrix `K = diag(1,1,−1,−1)` (det = 1, trace = 0, all `native_decide`); null vectors Λ₁ = (3,4,5,0) and Λ₂ = (4,−3,0,5) each satisfying ΛᵢᵀKΛᵢ = 0; mutual locality Λ₁ᵀKΛ₂ = 0; and the combined gappability criterion (det = 1 ∧ null vectors ∧ mutual locality). `TPFDisentangler` captures disentangler properties (constant depth, infinite-dim rotor requirement); `SPTStacking` formalizes anomaly additivity mod 16.

4. **Phase 5q — First Ext computation over a Steenrod sub-algebra** (`A1Ring.lean`, `A1Resolution.lean`, `A1Ext.lean`, `ExtBordismBridge.lean`).
   First machine-checked Ext^n_{A(1)}(F₂, F₂) computation over any Steenrod sub-algebra in any proof assistant. A(1) as a proper Lean `Ring` (newtype over `Fin 8 → ZMod 2`, convolution from the 512-entry structure table); explicit minimal free resolution of F₂ over A(1) through degree 5 with bidiagonal differentials; d² = 0 at every level via `native_decide`; exactness by RREF witness transformation matrices P, P⁻¹ (cross-validated externally in SageMath); minimality; and Ext dimensions **1, 2, 2, 2, 3, 4** for n = 0..5. `ExtBordismBridge.lean` decomposes the previously opaque spin-bordism input into four focused topological hypotheses (H1 ko-cohomology factorization, H2 change-of-rings, H3 ASS collapse, H4 Anderson–Brown–Peterson splitting), replacing one monolithic claim with strictly smaller inputs.

5. **Phase 5r — Change-of-rings discharge** (`ChangeOfRings.lean`).
   First change-of-rings discharge of the topological hypothesis H2 (`Ext_A ≅ Ext_{A(1)}`) via Hom-tensor adjunction — pure algebra, no topology required. Achieved via the abstract adjunction rather than the originally planned low-degree Steenrod-algebra-enumeration (Waves 1–2 bypassed), removing H2 from the load-bearing set. Three topological hypotheses (H1, H3, H4) remain.

6. **Phase 5s — 2+1D gapping witness, general modularity, instanton counting** (`FKGappedInterface.lean`, `ModularityTheorem.lean`, `InstantonZeroModes.lean` with 9 theorems).
   First Fidkowski–Kitaev 2+1D Cayley-calibrated gapped-interface construction in any proof assistant: explicit 16×16 integer Hamiltonian, ground-state energy **E₀ = −14**, unique ground state, spectral gap **Δ = 14**, symmetry commutators `[H, T] = [H, (−1)^F] = 0`, all checked by `native_decide`. Bridge theorem `gapped_interface_dimensional_ladder` (in `SPTClassification.lean`) bundles the 1+1D Villain witness and the 2+1D FK witness as *distinct-framework* evidence (K-matrix vs Cayley calibration), strengthening the axiom's evidence tier from "1D only" to "1D + 2D in different mathematical settings." `ModularityTheorem.lean` proves the general statement `det(S) ≠ 0 → Z₂ trivial` as pure linear algebra (no MTC-specific input), replacing three case-by-case `native_decide` proofs with one abstract theorem. `InstantonZeroModes.lean` machine-checks zero-mode counting for the Csáki et al. instanton mechanism by bypassing the 4D index theorem entirely: Clifford algebra isomorphism Cl(4) ≅ Cl(2) ⊗̂ Cl(2) separates variables, a 2D angular count (6×6 diagonal ℤ matrix) plus polynomial-space dimension gives 2|qn| = 4 zero modes per flavor → 16 total for N_f = 4 → the 8-fermion ADW vertex.

---

## Why This Matters

### For Condensed Matter Physics

The chirality-wall debate between the Thorngren–Preskill–Fidkowski (PRL 136, 2026) construction and the Golterman–Shamir no-go is the most actively contested frontier in lattice QFT, with independent supporting work from Butt–Catterall–Hasenfratz (PRL 2025, SMG numerical evidence) and from Fidkowski–Kitaev (8-Majorana gapping). Our formal analysis is the only machine-checked contribution to that debate. Phase 5h formalizes the 3+1D gauging obstruction as executable Lean content (non-on-site symmetry, SMG phase data, Golterman–Shamir propagator-zero); Phase 5n formalizes the 1+1D proof-of-concept side (Villain Hamiltonian, 3450 K-matrix gappability via null-vector plus mutual-locality); Phase 5s supplies a 2+1D witness in an entirely different mathematical framework (Cayley-calibrated FK, integer 16×16 Hamiltonian with spectral gap Δ = 14). The conjecture does not fall here — but its evidence base is now structured, machine-checked, and explicitly flagged as "strong in 1D, proved in 2D, axiomatized in 3D."

### For Topology / Algebraic Geometry

The Ext computation in Phase 5q is — to our knowledge — the first concrete Ext group of any sub-Steenrod-algebra computed inside a proof assistant. Mathlib's homological-algebra pipeline is entirely `noncomputable`; the path taken here was a brute-force `native_decide` resolution plus external SageMath cross-validation plus RREF witness matrices for exactness. Phase 5r then closes the change-of-rings step (H2) by a Hom-tensor-adjunction argument that sidesteps the originally planned low-degree enumeration. What remains as *hypotheses* — H1 (H*(ko; F₂) ≅ A ⊗_{A(1)} F₂, Adams 1974), H3 (Adams spectral sequence collapse at E₂ for ko, via Bott periodicity), H4 (Anderson–Brown–Peterson splitting, ABP 1967) — is classical textbook topology, each independently verifiable by a working topologist; discharging them in Lean would require spectrum theory and algebraic-topology infrastructure that no proof assistant currently supports. H3 in particular is assessed as *irreducibly* topological: the potential differential d₃(h₁²) → v can only be ruled out by knowing π_*(ko).

### For Emergent Gravity

Phase 5j brings a second, non-perturbative route to emergent gauge structure into the machine-checked layer. The Wen-ADW route was shown in Phase 5f to be perturbatively closed (G_Wen ≈ 0.0006 vs. G_c ≈ 4.0, about 6000× too weak) and to face a spin-connection gap with no known bridge. The Volovik–Zubkov |N| = 2 → SU(2) mechanism, **if** the speculative steps hold, would produce a matrix-valued vierbein and therefore a spin connection — potentially bypassing that gap. Our formalization is deliberate about what is and is not established: of six steps in the emergence chain, three are theorem-level, two heuristic, one speculative; SU(3) is formally proved *more speculative* than SU(2); Mechanism A (which does *not* produce non-Abelian gauge structure) is formally separated from Mechanism B (which does, at heuristic level). A residual chirality problem remains (Fermi-point coupling is vector, not chiral), independent of the coupling deficit.

---

## What's Next

- **H1, H3, H4 remain open.** These three topological hypotheses are outside what Lean can currently support (no algebraic-topology / spectrum-theory infrastructure in Mathlib). They are standard textbook results and independently verifiable, but their formalization would require foundational Mathlib work on the order of 15–25 person-years.
- **`gapped_interface_axiom` stays as the project's single load-bearing axiom.** Eliminability: hard. The 1+1D + 2+1D evidence ladder strengthens it but does not close it; no 3+1D or 4+1D proof is currently achievable with known techniques, and numerical verification at 4+1D is beyond lattice-scale reach.
- **Phase 6 deferred targets** include the non-Abelian TPF disentangler track, completion of the gauging step (promoting non-on-site chiral symmetry to a dynamical gauge field — open problem, Misumi instability as a known risk), and the Fermi-point chirality problem.
- **Aristotle submissions.** Any residual sorry gaps in the category-theoretic bookkeeping for `CenterFunctorZ2Equiv` (not part of the chirality or bordism load-bearing chains) remain Aristotle-eligible and are tracked separately in `Phase5s_Roadmap.md` Wave 9.
- **Paper updates.** Paper 7 (chirality formal) and Paper 8 (chirality master) absorb the 3+1D + 2+1D results. Paper 10 (modular generation constraint) now cites the machine-checked Ext computation and the H2 discharge in place of the earlier opaque bordism reference.
