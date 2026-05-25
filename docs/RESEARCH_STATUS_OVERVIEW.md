# SK-EFT Hawking: Research Status Overview

**Purpose:** Plain-language, rigorous assessment of all proven chains, their implications, gaps, and strategic situation. Written for the principal investigator and future collaborators.

**Last updated:** 2026-05-25 (Phase 6q strengthening close + B.1/B.2/B.3 substantive lifts + adversarial-review remediation)

**Prior update:** 2026-05-07 (Phase 6e–6o + Phase 7 bundle architecture sync)

**Current build:** **390 Lean modules, 7,339 theorems** (7,314 substantive + 25 placeholder), **0 axioms project-wide** (`gapped_interface_axiom` was refactored to tracked-Prop `TPFConjecture` on 2026-05-19 in Phase 5h Wave 1, eliminating the project's last load-bearing axiom), **0 sorry project-wide**. 131 Python modules across 19+ sub-packages (Phase 6q added `dkm_bootstrap/` for the CHHK MIR-bound numerical companion, alongside `bh_thermodynamics/`, `bbn/`, `strong_cp_de/`, `equivalence_principle/`, `qec_holography/`, `center_symmetry/`, `chiral_ssb/`, `cfl/`, `gravitational_waves/`, `dark_sector/`, `graphene/`, `fermi_hubbard/`, `adw/`, `wkb/`, `vestigial/`, `chirality/`, `fracton/`, `experimental/`, `resurgence/`, and others). 101 test files (4,220 pytest cases — 4,152 default-run + 68 slow-deselected; fast-pass in ~3 s + slow-marked extras), 156 figures, 89 notebooks, 42 paper drafts (none submitted). 322 theorems Aristotle-proved across 44 runs (no Aristotle calls in Phase 6 — all interactive-MCP closure). **Synced 2026-05-25** — counts refreshed from `docs/counts.json` (2026-05-25T08:12). Phase 6q DKM transport bootstrap added 11 new Lean modules under `lean/SKEFTHawking/DKMBootstrap/` (~2,716 LoC) + the Python companion at `src/dkm_bootstrap/` shipping the substantive graphene MIR constant `(2·β_2/(4π))^(1/3) ≈ 0.0756`; Stage-13 adversarial review surfaced and resolved 20 findings (1 BLOCKER + 12 REQUIRED + 7 RECOMMENDED).

The **`gaussianSaddleAsymptotic` axiom was retired** in Phase 6a Wave 7 via a project-local Laplace-method derivation (`LaplaceMethod.lean`), bringing the axiom count from 2 → 1. **Default test-suite runtime dropped from 9 m 26 s to 2.14 s (264× speedup)** with the introduction of a `slow` pytest marker that defers the three Lean-walking suites (`test_extract_lean_deps`, `test_build_graph`, `test_graph_integrity`) to opt-in runs (`-m ''`). The seven Phase 6 papers (paper29, paper32, paper34, paper35, paper36, paper37, paper38, note_rt_ch_bounds) now drive their abstract / formalization-section counts entirely through `\input{counts.tex}` macros, eliminating count-literal drift permanently for those papers.

Representative formal-verification firsts across the library — each phase has delivered at least one — include the `N_f ≡ 0 mod 3` generation constraint with machine-checked Ext^n_{A(1)}(F₂, F₂) computation, the first quantum group (U_q(sl₂)) and Hopf algebra in any proof assistant, the first rank-2 quantum group (U_q(sl₃)) and SU(3)_k fusion, the first parameterized `QuantumGroup k A` over arbitrary Cartan matrices with Kac–Walton fusion, the first complete braided modular tensor category (Ising) and verified knot invariants (trefoil = −1, figure-eight), the first Temperley–Lieb / Jones–Wenzl / WRT pipeline, the first Muger center and general dual-closure theorem, the first Fidkowski–Kitaev 2+1D Cayley-calibrated gapped-interface construction, the first Volovik–Zubkov Fermi-point → emergent-gauge formalization, the first Gibbs–Duhem emergent-vacuum obstruction theorem, the first closed-form vestigial-gravity EOS, the first formally verified Fermi-Hubbard geometric SWAP / Berry-phase theorem, the **first machine-checked four laws of black-hole mechanics partitioned across Schwarzschild and ADW-extremality regimes**, the **first formalization of the four energy conditions (WEC/NEC/DEC/SEC)** in any proof assistant per Phase 6f audit §3E, and the **first formalization of the CFL emergent-ℤ₃ ≡ QCD-center-ℤ₃ generator-level identification** (Hirono–Tanizaki).

---

## How to Read This Document

The project asks: **Can the mathematical structures of exotic matter also describe fundamental physics, and where does that idea break down?**

Ten proof chains address different aspects of this question. Chains 1–6 are the original programmes — dissipative Hawking radiation, the generation constraint, Onsager → quantum groups → MTC → TQFT → Fibonacci universality, the chirality wall, ADW emergent gravity, and Monte-Carlo vestigial gravity. Chains 7–9 — the Fermi-Hubbard doublon geometric gate, the graphene Dirac-fluid Hawking platform, and dark-sector connections — sit alongside them as peers rather than as extensions. Chain 10 is the **Phase 6 cosmology / strong-coupling / horizon-thermodynamics push** (Phases 6a / 6b / 6c / 6d / 6f), in which the SK-EFT + ADW + vestigial-gravity machinery is exercised against published constraints from BBN, the strong-CP problem, the equivalence principle, holographic-QEC structural bounds, RT / Casini–Huerta entanglement bounds, confinement / chiral-symmetry-breaking / CFL color-flavor-locking, gravitational-wave dispersion (GW170817), Bekenstein–Hawking entropy + four-laws thermodynamics, and the four energy conditions. Each chain is assessed for:
- **Solidity** — what is machine-checked vs. conjectured vs. open
- **Gaps** — what's missing and whether the gaps are technical or fundamental
- **Implications** — what follows if the chain holds or breaks

---

## Chain 1: Dissipative Hawking Radiation

**Status: SOLID. Fully machine-verified.**

**The chain:**
SK-EFT axioms (Crossley-Glorioso-Liu) → transport coefficient counting [count(N) = floor((N+1)/2)+1] → dissipative correction delta_diss = Gamma_H/kappa → frequency-dependent correction delta^(2)(omega) proportional to omega^3 → parity alternation at all EFT orders → CGL FDR derivation from first principles → exact WKB connection formula → modified Bogoliubov coefficients → observable Hawking spectrum with noise floor → platform-specific predictions (Steinhauer/Heidelberg/Trento/polariton)

**What's proved:**
- The counting formula tells you exactly how many free transport parameters appear at each EFT order. Proved for general N.
- The CGL fluctuation-dissipation relation pairs noise with odd-frequency dissipative terms. The sign is unique — Aristotle found explicit counterexamples disproving alternatives (negation proofs).
- The parity alternation theorem: even-order corrections require broken spatial parity (background flow), odd-order exist universally. Structural prediction, not parameter-dependent.
- The exact WKB connection formula reveals three non-perturbative effects beyond the perturbative EFT: (1) broken unitarity |alpha|^2 - |beta|^2 < 1 via the decoherence parameter delta_k = 2*Gamma_H/kappa, (2) an FDR-mandated noise floor n_noise = delta_k/2, and (3) a spectral floor where noise dominates Hawking radiation above ~6*T_H.
- The positivity constraint forces gamma_{2,1} + gamma_{2,2} = 0 at second order — a non-trivial consequence of unitarity.
- KMS optimality: the first-order constraint is the strongest possible (positivity if and only if both noise coefficients non-negative).
- Polariton platforms are ~10^10 x hotter than BEC systems. Tier 1 predictions computed with regime classification by cavity lifetime.

**Phase 5w extension (April 2026): Graphene Dirac fluid.**
The entire 1+1D BEC chain has been extended to the 2+1D graphene Dirac fluid — a natively relativistic system where the Dean group at Columbia demonstrated the first electronic sonic horizon (Geurs et al. 2509.16321, Sept 2025). Key results:
- 3×3 acoustic metric block-diagonalizes for quasi-1D flow → existing 1+1D WKB machinery applies directly (92% Lean theorem reuse)
- Predicted T_H ≈ 2.4 K for Dean bilayer nozzle (10⁹× BEC)
- Dissipative correction δ_diss ~ 10⁻¹³ is negligible (11 orders below dispersive δ_disp ~ -3%)
- Transport counting in 2+1D: 2 first-order (conformal), ~9 second-order (vs 2 in BEC)
- Wiedemann-Franz violation L/L₀ > 200× from two-channel transport
- Detection: current noise S_I(ω) in 0.5-85 GHz, bandwidth-cumulative SNR=1 in ~1 min
- Lean: DiracFluidMetric (9 thms) + GrapheneHawking (6 thms) + DiracFluidSK (9 thms) = 24 new, 0 sorry
- Paper 16 drafted, reviewed by 3 independent Opus agents (claims + figures + adversarial)

**What's missing:**
- Experimental verification (BEC/polariton). The Paris polariton group (Falque et al.) has observed negative-energy partner modes; spontaneous Hawking radiation detection is plausible within 1-2 years.
- Experimental verification (graphene). The Dean group has the sonic horizon; the Kim group (Harvard) has the noise thermometer. Neither has attempted Hawking detection. Collaboration outreach to Lucas/Dean can now proceed — noise formula is derived.
- The graphene noise formula ΔS_I(ω) = 2ℏω σ_Q Γ(ω) n_H(ω) is derived from first principles (Keldysh FDT + Landauer-Büttiker, Wave 10a COMPLETE). Principal remaining uncertainty: the device-specific greybody factor Γ(ω).
- Paper submission. Papers 1 (PRL), 2 (PRD), 4 (PRD) cover BEC; Paper 12 covers polariton; Paper 16 (new) covers graphene. None submitted.

**Key insight discovered during formalization:** The original KMS symmetry axiom was too weak (only constrained 4/9 action components). Aristotle found a counterexample. The corrected FirstOrderKMS constrains all 9 components. This is a concrete case of formal verification catching a physics error.

**Key insight from Phase 5w:** For graphene, dissipative corrections to T_H are negligible by 11 orders of magnitude. The SK-EFT framework's value is the systematic organization (transport counting, FDR constraints, formal verification), not the quantitative shift in T_H. This is an honest finding — the framework is right, but the correction it computes is irrelevant for this platform. The dispersive correction (-3%) is the dominant physical effect.

**Implication:** The SK-EFT framework is the correct language for dissipative analog gravity. If polariton experiments confirm the spectral predictions, this validates the EFT methodology for all emergent geometries. The graphene extension opens a new experimental frontier with T_H nine orders of magnitude above BEC and a realized sonic horizon. If the noise spectrum prediction is confirmed, it would be the first observation of analog Hawking radiation in an electronic system.

---

## Chain 2: The Generation Constraint and "16 Convergence"

**Status: SOLID. Fully machine-verified, zero axioms (all discharged).**

**The chain:**
SM fermion content (16 Weyl per generation) → Z_4 charges X = 5(B-L) - 4Y → all charges odd → anomaly index: 16 = 0 mod 16 (with nu_R) / 15 = -1 mod 16 (without nu_R) → chiral central charge c_- = 8*N_f → modular invariance requires 24 | c_- → **N_f = 0 mod 3** → minimal N_f = 3

**What's proved:**
- The Standard Model's 16 Weyl fermions per generation contribute an anomaly index of exactly 16 in the Z_16 classification. With a right-handed neutrino: 16 = 0 mod 16 (anomaly-free). Without: 15 = -1 mod 16 (anomalous). Three generations without nu_R: 3 * (-1) = -3 mod 16, forcing hidden sectors.
- The modular invariance constraint from the Dedekind eta function requires c_- = 0 mod 24. Combined with c_- = 8*N_f, this forces N_f = 0 mod 3. The smallest nontrivial solution is 3 — what nature chose. N_f = 1, 2 are proved impossible. N_f = 6 is the next allowed value.
- Right-handed neutrino argument: without nu_R, c_- = 15/2 per generation (fractional), which is a gravitational anomaly independent of mass-based arguments.
- All 3 originally-planned axioms either discharged to theorems (tautological as Lean statements) or removed (one was mathematically false — Aristotle disproved it).

**The "16 convergence":**
The number 16 appears independently in: (1) particle physics (16 Weyl per generation), (2) anomaly theory (Z_16 classification), (3) 4D topology (Rokhlin's theorem, sigma divisible by 16 for spin 4-manifolds), (4) condensed matter (Kitaev periodic table, class DIII period 16).

All four are proved to originate from the quaternionic structure of spinors in 4D. The separation between algebra (mod 8 from Serre's theorem, fully proved) and topology (the extra factor of 2 from smooth structure, axiomatized) is cleanly formalized. E8 with signature 8 concretely witnesses that algebra alone cannot reach 16 — the jump from 8 to 16 requires genuinely topological input.

**What's been machine-checked (Phase 5q, April 8 2026):**
- The algebraic core of the spin bordism computation: the minimal free resolution of F_2 over A(1) through degree 5, verified end-to-end via native_decide. d^2=0 at all levels, exactness via kernel enumeration (d1-d3) and RREF witnesses (d4-d5), minimality, Ext dimensions 1, 2, 2, 2, 3, 4. Zero sorry, zero Python trust. First machine-checked Ext computation over any Steenrod subalgebra in any proof assistant.
- The change-of-rings isomorphism Ext_A ≅ Ext_{A(1)} (Phase 5r, ChangeOfRings.lean) — pure algebra via the Hom-tensor adjunction, no topology needed.
- Ext^4 has dimension 3 (not 16 — the "16" enters through the infinite h_0-tower in stem 4 assembling to Z via Adams spectral sequence extensions).

**What's missing:**
- 3 topological hypotheses connecting the machine-checked Ext computation to the actual bordism group:
  - H1: H*(ko; F_2) ≅ A tensor_{A(1)} F_2 (ko spectrum cohomology — Adams 1974, Ch. 16)
  - H3: Adams spectral sequence for ko collapses at E_2 (comparison with Bott periodicity — Ravenel 2003, Ch. 3). Assessed as irreducibly topological: the potential differential d_3(h_1^2) -> v can only be ruled out by knowing pi_*(ko).
  - H4: Anderson-Brown-Peterson splitting pi_n(MSpin) ≅ pi_n(ko) for n < 8 (ABP 1967). Circularity note: ABP historically used Rokhlin-equivalent facts, documented in HYPOTHESIS_REGISTRY.
- These are standard textbook results, each independently verifiable by a topologist. They cannot be discharged without formalizing spectrum theory and algebraic topology in Lean, which no proof assistant currently supports.

**Implication:** Three generations is not arbitrary. It is forced by the combination of the Standard Model's particle content and mathematical consistency (modular invariance). The algebraic content of the bordism computation — the reason the answer is 16 rather than 8 or 32 — is machine-checked. What remains as hypotheses is standard textbook topology, not cutting-edge mathematics. The generation constraint is the project's most surprising result, and its formal foundation is the strongest achievable without formalizing algebraic topology in Lean.

---

## Chain 3: Quantum Groups through Topological Quantum Computation

**Status: SOLID with technical gaps. Longest verified mathematical chain in any proof assistant.**

**The chain:**
Onsager algebra (Dolan-Grady, Davies isomorphism) → Inonu-Wigner contraction to su(2) → U_q(sl_2) [FIRST quantum group in any proof assistant] → Hopf algebra [FIRST in any proof assistant] → affine U_q(sl_2 hat) → restricted quotient u_q → SU(2)_k fusion rules at k=1,2,3 → S-matrix unitarity and Verlinde formula → Q(sqrt(2)), Q(sqrt(5)), Q(zeta_16), Q(zeta_5) number fields with decidable equality → F-symbols and R-matrices → hexagon equations → ribbon structure → Gauss sum → trefoil knot invariant = -1 [FIRST verified knot invariant] → figure-eight knot invariant → TQFT partition functions (Atiyah-Segal axioms) → WRT surgery invariants → Temperley-Lieb algebra → Jones-Wenzl idempotents → topological quantum computation gates (Ising = Clifford, Fibonacci = universal) → Fibonacci braiding universality (Lie algebra spanning proof)

Extended: U_q(sl_3) [FIRST rank-2 quantum group in any proof assistant] → SU(3)_k fusion (first in any proof assistant) → generic U_q(g) parameterized by Cartan matrix → Kac-Walton fusion algorithm

Recently completed (Phase 5p, April 8 2026):
- **MugerCenter.lean** — FIRST Muger center formalization in any proof assistant. Key results:
  - `dual_isTransparent` — **FIRST machine-checked proof of general dual closure** via hexagon decomposition + tensorLeftHomEquiv injectivity (~80 lines)
  - `tensor_isTransparent` — tensor product closure via hexagon axioms
  - `iso_isTransparent` — isomorphism invariance via braiding naturality
  - Ising, Fibonacci, and toric code Muger triviality verified computationally (native_decide)
  - Full modularity certificates: det(S) != 0 AND Z_2 = Vec for each MTC
- **FPDimension.lean** — Frobenius-Perron dimensions derived from fusion matrices as eigenvalues (not declared)

**What's solid:**
- The Ising MTC is COMPLETE in the strongest sense: fusion rules, F-symbols, R-matrix, twist, all 6 hexagon equations, all 4 ribbon conditions, Gauss sum, Muger triviality — every piece machine-checked over exact algebraic number fields.
- The Fibonacci MTC is complete through hexagon + twist + universality proof.
- Concrete first-evers: Hopf algebra, quantum group, MTC definition, braided fusion category, verified knot invariant, SU(3)_k fusion, generic U_q(g), Temperley-Lieb algebra, string-net formalization, Muger center — all first in any proof assistant.
- The chain from lattice integrable systems all the way to TQFT invariants and quantum computation gates is constructive.
- Fibonacci braiding is proved universal for quantum computation via Lie algebra spanning (commutator matrices generate su(2) for qubit, su(3) directions for qutrit).

**What's missing:**
- **3 active sorry remaining** (all in CenterFunctorZ2Equiv, Wave 9 research-grade gaps):
  - `halfBraiding_sq_identity` tmul case (line 1035) — graded hexagon summand
    extraction at (eAdd, aAdd, aAdd) of (X ⊗ U ⊗ U) eAdd. Mathematical content
    VERIFIED (g² = 𝟙 via h_key_eAdd manual trace); blocker is missing Mathlib
    API for navigating `ι ≫ abstract_morphism ≫ desc` chains.
  - `halfBraiding_sq_identity_a` tmul case (line 1442) — mirror of above.
  - `h_cf2_G2` (line 1955) — needs Full + EssSurj for canonicalCenterToRep
    (estimated 1500-2800 LOC, independent of the tmul blocker).
- Plus 1 FALSE-wrapped placeholder in TetradGapEquation (not a real axiom).
- **Wave 8 q-Serre track COMPLETE 2026-04-14**: Uqsl2AffineHopf + Uqsl3Hopf both
  0 sorry. First formalization of quantum group Hopf algebra compatibility in
  any proof assistant.
- Wave 9 H_CF1 ✓ discharged 2026-04-15 via `gradedTotalSpaceFunctor`.
- Wave 9 H_CF2 ~95% infrastructure complete; 3 active sorries + Full/EssSurj
  pending. Zero downstream dependencies (OPTIONAL per roadmap).
- See `Phase5s_Roadmap.md` for full wave-by-wave status and `working-docs/
  phase5s_wave9_option_b_helpers.md` for 38-session Wave 9 investigation log.
- The Kazhdan-Lusztig equivalence Rep(u_q) = SU(2)_k-MTC is stated but not constructively proved (the full proof is 200 pages). Data-level verification done for k=1,2.
- The S-matrix/Muger bridge theorem Direction 1 (det(S) ≠ 0 → Z₂ trivial) is now proved as a GENERAL theorem (ModularityTheorem.lean) — pure linear algebra, no MTC-specific properties needed. Direction 2 (Z₂ trivial → det(S) ≠ 0) requires Muger's categorical trace machinery and is not yet formalized.
- Generic Hopf algebra structure for U_q(g) (Wave 2 of Phase 5m) not yet built.
- The lean-tensor-categories library has been extracted (20 files, 114 theorems, 78 defs, zero sorry) but the Mathlib PR process has not started.

**Implication:** This is the only verified infrastructure connecting exactly solvable lattice models to topological quantum field theory and quantum computation. Direct relevance to the quantum computing industry: Microsoft Majorana hardware uses Ising anyons (our verified gates), Google surface codes correspond to toric code (our Vec_{Z/2} string-net), Fibonacci anyons are universal for quantum computation (our verified proof).

---

## Chain 4: The Chirality Wall

**Status: MOST CONTESTED. Rigorous formal analysis, three identified gaps.**

**Three pillars proved:**

**Pillar 1 (Negative — the no-go doesn't apply):** Golterman-Shamir no-go theorem formalized with all 9 conditions as substantive Lean Props. The TPF construction proved to violate 5 of those 9 conditions. Therefore the no-go's conclusion (chirality is forbidden on a lattice) does not follow for the TPF construction.

**Pillar 2 (Positive — chirality can be achieved):** Gioia-Thorngren construction: the central commutator [H_BdG(k), Q_A(k)] = 0 is proved — it reduces to sin^2 + cos^2 = 1 in tau-space. The chiral charge is non-on-site (range R=1) and non-compact (eigenvalues +/- cos(p_3/2)), evading both GS conditions. The Onsager algebra encodes the Witten anomaly on the lattice. Witten anomaly identified as element 8 in Z_16 (proved). 

**Pillar 3 (Algebraic — the 16 connects everything):** Z_16 classification axiomatized, 16-fold way for super-modular categories, A(1) Steenrod algebra formalized (first in any proof assistant). Central charge constraint strengthened from mod 8 (string-net result) to mod 16 (from Z_16).

**3+1D extension:** Gauging obstruction formalized (NotOnSiteSymmetry, SymmetryDisentangler, GT Models 1+2), SMG phase data for BCH and HW constructions, Golterman-Shamir propagator-zero obstruction documented. SPT classification with gapped interface as structured axiom.

**1+1D proof-of-concept:** 3450 model anomaly cancellation proved, Villain Hamiltonian formalized (first in any proof assistant), K-matrix formalism built, TPF disentangler properties verified.

**The three gaps:**
1. **4+1D gapped interface conjecture** — the project's ONLY axiom (`gapped_interface_axiom` in SPTClassification.lean, eliminability: hard). This is the single load-bearing assumption in the entire codebase that is not a standard textbook result. Assessment:
   - *Evidence for:* The 1+1D analog is proved (3450 model, formalized in VillainHamiltonian.lean). The **2+1D analog is proved** (Fidkowski-Kitaev 8-Majorana gapping, machine-checked in FKGappedInterface.lean — first FK formalization in any proof assistant, 16×16 integer Hamiltonian with ground-state energy E₀ = −14, spectral gap Δ = 14, unique ground state, fermion parity preserved). **Wave 4 bridge theorem `gapped_interface_dimensional_ladder` (SPTClassification.lean) bundles both witnesses formally**, strengthening the axiom from "1D evidence only" (TPF original) to "1D + 2D in distinct mathematical frameworks — K-matrix vs Cayley calibration" (this work). The TPF construction (PRL 136, 2026) is built on this conjecture. Anomaly matching arguments are consistent. Butt-Catterall-Hasenfratz (PRL 2025) SMG numerical evidence is supportive.
   - *Evidence against / risks:* No proof exists in 3+1D. No numerical evidence in 4+1D (lattice too large). Proving the spectral gap requires Yang-Mills-mass-gap-difficulty techniques. Misumi instability and Kapustin-Fidkowski no-go (finite-dim CP can't have nonzero Hall conductance) create known obstructions that the TPF construction circumvents via infinite-dimensional rotor spaces — but this makes the gap question harder.
   - *Blast radius if wrong:* Chirality wall analysis (Papers 7/8) would need revision. All other chains (generation constraint, Hawking radiation, quantum groups, emergent gravity) are completely independent — zero impact.
   - *Assessment:* Reasonable conjecture, backed by PRL-level research, but genuinely unproved and potentially unprovable with current techniques. Correctly rated as "hard" eliminability.
2. **The gauging step** — promoting non-on-site chiral symmetry to a dynamical gauge field. The Onsager algebra is non-compact; gauging non-compact lattice symmetries is an open problem. Misumi instability is a known risk.
3. **Full Z_16 cobordism** — 15-25 person-years to formalize. Algebraic layer done (A(1) Ext computation machine-checked in Phase 5q, mod 8 bound proved). Topological factor of 2 enters through 3 focused hypotheses (H1, H3, H4 — see Chain 2).

**Implication:** The chirality wall is cracking but not broken. The formal analysis demonstrates that the GS no-go theorem and the TPF construction operate in genuinely different mathematical frameworks. But three gaps remain between "the no-go doesn't apply" and "chirality is achievable." The gapped interface axiom is the single load-bearing assumption — if it falls, the chirality conclusion falls with it, but nothing else in the project is affected. This is the most actively contested frontier in lattice QFT, and this project's formal analysis is the only machine-checked contribution to the debate.

---

## Chain 5: Emergent Gravity

**Status: MIXED. Clear positive results, clear negative results, clear open questions.**

**What works:**
- ADW gap equation: nontrivial Lorentzian-signature solution exists for G > G_c = 8*pi^2/(N_f*Lambda^2). Two massless spin-2 graviton modes emerge as Nambu-Goldstone bosons of GL(4)/SO(3,1) breaking. Cross-validated: integral formulation matches Coleman-Weinberg V_eff exactly. G_c formally unchanged at NLO (two-loop analysis). IVT existence and bifurcation at G_c machine-proved. Aristotle disproved the boundedness conjecture (found explicit counterexample: the gap solution is unbounded in G).
- The tetrad gap equation had never been explicitly written down in the published literature. This project identified it from the NJL-ADW structural correspondence.

**What definitively fails:**
- Perturbative Wen-ADW coupling: G_Wen approximately 0.0006 vs G_c approximately 4.0 — ~6000x too weak. The perturbative route from Wen's emergent QED to ADW tetrad condensation is closed.
- Non-Abelian fracton obstruction: fracton gauge symmetries are too rigid for the nonlinearities of Einstein's equations. Machine-proved negative result.
- Gauge erasure: only U(1)_EM survives passage through a fluid layer. SU(2) and SU(3) produce domain walls, not Goldstone modes. Universal structural theorem, machine-proved. Implication: non-Abelian gauge forces cannot emerge from fluid dynamics but CAN originate from topological order (via the quantum group route in Chain 3).

**What's open:**
- Abelian instantons (Csaki et al. 2024) generate unsuppressed 8-fermion vertices for N_f=4 — a non-perturbative mechanism that could bridge the coupling deficit. **Zero-mode counting NOW MACHINE-CHECKED** (InstantonZeroModes.lean, 9 theorems): the 4D index theorem is entirely bypassed via separation of variables (Clifford Cl(4) ≅ Cl(2) ⊗̂ Cl(2)) + 2D angular counting (6×6 diagonal ℤ matrix) + polynomial space dimension. Result: 2|qn| = 4 zero modes per flavor → 16 total for N_f=4 → 8-fermion ADW vertex. Previously RED, now GREEN. The O(1) amplitude (Schwinger model exact) remains physics, but the combinatorial input is machine-checked.
- Volovik's vestigial gravity (metric without tetrad): mean-field confirms the vestigial window, MC pending (L=8 RHMC running, matrix-free stencil unlocks L=12+).
- Fermi-point |N|=2 gauge emergence: formalized with explicit rigor tracking (theorem/heuristic/speculative per step). Theorem-level through step 2 only. SU(3) more speculative than SU(2) (proved). Could bypass the spin-connection gap but introduces its own unsolved chirality problem (vector coupling, not chiral).
- The spin-connection gap (U(1) to SO(3,1)) has no known path. This is the true showstopper for the Wen-ADW route.

**Implication:** Emergent gravity has a clear structural map. The perturbative route is dead. Three alternative routes remain: non-perturbative instantons, vestigial gravity, and Fermi-point topology. The gauge erasure result is a clean selection rule: which forces can emerge from where.

**Phase 6e extensions (May 2026): nonlinear emergent EFE through Einstein–Cartan torsion.** Six waves push beyond the linearized result of Phase 6a Wave 1 to a calibrated nonlinear emergent-gravity stack:
- **W1 — Heat-kernel calibration (paper39):** computes Christensen–Duff Dirac heat-kernel coefficients `a₀`, `a₂`, `a₄` to identify Sakharov–Adler `G_N^Sak ↔ G_N^emerg` matching locus and the Planck-anchor reduction. (See `docs/roadmaps/Phase6e_Roadmap.md` and `PAPER_DRAFT_MAPPING.md` row.)
- **W2 — Higher-curvature Stelle structure (paper40):** Stelle (α, β, γ) closed form at order `a₄`; observational ceiling check against published higher-curvature bounds.
- **W3 — Nonlinear diff invariance (paper41):** Decision Gate E.3 path-(b) — invariance of the emergent action through `a₄`.
- **W4 — Variational nonlinear EFE + multi-channel PPN (paper42):** trace-level emergent EFE with emergent-vs-matter `T_μν` decomposition; multi-channel PPN signatures.
- **W5 — Cosmological constant in emergent form (paper42b):** Decision Gate E.4 — `Λ^emerg` microscopic prediction; reproduces the magnitude side of the CC problem (heat-kernel `a₀` does not produce `Λ_obs` naturally — D5 cross-bridge documents this as an explicit non-prediction of the emergent route, *not* as a dark-energy mechanism).
- **W6 — Einstein–Cartan torsion (paper43):** EC torsion as the ADW spin current's nonlinear realization; **Kostelecký / Hughes–Drever bound passage formalized** (the torsion sector evades existing tests within the calibrated parameter window).

**Phase 6f (May 2026): classical-GR algebraic backbone — first formalization in any proof assistant.** Phase 6f W1–W6 ship the substrate (no per-wave drafts; lifts into D3 §22.5 + I1 sidebar):
- `Curvature.lean`, `EinsteinTensor.lean`, `EnergyConditions.lean` (already shipped Phase 6f W3 — first formalization of WEC/NEC/DEC/SEC in any proof assistant per audit §3E), `ExactSolutions.lean`, `ADM.lean`, `Tetrad.lean`.
- `paper44_riemannian_connection` (Phase 6f W7 + W8, expanding session-by-session): Lorentzian metric typeclass + Levi-Civita Christoffel uniqueness + full coordinate Riemann + algebraic + differential Bianchi machinery + bundle-level Riemann curvature consumer of Bonn `IsCovariantDerivativeOn` + `mlieBracket` API. Mathlib-PR-quality target.
- Deferred: `Curvature.lean` second-Bianchi at bundle scope (Phase 6f.1 / W3.1) sits behind upstream Mathlib Bonn-Massot ↔ Rothgang Levi-Civita branch (status unchanged from prior overview).

**Phase 6g (May 2026): causal structure + singularity hypothesis bundles + Schwarzschild area-monotone + Kerr no-hair.** Bundled into D3 §23–§27 + I1 sidebar (W5 Cauchy):
- W1–W4: causal structure axioms (Wald §8.1 + `realLineSpacetime` witness); Penrose hypothesis bundle with Riccati-focusing core + correctness-push-under-applicability biconditional; Hawking–Penrose SEC variant with cosmological-Λ-violates-SEC counterexample; classical area theorem for Schwarzschild monotone-mass + BH-entropy bridge.
- W6: Kerr no-hair with sub-extremality `J² ≤ M⁴` + Schwarzschild specialization.
- W5: Cauchy-problem well-posedness predicate framework (structural-Prop scope per Gate G.4 LMPP fallback; lifts to I1 as a methodology case study of the Mathlib-dependency-fallback discipline).

---

## Chain 6: Monte Carlo / Vestigial Gravity

**Status: IN PROGRESS.**

**Infrastructure built:**
- RHMC production code (PyTorch, L=4 complete, L=8 running)
- Matrix-free stencil Dirac operator (L=12+ feasible: 42 MB vs 220 GB dense)
- Verified statistical estimators (jackknife variance non-negative, autocorrelation — first in any proof assistant)
- Multiple algorithms tested: Metropolis, fermion-bag, Majorana sign-free, RHMC
- Mean-field-guided scan parameters center MC on G_c prediction

**What's blocking:** L=8 production data not yet conclusive. The vestigial phase window is exponentially narrow (BCS-like) and may require L >= 8-12 to resolve.

**Implication:** If vestigial phase confirmed numerically, it provides a concrete realization of metric-without-tetrad. If not, publishable negative result redirecting toward Fermi-point route.

---

## Chain 7: Fermi-Hubbard Geometric Quantum Gate

**Status: SOLID. Fully machine-verified, peer to the topological-quantum-computation strand of Chain 3.**

**The chain:**
Fermi-Hubbard dimer Hamiltonian on 6-dim Fock space → singlet-sector block decomposition → spectrum at U = 0 (dark state + two brights) → full charpoly factorization `X·(X − C√g)·(X + C√g)` over the singlet block → chiral-symmetry pinning of the zero mode via Γ = σ_x on the sub-lattice basis → symmetry-adapted 6×6 block-diagonal lift → geometric SWAP realized as Householder reflection `U_SWAP = I − (2/gap²) darkVec ⊗ darkVec` → Berry phase theorem: under a π-sweep the dark state picks up a −1 sign (closed-path statement), the dynamical phase vanishes (`⟨darkStateθ, H · darkStateθ⟩ = 0` under the kernel-angle condition), and the accumulated phase is purely geometric.

**What's proved (`FermiHubbardDimer.lean`, 143 theorems, 0 sorry):**
- Direct-exchange scaling: `E_plus(t, U) = (U + √(U² + 16t²))/2` with `HasDerivAt (E_plus t) (1/2) 0` (Tier-1 linear-in-U scaling).
- Tier-2 superexchange approximation bound `|J − 4t²/U| ≤ 16t⁴/U³` for `4|t| ≤ U`.
- Full chiral-symmetry layer: ker(H) is 1-dimensional and exactly `ℝ · darkVec`; sublattice projectors `P_± = (1 ± Γ)/2` are idempotent, orthogonal, and complete; Γ acts as ±1 on ±1 eigenspaces.
- Geometric SWAP unitarity proved via `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`; 6×6 symmetry-adapted lift `U_SWAP_adapted ∈ Matrix.unitaryGroup`.
- Minimal Berry-phase theorem bundles sign flip + zero dynamical phase into "accumulated phase is purely geometric and equals −1."

Python mirror (`src/fermi_hubbard/dimer.py` + `src/experimental/doublon_gate.py`, ED API + scaling curves + SWAP witnesses + superexchange benchmark), 43 tests, one figure (`fig_doublon_gate_spectrum`: singlet spectrum cross-verified numpy-vs-closed-form, superexchange envelope ±16t⁴/U³).

**What's missing:** The full adiabatic Aharonov–Anandan / Berry-connection formalism over a parameterized eigenbundle is explicitly deferred to Phase 6 (Target B); the current proof is the minimal geometric content without formalizing parallel transport on an eigenbundle.

**Implication:** First formally verified analysis of a symmetry-protected non-topological two-qubit gate. Distinct from Fibonacci-braiding universality (topological, Chain 3) — here the protection is symmetry-based and non-holonomic. Paper 18 documents the result.

---

## Chain 8: Graphene Dirac-Fluid Hawking Radiation

**Status: SOLID through formalized predictions; detection pending.**

**The chain:**
Graphene electronic sonic horizon (Dean group, Columbia, Sept 2025) → 3×3 acoustic metric for 2+1D Dirac fluid → block-diagonalization for quasi-1D flow → 1+1D WKB machinery applies directly (≈92% Lean theorem reuse from the existing `WKBAnalysis.lean`, `WKBConnection.lean`, `HawkingUniversality.lean`, `AcousticMetric.lean`) → predicted T_H ≈ 2.4 K for Dean bilayer nozzle (9 orders above BEC) → dissipative δ_diss ~ 10⁻¹³ (negligible) vs. dispersive δ_disp ~ −3% (dominant) → Wiedemann–Franz violation L/L₀ > 200× from two-channel transport → noise-spectrum formula `ΔS_I(ω) = 2ℏω σ_Q Γ(ω) n_H(ω)` from Keldysh FDT + Landauer–Büttiker.

**Lean modules (all zero sorry):** `DiracFluidMetric.lean` (9 thms), `GrapheneHawking.lean` (7 thms), `DiracFluidSK.lean` (9 thms), `GrapheneNoiseFormula.lean` (8 thms — corrected formula), `QuasiOneDReduction.lean` (extensions; Γ₀ ≈ 0.9994 and quasi-1D bound error ≤ 1.8% verified in Wave 10c). Python companions under `src/graphene/` (`bilayer_eos.py`, `hawking_predictions.py`, `platform_comparison.py`, `transport_counting.py`, `wkb_spectrum.py`).

**What's missing:** Detection itself. The Dean group has the sonic horizon; the Kim group (Harvard) has the noise thermometer; neither has attempted Hawking-radiation detection. Principal device-level uncertainty is the greybody factor `Γ(ω)` — the framework derivation is complete but the experimentalist-specific sample geometry sets the final bandwidth.

**Implication:** Opens a second experimental frontier alongside polaritons. T_H in the 1–3 K range with a realized sonic horizon in a solid-state system. Paper 16a documents the platform end-to-end.

---

## Chain 9: Dark-Sector Connections and the Structural No-Go for Emergent Dark Energy

**Status: SOLID as an obstruction-harvest. The negative results are machine-checked; the positive predictions (SFDM merger forecast, fracton DM viability) are forecasted and awaiting observation.**

**Two coupled sub-chains:**

**Sub-chain 9A — Dark matter candidate classification:**
ℤ₁₆ anomaly-driven enumeration of SM-singlet Weyl sectors (`HiddenSectorClassification.lean`, `HiddenSectorMixedCharge.lean`; extends Chain 2's anomaly framework) → T-0 TQFT candidate is invisible to all planned direct-detection experiments (`emergent_gravity_dm_invisible_collective` over 5-element enum) → SFDM merger sonic-boom forecast (`SFDMMergerForecast.lean`, 30 theorems; Bullet, El Gordo, Pandora, A520, MACS J0025 canonical-merger table; Rankine–Hugoniot density-jump closed form for γ = 2; Euclid × Roman stacked ≥ 30 mergers reaches 3.5–5.7σ; first 3σ detectable ~2028) → fracton DM viable in p-wave dipole superfluid phase at MeV–TeV (`FractonDarkMatter.lean`, 25 theorems; consumes `FractonFormulas.dipole_k4_damping` + `FractonNonAbelian.no_fracton_is_ym_compatible`) → Fang–Gu torsion DM kinematically excluded at CDM level (`FangGuTorsionDM.lean`, traceless T_μν forces w = 1/3) → seven cross-connection theorems in `DarkSectorSynthesis.lean` pinning the Paper 17 empirical-hook ranking to Lean-decidable ground (merger outranks direct detection).

**Sub-chain 9B — Dark energy structural obstruction:**
Gibbs–Duhem emergent-vacuum obstruction (`GibbsDuhemTheorem.lean`, 16 theorems) — Lorentz-invariance + Gibbs–Duhem equilibrium → `w_vac = −1` identically for any single-scalar self-tuning emergent-vacuum framework → Klinkhamer–Volovik q-theory no-go (`QTheoryNoGoTheorem.lean`) across all four tested realizations (4-form, 2-brane, fermionic-crystal, unimodular gravity) → four-factor orthogonality decomposition (`DarkEnergyObstructionPrinciple.lean`: Gibbs–Duhem ∩ `c_s² ≥ 0` ∩ natural `T_c` ∩ MICROSCOPE) + DESI DR2 comparison (`DESIComparison.lean`) → first closed-form vestigial-gravity EOS `w_vest(τ) = (1 − τ²)/(5τ² − 1)`, `c_s²(τ) = −(1 − τ²)/(3 − 5τ²)` (`VestigialEOS.lean`, 20 theorems; natural branch is phantom-today + `c_s² < 0` catastrophic gradient instability) → Layer-3 predictive-scope recalibration: SM+GR emergent physics IN, dark-energy sector OUT under the tested mechanisms (`docs/ARCHITECTURE_SCOPE.md`).

**What this does NOT claim:** q-theory is not falsified as a vacuum-stability framework (only as a DESI-compatible dark-energy mechanism). Additional Volovik-family mechanisms (3-form aether, H3 inflation-era q-dynamics) remain logically open but not realized in the phases explored.

**Implication:** A substantial class of emergent-vacuum dark-energy proposals is now structurally obstructed in a machine-checked way. For dark matter, the empirical-hook ordering (SFDM cluster mergers > fracton direct detection > hidden-sector direct detection) is grounded in Lean-decidable theorems. Paper 17 integrates both sub-chains.

---

## Chain 10: Phase 6 — Cosmology, Strong Coupling, and Horizon Thermodynamics

**Status: ACTIVELY SHIPPING. Phase 6a complete; Phase 6d closed; Phase 6c partially closed (4 of 5 waves shipped); Phase 6b W1 shipped; Phase 6f W3 shipped, W3.1 / 6f.1 deferred.**

This chain takes the project's machinery — SK-EFT corrections, ADW emergent gravity, vestigial gravity, the ℤ₁₆ anomaly framework, the MTC / TQFT layer, the Phase 5y Gibbs–Duhem obstruction — and runs it against an additional set of published cosmological / strong-coupling / horizon-thermodynamic constraints that the earlier phases never directly addressed. Each Phase 6 wave is one self-contained falsifier or correctness-push framed against a primary observational anchor.

### Phase 6a — Linearized gravity, FLRW, GWs, BH entropy, BH four laws

- **Wave 1 (LinearizedEFE.lean, 37 thms):** Linearized Einstein equations from the ADW microscopic theory; Sakharov–Adler `G_N^Sak = 12π / (N_f Λ²)`; ADW emergent `G_N^emerg = α_ADW · G_N^Sak`; correctness-push match locus + Planck anchor reduction; Vergeles structural Props (`H_VergelesPositivity`, `H_CriticalLimitCollapse`, `H_DeepGapReducesToAdler`).
- **Wave 4 (FLRWDynamics.lean, 14 thms):** Friedmann I/II + conservation + Bianchi consistency + ADW emergent-gravity bridge `hubbleSquared_ADW_pos` + Phase 5y DESI-DR2 cross-reference tracked hypothesis `H_DESICompatibility`. Track A shipped.
- **Track B Wave 2 (GravitationalWaves.lean, 21 thms, paper25):** GW propagation `c_GW = c · √χ_vest` from VestigialSusceptibility; **GW170817 falsifies the vestigial-second-sound graviton identification by ~7 × 10¹⁴** at the natural χ_vest range vs the LIGO Δc/c cap of 3 × 10⁻¹⁵. Tracked-hypothesis bundle `H_VestigialModeIsGraviton` carries 4 falsifiers; SK-EFT dispersion `dispersion_within_ligo_iff` biconditional.
- **Track C Wave 3 (BHEntropyMicroscopic.lean, 22 thms):** Bekenstein–Hawking `S = A/(4 G_N) − (3/2) log(A/(4 G_N))`; Kaul–Majumdar SU(2)_k closed form (Outcome-2 sub-corollary) decomposing the −3/2 logarithmic coefficient as `(−1/2 Gauss) + (−1 singlet)`; tracked-hypothesis bundle `H_HorizonBoundaryCondition` (Outcome-3) with 4 falsifiers (Sen 4D non-universality witness; abelian-MTC concrete F2 path; toric code FAILS F2; Fibonacci horizon non-vacuous witness via `fibonacciHorizonBC`); Immirzi γ tuning encoded as a structure field; bridge to Wave 1 G_N^emerg. The 1/4 area-law coefficient is itself the Immirzi γ-tuning.
- **Track C Wave 5 (BHThermodynamicsFourLaws.lean, 18 thms, paper27):** **First machine-checked four laws of black-hole mechanics partitioned by regime.** Schwarzschild ↔ ADW-extremality boundary at `M_c = (N_f · Λ_UV) / (12π · α_ADW)`; decidable `classify` function + 3 `classify_*_iff` theorems; `T_H_schottky` definition + 3 anchor theorems (Jacobson–Koike Eq. 13); tracked-hypothesis `H_RegimePartition` parameterized by *external* `slope` and `delta` reals (no ∃-absorption); `delta_consistent_with_ansatz` pins `δ = (α_ADW − 1) · Λ_UV` per deep-research §9; two correctness-push theorems (`regime_partition_criterion`, `four_laws_consistent_with_adw_bhs_cool_toward_extremality`); two FourLaws_* Prop bundles with opposite C-signs; `ADWSecondLaw` Prop encoding Glorioso–Liu SK-EFT entropy-current monotonicity (no NEC); four falsifiers (Davies vs Dymnikova boundary character; Israel vs Kehle–Unger third-law form; quadratic T_H form; χ_vest dependence). Cross-wave bridges to Wave 1 + Wave 3. Paper 27 cleared a 4-pass Stage 13 adversarial review and is **submission-ready** (Balbinot 2005 BEC-acoustic primary anchor + Hawking 1975 Schwarzschild contrast).
- **Wave 7 (LaplaceMethod.lean, 5 thms, axiom retirement):** Project-local Laplace-method derivation (gaussian saddle full integral + boundedness + IsBoundedRemainderOoneOverA helpers) **retires the `gaussianSaddleAsymptotic` axiom** that was introduced in Wave 3. BHEntropyMicroscopic §2 was restructured: the previously opaque `verlindeEntropy_SU2k` definition became a concrete Laplace-saddle-limit construction, and the corresponding axiom was upgraded to a theorem. **Project axiom count: 2 → 1.** A new tracked-hypothesis predicate `H_VerlindeKMLiteralSumDerivation` is left as an entry point for a future literal Verlinde-sum derivation via Hardy–Ramanujan.

### Phase 6b — Big-Bang nucleosynthesis (W1 shipped)

- **Wave 1 (BBN.lean, ~14 thms, paper29):** Five Phase 5x dark-matter candidates classified against PDG primordial light-element abundances (Y_p, D/H, ³He/H, ⁷Li/H); 3 conformant, 2 violators conditional on thermalization. `bbn_violators_share_n_eff_failure_mode`: BBN-violating candidates share an N_eff-mediated failure (only path to falsification is through an effective-relativistic-DOF inflation, not direct nuclear). 16 tests. **First wave to apply preemptive-strengthening discipline at first-pass:** 5 retroactive theorems vs the 6c.3 baseline of 12 (58% reduction). The discipline caught 2 patterns (∃-absorption + biconditional-tautology P5) at first-pass but missed 5 subtler patterns (identity-function wrapper, definitional-unfolding, within-own-±2σ-band tautologies, pairwise-distinctness on inductive constructors) that ruthless post-wave review surfaced — establishing that preemptive discipline is a useful filter but not a complete substitute for the post-wave audit.

### Phase 6c — Cosmological + holographic constraints (4 of 5 waves shipped)

- **Wave 1 (StrongCPTopologicalDE.lean, 8 thms, paper32):** Anomaly-matching chain ℤ₁₆ ↔ strong-CP ↔ Λ. **Zhitnitsky topological-DE prediction `ρ ~ Λ_QCD⁶ / M_P²` evaluates to ≈ 6.71 × 10⁻⁹ eV⁴ at PDG `Λ_QCD = 0.1 GeV`, within ≤ 3 orders of the observed 2.8 × 10⁻¹¹ eV⁴ with no free parameters**, and ≥ 120 orders below `M_P⁴`. The combined-mechanism falsifier (Zhitnitsky + KV q-theory both active) gives 240 × the observed value, **forcing the project to commit to ONE dark-energy mechanism**. `H_BothActiveGivesInconsistency` was tightened to `> zhitnitskyDE_eV4 0.1` so that `h_qtheory_pos` is genuinely load-bearing in the proof body. 14 tests + `fig_zhitnitsky_de_theta_scan`.
- **Wave 2 (EWBaryogenesisChiralityWall) — NOT YET SHIPPED.** This is the only Phase 6c wave still open. Roadmap calls for the Phase 5n chirality-wall infrastructure to be exercised against the electroweak-baryogenesis bubble-wall constraints.
- **Wave 3 (EquivalencePrinciple.lean, 25 thms, paper34):** 6 vestigial-physics mechanisms classified across WEP / EEP / SEP. `violationLevel` predicate + 6 single-claim `violationLevel` theorems + 3 quantitative `norm_num` comparisons of `MICROSCOPE_BOUND` / `STEP_TARGET` / `VESTIGIAL_PHASE_ETA_MAX` / `VESTIGIAL_RELICS_ETA`. Structural punchline: **EP violation is vestigial-only**. Cross-bridge `vestigial_microscope_violation_consistent` to `ClassificationTableDark`; cross-bridge `fangGu_failure_mode_is_kinematic_not_ep` calls `FangGuTorsionDM.fg_cdm_obstruction`. 39 tests + `fig_ep_violation_matrix`.
- **Wave 4 (QECHolographyBridge.lean, 8 thms, paper35):** Hayden–Preskill structural QEC on the Wave 3 HorizonMTCBC substrate. Code distance `d_C := log d_max`, scrambling time `t_scr := log D²`. Correctness-push absorbs both biconditionals: admissibility ↔ non-abelian + (P2) ⇒ positive scrambling. Fibonacci witness (`log φ < log 2`) calls Wave 3's `fibonacci_horizon_areaLawKappa_pos` through correctness-push. Substantive cross-bridge to Wave 3's `H_HorizonBoundaryCondition.areaLeading`. 30 tests + `fig_code_distance_vs_fusion_spectrum`. Trivial-abelian falsifier reroutes through correctness-push.1.mp.
- **Wave 5 (RTCasiniHuertaBounds.lean, 7 thms, note_rt_ch_bounds):** Ryu–Takayanagi and Casini–Huerta as external-hypothesis tracked Props. Knife-edge biconditional `rt_eq_kaulMajumdar_iff_trivial_reduced_area` is the named correctness-push (subsumes the prior `rt_classical_inconsistent_with_kaul_majumdar` via contrapositive). **Quantitative anchor: gap at reduced area = 2 is exactly `(3/2) log 2 ≈ 1.040`.** Substantive cross-bridge `rt_falsified_by_kaul_majumdar` consumes H_RT + biconditional contrapositive. Concrete H_CH witness saturated. Falsifier: `kaulMajumdar_not_H_RT`. Bulk minimal-surface and CH modular-Hamiltonian fully formalized are deferred per roadmap §A. 29 tests + `fig_rt_ch_bounds_mtc`.

Phase 6c summary: **4 of 5 waves SHIPPED + cross-wave-strengthened**; W2 (EW baryogenesis chirality wall) is the only outstanding wave.

### Phase 6d — QCD strong coupling (Track A CLOSED)

- **Wave 1 (CenterSymmetryConfinement.lean, 18 thms, paper36):** Confinement = ℤ_N 1-form center *unbreaking*; Polyakov loop = ℂ; Svetitsky–Yaffe deconfinement universality (SU(2) → 3D Ising, SU(3) → 3D 3-state Potts) with `ising_nu_gt_potts_nu` as the load-bearing comparison; KSS bound + Walker–Wang transport correctness-push (HPC-gated). `higher_form_discrete_iff_non_abelian` biconditional cross-bridge replaces an earlier identity wrapper; `walker_wang_witness_at_kss_lower` boundary witness. 30 tests + `fig_polyakov_loop_deconfinement`.
- **Wave 2 (ChiralSSB_QCD.lean, 10 thms, paper37):** Quark condensate ⟨q̄q⟩ as the WetterichNJL scalar channel; **GMOR PDG verification at ~4 × 10⁻⁸ GeV⁴ (~1 part in 10⁴)**; `chiral_unbroken_violates_gmor` contrapositive; tetrad-VEV / quark-condensate naturalness correctness-push (HPC-gated). 14 tests + `fig_gmor_relation_verification`.
- **Wave 3 (CFLChiralLagrangian.lean, 12 thms, paper38):** **THE Phase 6d correctness-push anchor: CFL emergent ℤ₃ (Hirono–Tanizaki) ≡ QCD center ℤ₃ (Wave 1) at the generator level.** First formalization of this identification. 17 tests + `fig_cfl_z3_center_bridge`.

Phase 6d summary: Track A (W1+W2+W3) shipped end-to-end; **Phase 6d is CLOSED**.

### Phase 6f — Energy conditions, curvature

- **Wave 3 (EnergyConditions.lean, 9 thms):** **First formalization of the four energy conditions (WEC / NEC / DEC / SEC) in any proof assistant** per Phase 6f audit §3E. WEC / NEC / DEC / SEC predicates on an abstract bilinear form + 3 chain implications + 5 counterexample witnesses (cosmological-Λ violates SEC; ghost scalar violates NEC; stiff-fluid violates DEC).
- **Wave 3.1 / 6f.1 (Curvature.lean) — DEFERRED.** Stage-1 scoping doc filed; implementation deferred behind the upstream Mathlib Bonn-Massot ↔ Rothgang Levi-Civita branch.

### Phase 6m — Dark-energy three-track closure (May 2026)

After Phase 5y closed the Volovik q-theory family, three additional mechanism families remained outside the Phase 5y tested scope. Phase 6m closes all three at the Lean-formalization scope (4 Lean modules; absorbed into D5 §8–§12):
- **Track A — Causal-set DE (`CausalSetDarkEnergy.lean`, 15 thms):** 3 NO-GO-R5 phenomenological prescriptions (Sorkin Models 1 + 2; BDG MYZ 2025) with 3 publishable structural caveats: GD-inapplicability across 4 prescriptions, Barrow-bound prescription dependence, BDG `σ_Λ` first-principles decomposition.
- **Track B — Entropic-gravity DE (`EntropicGravityDarkEnergy.lean`):** **8/8 unanimous NO-GO** — *first complete-mechanism-family unanimous closure* in Phase 6m (Tsallis, Barrow, Odintsov, Verlinde, ...; r_d-independent Bayesian thresholds all exceeding Jeffreys-decisive). Phase 7 absorption Session 5 honestly downgraded one Bayes-factor claim to mixed-threshold information-criteria (Luciano arXiv:2506.03019 Table II → ΔAIC = +4.7 for Barrow, AIC-only) preserving 3-of-4 as genuinely Bayes-decisive plus a fourth as AIC-disfavoured; first-mechanism-family closure survives via mixed-threshold aggregator.
- **Track C — Jacobson-thermo-GR DE (`JacobsonThermoGRDarkEnergy.lean`):** highest-survival 5+ R5 survivors. **M3 EGJ f(R) Exp+ArcTanh strongest CLEARED-R5 of any track** per Plaza-Kraiselburd ΔAIC ≃ ΔBIC ≳ 20; Hu-Sawicki NO-GO chameleon at `b ≈ 0.21 ≫ 100×` Solar-System bound; M4 Pure Lovelock NO-GO at 1σ-box edge; M8 KSS conditional path-(a); Phase 6e Sakharov 4-criterion cross-bridge: ³He-A satisfies + FLS BEC violates condition (ii); unimodular escape route admits 5/6 except KSS.
- **Wave 4 (`DarkSectorClassificationExtension.lean`):** unified Phase 6m **7-class GD taxonomy + 3-tier applicability gradient** + per-track class assignments + cross-class instantiation witnesses to Phase 5y orthogonality principle. This integrative structural framework is the most reusable Phase 6m output.

**Phase 6o W4a verdict (B) — biconditional retired, depletion field load-bearing (2026-05-08):** The proposed biconditional `Sakharov 4-criterion ↔ Λ_J = Λ_HK` was *retired* in favour of one-way implication + a load-bearing `depletion : ℝ` field on a strict-extension `SakharovExtended` structure. Volovik–Jannes 2012 §VII argues only forward; FLS BEC arXiv:1103.4841 + 1204.3039 Eq. 71 confirms forward but does not test (⇐). Five new substantive theorems (depletion-factor unconditional + ³He-A unit + FLS strict bounds + asymmetry + composed honest-one-way closure) shipped in `JacobsonThermoGRDarkEnergy.lean §8`; D5 §11 prose addendum + bibliography block shipped. The verdict is honest one-way implication and is documented as such in D5.

### Phase 6n — Mathematical substrate for the SK-EFT / SymTFT / horizon-thermodynamic / LDP layers (April–May 2026)

Phase 6n is the program's *mathematical substrate* push — no per-wave drafts, all output is sourceless Lean lifts into existing bundles (D1, D2, D3, D4, D5, I1, I2, I3, L3) per the D.4 protocol. Key deliverables:
- **Glorioso–Liu axiomatic skeleton (`GloriosoLiu/Axioms.lean`, `GloriosoLiu/SecondOrderProjection.lean`):** `SKEFTAxioms` typeclass; **FirstOrderKMS reframed as the first-order projection of the CGL / CGL II / Glorioso–Liu II 2017 axiomatic skeleton.** The 4-of-9 / 5-of-9 component partition (the original "Aristotle counterexample" finding from Phase 1) is now *recovered as a theorem* of first-order projection, not as a hand-tuned axiom strengthening. D.3 user-auth gate at I1 §3 (substantive reframing) + D3 + L3 (cross-ref-only upgrades).
- **Quantum Crooks NO-GO (Perarnau-Llobet) — including ℂ-form higher-dim NO-GO:** `QuantumCrooks/SKEFTConnection.lean` + `ReservoirCoupled.lean` + `HigherDimensional.lean` (block-diagonal embedding into `Matrix (Sum (Fin 2) T) ℂ`; substantive higher-dim ℂ no-go) + `ConcreteComplex.lean`. NO-GO landscape entry into D5 §13.
- **LDP linear-response framework (`CrooksAnalogHawking/LDPLinearResponse.lean`, `SKEFTGallavottiCohen.lean`):** `LDPLinearResponseData` + W-form Gallavotti–Cohen + abstract `IsLDPRateFunction` typeclass with `zero_at_zero` + `wForm_gc` fields + `linear_bias_plus_even` derived theorem (re-centered form; substantive finding: §2 Gaussian rate fn NOT zero at zero — re-centered Gaussian instance ships); 3 `IsLDPRateFunction` instances (linear-response centered + quartic + non-Gaussian); third Sakharov-style biconditional substrate-level discharge in W-form + σ-form.
- **Sakharov ↔ horizon-Crooks unification at horizon temperature `β_H` (`SKEFTHorizonBridge.lean`):** 6 theorems linking Wave 2a `SKEFTAxioms` machinery to Wave 2c `HorizonDetailedBalance` at `β_H`; `HorizonCrooks` predicate + biconditional with Sakharov 4-criterion + **explicit Verlinde-vs-Jacobson distinction at every claim site** (Phase 6m R2/R3 EGDE 8/8 NO-GO referenced as discriminator). D.3 user-auth gate at D3 §17.5 (NEW substantive subsection) + L3 (NEW "Substrate-class context" paragraph; ³He-A satisfies all 4 / FLS BEC violates condition (ii) — two classifications independent program axes).
- **SymTFT audit substrate (~100 substantive thms):** `SymTFTAudit/WittClass.lean` (`WittInvariant := ZMod 24` quotient + `AddMonoidHom`); `DrinfeldCenter.lean` (DMNO 2010 Witt-equivalence via Mathlib `Center.braidedCategoryCenter`; braided strengthening to genuine `IsBraidedEquivalence` in S16); `FreeKLinearCategory.lean` + `FreeKLinearMonoidal.lean` (free k-linear envelope `MonoidalCategory` + `Braided` + `MonoidalPreadditive` + `Linear k`); `DeligneTensor.lean` (`DeligneTensor C D k` as quotient with `Preadditive` + `Linear k` + `MonoidalCategory` + `Braided` + `CategoricalCcStructure` with `witt_additive` theorem); `PseudoUnitary.lean` (DMNO 2010 Theorem 5.2 substrate at restricted-form layer + strict refinement breaking trivial-witness equivalence); `CrossBridges.lean` (3 substantive cross-bridges). SymTFT audit verdict: **PartiallyApplicable**.

### Phase 6o — Soft theorems / classical double-copy / APS-η / Schellekens / ETH refutation / Itô + LDP (May 2026)

Phase 6o is also research-only (no per-wave drafts; all output is sourceless lifts):
- **G2 Boostless / Carrollian soft theorems (`SoftTheorems/Boostless.lean`, `Carrollian.lean`, `EmergentGraviton.lean`, `DissipativeNoGo.lean`, `NoiseFloorPrediction.lean`):** Strominger triangle closure on BEC + ADW + polariton; ADW graviton subleading factor; Lindbladian S-matrix axiomatization NO-GO joining D4's NO-GO landscape; **universal `n_noise / Hawking-flux` Wilson-coefficient-independence** as the most concrete near-term Phase 7 deliverable per On-Shell Methods DR §7.2 (cross-bridge into E1).
- **G4 Kerr–Schild double-copy on Petrov-D analog gravity (`KerrSchild/PetrovD.lean`, `SingleCopy.lean`, `WeylSpinor.lean`, `BCJNoGo.lean`, `PolaritonCrossBridge.lean`):** **First explicit classical double-copy on analog gravity in the literature.** Petrov-D verification on the draining-bathtub acoustic metric; Maxwell field on flat Minkowski via `A_μ = φ k_μ`; type-D vacuum reformulation `Ψ_ABCD = Φ_(AB Φ_CD) / S`; **3-obstruction strong-form BCJ NO-GO theorem-pair** (Lorentz-frame breaking + gauge-erasure abelianization + UV-vs-IR scale-ordering mismatch — productive-value structural negative result); polariton ringdown signature cross-bridge into E1.
- **G3 APS-η for analog horizons (`APSEta/Predicate.lean` + `BECAcoustic.lean` + `ADWHorizon.lean` + `He3A.lean` + `SymTFTBridge.lean` + `RegimePartition.lean`):** **First systematic substrate-side APS-η identification on a chirally-asymmetric analog Hawking horizon in the literature.** Parity-symmetric BEC + ADW give η = 0; ³He-A carries substantively non-zero η (Jackiw–Rebbi chiral edge mode at moving domain wall; ³He-A unique non-degenerate cell). Witten–Yonekura `η/16 mod 1 ↔ ℤ₁₆` cross-bridge via `WittClass`.
- **G1 Schellekens chain reframing (`Schellekens/SpinBordism.lean`, `AnomalyPolynomial.lean`, `ModularInvariance.lean`, `NiemeierLattice.lean`, `HolomorphicVOAc24.lean`, `Chain.lean`):** Per Modular Bootstrap DR §8 Tier 1(a) "the highest-leverage move": **`24 | c₋ → N_f ≡ 0 mod 3` reframed as a theorem-quality classification corollary of Möller–Scheithauer 2024 c=24 holomorphic-VOA classification.** D.3 user-auth gate at D2 §2 (substantive reframing) + L2 (paired-splash update preserving the central "Three Generations" claim) + F §5.
- **G10 ETH-α refutation tableau (`ETH/Predicates.lean` + `ConcreteWitness.lean` + `RefutationTableau.lean`):** 5 candidate `ETHAnsatz` predicates (A1 Srednicki / A2 free-cumulant Pappalardi–Foini–Kurchan / A3 Helbig–Hofmann–Thomale–Greiter Theory-of-ETH / A4 Wang Eigenstate-Typicality-Principle / A5 Inozemcev–Volovich-corrected); 4-site Ising chain witness substrate; **3 concrete refutation theorems** (T1 Inozemcev–Volovich gap via β-equation contradiction; T2 ETP doesn't imply Srednicki via n=16 zero-mean failure; T3 free-cumulant doesn't imply Srednicki via n=1 sum=1 violation). MCP-CLOSED — Aristotle batch deferred (zero residue after MCP).
- **I3 Itô + LDP-α + LDP-β substrate (12 modules):** `Itô/StochasticIntegral.lean` + `QuadraticVariation.lean` + `Semimartingale.lean` + `ItoIsometry.lean` + `ItoLemma.lean` + `Novikov.lean` + `LDP/CramerIID.lean` + `Sanov.lean` + `Contraction.lean` + `CramerLowerBound.lean` + `Varadhan.lean` + `LDPCompatibleSKEFT.lean` typeclass connecting to Phase 6n W2c `IsLDPRateFunction` + Phase 6n W2a Glorioso–Liu monotonicity. **I3 is the new 14th publication target** (added Phase 6n Session 4 commit `a72ba68` under Pipeline Invariant #14 user-auth) — sourceless bundle initial lift via D.4 protocol, analogous to I2's lean-tensor-categories framing.

### Implications of the Phase 6 push as a whole

- **Falsifications, not just consistency checks.** The Phase 6 waves run the project's emergent-physics machinery against published constraints and frequently produce ratios in the 10¹⁴ range (GW170817 vs vestigial graviton) or order-of-magnitude tensions (combined-DE-mechanisms × 240) that are either decisive or force model-commitment.
- **Single-DE-mechanism commitment.** Phase 6c W1 forces the project to commit to one dark-energy mechanism (Zhitnitsky topological DE) rather than to combine it with KV q-theory.
- **Vestigial-only EP violation.** Phase 6c W3 establishes that within the project's mechanism inventory, only the vestigial sector violates the EP — Fang–Gu torsion DM, fracton DM, SFDM, and the hidden-sector candidates do not, and the failure modes for Fang–Gu are kinematic (CDM-trace) not EP.
- **Holographic + QEC cross-bridges.** Phase 6c W4 + W5 wire the Wave 3 horizon-MTC substrate to QEC and RT/CH frameworks via tracked-hypothesis correctness-pushes; this is the project's first formal contact with holographic structural bounds.
- **QCD strong coupling closed.** Phase 6d closes the chirality + confinement + CFL triangle at the generator level, with GMOR PDG-verified to ~1 part in 10⁴.
- **Energy-conditions formalization.** Phase 6f W3 is a foundational contribution — the four energy conditions and their counterexamples are now machine-checked at the abstract-bilinear-form level and available as substrate for any future emergent-gravity / vestigial-EOS / dark-energy work.
- **Phase 6m three-track dark-energy closure.** Causal-set, entropic-gravity, and Jacobson-thermo-GR DE families closed at Lean-formalization scope; Track B is the **first complete-mechanism-family unanimous NO-GO** in Phase 6m; Track C surfaces the strongest *positive* survivor (M3 EGJ f(R) Exp+ArcTanh CLEARED-R5 with ΔAIC ≃ ΔBIC ≳ 20). The 7-class GD taxonomy + 3-tier applicability gradient is the most reusable integrative framework. Phase 6o W4a verdict (B) honestly retired the proposed Sakharov 4-criterion ↔ Λ_J = Λ_HK biconditional in favour of one-way implication + load-bearing depletion field.
- **Phase 6n mathematical substrate.** Glorioso–Liu axiomatic skeleton makes FirstOrderKMS a *theorem* of first-order projection (not an axiom strengthening); Quantum Crooks NO-GO including ℂ-form higher-dim no-go formally added to the program's NO-GO landscape; LDP linear-response framework with W-form Gallavotti–Cohen + abstract `IsLDPRateFunction` typeclass; Sakharov ↔ horizon-Crooks unification at `β_H` with explicit Verlinde-vs-Jacobson distinction; SymTFT audit substrate (DrinfeldCenter via DMNO 2010 Witt-equivalence with braided strengthening; FreeKLinear monoidal; DeligneTensor as quotient; PseudoUnitary at restricted-form layer).
- **Phase 6o substrate-side firsts.** *First* explicit classical double-copy on analog gravity (G4 Kerr–Schild Petrov-D); *first* systematic substrate-side APS-η identification on a chirally-asymmetric analog Hawking horizon (G3); G1 Schellekens-chain reframing of `24 | c₋ → N_f ≡ 0 mod 3` as a Möller–Scheithauer 2024 corollary; G10 productive-value ETH-α refutation tableau; G2 boostless / Carrollian soft theorems with universal noise-floor / Hawking-flux Wilson-coefficient-independence as a near-term experimental deliverable.

---

## Architectural Scope (Phase 6m post-closure)

The three-layer architecture (Layer 1 lattice / Layer 2 SK-EFT / Layer 3 emergent SM + GR) is now scope-explicit for what it predicts and what it does *not* predict, with the boundary tightened by Phases 5y, 6m, and 6o W4a.

**In scope (Layer 3):** SM + GR-sector emergent physics under the tested mechanisms — ADW tetrad condensation, gauge erasure, fracton hydrodynamics, and vestigial gravity (with the Phase 6e nonlinear-EFE + Einstein–Cartan torsion calibration).

**Out of scope (under tested mechanisms — *not* a global no-go):**
- *Volovik-family dark-energy* (Phase 5y closure): four q-theory realizations + vestigial-gravity EOS + second-sound graviton all returned NO-GO for DESI DR2 compatibility; structural obstruction is Gibbs–Duhem locking `w_vac ≡ −1` for any single-scalar self-tuning emergent-vacuum framework.
- *Causal-set DE* (Phase 6m Track A): NO-GO across 4 prescriptions with 3 publishable structural caveats.
- *Entropic-gravity DE* (Phase 6m Track B): **first complete-mechanism-family unanimous NO-GO** with mixed-threshold aggregator (3 Bayes-decisive + 1 AIC-disfavoured after Phase 7 absorption Session 5 honesty correction).
- *Jacobson-thermo-GR DE* (Phase 6m Track C): mostly NO-GO; **highest-survival 5+ R5 survivors** including M3 EGJ f(R) Exp+ArcTanh as the strongest CLEARED-R5 of any track. (Track C is the *positive* track within Phase 6m.)
- *Cosmological-constant magnitude prediction from heat-kernel `a₀`* (Phase 6e W5 / D5 §7): the emergent route does **not** predict `Λ_obs` naturally — explicit non-prediction documented as a CC-channel constraint.

**Implication:** Phase 6m / 6o close the *negative* boundary on the program's predictive scope while preserving Track C's positive survivors. The architecture is no weaker for SM + GR; it is *more honest* about which dark-energy mechanism families are accessible from condensed-matter substrates and which are not. Full scope-ledger is in `docs/ARCHITECTURE_SCOPE.md`.

---

## Paper Strategy / Phase 7 Bundle Architecture

Phase 6i Wave 7 introduced a fourteen-target publication architecture that supersedes the per-wave-paper convention for *external* communication. The 32+ existing per-wave drafts in `papers/paperN_*/` continue as internal source material that is *consolidated* into the bundles defined here. Authoritative documents:
- `docs/PAPER_STRATEGY.md` — canonical bundle architecture (1 flagship + 5 Tier 1 deep + 3 Tier 2 PRL + 3 Tier 3 infrastructure + 2 Tier 4 experimental = 14)
- `docs/PAPER_DRAFT_MAPPING.md` — per-existing-draft → per-bundle assignment table
- `docs/BUNDLE_LIFT_PROCEDURE.md` — frozen 14-step lift workflow (Stages I1, I2, D1–D5, L1–L3, F, E1, E2)
- `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` — frozen Stage A–G protocol for absorbing future Phase 6X waves into already-drafted bundles (D.1/D.2/D.3/D.4 branches)
- `docs/BUNDLE_READINESS_HEATMAP.md` — auto-generated N-gate × 14-bundle Stage-13 readiness summary

**The 14 publication targets:**

| Tier | Bundle | Title (working) |
|---|---|---|
| 0 | **F** | Fluid-Based Approaches to Fundamental Physics — A Formally Verified Survey |
| 1 | **D1** | Formally Verified Analog Hawking Radiation Across Three Platforms |
| 1 | **D2** | Anomaly Constraints on Standard-Model Particle Content |
| 1 | **D3** | Emergent Gravity from Microscopy — Linearized EFE through BH Thermodynamics |
| 1 | **D4** | Topological Quantum Computation — First Machine-Verified Foundations |
| 1 | **D5** | The Dark Sector under Substrate Constraints |
| 2 | **L1** | GW170817 Falsifies the Vestigial-Second-Sound Graviton Identification by 7 × 10¹⁴ |
| 2 | **L2** | Three Generations of SM Fermions from Modular Invariance — Machine-Checked |
| 2 | **L3** | Bardeen–Carter–Hawking Four Laws Partitioned by Regime in an Emergent-Gravity Substrate |
| 3 | **I1** | Formal Verification at Scale in Theoretical Physics — Methodology with Worked Cases |
| 3 | **I2** | Verified Statistical Estimators and the lean-tensor-categories Library |
| 3 | **I3** | **Verified Stochastic Calculus for Mathlib4 — Stochastic Integral, Quadratic Variation, Itô's Lemma, and LDP Foundations** (added Phase 6n Session 4 under Pipeline Invariant #14 user-auth) |
| 4 | **E1** | Falsifiable Hawking Spectrum for Polariton Microcavities at Paris-LKB Device Parameters |
| 4 | **E2** | Falsifiable Hawking Noise Spectrum for Graphene Dirac-Fluid at Dean-Kim-Lucas Device Parameters |

**Readiness:** As of 2026-05-06, **all 14 bundles are GREEN** in `BUNDLE_READINESS_HEATMAP.md` (0 blockers; F has 1 minor advisory and D3 has 1 minor advisory; all others have no open findings). I3 is the youngest bundle and reached GREEN at Phase 6n Session 4 close.

**Phase 7 absorption status (as of 2026-05-08):** Phase 7 (Phase 6n + 6o → bundles) absorption is in flight across multiple sessions:
- **Session 1 (2026-05-06):** Stages A→E COMPLETE + all 3 D.3 user-auth gates COMPLETE (GATE 1 I1 §3 Glorioso–Liu projection reframing; GATE 2 D3 §17.5 + L3 Sakharov ↔ horizon-Crooks unification; GATE 3 D2 §2.7 + L2 paired-splash Schellekens-chain reframing).
- **Sessions 2–5:** Stage F reviewer triple per affected bundle; multi-bundle parallelism; mid-session BLOCKER remediation; primary-source PDF caching (213 → 264; 0 missing); citation cache pipeline (Pipeline Invariant #11) caught one fabricated `BelgiornoCacciatori2024` registry entry; Bayes-factor → information-criteria honesty correction (Luciano arXiv:2506.03019); paper_provenance LaTeX-comment-strip fix.
- **Phase 6o W4a Track 4 (Session 5):** authorized + shipped; honest one-way verdict (B) with load-bearing `depletion : ℝ` field on `SakharovExtended`.

**Pipeline additions in Phase 7:**
- **Primary-source WebFetch + verify is now project policy** (user-authorized 2026-05-08, "do that kind of thing from now on"): when a numerical magnitude in a Lean constant / paper claim / registry entry is registry-anchored or unverified, fetch the primary-source PDF (WebFetch + pdfminer.six fallback) and verify before relying.
- **Pipeline Invariant #11 — Citation cache pipeline:** every cited primary source has a cached PDF + extracted-content snapshot under `papers/.citation_cache/`; fabricated bibitem entries (hallucinated DOIs, hallucinated titles, hallucinated authors) are caught at promotion time. Several "et al."-only / hallucinated-title artifacts were repaired across Phase 7 absorption.
- **Pipeline Invariant #14 — Bundle assignment mandatory at Stage 1:** every wave's Stage 1 scoping doc must declare its target bundle(s); user-auth required to spawn a *new* bundle target (I3 was authorized this way Phase 6n Session 4).

---

## Axioms

The project's axiom count is **1**: `gapped_interface_axiom` (`SPTClassification.lean`, eliminability: hard) — the 4+1D gapped interface conjecture. This is the single load-bearing assumption in the entire codebase that is not a standard textbook result.

**Retired:** `gaussianSaddleAsymptotic` was retired in Phase 6a Wave 7 (`LaplaceMethod.lean`) via a project-local Laplace-method derivation; `BHEntropyMicroscopic §2`'s `verlindeEntropy_SU2k` is now a concrete Laplace-saddle-limit construction, and the corresponding axiom is now a theorem.

---

## Strategic Situation

### Epistemic layers

**Layer 1 — Rock solid (machine-checked, zero sorry):**
- SK-EFT corrections to Hawking radiation (complete through all orders, with graphene Dirac-fluid extension)
- `N_f ≡ 0 mod 3` generation constraint (zero axioms, Ext computation machine-checked)
- Ext^n_{A(1)}(F₂, F₂) computation (first in any proof assistant — resolution, d² = 0, minimality, dimensions)
- Change-of-rings isomorphism Ext_A ≅ Ext_{A(1)} (closes topological hypothesis H2)
- Gauge erasure theorem
- Fracton-gravity incompatibility
- E8 / Serre mod 8 / algebra-topology separation
- Ising + Fibonacci MTCs (modularity + Muger triviality), SU(2)_k at k=1..5, SU(3)_k at k=1,2
- TQFT partition functions + WRT surgery invariants (end-to-end pipeline)
- Fibonacci universality for quantum computation (braiding Lie-algebra spanning)
- Temperley–Lieb algebra, Jones–Wenzl idempotents, Muger center, FP-dimension eigenvalues
- Parameterized `QuantumGroup k A` over arbitrary Cartan matrices + Kac–Walton fusion
- Fermi-Hubbard geometric SWAP and minimal Berry-phase theorem (symmetry-protected qubit gate)
- Fidkowski–Kitaev 2+1D Cayley-calibrated gapped interface (bridges axiom evidence from 1D → 2D)
- Gibbs–Duhem emergent-vacuum obstruction + closed-form vestigial-gravity EOS + four-factor orthogonality
- Verified jackknife + autocorrelation statistical estimators for lattice Monte Carlo
- **Phase 6a: linearized Einstein equations from ADW; FLRW + Bianchi consistency; GW propagation `c_GW = c · √χ_vest` with GW170817 falsification of vestigial-second-sound graviton ID; Bekenstein–Hawking + Kaul–Majumdar SU(2)_k −3/2 closed-form; first machine-checked four laws of BH mechanics partitioned by Schwarzschild / ADW-extremality regime; project-local Laplace-method axiom retirement (`gaussianSaddleAsymptotic` 2 → 1)**
- **Phase 6b: BBN classification of Phase 5x DM candidates (3 conformant / 2 conditional violators), shared N_eff failure mode**
- **Phase 6c: Zhitnitsky topological-DE prediction within ≤ 3 orders of observed (no free parameters); single-DE-mechanism commitment forced; vestigial-only EP-violation theorem; Hayden–Preskill structural QEC on horizon-MTC substrate; RT / Casini–Huerta as external-hypothesis tracked Props with knife-edge biconditional against Kaul–Majumdar**
- **Phase 6d (Track A CLOSED): confinement = ℤ_N 1-form center unbreaking; GMOR PDG-verified to ~1 part in 10⁴; CFL emergent ℤ₃ ≡ QCD center ℤ₃ at the generator level (Hirono–Tanizaki)**
- **Phase 6f W3: first formalization of the four energy conditions (WEC / NEC / DEC / SEC) in any proof assistant, with counterexample witnesses**

**Layer 2 — Solid structural results with known gaps:**
- Chirality-wall three-pillar analysis (gaps clearly identified, rigor-tracked)
- ADW gap equation (solution exists, G_c proved, coupling deficit quantified, instanton zero-mode counting machine-checked)
- Fermi-point |N|=2 → SU(2) gauge emergence (rigor tracked: theorem/heuristic/speculative per step)
- Paper provenance / readiness state machine (Phase 5v infrastructure; 11 gates, PG+AGE-backed knowledge graph)

**Layer 3 — Open / in progress:**
- Vestigial gravity MC at L≥8 (RHMC in flight; matrix-free stencil unlocks L=12+)
- Full Kazhdan–Lusztig equivalence Rep(u_q) ≅ SU(2)_k-MTC (data-level verified at k=1,2; full constructive proof is a ~200-page theorem)
- S-matrix ↔ Muger bridge direction 2 (Z₂ trivial → det(S) ≠ 0) requires categorical-trace machinery not yet formalized
- Paper submission (arXiv voucher prerequisite) + Mathlib PR process (AI-content policy requires relationship-building)
- Three residual topological hypotheses for the generation-constraint chain (H1 ko-cohomology, H3 ASS collapse, H4 ABP splitting) — each independently verifiable by a topologist; formalizing them requires algebraic-topology machinery no proof assistant currently supports

### Publication situation

32 paper drafts, 0 submitted as of 2026-04-28. Papers span all ten chains: first-order (1), second-order (2), gauge erasure (3), exact WKB (4), ADW (5), vestigial gravity + MC (6), chirality formal (7), chirality master (8), SM anomaly + Drinfeld center (9), modular generation constraint (10), quantum group formalization (11), polariton analog Hawking (12), braided MTC + knot invariants (14), verification methodology (15), graphene Dirac-fluid SK-EFT (16a), WRT TQFT pipeline formalization (16b), dark-sector connections (17), geometric quantum gate (18), Phase 5z scalar/Majorana rung (20–21), Phase 6a Track A linearized + FLRW (23), Track B GW170817 vs vestigial graviton (25), Track C BH-entropy + Kaul–Majumdar (26), Track C four-laws BCH (27 — submission-ready), Phase 6b BBN (29), Phase 6c strong-CP topological DE (32), Phase 6c equivalence principle (34), Phase 6c QEC-holography bridge (35), Phase 6d confinement (36), Phase 6d chiral SSB / GMOR (37), Phase 6d CFL color-flavor locking (38), and the Phase 6c W5 RT / Casini–Huerta short note (`note_rt_ch_bounds`). The deliberate strategy has been to push boundaries and cross-validate chains before locking down papers; the per-paper readiness state machine (Phase 5v, 11 gates) now gates submission.

The seven Phase 6 papers (paper29, paper32, paper34, paper35, paper36, paper37, paper38, note_rt_ch_bounds) now drive their abstract / formalization-section counts entirely through `\input{counts.tex}` macros — 14 new macros added (`\strongCpDeThms`, `\strongCpDeTests`, `\epThms`, `\epTests`, `\qecHolographyThms`, `\qecHolographyTests`, `\centerSymmThms`, `\centerSymmTests`, `\chiralSsbThms`, `\chiralSsbTests`, `\cflThms`, `\cflTests`, `\rtChThms`, `\rtChTests`) — eliminating count-literal drift permanently for those papers. The `update_counts.py` helper was extended with `_module_thm_count_strict` (BOL-anchored to avoid over-counting docstring "lemma" prose) + a `_pytest_count` helper.

External constraints:
- arXiv requires a voucher for first submissions
- Mathlib has a guarded stance on AI-generated content; contributing requires substantive discussion and relationship-building, plus strong personal familiarity with the work to communicate effectively

### Strongest publication candidates (balanced across chains)

- **Paper 10 (modular generation constraint)** — zero axioms, backed by machine-checked Ext computation + change-of-rings discharge. Independent of other chains.
- **Paper 11 (quantum group formalization)** — first quantum group + first Hopf algebra + first rank-2 quantum group in any proof assistant, with Muger center + FP-dimension strengthening.
- **Paper 12 (polariton analog Hawking)** — experimentally actionable, Paris group active.
- **Papers 7/8 (chirality wall)** — timely given the ongoing TPF/GS debate in the lattice-QFT community.
- **Paper 14 (braided MTC + knot invariants)** — first complete Ising braided MTC and first formally verified knot invariants.
- **Paper 15 (methodology)** — the 12-stage verification pipeline + Stage 13 adversarial review + Stage 14 QI register, written up as a reusable recipe for formal-verification-led physics research.
- **Paper 16a (graphene Dirac fluid)** — timely given the Dean group's 2025 sonic-horizon realization.
- **Paper 16b (WRT TQFT formalization)** — first complete surgery-based TQFT pipeline in any proof assistant.
- **Paper 17 (dark-sector connections)** — SFDM merger forecast is the most actionable new prediction; Gibbs–Duhem obstruction is a genuine structural negative result.
- **Paper 18 (geometric quantum gate)** — first formally verified symmetry-protected two-qubit gate; quantum-information relevance.
- **Paper 25 (GW170817 vs vestigial graviton)** — clean falsification (~7 × 10¹⁴) at LIGO-precision dispersion.
- **Paper 27 (BH four laws BCH partitioned by regime)** — **submission-ready**; cleared a 4-pass Stage 13 adversarial review on the Balbinot 2005 BEC-acoustic primary anchor + Hawking 1975 Schwarzschild contrast.
- **Paper 32 (Zhitnitsky topological DE)** — within ≤ 3 orders of the observed value with no free parameters; combined-mechanism falsifier forces single-DE-mechanism commitment.
- **Paper 34 (equivalence principle)** — vestigial-only EP violation across WEP / EEP / SEP, with quantitative MICROSCOPE / STEP comparisons.
- **Paper 38 (CFL color-flavor locking)** — first formalization of the CFL emergent ℤ₃ ≡ QCD center ℤ₃ generator-level identification.

### Technical blockers and outstanding work

- **L=8 RHMC convergence** for the vestigial-gravity Monte Carlo. Narrow BCS-like phase window may need L ≥ 12. Matrix-free stencil Dirac operator (42 MB vs. 220 GB dense) unlocks L=12+ on workstation hardware; Phase 6A tracks Path A (sparse CG), Path B (Metal GPU), Path C (CUDA).
- **Topological input for generation-constraint chain** — three standard textbook facts (H1/H3/H4) remain as hypotheses pending Lean algebraic-topology infrastructure.
- **Mathlib PR pipeline** — the lean-tensor-categories extraction (20 files, 114 theorems, zero sorry) is ready but not yet upstreamed; Mathlib's AI-content policy requires a relationship-building discussion before PR.
- **arXiv voucher** for first submission.
- **Phase 6c W2 EWBaryogenesisChiralityWall** — the only Phase 6c wave that has not shipped; planned to exercise the Phase 5n chirality-wall infrastructure against electroweak-baryogenesis bubble-wall constraints.
- **Phase 6f.1 Curvature.lean** — Stage-1 scoping doc filed; implementation deferred behind upstream Mathlib Bonn-Massot ↔ Rothgang Levi-Civita branch.
- **Aristotle batch** — pending; last submission is the Phase 6c.1 baseline. User-triggered.
- **Stage 11 notebooks** — pending for the Phase 6 waves; deferred post-compact per user.
- **Stage 13 adversarial-review re-run** — closing act of the current session; seven Phase-6 papers were already cleared in the 2026-04-28 review-driven strengthening pass (two deferred REQUIREDs closed: the q-theory `H_BothActiveGivesInconsistency` Prop tightening, and the P5 self-equality tautology removal in EquivalencePrinciple; eight RECOMMENDEDs cleared in the same pass — Planck-anchor tightening, decorative-marker removal, redundant ν-threshold pair removal, four prose disclosures, and two Lean-docstring clarifications).

---

## Module Inventory (187 active Lean modules)

**Phase 1–2 (foundational SK-EFT):** `AcousticMetric`, `SKDoubling`, `HawkingUniversality`, `SecondOrderSK`, `WKBAnalysis`, `CGLTransform`, `Basic`.
**Phase 3 (emergent geometry & first results):** `ThirdOrderSK`, `GaugeErasure`, `WKBConnection`, `ADWMechanism`, `ChiralityWall`, `VestigialGravity`.
**Phase 4 (fracton + experimental predictions):** `FractonHydro`, `FractonGravity`, `FractonNonAbelian`, `KappaScaling`, `PolaritonTier1`.
**Phase 5 (Monte-Carlo core + categorical scaffolding):** `SU2PseudoReality`, `FermionBag4D`, `LatticeHamiltonian`, `GoltermanShamir`, `TPFEvasion`, `KLinearCategory`, `SphericalCategory`, `FusionCategory`, `FusionExamples`, `VecG`, `DrinfeldDouble`, `GaugeEmergence`, `SO4Weingarten`, `FractonFormulas`, `WetterichNJL`, `VestigialSusceptibility`, `QuaternionGauge`, `GaugeFermionBag`, `HubbardStratonovichRHMC`, `MajoranaKramers`.
**Phase 5a (chirality wall 1+1D infrastructure):** `OnsagerAlgebra`, `OnsagerContraction`, `Z16Classification`, `SteenrodA1`, `SMGClassification`, `PauliMatrices`, `WilsonMass`, `BdGHamiltonian`, `GTCommutation`, `GTWeylDoublet`, `ChiralityWallMaster`.
**Phase 5b (SM anomaly → modular generation → Drinfeld center → first quantum group):** `SMFermionData`, `Z16AnomalyComputation`, `GenerationConstraint`, `DrinfeldCenterBridge`, `VecGMonoidal`, `ToricCodeCenter`, `S3CenterAnyons`, `CenterEquivalenceZ2`, `DrinfeldDoubleAlgebra`, `DrinfeldDoubleRing`, `DrinfeldEquivalence`, `WangBridge`, `ModularInvarianceConstraint`, `RokhlinBridge`, `QNumber`, `Uqsl2`, `Uqsl2Hopf`.
**Phase 5c (affine/restricted quantum groups + SU(2)_k fusion + E8/Rokhlin):** `Uqsl2Affine`, `SU2kFusion`, `SU2kSMatrix`, `RestrictedUq`, `RibbonCategory`, `E8Lattice`, `AlgebraicRokhlin`, `SpinBordism`, `VerifiedJackknife`.
**Phase 5d (tetrad gap equation + Ising/Fibonacci MTCs + polariton):** `TetradGapEquation`, `SU2kMTC`, `QSqrt2`, `QSqrt5`, `FibonacciMTC`, `Uqsl2AffineHopf`, `VerifiedStatistics`, `KerrSchild`, `CoidealEmbedding`, `RepUqFusion`, `StimulatedHawking`, `CenterFunctor`.
**Phase 5e (braided MTCs + first knot invariant):** `QCyc16`, `QCyc5`, `IsingBraiding`, `QSqrt3`, `QLevel3`, `QCyc5Ext`.
**Phase 5f (TQFT bridge + emergent-gravity bounds):** `TQFTPartition`, `FigureEightKnot`, `EmergentGravityBounds`.
**Phase 5h (chirality wall 3+1D + gauging obstruction):** `SPTClassification`, `GaugingStep`.
**Phase 5i (first rank-2 quantum group + SU(3)_k fusion):** `Uqsl3`, `Uqsl3Hopf`, `SU3kFusion`, `PolyQuotQ`, `PolyQuotOver`, `QCyc3`, `QCyc15`, `QCyc15SqrtPhi`, `SU3k2SMatrix`, `SU3k2FSymbols`.
**Phase 5j (Fermi-point → emergent gauge group):** `FermiPointTopology`.
**Phase 5k (WRT TQFT pipeline):** `TemperleyLieb`, `SurgeryPresentation`, `WRTInvariant`, `WRTComputation`.
**Phase 5l (topological quantum computation):** `JonesWenzl`, `IsingGates`, `FibonacciBraiding`, `FibonacciQutrit`, `FibonacciUniversality`, `FibonacciQutritUniversality`, `StringNet`.
**Phase 5m (generic parameterized quantum groups + Kac–Walton):** `QuantumGroupGeneric`, `QuantumGroupCoproduct`, `QuantumGroupAntipode`, `QuantumGroupHopf`, `QuantumGroupInstantiation`, `QuantumGroupMeta`, `KacWaltonFusion`.
**Phase 5n (chirality wall — anomaly inflow + gapping):** `KMatrixAnomaly`, `VillainHamiltonian`, `TPFDisentangler`, `SPTStacking`.
**Phase 5p (categorical closure — Muger + FP-dim + modularity):** `MugerCenter`, `FPDimension`, `D2Formula`.
**Phase 5q (first Ext computation over Steenrod sub-algebra):** `A1Ring`, `A1Resolution`, `A1Ext`, `ExtBordismBridge`.
**Phase 5r (change-of-rings):** `ChangeOfRings`.
**Phase 5s (chirality-wall 2+1D bridge + general modularity + instanton counting):** `FKGappedInterface`, `ModularityTheorem`, `InstantonZeroModes`; plus k=5 extensions to `SU2kFusion` / `SU2kSMatrix`; plus `CenterFunctorZ2` + `CenterFunctorZ2Equiv`.
**Phase 5t (Fermi-Hubbard geometric gate):** `FermiHubbardDimer`.
**Phase 5w (graphene Dirac-fluid platform):** `DiracFluidMetric`, `GrapheneHawking`, `GrapheneNoiseFormula`, `DiracFluidSK`, `QuasiOneDReduction`.
**Phase 5x (dark-matter classification + SFDM merger forecast + fracton DM):** `HiddenSectorClassification`, `HiddenSectorMixedCharge`, `CosmologicalConstant`, `FangGuTorsionDM`, `FractonDarkMatter`, `SFDMMergerForecast`, `DarkSectorSynthesis`.
**Phase 5y (dark-energy obstruction + vestigial-EOS closure):** `GibbsDuhemTheorem`, `QTheoryNoGoTheorem`, `DarkEnergyObstructionPrinciple`, `DESIComparison`, `CondensedMatterAnalog`, `VestigialMapping`, `VestigialEOS`, `ClassificationTableDark`; plus extensions to `VestigialGravity`, `VestigialSusceptibility`, `TetradGapEquation`.
**Phase 5z (scalar / Majorana rung on the fermionic substrate):** `MajoranaRung`, `NeutrinoMixing`, `MajoranaRungDecoupling` (plus the prior scalar-rung extensions).
**Phase 6a (linearized gravity, FLRW, GWs, BH entropy + four laws, axiom retirement):** `LinearizedEFE` (Track A W1), `FLRWDynamics` (Track A W4), `GravitationalWaves` (Track B W2), `BHEntropyMicroscopic` (Track C W3), `BHThermodynamicsFourLaws` (Track C W5), `LaplaceMethod` (W7 — retires `gaussianSaddleAsymptotic`).
**Phase 6b (cosmology — light-element abundances):** `BBN` (W1).
**Phase 6c (cosmology + holography — strong CP, EP, QEC, RT/CH):** `StrongCPTopologicalDE` (W1), `EquivalencePrinciple` (W3), `QECHolographyBridge` (W4), `RTCasiniHuertaBounds` (W5). W2 (`EWBaryogenesisChiralityWall`) outstanding.
**Phase 6d (QCD strong coupling — Track A CLOSED):** `CenterSymmetryConfinement` (W1), `ChiralSSB_QCD` (W2), `CFLChiralLagrangian` (W3).
**Phase 6f (energy conditions + curvature):** `EnergyConditions` (W3). `Curvature` (W3.1 / 6f.1) deferred behind upstream Mathlib Bonn-Massot ↔ Rothgang Levi-Civita branch.
**Phase 6e (nonlinear emergent EFE through Einstein–Cartan torsion — May 2026):** heat-kernel calibration (W1), higher-curvature Stelle (W2), nonlinear diff invariance (W3), variational nonlinear EFE + multi-channel PPN (W4), CC in emergent form (W5), Einstein–Cartan torsion + Kostelecký / Hughes–Drever bound passage (W6). See `docs/roadmaps/Phase6e_Roadmap.md` and per-paper drafts (paper39–paper43).
**Phase 6f W1–W6 (classical-GR algebraic backbone — May 2026):** `Curvature`, `EinsteinTensor`, `EnergyConditions` (= 6f W3 above), `ExactSolutions`, `ADM`, `Tetrad` — *first formalization in any proof assistant* per audit §3E. Plus `paper44_riemannian_connection` (Phase 6f W7 + W8): Lorentzian metric typeclass + Levi-Civita Christoffel uniqueness + bundle-level Riemann curvature consumer of Bonn `IsCovariantDerivativeOn`. Lifts into D3 §22.5 + I1 sidebar.
**Phase 6g (causal structure + singularity bundles + area-monotone + Kerr no-hair — May 2026):** causal structure axioms (W1), Penrose hypothesis bundle (W2), Hawking–Penrose SEC variant + counterexamples (W3), Schwarzschild area-monotone + BH-entropy bridge (W4), Cauchy-problem well-posedness predicate framework (W5; structural-Prop scope per Gate G.4 LMPP fallback), Kerr no-hair with sub-extremality (W6). Lifts into D3 §23–§27 + I1 sidebar.
**Phase 6m (dark-energy three-track closure — May 2026):** `CausalSetDarkEnergy` (Track A), `EntropicGravityDarkEnergy` (Track B — first complete-mechanism-family unanimous NO-GO), `JacobsonThermoGRDarkEnergy` (Track C — highest-survival 5+ R5; M3 EGJ f(R) Exp+ArcTanh strongest CLEARED-R5; Phase 6o W4a verdict-(B) Sakharov-extension shipped here), `DarkSectorClassificationExtension` (Wave 4 — 7-class GD taxonomy + 3-tier applicability gradient).
**Phase 6n (mathematical substrate — April–May 2026, no per-wave drafts; sourceless Lean lifts into D1/D2/D3/D4/D5/I1/I2/I3/L3):** `GloriosoLiu/Axioms` + `SecondOrderProjection`; `QuantumCrooks/SKEFTConnection` + `ReservoirCoupled` + `HigherDimensional` + `ConcreteComplex`; `CrooksAnalogHawking/LDPLinearResponse` + `HorizonDetailedBalance` + `SKEFTGallavottiCohen` (with abstract `IsLDPRateFunction` typeclass + 3 instances); `SKEFTHorizonBridge` (Sakharov ↔ horizon-Crooks at `β_H` with Verlinde-vs-Jacobson distinction); `SymTFTAudit/WittClass` + `DrinfeldCenter` (DMNO 2010 + braided strengthening) + `FreeKLinearCategory` + `FreeKLinearMonoidal` + `DeligneTensor` + `PseudoUnitary` + `CrossBridges`.
**Phase 6o (soft theorems / classical double-copy / APS-η / Schellekens / ETH refutation / Itô + LDP — May 2026, no per-wave drafts):** `SoftTheorems/Boostless` + `Carrollian` + `EmergentGraviton` + `DissipativeNoGo` + `NoiseFloorPrediction`; `KerrSchild/PetrovD` + `SingleCopy` + `WeylSpinor` + `BCJNoGo` + `PolaritonCrossBridge` (first explicit classical double-copy on analog gravity); `APSEta/Predicate` + `BECAcoustic` + `ADWHorizon` + `He3A` + `SymTFTBridge` + `RegimePartition` (first systematic substrate-side APS-η identification on a chirally-asymmetric analog Hawking horizon); `Schellekens/SpinBordism` + `AnomalyPolynomial` + `ModularInvariance` + `NiemeierLattice` + `HolomorphicVOAc24` + `Chain`; `ETH/Predicates` + `ConcreteWitness` + `RefutationTableau`; **I3 Itô + LDP substrate** — `Itô/StochasticIntegral` + `QuadraticVariation` + `Semimartingale` + `ItoIsometry` + `ItoLemma` + `Novikov` + `LDP/CramerIID` + `Sanov` + `Contraction` + `CramerLowerBound` + `Varadhan` + `LDPCompatibleSKEFT` typeclass.
**Infrastructure (cross-phase):** `ExtractDeps` (environment-walker for axiom-dependency extraction; see Pipeline Invariant #10 exception clause).

> **Note (2026-05-07):** Module-count and theorem-count totals in this document's header reflect the 2026-04-28 snapshot. Phase 6e/6f/6g/6m/6n/6o additions have *not* been propagated into the count macros at the top of this file (other agents handle that pass). The narrative additions above are the substantive update; see `SK_EFT_Hawking_Inventory.md` and `BUNDLE_READINESS_HEATMAP.md` for current authoritative counts.

---

*This document is a snapshot. For module-level details consult the [Inventory Index](../SK_EFT_Hawking_Inventory_Index.md). For the execution process consult the [Wave Execution Pipeline](WAVE_EXECUTION_PIPELINE.md). For the full module map and theorem counts consult the [Full Inventory](../SK_EFT_Hawking_Inventory.md). For predictive-scope boundaries consult [ARCHITECTURE_SCOPE.md](ARCHITECTURE_SCOPE.md).*
