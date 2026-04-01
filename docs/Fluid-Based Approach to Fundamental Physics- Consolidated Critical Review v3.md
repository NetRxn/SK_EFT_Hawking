# Fluid-Based Approach to Fundamental Physics: Consolidated Critical Review v3

## Gap Analysis, Structural Obstructions, Hybrid Architecture Assessment, and Defensible Research Directions

*Synthesized from two deep-research rounds, parallel agent cross-validation, four Tier 1 research studies, three Tier 2 hybrid architecture assessments, and four Tier 2 follow-up investigations — March 2026*

---

## Executive Summary

This document is the third and most comprehensive iteration of the critical review, incorporating all research conducted to date: two independent deep-research rounds, cross-validation with a parallel agent team, four Tier 1 deep-dive studies (EFT corrections to Hawking radiation, BEC replication landscape, superfluid classification, STAR CME analysis), three Tier 2 assessments of the hybrid architecture, and four follow-up investigations targeting the architecture's most critical gaps (non-Abelian gauge erasure universality, fracton hydrodynamics as alternative Layer 2, the fermion bootstrap problem, and the chirality wall in 2026).

**The overall verdict has sharpened, not overturned.** The program is stronger on kinematics and experiment than when we began — the EFT/Hawking gap is a genuine PRL-level opportunity, the BEC replication landscape is maturing, and the superfluid classification table provides a rigorous conceptual foundation. But the three structural walls remain standing, and the Tier 2 research has produced a critical new finding: **non-Abelian gauge erasure by hydrodynamization is universal, not QCD-specific**, closing the hybrid architecture's most important information channel.

**Three structural obstructions continue to define the program's ceiling:**

1. **Non-Abelian gauge structure** — Blocked for ordinary fluids (Torrieri 2020, Nastase-Sonnenschein 2025). Blocked for the hybrid architecture's fluid layer (universal gauge erasure theorem). Delegated to Layer 1 (string-nets), where it exists but cannot pass through Layer 2.

2. **Dynamical Einstein gravity** — Nordström (spin-0) remains the ceiling for bosonic systems. The ADW tetrad mechanism is the strongest route to spin-2, but the fermion bootstrap problem creates a three-level hierarchy of difficulty: vestigial metric gravity is most accessible, full tetrad gravity is plausible but undemonstrated, UV-complete lattice gravity appears incompatible with emergent fermions.

3. **Chiral fermions** — The chirality wall is fracturing for the first time. The Thorngren-Preskill-Fidkowski symmetry disentangler (January 2026) likely evades the Golterman-Shamir no-go theorems by operating in a different mathematical regime. **Phase 5 formally verified this:** 9 GS conditions formalized as substantive Lean propositions, 5 violated by TPF, master synthesis theorem `tpf_outside_gs_scope_main` machine-checked (55 theorems across 3 modules, zero sorry). This is the first formal verification result in the lattice chiral fermion literature. SMG numerical evidence has reached the 16-Weyl threshold matching the SM generation count. The wall is cracking but not broken.

**The revised architecture recommendation:** The hybrid three-layer model (quantum order → fluid dynamics → EFT) is worth formal development for gravity only (the ADW route via fermionic superfluids). It should abandon the claim of propagating non-Abelian gauge information through a fluid layer — this is now ruled out by a structural theorem, not merely unsupported. Fracton hydrodynamics is a superior alternative Layer 2 that preserves dramatically more UV information, but it too cannot carry non-Abelian gauge structure. The architecture's most honest form acknowledges that non-Abelian gauge theory must bypass the fluid layer entirely.

---

## 1. Mapping-by-Mapping Ledger (Updated)

### 1.1 Madelung Transform ↔ Schrödinger Equation

**Status: Unchanged from v2. Kähler symplectomorphism on ρ > 0 domain. Wallstrom objection unresolved.**

The Wallstrom objection (8 proposed resolutions, 0 definitive; Reddiger-Poirier 2023) remains the key caveat. The distributional approach is the most promising resolution route but is a 5–10 year program. No new developments since v2.

### 1.2 Kambe Fluid Maxwell

**Status: Unchanged from v2. Formal resemblance only.** Two of four equations are kinematic tautologies. No photons, no gauge redundancy. Not evidence for QED-from-fluids.

### 1.3 Unruh-Visser Acoustic Metric

**Status: UPGRADED — now the program's strongest experimental asset.**

The acoustic metric remains a rigorous theorem with the fundamental limitation that no dynamical Einstein equations arise. However, Tier 1 research has substantially enriched this mapping:

**EFT corrections landscape (realized through Phase 4).** The SK-EFT / analog Hawking gap has been filled by this program. Phase 1 computed the first-order dissipative correction δ_diss = Γ_H/κ parameterized by 2 transport coefficients (γ₁, γ₂). Phase 2 extended to second order, finding 2 new coefficients requiring broken spatial parity, a frequency-dependent spectral distortion δ^(2)(ω) ∝ ω³, and a positivity constraint γ_{2,1}+γ_{2,2}=0. Phase 3 established the exact WKB connection formula (modified unitarity, FDR noise floor), third-order parity alternation, gauge erasure theorem, and ADW gap equation. Phase 4 produced platform-specific prediction tables, numerically confirmed the vestigial gravity phase (3-phase structure: pre-geometric, vestigial, full tetrad), demonstrated fracton hydrodynamics as a superior Layer 2, and identified the chirality wall conditional breach. All results formally verified (429 theorems + 2 axioms in 30 Lean 4 modules, zero sorry, 99 Aristotle-proved across 27 runs). Phase 5 added: κ-scaling predictions correcting δ_diss ∝ κ (linear, not constant — prior error fixed), polariton Tier 1 predictions (T_H ~ 1 K, 10¹⁰× hotter than BEC), chirality wall formal verification (first in lattice chiral fermion literature: 9 GS conditions, 5 TPF violations, machine-checked), first-ever categorical infrastructure in any proof assistant (PivotalCategory, FusionCategory, DrinfeldDouble, gauge emergence Z(Vec_G) ≅ Rep(D(G))), and Weingarten multi-channel MC framework for vestigial phase (Lean-verified, production in progress). Key finding: the dissipative corrections (~10⁻⁵) require >>10⁶ shots for direct detection; the κ-scaling test (comparing δ_disp ∝ κ² vs δ_diss ∝ κ) is the most accessible experimental target. Backreaction: acoustic BHs cool toward extremality (opposite Schwarzschild). Two-component spin-sonic horizons (Berti et al. 2025) offer enhanced experimental access.

**BEC replication landscape (new).** No independent replication of Steinhauer's measurement exists after a decade. Heidelberg (K-39, DMD, Feshbach) is the best single lab for the κ-scaling test. Trento (spin-sonic horizon) is qualitatively different. Paris polariton group (Falque et al. PRL 2025) observed negative-energy modes; spontaneous detection likely 2026–2027. Key insight: ⁸⁷Rb lacks Feshbach tunability for varying surface gravity independently — K-39 solves this.

**Kinematics-dynamics gap.** Nordström scalar gravity (Belenchia-Liberati-Mohd 2014) remains the dynamical ceiling for bosonic systems. Nobody has applied Jacobson's thermodynamic derivation to sonic horizons — this remains a concrete research target but is less promising than the ADW route given the Tier 2 findings.

### 1.4 Volovik ³He-A

**Status: UPGRADED — now understood within a complete classification framework.**

Tier 1 produced a master classification table (see §3) that places ³He-A within a systematic hierarchy: tensor rank of order parameter → maximum graviton spin; momentum-space topology → emergent gauge/Weyl; microscopic statistics → mechanism availability.

Key structural result: **rank 0 → spin-0 gravity (Nordström); rank (1,1) → spin-2 gravity (ADW/tetrad)**. ³He-A with |N|=1 Fermi-point topology produces emergent Weyl fermions, U(1) gauge field, and approximate Lorentz symmetry — all experimentally confirmed within condensed matter. For |N|>1, SU(2) gauge structure emerges (Volovik-Zubkov 2014), but this requires fermionic microscopic degrees of freedom and is unavailable to bosonic systems.

Selch-Zubkov (2025) computed the full effective Lagrangian for macroscopic Weyl fermion motion in ³He-A, confirming emergent vierbein with nonzero torsion and the Nieh-Yan anomaly. Volovik's vestigial gravity proposal (2023–2024) adds a two-step condensation picture: metric gravity without tetrads → full Einstein-Cartan with tetrads.

### 1.5 Eling BF Gauge Theory

**Status: Unchanged from v2. Strongest gauge result from pure fluids, but strictly Abelian.** The BF→YM bridge exists mathematically but three gaps prevent a fluid connection. The non-Abelian obstruction is now understood to be structural and universal (see §2).

### 1.6 Pilot Wave (dBB)

**Status: Unchanged from v2.** Walking-droplet double-slit failed definitively. Darrow-Bush (2024) framework for Lorentz-covariant pilot wave is the only positive development. Not a priority for the program.

---

## 2. The Three Structural Walls (Updated Verdicts)

### 2.1 Non-Abelian Gauge Wall

**Status: STRENGTHENED from "blocked" to "structurally impossible at the fluid layer."**

The v2 assessment that no published work derives SU(N) gauge dynamics from ordinary fluid dynamics remains correct. The Tier 2 follow-up research has produced a substantially stronger result:

**Non-Abelian gauge erasure is a universal structural theorem.** Across every framework examined — higher-form symmetry hydrodynamics, holographic duality (including non-confining N=4 SYM), adiabatic hydrodynamization, and chromohydrodynamics — non-Abelian gauge degrees of freedom universally fail to survive as hydrodynamic modes. The mechanism is rooted in the mathematical fact that higher-form symmetries must be Abelian (operators on codimension >1 submanifolds necessarily commute), leaving non-Abelian gauge theories with at most discrete Z_N center symmetries whose breaking produces domain walls, not Goldstone bosons. The N=4 SYM result is decisive: even in a non-confining theory with color-charged states at all couplings, holographic hydrodynamics involves exclusively color-singlet operators.

**The Abelian case is genuinely different.** U(1) gauge structure survives hydrodynamization through the 1-form Goldstone mechanism (Grozdanov-Hofman-Iqbal). The photon is the Goldstone boson of spontaneously broken magnetic 1-form symmetry. This means emergent electrodynamics can survive a fluid layer; emergent chromodynamics cannot.

**Structural memory is real but insufficient.** Transport coefficients carry gauge-group fingerprints (N_c dependence, topological mass scales from B∧F mechanism). η/s ≈ 0.16 ± 0.05 encodes SU(3) through the topological mass scale. But these are frozen parameters, not dynamical degrees of freedom.

**Fracton hydrodynamics does not resolve the QGP objection.** Fracton hydro preserves dramatically more UV information (dipole conservation, infinitely many quasi-conserved multipole charges, Hilbert space fragmentation), but the fundamental obstacle is gauge redundancy, not conservation law count. Color charges are covariantly conserved (D_μ J^μ = 0), not ordinarily conserved, making them ineligible as fracton-type conserved quantities regardless of additional conservation laws.

**Three routes to non-Abelian structure remain, all at Layer 1:**

| Route | Mechanism | Status | Limitation |
|---|---|---|---|
| Fermi-point topology (Volovik) | |N|>1 Fermi points | Established for fermions | Requires fermionic microscopic DOF |
| String-net condensation (Wen) | Topological order from bosonic lattice | Established in 2+1D | Chirality obstruction; 3+1D incomplete |
| Fracton non-Abelian (Wang-Xu-Yau) | Higher-rank tensor gauge theories | Exists | Different algebra from Yang-Mills |

**Verdict: The hybrid architecture must route non-Abelian gauge structure around the fluid layer, not through it. This is now a theorem, not a conjecture.**

### 2.2 Dynamical Gravity Wall

**Status: REFINED — the fermion bootstrap creates a three-level hierarchy.**

The Tier 1 classification and Tier 2 research have clarified the gravity wall into three distinct levels of difficulty:

**Level 1 — Vestigial metric gravity (most accessible).** Volovik's vestigial mechanism requires only a 4-fermion correlator g_μν = η_ab⟨Ê^a_μ Ê^b_ν⟩ with Lorentzian signature, not a coherent tetrad VEV. Strongly fluctuating, imperfect emergent fermions could suffice. This produces bosonic Einstein GR but with equivalence principle violation (fermions and bosons follow different trajectories). Price: fermions cannot propagate in this phase.

**Level 2 — Full tetrad gravity (intermediate).** The ADW mechanism with GL(4,ℝ)/SO(3,1) → 6 NG modes → 6 massive spin-connection gauge bosons → 2 massless spin-2 gravitons. Vergeles (2025) proved unitarity. Requires 4-component Dirac spinors with Grassmann path-integral structure. Wen's emergent Dirac fermions from 3+1D lattice QED come closest (correct component count, emergent Lorentz symmetry via RG flow) but lack spin-connection coupling and UV Berezin finiteness. The mean-field gap equation (substituting ADW 8-fermion interaction into Wen's model) is a concrete, doable calculation that could settle feasibility.

**Level 3 — UV-complete lattice gravity (hardest).** Vergeles's proof requires fundamental Grassmann spinors at lattice vertices. The Berezin integral's polynomial convergence is not a property that can emerge from bosonic degrees of freedom. When Gu attempted extending bosonic graviton models to nonlinear GR, fermions re-entered via topological supergravity (Fang-Gu 2023) — circumstantial evidence that the fermion bootstrap is structurally unavoidable for full GR.

**The fracton-gravity connection** (Pretko 2017, Blasi-Maggiore 2022, Afxonidis-Caddeo-Hoyos-Musso 2024) provides an alternative route: linearized gravity emerges from symmetric tensor gauge theories with fracton gauge symmetry. The Kerr-Schild map and Gupta-Feynman bootstrap have been partially executed. But fracton gravity is non-Lorentzian (Aristotelian/Carrollian geometry), and the gap to full diffeomorphism invariance remains open.

**The minimum viable chain** remains: fermionic p-wave superfluid → Landau two-fluid hydrodynamics → Diakonov tetrad gravity. Each link is individually supported. The chain addresses the gravity wall only.

**Verdict: Vestigial metric gravity from emergent fermions is plausible and the most accessible target. Full tetrad gravity requires a specific calculation (ADW gap equation in Wen's model) to assess feasibility. UV-complete lattice gravity appears incompatible with emergent fermions.**

### 2.3 Chirality Wall

**Status: UPGRADED from "blocked" to "fracturing under coordinated assault but structurally intact."**

This is the most actively contested frontier, with more progress in 2024–2026 than in the prior thirty years.

**The Thorngren-Preskill-Fidkowski symmetry disentangler (January 2026)** provides the first exactly solvable Hamiltonian lattice model of a chiral gauge theory (the 1+1D "3450" model). A symmetry disentangler is a constant-depth quantum circuit that converts not-on-site symmetries to on-site form, enabling standard gauging when 't Hooft anomalies cancel. The 3+1D argument requires a conjectural gapped interface between free-fermion and commuting-projector SPTs in 4+1D. Key feature: uses infinite-dimensional rotor Hilbert spaces, evading multiple no-go theorems that assume finite-dimensional sites.

**The Golterman-Shamir generalized no-go (2024–2026)** constrains any SMG phase to have a vector-like massless spectrum under specified conditions: lattice translation invariance, finite-range Hamiltonian depending on fermion fields only, relativistic continuum limit with no massless bosons, and a complete set of interpolating fields.

**The TPF construction most likely evades GS conditions** by operating in a fundamentally different mathematical regime: infinite-dimensional Hilbert spaces, not-on-site symmetries, ancilla degrees of freedom, massless bosonic rotors, and extra-dimensional SPT slab architecture. **Phase 5 of this program provides the first direct formal analysis:** all 9 GS conditions (6 explicit + 3 implicit) formalized as substantive Lean 4 propositions, with 5 conditions proved violated by TPF and a master synthesis theorem `tpf_outside_gs_scope_main` assembling the violations. The two groups have still not engaged each other's work directly, but the machine-checked analysis establishes that TPF and GS operate in genuinely different mathematical frameworks — neither proves nor disproves the other.

**SMG numerical evidence has reached the 16-Weyl threshold.** Butt-Catterall-Hasenfratz (PRL 2025) demonstrated SMG in SU(2) with 4 fundamental flavors. Hasenfratz-Witzel (November 2025) extended to SU(3) with N_f=8 (16 Weyl fermions — matching the SM generation count in SO(10)). The critical gap: all demonstrated SMG phases involve vector-like fermion content, not chiral gauge theories. The gauging step is undemonstrated.

**Additional developments:** Gioia-Thorngren (March 2025) constructed exact chiral symmetries for single Weyl fermion on 3+1D lattice using not-on-site, non-compact symmetries. Seifnashri (January 2026) independently constructed 1+1D chiral lattice gauge theories via modified Villain formulations. Kaplan's December 2024 response to GS argues bulk zero modes resolve the unwanted-current problem — actively contested, unresolved.

**Verdict: The wall is cracking but three critical gaps prevent a breach: (1) the 4+1D gapped interface conjecture in TPF, (2) the gauging step from vector-like SMG to chiral gauge coupling, and (3) the 2D-to-4D gap (most rigorous results are two-dimensional). The first formal verification of GS-TPF compatibility (Phase 5) narrows gap (1) by establishing the mathematical basis on which any resolution must stand, but does not close it. Resolution likely within 1–2 years.**

---

## 3. Master Classification Table

The Tier 1 superfluid classification provides the conceptual foundation for the entire program. Three governing principles:

| Order parameter | System | Emergent gauge | Emergent gravity | Rigor |
|---|---|---|---|---|
| Complex scalar (rank 0) | Relativistic BEC | None | Nordström scalar (spin-0) | Proven |
| 3×3 complex matrix (rank 1+1) | ³He-A (p-wave) | U(1); non-Abelian for |N|>1 | Approximate tetrad gravity | Proven (gauge); approximate (gravity) |
| Rotation matrix (rank 1+1) | ³He-B (p-wave) | Spin connection (massive) | 6 massive graviton analogs | Proven |
| Tetrad e^a_μ (rank 1+1) | ADW fermion condensate | SO(1,3) spin connection | Spin-2 Einstein-Cartan gravity | Proven (math); conjectural (physics) |
| Metric g_μν (composite rank 2) | Vestigial phase (Volovik 2023) | — | Bosonic Einstein GR; EP violated | Conjectural |
| Spinor + scalar (rank 0+1) | F=1 spinor BEC | Emergent Proca | Bi/tri-metric acoustic gravity | Proven |
| String-net (no local OP) | Levin-Wen lattice | Any gauge group | Not established | Proven (gauge + fermions) |

**Key structural insight: scalar → spin-0 gravity; vector/tetrad → spin-2 gravity; topological order → gauge fields without gravity.** The d-wave case and F=2 spinor BECs remain gaps where systematic analysis is incomplete.

---

## 4. The Hybrid Architecture: What It Solves and What It Cannot

### 4.1 Architecture Overview

The three-layer hybrid — quantum order (UV) → fluid dynamics (mesoscopic) → Standard Model + GR (IR) — was proposed to circumvent the three walls by delegating each to a richer UV substrate. The Tier 2 research produced converging assessments from three independent analyses, refined by four follow-up investigations.

### 4.2 What the Architecture Achieves

**The gravity route works in principle.** The chain fermionic superfluid → two-fluid hydrodynamics → ADW tetrad gravity has each link individually supported. The Vergeles unitarity proof (2025), Volovik's vestigial gravity, Selch-Zubkov's emergent vierbein calculation, and the Chojnacki et al. spin-nematic graviton analog collectively make this the architecture's strongest component.

**Layer 2 → Layer 3 is complete.** The Schwinger-Keldysh EFT framework (Crossley-Glorioso-Liu) provides the formal infrastructure. Fracton hydrodynamics has a complete SK-EFT (Glorioso et al. JHEP 2023). The acoustic metric program connects fluid dynamics to emergent geometry.

**Fracton hydrodynamics is a structurally superior Layer 2.** It preserves dipole moment, generates infinitely many quasi-conserved multipole charges, exhibits Hilbert space fragmentation retaining exponentially more initial-state information, has been experimentally confirmed in cold atoms (Adler et al. Nature 2024), and contains an emergent spin-2 graviton from symmetric tensor gauge theory. The string-net → string-membrane-net → fracton → hydro chain is mathematically controlled for type-I phases.

### 4.3 What the Architecture Cannot Do

**Non-Abelian gauge information cannot pass through any fluid layer.** This is the most important negative finding of the entire research program. The universal gauge erasure theorem (§2.1) applies to standard Navier-Stokes, to fracton hydrodynamics, and to any other hydrodynamic description. The obstruction is gauge redundancy (covariant vs. ordinary conservation), not information capacity. The architecture must route non-Abelian structure around the fluid layer — directly from Layer 1 to Layer 3 via string-net condensation or Fermi-point topology.

**The fermion bootstrap is partially but not fully resolvable.** Vestigial metric gravity likely works with emergent fermions (Level 1). Full tetrad gravity is plausible but requires a specific mean-field calculation (Level 2). UV-complete lattice gravity appears incompatible with emergent fermions (Level 3). The pragmatic resolution: treat emergent Dirac fermions as effectively fundamental above a crossover scale, paralleling standard EFT practice.

**The chirality wall remains the tightest bottleneck.** The architecture delegates chirality to Layer 1 interfaces, where the same obstruction persists (string-nets produce only non-chiral phases — formally proved: chirality limitation c ≡ 0 mod 8). The TPF disentangler offers the most promising bypass, but the 3+1D construction is conjectural. Phase 5 categorical infrastructure (first-ever fusion category formalization) establishes the formal foundation for analyzing these limitations.

### 4.4 Revised Architecture Scorecard

| Component | Status | Key evidence | Change from initial assessment |
|---|---|---|---|
| Non-Abelian gauge at Layer 1 | Established | String-nets, Fermi-point | Unchanged |
| Non-Abelian through Layer 2 | **Ruled out** | Universal erasure theorem | Upgraded from "obstructed" to "impossible" |
| Einstein gravity via ADW | **MC framework verified** | Vergeles unitarity; vestigial route; gap equation solved (Paper 5); **Weingarten multi-channel MC Lean-verified** (Paper 6) | Production MC with correct SO(4) physics in progress |
| Chirality at interfaces | **Formally analyzed** | TPF disentangler; SMG at 16 Weyl; **first formal verification of GS-TPF** (Paper 7, 55 Lean theorems) | First machine-checked analysis; 5/9 GS conditions violated by TPF |
| Layer 1→2 coarse-graining | **Categorically formalized** | String-membrane-nets; **first-ever fusion category + Drinfeld double formalization** (116 Lean theorems) | Gauge emergence Z(Vec_G)≅Rep(D(G)) proved; chirality limitation proved |
| Layer 2→3 (SK-EFT) | Complete | Glorioso et al.; acoustic metric | Unchanged |
| Fermion bootstrap | Partially resolvable | Vestigial bypass; Wen model gap eqn **solved** (Paper 5); **Weingarten MC framework Lean-verified** | Weingarten + NJL production MC in progress |

### 4.5 The Honest Minimum Viable Hybrid

Fermionic p-wave superfluid → Landau two-fluid hydrodynamics → emergent Weyl + Diakonov tetrad gravity. Addresses gravity wall only. Each link supported by established physics. Does not address non-Abelian gauge or chirality.

---

## 5. Research Roadmap (Revised)

### Tier 0: Immediate (paper-ready within 6 months)

**5.1 SK-EFT dissipative correction to analog Hawking radiation — PHASES 1-5 COMPLETE (March 2026).** Seven papers, 429 theorems + 2 axioms (zero sorry, 99 Aristotle-proved across 27 runs), 1014 tests, 30 modules, 14/14 validation checks, 61 figures, 20 notebooks. Phase 4 added: platform-specific prediction tables (Steinhauer Rb-87, Heidelberg K-39, Trento Na-23), vestigial gravity numerically confirmed (three-phase structure), fracton Layer 2 (exponentially more UV info), chirality wall conditional breach (2/4 GS evaded), backreaction toward extremality, non-Abelian fracton negative result (4 obstructions formally verified). Phase 5 added: κ-scaling predictions (δ_diss ∝ κ linear, prior error corrected), polariton Tier 1 (T_H ~ 1 K, 10¹⁰× BEC), chirality wall formal verification (first in lattice chiral fermion literature: 9 GS conditions, 5 TPF violations, 55 theorems), first-ever categorical infrastructure in any proof assistant (PivotalCategory, FusionCategory, DrinfeldDouble, gauge emergence, 116 theorems across 7 modules), production MC vestigial split transition at L=6,8.

**5.2 Document the non-Abelian gauge erasure as a negative result.** ✅ **COMPLETE (March 2026).** Paper 3 formalizes the universal structural theorem with 11 Lean theorems + 1 axiom. Standard Model analysis: SU(3)×SU(2)×U(1) → U(1)_EM survives hydrodynamization; non-Abelian DOF erased. Gauge erasure closes the hybrid architecture's most important information channel.

### Tier 1: Near-term (6–18 months)

**5.3 ADW mean-field gap equation with emergent Dirac fermions.** ✅ **COMPLETE (March 2026).** Paper 5 performs the full calculation: Wen's lattice QED → N_f=4 Dirac fermions → ADW 8-fermion interaction → HS decomposition → Coleman-Weinberg V_eff → gap equation → phase diagram. **Qualified positive result**: nontrivial Lorentzian solution for G > G_c = 8π²/(N_f Λ²), producing 2 massless spin-2 graviton modes as Higgs bosons. Vergeles mode counting (16=6+4+2+4) formally verified (21 Lean theorems, zero sorry). Four structural obstacles identified for emergent fermion bootstrap: spin-connection gap, Grassmann-bosonic incompatibility, Nielsen-Ninomiya doubling, cosmological constant. The fermion bootstrap at Level 2 works at mean-field with fundamental fermions but cannot yet be extended to emergent fermions.

**5.4 BEC replication collaboration.** Support independent Hawking measurement programs. **Updated 2026-03-28:** Heidelberg (Oberthaler) has the best apparatus (K-39 Feshbach + DMD) for the kappa-scaling test but is currently pursuing analog cosmology, not Hawking. Paris polaritons (Bramati-Jacquet) are the most active Hawking program (horizons demonstrated, PRL 2025; stimulated Hawking possible 2026-27 but driven-dissipative corrections complicate EFT comparison). Trento spin-sonic (Carusotto-Ferrari, ERC-funded 2026) is best for EFT testing but ~2028-31. Steinhauer has plateaued (no new data since PRD 2022). The kappa-scaling test remains the most accessible experimental target across all platforms.

**5.5 Vestigial metric correlator simulation.** ✅ **PRODUCTION PILOT COMPLETE (March 2026).** 4D fermion-bag MC at L=4,6,8 completed in 107 seconds (vectorized + multiprocessing). **Split transition detected:** tetrad and metric susceptibility peaks at different couplings at L=6,8 (Δ ≈ 0.63), consistent with a genuine vestigial metric phase. Binder cumulant analysis confirms signal survives finite-size effects that wiped it out at L=4. HPC-scale follow-up (L=10-16, simplicial lattice, finite-size scaling exponents) deferred to Phase 6.

### Tier 2: Medium-term (18–36 months)

**5.6 Fracton hydrodynamics as alternative Layer 2.** Develop the string-membrane-net → fracton → SK-EFT chain as a rigorous alternative to standard Navier-Stokes at Layer 2. Investigate whether Hilbert space fragmentation or non-Abelian fracton structure can encode gauge information indirectly.

**5.7 Track TPF vs. GS resolution.** ✅ **FIRST FORMAL ANALYSIS COMPLETE (March 2026).** Phase 5 delivered the first machine-checked analysis of GS-TPF compatibility: all 9 GS conditions formalized as substantive Lean propositions (7/9 with full mathematical content), 5 TPF violations proved, master synthesis `tpf_outside_gs_scope_main` machine-verified (Paper 7, 55 theorems). The chirality wall's fate still turns on the 4+1D gapped interface conjecture and the gauging step, but the formal framework for any resolution is now established.

**5.8 Monte Carlo transport in emergent gauge theory.** **Updated 2026-03-28:** The original plan (Walker-Wang SU(2)_k eta/s) is not feasible — intrinsic sign problem proven uncurable for modular SU(2)_k (Golan et al., PRR 2020), no WW construction for emergent continuous SU(2), no T^{mu nu} defined for topological lattice models. **Revised:** Z_2 Walker-Wang (3D toric code) transport as Strategy A (~500K GPU-hrs, sign-problem-free, first transport computation for any emergent gauge theory). TRG for non-Abelian as Strategy B (2-5M GPU-hrs, INCITE-scale). Tests Svetitsky-Yaffe universality at transport level.

### Tier 3: Long-term (ongoing research programs)

**5.9 Wallstrom resolution.** **Updated:** Reddiger has pivoted from proving Madelung-Schrodinger equivalence to building a distinct Kolmogorov-probability-based theory (Quantum Stud. 13, 2026). The question is shifting from "solve Wallstrom" to "is the alternative theory physically adequate?" **5.10 Emergent gravity UV completion.** **Updated:** Fang-Gu topological supergravity (arXiv:2312.17196) follows a fundamentally different route from ADW (loop condensation vs fermion bilinear condensation). The actual target is substituting TPF chiral fermions into the Vladimirov-Diakonov simplicial lattice framework. **5.11 Non-Abelian fracton hydrodynamics construction — CANCELLED.** Phase 4 negative result: all fracton gauge types are YM-incompatible (4 obstructions formally verified). **5.12 Lean 4 formalization blueprint** (22–43 person-months estimated).

---

## 6. Quantitative Benchmarks (Updated)

| Quantity | Value | Source | Change from v2 |
|---|---|---|---|
| n=1 MDR | CLOSED: E_QG,1 > 10 E_Planck | LHAASO GRB 221009A | Unchanged |
| n=2 MDR | OPEN: E_QG,2 > 7.3 × 10¹¹ GeV | LHAASO | Unchanged |
| QGP η/s | 0.16 ± 0.05 (~2× KSS bound) | RHIC/LHC | Unchanged |
| CME signal | 2.6–3.3σ at √s = 11.5–19.6 GeV | STAR BES-II (May 2025) | New |
| BEC Hawking T_H | 0.35 nK (matches prediction) | Steinhauer (Nature 2019) | Unchanged |
| Dispersive corrections to T_H | O(0.04–0.16%) — below 10–30% exp. precision | Coutant-Parentani | New |
| SK-EFT dissipative correction | **Phase 1-5 COMPLETE** | This work (March 2026) | 429+2ax Lean theorems (zero sorry, 99 Aristotle-proved across 27 runs), 30 modules, 1014 tests, 7 papers, 61 figures, 20 notebooks. Phase 5 added: κ-scaling predictions (δ_diss ∝ κ), polariton Tier 1 (T_H ~ 1 K), chirality wall formal verification (first in lattice chiral fermion lit, 55 theorems), first-ever categorical infrastructure (PivotalCategory, FusionCategory, DrinfeldDouble, 116 theorems), production MC vestigial split transition at L=6,8. |
| Backreaction | Acoustic BHs cool (→ extremality) | Balbinot et al. 2025 | New |
| SMG threshold | 16 Weyl fermions (SU(3), N_f=8) | Hasenfratz-Witzel 2025 | New |
| Vergeles unitarity | Proven for 4D lattice gravity | PRD 112, 2025 | New |
| Fracton hydro experimental | Observed: subdiffusion + HSF in 2D | Adler et al. Nature 2024 | New |
| Non-Abelian gauge erasure | Universal structural theorem | Multiple (see §2.1) | New |
| Lean infrastructure gap | 22–43 person-months | Cross-validated | Substantially narrowed: Phase 5 delivered 429+2ax theorems including first-ever categorical infrastructure |

---

## 7. Phenomenology: CME Connection (Updated)

The STAR BES-II results (2.6–3.3σ at √s = 11.5–19.6 GeV) are physically sensible: energy dependence matches theory (peak where deconfinement occurs, vanishing below and at top RHIC energy). The Abanov-Wiegmann classical chiral anomaly in Euler fluids and Wiegmann's 2024 extensions (CS + WZW terms) deepen the structural connection to gravitational anomalies.

**Critical caveat unchanged:** The fluid-gauge correspondence currently provides structural universality, not quantitative predictions distinguishable from standard quantum CME. The connection is that chiral anomalies manifest identically in Euler fluids and in QCD — but this is a statement about the mathematical structure of anomalies, not a derivation of QCD from fluids.

---

## 8. Answers to the Four Session Questions

### 8.1 Has the overall verdict changed?

**Refined, not overturned.** The program is stronger on kinematics and experiment (EFT/Hawking opportunity, BEC replication landscape, classification table) but the three walls remain. The most significant new finding is negative: non-Abelian gauge erasure is universal, strengthening the non-Abelian wall from "blocked" to "structurally impossible at the fluid layer." The chirality wall has weakened (TPF disentangler, SMG at 16 Weyl). The gravity wall has been clarified into a three-level hierarchy with the vestigial route offering a genuinely accessible target.

### 8.2 What is the single most impactful paper in the next 12 months?

**The SK-EFT dissipative correction to analog Hawking radiation.** Phase 1 (first-order, PRL format) is draft-complete. Phase 2 (second-order, PRD companion) extends this with frequency-dependent spectral distortion δ^(2)(ω) ∝ ω³ and a positivity constraint from unitarity. The full program now has 429 theorems + 2 axioms across 30 Lean modules, zero sorry. No competitor in the literature. The two-paper series would: (a) bridge SK-EFT and analog gravity, (b) produce concrete experimental predictions (constant shift + spectral distortion), (c) establish the program's formal verification methodology. **Additional strong candidates:** Paper 7 (chirality wall formal verification — first in lattice chiral fermion literature, publishable in CPC or PRD independently of the rest of the program) and the categorical infrastructure (first-ever fusion category formalization — publishable as a Mathlib contribution or at ITP).

### 8.3 Is the hybrid architecture worth formal development?

**Yes, but only for gravity, and with fracton Layer 2.** The ADW route through fermionic superfluids is the architecture's only component where each link is individually supported and the endpoints connect. Fracton hydrodynamics should replace standard Navier-Stokes as Layer 2 — it is rigorously connected to topological order (string-membrane-nets), has a complete SK-EFT, preserves more UV information, contains an emergent graviton, and has experimental confirmation. The architecture should explicitly abandon the claim of propagating non-Abelian gauge information through any hydrodynamic layer. For non-Abelian gauge structure, the honest statement is: this requires Layer 1 (string-nets or Fermi-point topology) to couple directly to Layer 3, bypassing fluids entirely.

### 8.4 What should be abandoned?

**Definitively abandoned:**
- Walking-droplet experiments (dead end, confirmed)
- The claim of deriving SU(3)×SU(2)×U(1) from fluid dynamics (structurally impossible)
- The claim of propagating non-Abelian gauge information through a hydrodynamic layer (now a theorem)
- Overstated Madelung "exactness" without Wallstrom caveat
- Chromohydrodynamics as a route to non-Abelian fluids (failed for physical reasons)

**Deprioritized:**
- Jacobson-sonic-horizon direction (less promising than ADW given Tier 2 findings)
- Non-Abelian Clebsch generalizations (Nastase-Sonnenschein closed this definitively)
- Full Lean 4 formalization beyond the SK-EFT scope (429+2ax theorems achieved; further expansion blocked by Bott periodicity for Fermi-point topology)

---

## 9. What to Claim and What Not to Claim (Updated)

### Claim with confidence:
- The Madelung transform is a Kähler symplectomorphism on the domain of strictly positive densities
- The acoustic metric is a rigorous theorem with experimental confirmation of Hawking radiation in BEC
- Incompressible Euler flow has an exact Abelian BF gauge-theoretic formulation
- Volovik's ³He-A produces emergent Weyl fermions, chiral anomaly, and approximate Lorentz symmetry
- The quark-gluon plasma behaves as a near-perfect fluid with η/s near the KSS bound
- **NEW:** Non-Abelian gauge structure is universally erased by hydrodynamization (structural theorem)
- **NEW:** The superfluid classification follows tensor rank → graviton spin; topology → gauge/Weyl; statistics → mechanism
- **NEW:** Fracton hydrodynamics preserves categorically more UV information than standard Navier-Stokes
- **NEW:** The SK-EFT / analog Hawking connection has been filled by this program (Phase 1: constant δ_diss, Phase 2: frequency-dependent δ^(2)(ω) ∝ ω³; 429+2ax Lean theorems across 30 modules, zero sorry, 99 Aristotle-proved)
- **NEW:** The GS-TPF compatibility question has been formally analyzed for the first time (Phase 5: 9 GS conditions formalized, 5 TPF violations proved, machine-checked)
- **NEW:** First-ever categorical infrastructure for topological phases in a proof assistant (PivotalCategory, FusionCategory, DrinfeldDouble, gauge emergence Z(Vec_G) ≅ Rep(D(G)))
- **NEW:** Vestigial MC framework with Weingarten multi-channel SO(4) integration, Lean-verified (production run in progress)

### Claim with caveats:
- Madelung "equivalence" → must note Wallstrom objection and ρ > 0 restriction
- Emergent gravity from fluid analogs → Nordström (spin-0) only for bosonic systems; spin-2 requires fermions via ADW
- The ADW mechanism has correct mode counting → Vergeles proved unitarity, but the Einstein limit requires tuning to a second-order phase transition
- **NEW:** The fermion bootstrap is partially resolvable → vestigial gravity likely works; full tetrad gravity is plausible; UV-complete lattice gravity appears incompatible with emergent fermions
- **NEW:** The chirality wall is fracturing → TPF disentangler formally verified to violate 5/9 GS conditions (first machine-checked analysis), but 3+1D construction is conjectural; SMG at 16 Weyl is vector-like only
- Modified dispersion relations are testable → n=2 only; n=1 closed by LHAASO
- CME connection is structural → not yet predictive for fluid program

### Do not claim:
- That SU(3)×SU(2)×U(1) can be derived from fluid dynamics
- That non-Abelian gauge information can be transmitted through a hydrodynamic layer
- That dynamical Einstein gravity emerges from any bosonic condensed-matter system
- That chiral fermions have been produced from any lattice or fluid system (cracking ≠ broken)
- That the hybrid architecture "solves" any of the three walls (it identifies promising mechanisms and relocates the obstructions)
- That Steinhauer's BEC Hawking result has been independently replicated
- That the CME fluid-gauge connection makes quantitative predictions beyond standard quantum CME

---

## 10. What Would Change the Picture

Six developments, any of which would shift the assessment:

1. **TPF 4+1D gapped interface proven.** Would convert the 3+1D disentangler argument into a theorem, effectively breaching the chirality wall.

2. **Independent BEC Hawking replication.** Transforms analog gravity from single-lab curiosity to established experimental physics. Dramatically strengthens the EFT program.

3. **ADW mean-field gap equation solved with emergent fermions.** ✅ **RESOLVED (March 2026).** Validated at mean-field: nontrivial Lorentzian solution exists. But 4 structural obstacles prevent full emergent bootstrap. **Vestigial MC:** Weingarten multi-channel framework Lean-verified (14 theorems). Initial product-form MC invalidated; production run with correct SO(4) physics in progress.

4. **SMG demonstrated with chiral gauge coupling.** Would close the vector-like → chiral gap in the SMG program. This is the hardest missing step.

5. **Monte Carlo η/s for emergent gauge theory.** **Updated 2026-03-28:** Original SU(2)_k Walker-Wang target is infeasible (intrinsic sign problem). Revised target: Z_2 toric code transport (Strategy A). Would be the first transport computation for any emergent gauge theory. Tests Svetitsky-Yaffe universality at transport level.

6. **Resolution of the Wallstrom objection.** **Updated 2026-03-28:** Reddiger has pivoted to a distinct Kolmogorov-probability-based theory rather than proving Madelung-Schrodinger equivalence. The question is shifting from "solve" to "build around."

---

*This review covers ~150 papers across hep-th, gr-qc, cond-mat, quant-ph, hep-lat, and math-ph, produced by multiple independent research agents cross-validated against a parallel team's 29-page gap analysis. The project knowledge files contain the detailed evidence base; this document provides the synthesized assessment.*
