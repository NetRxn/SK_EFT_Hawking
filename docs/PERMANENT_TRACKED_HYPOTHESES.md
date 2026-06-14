# Permanent Tracked Hypotheses

> **AUTO-GENERATED — DO NOT EDIT BY HAND.** This document is rendered from `HYPOTHESIS_REGISTRY` in `src/core/constants.py` by `scripts/render_tracked_hypotheses.py` (Substrate Integrity Gates W3, ADR-004). The registry is the single source of truth; edit it, then regenerate. Freshness enforced by `validate.py --check tracked_hypotheses_fresh`.

**Purpose.** Catalogue the project's load-bearing tracked-hypothesis Props — Lean predicates consumed by substantive theorems but NOT independently derived. Each is a *constructive* alternative to a global `axiom`: the claim is packaged as a `def … : Prop` and taken as an explicit hypothesis, making the project's assumption surface visible at the type-signature level (Pipeline Invariant #15/#16).

**Count.** 31 tracked hypotheses 4 headline, 14 external_boundary, 7 discharge_future, 6 local.

---

## Headline-gating (a published-paper headline rides on it)

### `H_Fib_NonCentralConjugateWitness`

**Statement.** There exist (g₁,g₂) ∈ H_Fib × H_Fib with g₁ not commuting with its g₂-conjugate (non-central-conjugate antecedent for the Fibonacci density argument).

- status `active` · eliminability `hard` · module `FKLW.CartanSubstrate`
- **Posture.** Non-central-conjugate witness feeding the Fibonacci density argument.
- **Discharge path.** Discharge plan: g₁=σ_Fib_1, g₂=σ_Fib_2 (deferred ~50-150 LoC).
- **Source.** FKLW Fibonacci density.
- **Risk.** Headline-gating density sub-witness.

### `H_Fib_TwoLITangents`

**Statement.** Two ℝ-linearly-independent tangent directions exist in the Lie algebra of H_Fib (companion antecedent for the Fibonacci density v4 witness).

- status `active` · eliminability `hard` · module `FKLW.CartanSubstrate`
- **Posture.** Two-LI-tangents witness feeding the Fibonacci density argument.
- **Discharge path.** Discharge ~50-150 LoC (deferred).
- **Source.** FKLW Fibonacci density.
- **Risk.** Headline-gating density sub-witness.

### `H_Fib_v4_witness`

**Statement.** exp(ℝ•X₁) ⊆ H_Fib for two ℝ-linearly-independent tangents X₁, X₂ — the v4 density witness for the Fibonacci closure subgroup.

- status `active` · eliminability `hard` · module `FKLW.CartanSubstrate`
- **Posture.** Fibonacci-density v4 witness; the Fibonacci universality headline rides on the H_Fib density witnesses.
- **Discharge path.** Discharge ~50-150 LoC (deferred); gates the FKLW Fibonacci SU(2) density / universality headline (audit #8 "sound predicate v3/v4").
- **Source.** FKLW Fibonacci density (Cartan substrate).
- **Risk.** Headline-gating density witness.

### `H_PMNSAnglesFromExactSubstrate`

**Statement.** A PMNS matrix exhibits exact substrate μ-τ row symmetry (holds at θ₂₃ = π/4; NuFit-6.0 best fit 49.1° does NOT satisfy it — row magnitudes differ by ≈0.1).

- status `active` · eliminability `hard` · module `NeutrinoMixing`
- **Posture.** Headline-gating: the PMNS prediction is conditional on exact substrate μ-τ symmetry, which the empirical best fit does not exactly satisfy.
- **Discharge path.** WAVE2-OPEN-2: derive exact μ-τ symmetry from the substrate (vs assume); gates the PMNS prediction (paper40).
- **Source.** NuFit-6.0; substrate μ-τ symmetry.
- **Risk.** Strict predicate, falsifiable against NuFit; headline-gating for the neutrino-mixing prediction.

---

## External boundary / KEEP_AS_TRACKED (research-grade or project-scope)

### `H_CasiniHuerta_Bound_Valid`

**Statement.** For a 2D-CFT entanglement entropy S_ent(L) with central charge c and UV cutoff ε, the Casini–Huerta log bound S_ent(L) ≤ (c/3) log(L/ε) holds for all L > ε > 0.

- status `active` · eliminability `hard` · module `RTCasiniHuertaBounds`
- **Posture.** External CFT boundary input consumed by the RT/Casini-Huerta bridge theorems.
- **Source.** Casini–Huerta (CFT entanglement-entropy bound).
- **Risk.** Established CFT result; tracked as external CFT input.

### `H_HorizonBoundaryCondition`

**Statement.** Bundles the five conditions a horizon-bounding MTC must satisfy for S(A) = A/(4 G_N^emerg) + log corrections (positivity, area-leading, …).

- status `active` · eliminability `hard` · module `BHEntropyMicroscopic`
- **Posture.** A 5-condition bundle Prop; consumed by the microscopic-entropy and QEC-holography bridges.
- **Source.** Microscopic BH-entropy program (BHEntropyMicroscopic / QECHolographyBridge).
- **Risk.** Bundle of well-motivated horizon conditions; tracked as external boundary.

### `H_KLRS_SM_Crossover`

**Statement.** The full thermal-resummed SM electroweak phase transition is a crossover (not first-order) at the physical Higgs mass m_H = 125.20 GeV. Equivalently: the strict-LO smBenchmarkParams cubic coefficient E = 0.01 is driven below the crossover threshold by full thermal corrections at m_H ≫ KLRS endpoint 72.4 GeV.

- status `active` · eliminability `hard` · module `EWBaryogenesisChiralityWall`
- **Discharge path.** Requires formalizing finite-temperature lattice thermodynamics infrastructure (Wilson-flow gradient + dimensional reduction at T ≳ T_c + lattice artifact extrapolation) to derive the KLRS 1996 / CFH 1999 endpoint at m_H = 72.4 ± 1.7 GeV from continuum perturbation theory. Out of scope for the Lean library; replication is the standard validation path. The quantitative anchor sm_klrs_overshoot_ratio_gt_threshold (1.5 < 125.20/72.4 ≈ 1.73) provides a falsifiable physical-input lever: if a future lattice study revises the endpoint upward to m_H > 83.5 GeV, the overshoot would drop below 1.5 and the hypothesis would weaken.
- **Source.** Kajantie, Laine, Rummukainen, Shaposhnikov, PRL 77, 2887 (1996), arXiv:hep-ph/9605288 (initial endpoint); refined by Csikor, Fodor, Heitger, PRL 82, 21 (1999), arXiv:hep-ph/9809291 (m_H endpoint = 72.4 ± 1.7 GeV).
- **Risk.** Extremely low — KLRS / CFH are well-established lattice results, replicated by independent groups (Aoki et al., Bödeker et al.) and consistent with continuum dimensional-reduction analyses. The crossover verdict at m_H = 125.20 GeV is universally accepted in the EWBG community.
- **Circularity.** None. The hypothesis is a downstream lattice result that takes the SM gauge + Higgs sector as input and produces a thermodynamic verdict; no logical dependency on theorems within the project.
- **Consumers.** `SKEFTHawking.EWBaryogenesisChiralityWall.sm_with_3nu_R_ewbg_forbidden_under_klrs`, `SKEFTHawking.EWBaryogenesisChiralityWall.sm_no_nu_R_ewbg_doubly_forbidden`

### `H_MixedChannelZ16Cancels`

**Statement.** Wan–Wang ℤ₁₆ ⊕ ℤ₄ joint-charge cancellation of a mixed-charge hidden sector (parameterized by a ℤ₁₆ indexing φ; SM +13 ≡ −3 mod 16).

- status `active` · eliminability `hard` · module `HiddenSectorMixedCharge`
- **Posture.** Mixed-charge hidden-sector anomaly cancellation under the Wan-Wang ℤ₁₆⊕ℤ₄ scheme.
- **Source.** Wan–Wang ℤ₁₆ classification.
- **Risk.** Tracked anomaly-cancellation hypothesis; parallel to the CenterFunctor center-functor Props.

### `H_RT_Formula_Valid`

**Statement.** A black-hole-entropy function S_BH satisfies the Ryu–Takayanagi proportionality S = A/(4 G_N) for all positive (A, G_N).

- status `active` · eliminability `open` · module `RTCasiniHuertaBounds`
- **Posture.** KEEP_AS_TRACKED. Load-bearing boundary condition; consumers establish RT-vs-Kaul-Majumdar/loop-quantum-gravity distinguishability. External comms hedge when used outside AdS/CFT.
- **Discharge path.** Out of Phase-6 scope (no holographic dual derived). RT is a QG conjecture outside AdS/CFT.
- **Source.** Ryu–Takayanagi; Lewkowycz–Maldacena replica trick (AdS/CFT).
- **Risk.** Empirically supported in AdS/CFT; research-grade conjecture in general QG. 4 substantive consumers (RT-vs-alternatives distinguishable).
- **Consumers.** `SKEFTHawking.rt_entropy_pos`, `SKEFTHawking.rt_falsified_by_kaul_majumdar`, `SKEFTHawking.isolatedHorizon_violates_H_RT`, `SKEFTHawking.kaulMajumdarS_violates_H_RT_via_IH`

### `H_RegimePartition`

**Statement.** Glorioso–Liu second-law bundle: dynamical-KMS ℤ₂ symmetry + unitarity (Im S_eff ≥ 0) ⟹ local entropy-current monotonicity ∂_μ s^μ ≥ 0, without invoking pointwise NEC.

- status `active` · eliminability `hard` · module `BHThermodynamicsFourLaws`
- **Posture.** Post-Stage-13 strengthened bundle encoding the Glorioso-Liu entropy-current theorem.
- **Source.** Glorioso–Liu, arXiv:1612.07705 §III Eq. 3.20.
- **Risk.** Established SK-EFT result; tracked as external theorem-bundle input.

### `H_VergelesPositivity`

**Statement.** Osterwalder–Schrader reflection-positivity on the lattice ADW theory ⟹ α_ADW > 0 strictly inside the broken phase (G/G_c > 1).

- status `active` · eliminability `hard` · module `LinearizedEFE`
- **Posture.** External lattice-positivity input giving α_ADW > 0 in the broken phase.
- **Source.** Vergeles, PRD 112, 054509 (2025).
- **Risk.** Published lattice reflection-positivity result; tracked as external input.

### `H_VestigialModeIsGraviton`

**Statement.** A vestigial-mode coupling χ_vest represents a graviton-like d.o.f.: 0<χ_vest ∧ LigoSatisfied(c_GW_deviation χ_vest) ∧ |c_GW_deviation χ_vest| < 1/2.

- status `active` · eliminability `open` · module `GravitationalWaves`
- **Posture.** KEEP_AS_TRACKED. The hydrodynamic-mode→graviton bridge is, to our knowledge, not derived in any published source; the tracked-Prop form is the principled treatment. Discharging would mean shipping a different microscopic theory than this project commits to.
- **Discharge path.** Out of scope for SK_EFT_Hawking (analog-Hawking BEC, not full QG). Would require a microscopic substrate from which the vestigial-mode→graviton bridge follows.
- **Source.** Volovik 2024 ("second-sound graviton"): derives s₂=c at equilibrium but NO off-shell propagator / matter coupling; "the type of graviton this mode represents requires further consideration".
- **Risk.** Conjectural. Anchor at χ_vest=1 + 4 falsifiers establish non-vacuity.

### `TPFConjecture`

**Statement.** For every anomaly-free SPT phase there exists a local, symmetric, gapped interface Hamiltonian with unique ground state and short-range entanglement (Thorngren–Preskill–Fidkowski 2026).

- status `active` · eliminability `open` · module `SPTClassification`
- **Posture.** KEEP_AS_TRACKED (ex-axiom). The conversion from a global axiom to a consumed tracked Prop made the assumption visible at the type level; this is the principled framing pending a constructive interface proof.
- **Discharge path.** No proof in any proof assistant; would need the full TPF gapped-interface construction.
- **Source.** Thorngren–Preskill–Fidkowski 2026 (TPF conjecture). Converted from `axiom gapped_interface_axiom` → tracked Prop on 2026-05-19.
- **Risk.** Research-grade conjecture. Strengthened by FKGappedInterface.lean.

### `c_minus_equals_8Nf`

**Statement.** The chiral central charge of N_f generations of SM fermions is c₋ = 8N_f

- status `active` · eliminability `algebraic` · module `WangBridge`
- **Discharge path.** This was DERIVED (not hypothesized) in WangBridge.lean from the 16 Weyl fermions per generation. But the derivation assumes the standard SM fermion content — the hypothesis is that the SM has exactly 16 Weyl fermions per generation.
- **Source.** SM fermion content (standard textbook result)
- **Risk.** Zero — this is the definition of the SM.
- **Consumers.** `SKEFTHawking.central_charge_from_sm`

### `characteristic_square_mod_8`

**Statement.** For any unimodular symmetric bilinear form and any characteristic vector c, c^T M c ≡ σ(M) mod 8

- status `superseded_on_wiring_path` · eliminability `hard` · module `AlgebraicRokhlin (alternate route; no longer on the SpinRokhlinInterface wiring path)`
- **Discharge path.** SUPERSEDED ON THE WIRING PATH (2026-06-04): the rewired SmoothSpinManifold4 interface no longer consumes this characteristic-vector formulation (serre_even_unimodular_mod8 used it only at c=0, i.e. only to extract 8|σ). The interface now carries the precise residual eight_dvd : 8 | latticeSig form directly, whose discharge target is the even-unimodular CLASSIFICATION (E8^a (+) (-E8)^b (+) H^c), with the signature calculus already complete (RokhlinClassification et al.) and only the classification existence ([E2] Smith-Normal-Form basis-completion + [HM] Hasse-Minkowski + [Theta] theta-modularity) remaining. This entry is retained as a valid ALTERNATE algebraic formulation (Serre/van der Blij characteristic-vector route); it still requires the classification of indefinite unimodular forms (Hasse-Minkowski) or the van der Blij Gauss-sum lemma, neither in Mathlib. serre_even_unimodular_mod8 and CharacteristicSquareModEight remain defined and valid in AlgebraicRokhlin.lean.
- **Source.** Serre, "A Course in Arithmetic" (1973), Ch. V; van der Blij, Math. Z. 74, 18 (1960)
- **Risk.** Extremely low — proved independently by Serre (1973) and van der Blij (1960). Textbook result.
- **Circularity.** None. Purely algebraic result about bilinear forms, independent of topology.
- **Consumers.** `SKEFTHawking.serre_even_unimodular_mod8`

### `modular_invariance_framing`

**Statement.** The framing anomaly requires e^{2πic/24} = 1 for a consistent TQFT, i.e., 24 | c₋

- status `active` · eliminability `hard` · module `WangBridge`
- **Discharge path.** Requires formalizing: (a) Atiyah 2-framing on 3-manifolds, (b) the relation between central charge and framing anomaly, (c) Witten-Reshetikhin-Turaev invariant modularity. The algebraic consequence (24 | c₋) is proved; the physical INPUT (framing anomaly = modularity constraint) is the hypothesis.
- **Source.** Witten, Comm. Math. Phys. 121, 351 (1989); Atiyah, Topology 29, 1 (1990)
- **Risk.** Extremely low — foundational result in TQFT, universally accepted.
- **Consumers.** `SKEFTHawking.wang_bridge_full_chain`, `SKEFTHawking.generation_constraint_iff`

### `rokhlin_sigma_mod_16`

**Statement.** For any closed smooth spin 4-manifold M, 16 | σ(M)

- status `active (8|σ proven & unconditional; the irreducible topological factor 2|σ/8 is carried as the tracked input topo)` · eliminability `very_hard` · module `SpinRokhlinInterface (Phase 5q.B, rewired to latticeSig); E8Signature + LatticeSignatureCongr + BlockSignature + GeneratorNondeg + LatticeSigBlock + RokhlinClassification (signature calculus, classification route); LatticePrimitive + EvenLatticeForm (classification scaffolding [E1]/[E2]); LatticeSignature (latticeSig); RokhlinBridge (legacy hypothesis form)`
- **Discharge path.** Phase 5q.B (Route B) DECOMPOSED this opaque hypothesis into the narrow SmoothSpinManifold4 interface (SpinRokhlinInterface.lean) and PROVED 16|σ as a kernel-pure theorem over it: SmoothSpinManifold4.rokhlin, via even-unimodular + 8|σ composed with 2|σ/8 (sixteen_dvd_latticeSig_of_eight_dvd_of_topo = rokhlin_from_serre_plus_topology on latticeSig). INTERFACE REWIRED (2026-06-04): the signature is now the GENUINE latticeSig of the intersection form (sig := latticeSig form, closing the prior free-unconnected-integer gap), and the algebraic residual is carried as the PRECISE field eight_dvd : 8 | latticeSig form (the isolated van der Blij wall), replacing the opaque charSq/CharacteristicSquareModEight. Remaining interface inputs: (i) even_unimod [Wu formula, topological], (ii) eight_dvd : 8|latticeSig form [van der Blij, the Wave-B1 ALGEBRAIC target], (iii) topo : 2|σ/8 [Â-genus even (Atiyah-Singer index parity) / geometric Guillou-Marin Arf of a characteristic SURFACE (Freedman-Kirby) — the single IRREDUCIBLE topological input. NOTE 2026-06-13: this is NOT the lattice Arf(redQuad), which is identically 0 on every even unimodular form (E₈: Arf=0 but σ/8=1); the lattice Arf bridge is FALSE, see RokhlinArfNoGo.lean]. USER DECISION 2026-06-04: GO FULL via the CLASSIFICATION route (E8^a (+) (-E8)^b (+) H^c), zero-axiom. SIGNATURE CALCULUS COMPLETE this session (all kernel-pure, ExtractDeps baseline green 9073 jobs): E8Signature (sigma(E8)=8, sigma(-E8)=-8 via the integer-Cholesky C8^T C8 = 4.E8lit decide-over-Z route), LatticeSignatureCongr (latticeSig_congr = Sylvester congruence invariance; sigma(H)=0), BlockSignature (sigma(A (+) B)=sigma A+sigma B; nondeg bridge), GeneratorNondeg (generator nondegeneracy), LatticeSigBlock (latticeSigOf on any index + block additivity + reindex invariance), RokhlinClassification (the [E3] assembly: generators 8|sigma, block-sum/congruence/reindex closure, and the bridge sixteen_dvd_latticeSig_of_eight_dvd_of_topo). CLASSIFICATION SCAFFOLDING: [E1] primitive vectors + dual (LatticePrimitive); [E2]-partial exists_hyperbolic_pair ({v,w-prime} Gram = H) + even_form_dvd; [E3] assembly DONE. The signature side is CLOSED: any normal form E8^a (+) (-E8)^b (+) H^c gives latticeSig = 8(a-b), hence 8|sigma. ✅ DISCHARGED 2026-06-08: BOTH irreducible inputs are now kernel-pure THEOREMS. [Theta] theta-modularity (definite 8|rank) = eight_dvd_latticeSig_of_definite (shipped earlier). [HM] Hasse-Minkowski (indefinite even unimodular ⟹ isotropic vector) = hasIsotropicVector (RokhlinHMRankFour), discharging HasWeakIsotropicVectorHyp at EVERY rank: rank ≥5 (weakIsotropic_of_five_le, general-rank diagonal HM spine diag_nary_zero_of_local with ℝ + odd-p + 2-adic local isotropy all proven), rank 2 (weakIsotropic_rank_two, det=-1 mod-4), ranks 1 & 3 (no even unimodular form exists), rank 4 (weakIsotropic_rank_four: det=1 forces square discriminant, then brick (a) odd-p ℤ_p-unimodular isotropy [Chevalley-Warning + Hensel] + brick (b) p=2 via binary Hilbert reciprocity [quaternary_sqdisc_iso_iff_ternary + hilbertGlobalProd_eq_one] transported through the explicit congruence A=PᵀdiagP). Hence eight_dvd_latticeSig (8|σ for every even unimodular form) and sixteen_dvd_latticeSig (16|σ given 2|σ/8) are UNCONDITIONAL. The SmoothSpinManifold4 structure no longer carries the eight_dvd field — SmoothSpinManifold4.rokhlin (16|σ) is derived from even_unimod + topo (2|σ/8) ALONE. The ONLY remaining interface input is the genuinely-topological factor 2|σ/8 (Â-genus even / geometric Guillou-Marin characteristic-surface Arf — NOT the lattice Arf(redQuad), which is content-free [≡0]; RokhlinArfNoGo.lean). All kernel-pure {propext,Classical.choice,Quot.sound}, axiom_closure_allowlist GREEN. sixteen_convergence_unconditional is the companion to sixteen_convergence_full with the 16|σ conjunct now a full theorem, not an assumed h_rokhlin. Full living decomposition: docs/roadmaps/Phase5qB_LabNotebook.md.
- **Source.** Rokhlin, Dokl. Akad. Nauk SSSR 84, 221 (1952); van der Blij, Math. Z. 74, 18 (1960); Freedman-Kirby (1978)
- **Risk.** Extremely low — proved 1952, independently confirmed by Atiyah-Singer (1963), Freedman-Kirby (1978). As solid as any result in topology.
- **Circularity.** Anti-circularity verified: the wired derivation routes even-unimodular + van der Blij ⟹ 8|σ, plus 2|σ/8 ⟹ 16|σ; it does NOT use Anderson-Brown-Peterson or Rokhlins theorem as input (Rokhlins theorem IS the conclusion). The 2-axiom bordism alternative (Ω^Spin_4 ≅ Z) WOULD be circular (ABP used Rokhlin-equivalent facts) — deliberately NOT used.
- **Consumers.** `SKEFTHawking.SmoothSpinManifold4.rokhlin`, `SKEFTHawking.SmoothSpinManifold4.eight_dvd_sig`, `SKEFTHawking.hasWeakIsotropicVector`, `SKEFTHawking.hasIsotropicVector`, `SKEFTHawking.weakIsotropic_rank_four`, `SKEFTHawking.eight_dvd_latticeSig`, `SKEFTHawking.sixteen_dvd_latticeSig`, `SKEFTHawking.sixteen_dvd_latticeSig_of_eight_dvd_of_topo`, `SKEFTHawking.sixteen_convergence_unconditional`, `SKEFTHawking.sixteen_convergence_full`, `SKEFTHawking.z16_anomaly_without_nu_R`

### `spin_bordism_iso_Z`

**Statement.** Ω^Spin_4 ≅ Z, generated by the K3 surface with σ(K3) = -16

- status `proposed` · eliminability `very_hard` · module `proposed: SpinBordism.lean`
- **Discharge path.** Requires Adams spectral sequence computation (Anderson-Brown-Peterson 1966-67). Probably 10+ years from formalization in any proof assistant.
- **Source.** Anderson-Brown-Peterson, Bull. AMS 72, 256 (1966)
- **Risk.** Extremely low — standard result in algebraic topology.
- **Circularity.** CAUTION: The ABP computation historically used facts equivalent to Rokhlin theorem. Using this to DERIVE Rokhlin creates a logical dependency chain where A proves B but A was originally proved using B. The mathematical content is not circular (ABP can be proved independently of Rokhlin via Adams spectral sequence), but the historical provenance is tangled. If used, should be clearly documented as an independent route, not as "proving" Rokhlin from more basic facts.

---

## Discharge-future (in-principle derivable; scheduled)

### `H_DESICompatibility`

**Statement.** A dark-energy predictor produces (w₀,w_a) within (0.1, 0.2) of the DESI DR2 CPL best-fit (−0.838, −0.62) for some positive (Λ_UV, N_f, α_ADW).

- status `active` · eliminability `hard` · module `FLRWDynamics`
- **Posture.** DISCHARGE_FUTURE_PHASE (6b.2). Honest interim framing: expected to follow derivatively from ADW dynamics once cosmological-perturbation machinery ships. External writeups must hedge "predicated on H_DESICompatibility, open pending 6b.2".
- **Discharge path.** Phase 6b.2 (NOT currently active): coupled FLRW perturbations → growth observable → CPL extraction → DESI likelihood. ~50 person-hours.
- **Source.** DESI DR2 CPL best-fit; ADW multi-scalar mechanism (FLRWDynamics).
- **Risk.** Derivable in principle within the substrate; not yet executed. 3 falsifiers establish non-vacuity (ΛCDM CPL gap 0.162 > 0.1).

### `H_MR_FromADWSubstrate_BCS_LNV`

**Statement.** The BCS-exponential M_R form derived from the projected Majorana-channel NJL gap equation, conditional on H_LeptonNumberViolated G_LV (G_LV=0 ⟹ G_M≡0).

- status `active` · eliminability `hard` · module `MajoranaRung`
- **Posture.** BCS M_R form for the Majorana rung, gated on lepton-number violation.
- **Source.** WAVE2-OPEN-1b; projected Majorana-channel NJL gap equation.
- **Risk.** Conditional on explicit substrate-L violation; tracked.

### `H_MR_FromSMGGap`

**Statement.** The per-generation Majorana mass M_R i arises from the substrate SMG gap scale via M_R i = c_i · Λ_SMG for c_i ∈ (0,1] (no lepton-number-violation precondition).

- status `active` · eliminability `hard` · module `MajoranaRungSMG`
- **Posture.** M_R from the SMG gap scale; the unconditional companion to H_MR_FromADWSubstrate_BCS_LNV.
- **Source.** WAVE4-OPEN-2; substrate SMG gap.
- **Risk.** Tracked seesaw-scale hypothesis.

### `H_ScalarChannelIsTetradBifurcationOutput`

**Statement.** For a ScalarChannel s arising from the TetradGapEquation supercritical branch and a UV cutoff Λ_UV, the condensate VEV satisfies √(μ²/λ) ≤ Λ_UV (no super-UV condensates).

- status `active` · eliminability `hard` · module `ScalarRungInterpretation`
- **Discharge path.** Requires resolution of Open Question O.2: a quantitative bridge mapping the Wetterich scalar-channel parameters (μ², λ) to the GL-expansion coefficients of the tetrad gap-equation bifurcation. Once O.2 is closed (via deep-research derivation of the supercritical-branch coefficient identities), the kinematic bound √(μ²/λ) ≤ Λ_UV becomes a theorem of TetradGapEquation rather than an external hypothesis.
- **Source.** Tracked external hypothesis pending Open Question O.2 (deep-research-gated). Disclosed in paper20 (papers/paper20_scalar_rung/paper_draft.tex L181, L368). Project precedent: same tracked-hypothesis pattern in HiddenSectorMixedCharge.H_MixedChannelZ16Cancels and DarkSectorSynthesis.H_VestigialRelicCarriesZ16Charge.
- **Risk.** Low — the kinematic constraint √(μ²/λ) ≤ Λ_UV is a generic effective-field-theory consistency requirement (no super-UV condensates) and is expected to hold for any ScalarChannel that genuinely emerges from the tetrad gap-equation supercritical branch. The hypothesis is genuinely non-trivial (can fail for super-UV scalar channels) but is structurally aligned with EFT validity. The contrapositive `bridge_excludes_super_uv_vev` provides explicit falsifiability.
- **Circularity.** None. The hypothesis cleanly separates the qualitative bifurcation-output identification (currently external) from the algebraic Mexican-hat consequences (proved in Lean). No circular dependency on any downstream theorem.
- **Consumers.** `SKEFTHawking.mexican_hat_vev_under_supercritical_bridge`, `SKEFTHawking.bridge_excludes_super_uv_vev`

### `H_SubstrateNearSMGFixedPoint`

**Statement.** The substrate parameters sit in the seesaw-restricted SMG window AND Λ_SMG = c_SMG·Λ_UV with c_SMG ∈ [10⁻¹⁰, 10⁻⁴] (NJL-derived band).

- status `active` · eliminability `hard` · module `MajoranaRungSMG`
- **Posture.** Substrate-near-SMG-fixed-point window for the Majorana-rung seesaw.
- **Source.** WAVE4-OPEN-1; NJL seesaw-restricted band.
- **Risk.** Tracked window hypothesis.

### `H_VestigialRelicCarriesZ16Charge`

**Statement.** The vestigial relic carries the ℤ₁₆ anomaly-cancellation charge +3 required by the SM deformation class (existence anomaly-forced).

- status `active` · eliminability `hard` · module `DarkSectorSynthesis`
- **Posture.** Tracked dark-sector Prop: the relic-carries-ℤ₁₆-charge claim that anomaly-forces the vestigial relic.
- **Source.** Wave 8 dark-sector synthesis; SM ℤ₁₆ deformation class.
- **Risk.** Not a Lean theorem; tracked dark-sector hypothesis.

### `Phase6hHyperchargeSplittingHypothesis`

**Statement.** Bundle of the three substrate parameters (δ_f flavour charge, α_∗ AS fixed-point coupling, Λ_UV) that would parametrize the closed-form light-quark prediction m_f/Λ_UV ~ exp(...).

- status `active` · eliminability `hard` · module `LightQuarkHierarchyFallthrough`
- **Posture.** Discharge-future bundle for the (inactive) Phase-6h light-quark-hierarchy extension.
- **Discharge path.** Phase 6h W4 (Gate Z.4 NEGATIVE / inactive): rigorous only in 2D; 4D needs Catterall mirror decoupling.
- **Source.** Phase 6h hypercharge-splitting path (asymptotic-safety).
- **Risk.** Phase 6h inactive; tracked bundle.

---

## Local / intermediate (module-scoped algebraic hypothesis)

### `H_BilocalPointlikeLimit`

**Statement.** In the pointlike limit ϕ(0)→ϕ(∞) (dilution→1) the bilocal field reduces to the pointlike SM Higgs doublet; the non-trivial content is bilocalDilution b = 1.

- status `active` · eliminability `hard` · module `BHLGaugeEmbedding`
- **Posture.** Pointlike-limit reduction of the bilocal BHL field to the SM Higgs doublet.
- **Source.** BHL minimal embedding (bilocal → pointlike).
- **Risk.** Non-trivial quantitative claim (any spread bilocal field has dilution<1).

### `H_CFZ2_sq_a`

**Statement.** Mirror of H_CFZ2_sq_e at the (aAdd, aAdd, aAdd) index triple (hexagon double-swap identity for the Z/2 Drinfeld-center functor).

- status `active` · eliminability `hard` · module `CenterFunctorZ2Equiv`
- **Posture.** Local hexagon double-swap identity (aAdd summand) for the deferred Z/2 Drinfeld-center categorical functor (no downstream paper consumer).
- **Source.** Phase 5s Wave 9 Option A (2026-04-20).
- **Risk.** Local algebraic hexagon identity. RESOLVED — same as H_CFZ2_sq_e: gates only the deferred categorical functor (zero downstream); paper7 cites the unconditional `full_correspondence`, not this. W1 "Z/2 fully verified" framing sound.

### `H_CFZ2_sq_e`

**Statement.** The halfBraiding double-swap (hexagon-derived β≫β_can≫β≫desc = ρ) identity at the (eAdd, aAdd, aAdd) index triple of the Z/2 Drinfeld-center functor.

- status `active` · eliminability `hard` · module `CenterFunctorZ2Equiv`
- **Posture.** Local hexagon double-swap identity (eAdd summand) for the deferred Z/2 Drinfeld-center categorical functor (no downstream paper consumer).
- **Source.** Phase 5s Wave 9 Option A (2026-04-20); hexagon identity for Z(Vec_{ℤ/2}).
- **Risk.** Local algebraic hexagon identity. RESOLVED (ADR-004 W7 review, 2026-06-13): gates ONLY the deferred categorical functor `CenterFunctorZ2Equiv.canonicalCenterToRep` (proven Faithful; full Equivalence explicitly DEFERRED, zero downstream consumers). paper7 cites `CenterEquivalenceZ2.full_correspondence` — the unconditional finite object/fusion/braiding correspondence of the 4 simples — NOT this functor; so the W1 "Z/2 fully verified" framing is sound and no paper claim rides on H_CFZ2.

### `H_DecouplingBoundDim6`

**Statement.** The amplitude-difference amp_diff(E) between Embedding III (substrate-bound ν_R) and Embedding I (fundamental ν_R) is bounded above by the natural Wilson coefficient × (E/Λ_ADW)² at every energy.

- status `active` · eliminability `hard` · module `MajoranaRungDecoupling`
- **Posture.** Dim-6 decoupling bound between the two ν_R embeddings.
- **Source.** WAVE2-OPEN-5b (k=2, generic dim-6) EFT decoupling.
- **Risk.** Tracked EFT-decoupling bound.

### `H_HSCovariantBosonisation`

**Statement.** Hubbard–Stratonovich bosonisation of the BHL 4-fermion operator yields an auxiliary field gauge-covariant under SU(2)_L×U(1)_Y with hypercharge +1/2.

- status `active` · eliminability `hard` · module `BHLGaugeEmbedding`
- **Posture.** Gauge-covariance + hypercharge of the HS auxiliary field in the BHL embedding.
- **Source.** BHL gauge embedding; HS bosonisation.
- **Risk.** Non-trivial (hypercharge could be 0 or +1).

### `IsCurveTheoreticPenroseHypothesis`

**Statement.** The 4-conjunct hypothesis bundle (initial_expansion, focal_config, …) for the curve-theoretic Penrose wave-completion composition theorem.

- status `active` · eliminability `hard` · module `PenroseSingularityCurveTheoretic`
- **Posture.** Curve-theoretic Penrose focal-configuration bundle for the singularity-completion theorem.
- **Source.** Curve-theoretic Penrose singularity (wave-completion).
- **Risk.** Bundle of focal-configuration conditions; tracked.

---
