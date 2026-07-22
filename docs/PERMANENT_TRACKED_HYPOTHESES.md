# Permanent Tracked Hypotheses

> **AUTO-GENERATED — DO NOT EDIT BY HAND.** This document is rendered from `HYPOTHESIS_REGISTRY` in `src/core/constants.py` by `scripts/render_tracked_hypotheses.py` (Substrate Integrity Gates W3, ADR-004). The registry is the single source of truth; edit it, then regenerate. Freshness enforced by `validate.py --check tracked_hypotheses_fresh`.

**Purpose.** Catalogue the project's load-bearing tracked-hypothesis Props — Lean predicates consumed by substantive theorems but NOT independently derived. Each is a *constructive* alternative to a global `axiom`: the claim is packaged as a `def … : Prop` and taken as an explicit hypothesis, making the project's assumption surface visible at the type-signature level (Pipeline Invariant #15/#16).

**Count.** 47 tracked hypotheses 4 headline, 15 external_boundary, 22 discharge_future, 6 local.

---

## Headline-gating (a published-paper headline rides on it)

### `H_Fib_NonCentralConjugateWitness`

**Statement.** There exist (g₁,g₂) ∈ H_Fib × H_Fib with g₁ not commuting with its g₂-conjugate (non-central-conjugate antecedent for the Fibonacci density argument).

- status `discharged` · eliminability `hard` · module `FKLW.CartanSubstrate`
- **Posture.** Non-central-conjugate witness — DISCHARGED by H_Fib_NonCentralConjugateWitness_discharged; fed the Fibonacci density argument.
- **Discharge path.** DISCHARGED (2026-07-20, R-07 registry hygiene): proved unconditionally (sorry-free) by `H_Fib_NonCentralConjugateWitness_discharged` (CartanSubstrate.lean §4.9, verified in lean_deps.json). Retained for provenance; no longer an open frontier apex.
- **Source.** FKLW Fibonacci density.
- **Risk.** Was headline-gating; DISCHARGED by an unconditional producer.

### `H_Fib_TwoLITangents`

**Statement.** Two ℝ-linearly-independent tangent directions exist in the Lie algebra of H_Fib (companion antecedent for the Fibonacci density v4 witness).

- status `discharged` · eliminability `hard` · module `FKLW.CartanSubstrate`
- **Posture.** Two-LI-tangents witness — DISCHARGED by H_Fib_TwoLITangents_unconditional; fed the Fibonacci density argument.
- **Discharge path.** DISCHARGED (2026-07-20, R-07 registry hygiene): proved unconditionally (sorry-free) by `H_Fib_TwoLITangents_unconditional` (OneParameterSubgroupSU2.lean §78, verified in lean_deps.json). Retained for provenance; no longer an open frontier apex.
- **Source.** FKLW Fibonacci density.
- **Risk.** Was headline-gating; DISCHARGED by an unconditional producer.

### `H_Fib_v4_witness`

**Statement.** exp(ℝ•X₁) ⊆ H_Fib for two ℝ-linearly-independent tangents X₁, X₂ — the v4 density witness for the Fibonacci closure subgroup.

- status `discharged` · eliminability `hard` · module `FKLW.CartanSubstrate`
- **Posture.** Fibonacci-density v4 witness — DISCHARGED by H_Fib_v4_witness_unconditional; the Fibonacci universality headline rode on the H_Fib density witnesses, now unconditional.
- **Discharge path.** DISCHARGED (2026-07-20, R-07 registry hygiene): proved unconditionally (no hypothesis arguments, sorry-free) by `H_Fib_v4_witness_unconditional` (OneParameterSubgroupSU2.lean §80, verified in lean_deps.json). Retained for provenance; no longer an open frontier apex.
- **Source.** FKLW Fibonacci density (Cartan substrate).
- **Risk.** Was headline-gating; DISCHARGED by an unconditional producer.

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

**Statement.** Bundles the five conditions a horizon-bounding MTC must satisfy for S(A) = A/(4 G_N^emerg) + log corrections: positivity, area-leading (κ>0), second law (monotone), modularInvariant (S-matrix non-degenerate), anomalyMatch (8 ∣ c₋, the Walker–Wang Z₂ inflow). Wave 8 (2026-06-14) replaced the modularInvariant/anomalyMatch True placeholders with these real, falsifiable predicates.

- status `active` · eliminability `hard` · module `BHEntropyMicroscopic`
- **Posture.** A 5-condition bundle Prop carrying a companion HorizonModularData (S-matrix + c₋); consumed by the microscopic-entropy and QEC-holography bridges. Wave 8: modularInvariant := md.modular, anomalyMatch := (8 ∣ c₋) — no longer True placeholders.
- **Source.** Microscopic BH-entropy program (BHEntropyMicroscopic / QECHolographyBridge).
- **Risk.** Bundle of well-motivated horizon conditions; tracked as external boundary (no published derivation pins a specific MTC at a 4D ADW horizon). Wave-8 hardened: each conjunct is independently witnessed AND falsified, and the full bundle is satisfiable (fibonacci_horizon_satisfies_H_HorizonBoundaryCondition).

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

### `H_Sakharov`

**Statement.** Sakharov induction condition: the physical Newton constant is fully induced by N_f Dirac fermion loops (no bare gravitational action), G_N = G_N_from_a2 = 12π/(N_f Λ²). Consumed by the Frolov–Fursaev induced-gravity 1/4 conditional (Phase 6a Wave 9, frolov_fursaev_quarter_coefficient).

- status `active` · eliminability `hard` · module `InducedGravityEntropy`
- **Posture.** The fully-induced-G_N condition consumed by frolov_fursaev_quarter_coefficient to derive κ = 1/(4 G_N) (Gate A.2). Witnessed (Dirac, frolov_fursaev_dirac_witness) and falsified (wrong heat-kernel coefficient, frolov_fursaev_falsifier_wrong_coeff).
- **Source.** Sakharov 1967 induced gravity; Adler 1982; Frolov–Fursaev–Zelnikov, Nucl. Phys. B 486 (1997), hep-th/9607104.
- **Risk.** Standard induced-gravity premise (no bare action); equivalent to α_ADW = 1 (δG = 0) via matchResidual_eq_zero_iff_alpha_unity (bridge H_Sakharov_iff_alpha_unity). Independent of the BH-entropy normalization — does NOT assume S = A/4G.
- **Circularity.** None — Sakharov induction (G_N from loops) is independent of demanding S = A/4G; bridged to α_ADW = 1, and the 1/4 emerges from the shared Seeley–DeWitt a₂ ratio (48:12), not a tuning.

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
- **Consumers.** `SKEFTHawking.fermion_count_gives_central_charge`

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
- **Consumers.** `SKEFTHawking.SpinSigmaRoute.SpinSigmaPresentation.dataBordismGrp_equiv_int`, `SKEFTHawking.SpinSigmaRoute.SpinSigmaPresentation.sig_injective`, `SKEFTHawking.SpinSigmaRouteDoor.omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_full`

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

### `acoustic_petrov_d_np_classification`

**Statement.** The draining-bathtub / acoustic Kerr-Schild metric is Petrov type D in the full Newman-Penrose sense: the Weyl curvature spinor satisfies the type-D vacuum reformulation Psi_ABCD = Phi_(AB Phi_CD)/S for the KS congruence. DISTINCT from the PROVEN in-tree content (2026-07-20 R-02 rebuild): the genuine Kerr-Schild decomposition with a falsifiable null condition + the exact Sherman-Morrison inverse (`kerrSchild_exact_inverse`), the Maxwell single copy A = phi*k, the derived 3-obstruction BCJ no-go, and `IsPetrovD` in the KS repeated-principal-null sense (KS form + nonzero null congruence).

- status `proposed — NOT consumed by any Lean theorem (the R-02 rebuild dropped the redundant conjunction; WeylSpinor.lean records only the KS precondition). Tracks the residual full-NP-classification claim carried by README/RESEARCH_STATUS_OVERVIEW prose (both updated 2026-07-20 to cite this entry).` · eliminability `very_hard` · module `DoubleCopy/WeylSpinor.lean (documents the gap; the genuine KS content lives in DoubleCopy/PetrovD.lean + SingleCopy.lean + BCJNoGo.lean and KerrSchild.lean)`
- **Posture.** The acoustic Kerr-Schild metric is type D in the KS repeated-principal-null sense (proven); the full Newman-Penrose Petrov classification and the type-D vacuum reformulation await a spinor formalism absent from Mathlib.
- **Discharge path.** Requires a Newman-Penrose / 2-spinor formalism absent from Mathlib AND PhysLib (VERIFIED 2026-07-20: pinned Mathlib v4.29.1 has CliffordAlgebra + spinGroup/pinGroup — the abstract Clifford/Spin layer only; recent Mathlib master adds Riemannian METRICS/bundles (IsRiemannianManifold) but NO curvature tensors of any kind, no Lorentzian signature machinery, no tetrads, no SL(2,C) 2-spinor calculus, no Petrov classification; the PhysLib Lake dep is QuantumInfo-only — zero GR content, direct package read). Missing layer: spinor dyads, the Weyl curvature spinor, principal null directions, the Petrov classification theorem (CK-Duality DR §8.2 flags the same absence for spinor-helicity). A future Phase 6X wave or Mathlib spinor-geometry contribution; Phase 6o-prime Wave 1b-prime tracks it (docs/roadmaps/Phase6o_prime_Roadmap.md).
- **Source.** Stephani et al., Exact Solutions of Einstein Field Equations (Petrov classification); Monteiro-O'Connell-White JHEP 12 (2014) 056 (Kerr-Schild double copy); Color-Kinematics Duality DR §8.2.
- **Risk.** Low physically (the draining-bathtub metric being type D is standard in the analog-gravity literature); carried honestly as a landmark. The load-bearing double-copy content (KS + single copy + BCJ no-go) is PROVEN and does not depend on this entry.

### `acyclic_factor_graph_has_rank_cert`

**Statement.** Every acyclic (tree) factor graph admits a BP rank certificate (BeliefPropagation.BPRankCert G): a topological subtree-depth order on directed message endpoints with the two strict-monotonicity properties. Equivalently `IsAcyclicFactorGraph G → Nonempty (BPRankCert G)`.

- status `proposed — BUILDABLE follow-up (corrected-posture: on the build queue, not a permanent assumption). The genuine convergence theorem `bp_converges_on_ranked_acyclic` is PROVEN taking a concrete BPRankCert as an explicit binder, and fires non-vacuously on a real 3-node tree (`bp_converges_on_star`). This entry tracks ONLY the general acyclic⟹cert-exists step, which would upgrade the theorem to `IsAcyclicFactorGraph G → (BP converges)` with no cert hyp.` · eliminability `hard` · module `BeliefPropagation.lean (`bp_converges_on_ranked_acyclic` takes cert : BPRankCert G explicitly; `bp_converges_on_star` is the concrete-tree non-vacuity witness)`
- **Posture.** Belief propagation converges to a fixed point on tree (acyclic) factor graphs in ≤ diameter rounds. The project proves this on the actual message-passing dynamics GIVEN the tree rank certificate (witnessed on a real tree); the general "every acyclic graph admits the certificate" step is a buildable follow-up.
- **Discharge path.** A finite well-founded construction: leaf-strip the acyclic bipartite incidence graph (SimpleGraph.deleteEdges + dist + connected-component sup) to assign the subtree-depth rank and discharge the two strict-monotonicity obligations by a strict-subset cardinality argument. In-tree buildable (a routine graph-theory grind); scoped as a follow-up brick.
- **Source.** Standard: belief propagation is exact on trees (Pearl 1988; Yedidia–Freeman–Weiss 2003). The rank certificate = the tree topological / subtree-depth order.
- **Risk.** Very low — BP-exact-on-trees is textbook; the certificate is a routine finite well-founded construction. Buildable in-tree.

### `carrollian_boundary_bms_vertex`

**Statement.** The acoustic analog-Hawking null boundary (sonic horizon) carries a Carrollian structure (degenerate boundary metric + null direction) whose BMS-type asymptotic-symmetry supertranslation charges satisfy the charge-conservation Ward identity equivalent to the acoustic soft theorem — the THIRD Strominger-triangle vertex. The other triangle content is PROVEN kernel-pure: the soft theorem (Boostless.lean) and the memory↔soft edge (SoftTheorems/Carrollian.lean `memory_eq_softCharge`, FTC-proved, with `burst_satisfies_ward`).

- status `proposed — BUILDABLE follow-up (operator-authorized 2026-07-20, corrected-posture: on the build queue, not a permanent assumption). The former `True`-placeholder predicates (`IsCarrollianBoundary`, `IsAsymptoticSymmetryWard`) were REMOVED in the R-01 remediation (2026-07-20); nothing in-tree asserts this vertex. This entry tracks the genuine build.` · eliminability `moderate` · module `SoftTheorems/Carrollian.lean (the "Documented GAP" section states the three required structures precisely; the proven memory/soft content lives in the same module)`
- **Posture.** The Strominger triangle for analog Hawking systems has two of its three corners proven in-tree (soft theorem; memory↔soft-charge Ward relation). The third — Carrollian null-boundary geometry carrying BMS supertranslation charges whose conservation IS the soft theorem — requires a bounded Carrollian/BMS formalization arc (Phase 6o-prime Wave 1a-prime), fenced to analog fidelity. Tracked here until the arc discharges it.
- **Discharge path.** The Phase 6o-prime Wave 1a-prime arc (docs/roadmaps/Phase6o_prime_Roadmap.md): C0 literature-anchoring scout (horizon/membrane-paradigm BMS charge algebra for the analog case) -> C1 CarrollianStructure (degenerate metric + null field) + acoustic-horizon instance -> C2 Witt/Virasoro in-tree (Mathlib has LieAlgebra.Extension for the central extension; no named Virasoro) -> C3 BMS semidirect product + supertranslation subalgebra -> C4 boundary phase-space model + charge functionals (the vacuity-risk item; Fable-gate before consumption) -> C5 the charge Ward identity wiring the triangle third vertex -> C6 vacuity gate round. SCOPE FENCE: analog-appropriate fidelity ONLY (acoustic horizon, BMS-3 / Carrollian-line, algebraic phase-space model) — NOT asymptotically-flat BMS-4 with asymptotic expansions. Reference class: the cylinder cap-cross arc (~10 worker tasks).
- **Source.** Penna arXiv:1508.06577 (membrane-paradigm horizon charges — THE transcription target per the C0 verdict: Q_f = ∫ f·κ/8π, conservation via Damour-Navier-Stokes); Agrawal-Nguyen arXiv:2504.10577 (the supertranslation Ward identity <-> soft-mode insertion; attribution corrected 2026-07-20 — formerly miscited as Have-Nguyen-Prohazka-Salzer, = arXiv:2402.05190); Donnay-Giribet-Gonzalez-Pino arXiv:1511.08687 (horizon Vect(S¹)⋉C∞(S¹)_ab algebra); Donnay-Marteau arXiv:1903.09654 (horizon = Carrollian geometry); Barnich-Compere gr-qc/0610130 (BMS₃; central extension lives in the CHARGE algebra only); Strominger-Zhiboedov arXiv:1411.5745 (the memory corner); Mason-Ruzziconi-Yelleshpur Srikant arXiv:2312.10138 (Carrollian amplitudes); Datta-Fischer arXiv:2011.05837 (BEC acoustic memory); C0 verdict: Lit-Search/Phase-6o-prime/C0_horizon_BMS_charge_algebra_verdict_20260720.md; On-Shell Methods DR §4.3, §8.2.
- **Risk.** Low physically (the Carrollian/BMS soft-theorem correspondence is established for gravitational systems; the analog transcription is standard-shaped). Formalization-novel: no paper proves a BMS theorem for an acoustic analog (On-Shell DR §4.3), so the bounded build is itself a novel result. Main technical risk concentrates in C4 (the phase-space / charge model must act non-trivially — vacuity-gated).

### `he3a_moving_eta_nonzero`

**Statement.** The APS η-invariant (regularized spectral asymmetry of the non-zero spectrum) of the ³He-A MOVING (boosted / time-dependent 3D) domain-wall Dirac operator on the horizon 3-manifold Σ = S²×ℝ is non-zero. DISTINCT from the zero-mode / boundary-correction term h(Σ)=1, which IS proven kernel-pure (APSEta/He3A.lean: a genuine Jackiw–Rebbi normalizable zero mode → boundaryKernelDim_He3AMovingDomainWall_eq_one → apsIndex_..._ne_zero, apsIndex = −1/2 ≠ 0).

- status `proposed — NOT consumed by any Lean theorem; the in-tree `etaInvariant .He3AMovingDomainWall = 0` is kept HONEST (the static 1D reduction has a λ↦−λ symmetric non-zero spectrum, so η = 0 genuinely). This entry tracks ONLY the residual η-spectral-asymmetry-SYMBOL claim for the full moving operator; the genuine non-zero APS boundary CONTENT ³He-A carries (apsIndex ≠ 0) is a separate proven theorem.` · eliminability `very_hard` · module `APSEta/He3A.lean (§7 documents this gap precisely; §1–§6 ship the PROVEN Jackiw–Rebbi zero-mode / boundary-correction content)`
- **Posture.** The ³He-A moving-domain-wall analog horizon is expected to carry a non-zero APS η spectral-asymmetry invariant (Volovik chirality-vector framework). The project PROVES the non-zero APS boundary correction (apsIndex = −1/2, from a genuine Jackiw–Rebbi zero mode); the η-invariant symbol for the full moving 3D operator awaits Dirac-operator / APS-index infrastructure absent from Mathlib.
- **Discharge path.** Requires substrate absent from Mathlib v4.29.1 and in-tree: (1) the moving 3D domain-wall Dirac operator as an unbounded self-adjoint operator on an L² section space; (2) its discrete spectrum with multiplicities (compact-resolvent spectral theory); (3) the APS η-function η(s)=Σ_{λ≠0} sgn(λ)|λ|^{−s} + analytic continuation to s=0; (4) the APS index theorem for manifolds with boundary (Mathlib lacks even the closed-manifold Atiyah–Singer theorem). A future Phase 6X wave or a Mathlib Dirac/APS contribution.
- **Source.** Volovik, The Universe in a Helium Droplet (2003); Phys. Rep. 351 (2001) 195 (chirality vector, moving domain wall); Atiyah–Patodi–Singer I–III (1975–76).
- **Risk.** Low physically (Volovik chirality asymmetry is well-established) — but UNPROVEN in-tree; carried honestly as a landmark, NOT asserted as a theorem.

### `intCapIsoData_determinant_datum`

**Statement.** For a closed ORIENTED 4-manifold M with integral fundamental class [M] : Homology X 4 and a finite free H²-basis B : IntH2Basis X, the integral Poincaré duality is carried (Phase 5q.H · E1 Substrate-G, brick 10) as the CONCRETE, CHECKABLE determinant datum SKEFTHawking.SingularCohomologyInt.IntCapIsoData zM B — the sharpened replacement for IntCapIso's two abstract ≃ₗ fields. It discloses ONLY: (a) h2Basis : Module.Basis (Fin B.rank) ℤ (Homology X 2) — a finite free basis of H₂(M;ℤ) indexed by the SAME Fin B.rank as the H² basis (the equal-rank index IS the Poincaré-duality fact b₂(H₂)=b₂(H²); the homology-side analogue of IntH2Basis); (b) capUnit : IsUnit (det ((toMatrix B.basis h2Basis) (capMapLin zM))) — the integer cap matrix is unimodular; (c) kronUnit : IsUnit (det ((toMatrix h2Basis B.basis.dualBasis) kronMapLin)) — the integer Kronecker matrix is unimodular. The MAPS capMapLin := capHInt 2 1 · [M] and kronMapLin := (kroneckerHInt 2).flip are BUILT (kernel-pure), not disclosed; only their invertibility (as ONE integer determinant unit each, det = ±1 by Int.isUnit_iff) is disclosed. IntCapIsoData → IntCapIso → IntPoincareDuality via IntCapIsoData.toIntCapIso (LinearEquiv.ofIsUnitDet on each map) + intPoincareDualityOfCapIso. This is the exact integer analogue of the H²-side interMatrix datum, strictly sharper than IntCapIso's abstract isos.

- status `superseded_on_wiring_path (2026-07-12 arm-2: the live σ÷16 wiring is hcoreG_intrinsicInt → openDuality_univ_bij_of_hcoreGInt → capEquivInt → sixteen_dvd_latticeSig_of_capEquiv, and SingularSixteenDvdUnconditionalInt.sixteen_dvd_latticeSigInt consumes NO capIso/intPD datum; this datum remains a valid ALTERNATIVE interface for datum-supplied PD, off the critical path)` · eliminability `hard` · module `IntPoincareDualityCapIso`
- **Posture.** The integral Poincaré-duality input, sharpened one further step (Phase 5q.H · E1 Substrate-G brick 10) from the abstract IntCapIso to the CONCRETE determinant datum IntCapIsoData: an H₂ free basis + two unimodular integer determinants (cap matrix, Kronecker matrix) on the BUILT maps capMapLin/kronMapLin, reduced to IntCapIso via LinearEquiv.ofIsUnitDet. The exact integer analogue of the H²-side interMatrix datum. The on-main mod-2 injective nondeg_of_closed is captured algebraically by odd_capMatrix_det_of_mod2_unit (unit mod-2 reduction ⟹ Odd det) — the honest floor, one parity-step short of the full det = ±1. Feeds IsEvenUnimodular → σ ÷ 16 via interMatrix_isUnimodular_of_capIsoData.
- **Discharge path.** Discharge (a) h2Basis: build integral singular H₂(M;ℤ), prove it finitely generated, split off the free part (Module.Free/Module.Finite over the PID ℤ ⟹ a finite basis) — the exact homology-side mirror of the H² intH2_basis_datum discharge. Discharge (b) capUnit + (c) kronUnit: prove the built maps capMapLin / kronMapLin have unimodular matrices — the integral local-global cap-iso (Mayer–Vietoris + the Euclidean/ball local model over ℤ) and the integral UCT perfect pairing (Ext-free free-part), each now a SINGLE integer-determinant fact rather than an abstract iso. PARTIAL DONE (brick 10): odd_capMatrix_det_of_mod2_unit derives Odd (det cap matrix) from a unit mod-2 reduction of the cap matrix (the exact algebraic content of the on-main mod-2 injective nondeg_of_closed in matching rank), via RingHom.map_det + ZMod 2 being a field — the HONEST floor the mod-2 shadow gives, one parity-step short of IsUnit det (det odd, e.g. 3, is NOT unimodular). The residual is exactly the parity → unit strengthening.
- **Source.** Standard 4-manifold topology (Poincaré duality; Hatcher §3.3 Thm 3.30, Milnor–Stasheff): ·⌢[M] is an iso and the Kronecker/UCT pairing identifies H₂ with the ℤ-dual of H² on the free part — each an invertible integer matrix in matched free bases. The reduction map-with-unit-det ⟹ ≃ₗ uses the Mathlib bridge LinearEquiv.ofIsUnitDet (f with IsUnit ((toMatrix v v') f).det is a ≃ₗ underlying f, LinearEquiv.ofIsUnitDet_apply), proved unconditionally here. The mod-2 floor uses RingHom.map_det (f (det M) = det (f.mapMatrix M)) + Int.two_dvd_ne_zero / ZMod.intCast_zmod_eq_zero_iff_dvd.
- **Risk.** Low mathematically (textbook PD; each disclosed fact is a single unimodular integer determinant); cost is the from-scratch Lean construction of integral H₂ + the two iso proofs, now isolated as concrete determinant units. Every result in IntPoincareDualityCapIso holds for an ARBITRARY IntCapIsoData datum.
- **Circularity.** None. IntCapIsoData.toIntCapIso builds IntCapIso for an ARBITRARY IntCapIsoData; the maps capMapLin/kronMapLin are BUILT and the reduction (LinearEquiv.ofIsUnitDet + intPoincareDualityOfCapIso) assumes no property of a specific future datum. The mod-2 partial odd_capMatrix_det_of_mod2_unit is a pure algebraic implication (unit mod-2 reduction ⟹ odd det), taking its hypothesis as given — it does NOT assume the conclusion. This datum REFINES intCapIso_datum (which remains valid) by exposing the concrete determinant decomposition. NOT the lattice-Arf route (nogo_lattice_arf_not_sigma8): a genuine PD fact, orthogonal to the banned σ/8 ≡ Arf congruence.
- **Consumers.** `SKEFTHawking.SingularCohomologyInt.capMapLin`, `SKEFTHawking.SingularCohomologyInt.kronMapLin`, `SKEFTHawking.SingularCohomologyInt.IntCapIsoData.toIntCapIso`, `SKEFTHawking.SingularCohomologyInt.intPoincareDualityOfCapIsoData`, `SKEFTHawking.SingularCohomologyInt.interMatrix_isUnimodular_of_capIsoData`, `SKEFTHawking.SingularCohomologyInt.odd_det_of_isUnit_det_map_zmod2`, `SKEFTHawking.SingularCohomologyInt.odd_capMatrix_det_of_mod2_unit`

### `intCapIso_datum`

**Statement.** For a closed ORIENTED 4-manifold M with integral fundamental class [M] : Homology X 4, the integral Poincaré duality is carried (Phase 5q.H · E1 Substrate-G, brick 6) as the CLEANER GEOMETRIC datum SKEFTHawking.SingularCohomologyInt.IntCapIso zM, holding two ISO facts: (i) capEquiv : Cohomology X 2 ≃ₗ[ℤ] Homology X 2 = the integral CAP MAP ·⌢[M] : H²(M;ℤ) → H₂(M;ℤ) is an isomorphism (with capEquiv_apply fixing its underlying map to capHInt 2 1 · [M]); (ii) kronEquiv : Homology X 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology X 2) = the integral KRONECKER pairing H₂(M;ℤ) → Dual ℤ H²(M;ℤ) is a perfect pairing (with kronEquiv_apply fixing it to h ↦ ⟨·,h⟩ = kroneckerHInt 2 · h). This SUPERSEDES/refines intPoincareDuality_perfectPairing_datum: the integral cap product ·⌢[M], the descent to (co)homology capHInt, the integral Kronecker kroneckerHInt, and the cap–cup adjunction ⟨a∪b,[M]⟩=⟨b,a⌢[M]⟩ are now ALL BUILT (kernel-pure), so IntPoincareDuality is inhabited from IntCapIso by intPoincareDualityOfCapIso (its toDualEquiv = capEquiv.trans kronEquiv, toDualEquiv_apply from interFormInt_eq_kroneckerHInt_capHInt). The residual disclosed input is now PRECISELY the two isos (cap-iso + Kronecker perfect pairing) — the exact char-0 upgrade of the on-main mod-2 INJECTIVE nondeg_of_closed (mod-2 injectivity of ·⌢[M] → integral iso).

- status `superseded_on_wiring_path (2026-07-12 arm-2: the live σ÷16 wiring is hcoreG_intrinsicInt → openDuality_univ_bij_of_hcoreGInt → capEquivInt → sixteen_dvd_latticeSig_of_capEquiv, and SingularSixteenDvdUnconditionalInt.sixteen_dvd_latticeSigInt consumes NO capIso/intPD datum; this datum remains a valid ALTERNATIVE interface for datum-supplied PD, off the critical path)` · eliminability `hard` · module `IntCapProductInt`
- **Posture.** The integral Poincaré-duality input, sharpened (Phase 5q.H · E1 Substrate-G brick 6) to the CLEANER geometric datum IntCapIso: the integral cap map ·⌢[M] : H²(M;ℤ) → H₂(M;ℤ) is an iso + the integral Kronecker H₂ ≃ Dual H² is a perfect pairing. With the integral cap product, its descent to (co)homology (capHInt), the integral Kronecker, and the cap–cup adjunction now ALL BUILT kernel-pure, IntPoincareDuality is inhabited from IntCapIso (intPoincareDualityOfCapIso), so the residual reduces to exactly the two isos — the char-0 upgrade of the on-main mod-2 injective nondeg_of_closed. Feeds the whole IsEvenUnimodular → σ ÷ 16 leg via interMatrix_isUnimodular_of_capIso.
- **Discharge path.** Discharge (i) the cap-iso: prove capHInt 2 1 · [M] : H²(M;ℤ) → H₂(M;ℤ) is bijective — the integral upgrade of the on-main mod-2 injective SingularPD4Instances.nondeg_of_closed (the capH-injectivity / P₄(univ) Bott–Tu tower), which needs the integral local-global cap-iso theorem (Mayer–Vietoris + the Euclidean/ball local model over ℤ). Discharge (ii) the Kronecker perfect pairing H₂(M;ℤ) ≃ Dual ℤ H²(M;ℤ): universal coefficients over ℤ for a finitely-generated free-part (co)homology — the integral UCT (Ext-term); over a field this is homology_eq_zero_of_kroneckerH (the mod-2 shadow). Both are the community-scale integral-PD core; everything ELSE (cap, adjunction, descent, the reduction) is now proved.
- **Source.** Standard 4-manifold topology (Poincaré duality via the cap product with the fundamental class; Hatcher §3.3 Thm 3.30, Milnor–Stasheff): for a closed oriented M, ·⌢[M] : Hᵏ(M;ℤ) → H_{n-k}(M;ℤ) is an isomorphism, and the Kronecker/UCT pairing identifies H₂ with the ℤ-dual of H² on the free part. The signed cap-Leibniz ∂(a⌢c)=(-1)ᵏ⁺¹(δa⌢c)+(-1)ᵏ(a⌢∂c) (capInt_leibniz) is the genuine ℤ boundary identity (the mod-2 file dropped the signs via +1=-1); the cap–cup adjunction ⟨a∪b,c⟩=⟨b,a⌢c⟩ is sign-free.
- **Risk.** Low mathematically (textbook Poincaré duality); cost is the from-scratch Lean proof of the two isos (cap-iso + Kronecker perfect pairing), the integral upgrade of the on-main mod-2 injective tower. Every result here holds for an ARBITRARY IntCapIso datum, so the datum is the ONLY unproved input to unimodularity via this route.
- **Circularity.** None. intPoincareDualityOfCapIso builds IntPoincareDuality for an ARBITRARY IntCapIso; the reduction (toDualEquiv = capEquiv.trans kronEquiv, compatibility from the PROVED adjunction interFormInt_eq_kroneckerHInt_capHInt) assumes no property of a specific future cap-iso. NOT the lattice-Arf route (nogo_lattice_arf_not_sigma8): the cap-iso is a genuine geometric PD fact, orthogonal to the banned σ/8 ≡ Arf congruence. This datum REFINES intPoincareDuality_perfectPairing_datum (which remains valid; this one exposes the cleaner cap-iso decomposition now that the cap tower is built).
- **Consumers.** `SKEFTHawking.SingularCohomologyInt.capHInt`, `SKEFTHawking.SingularCohomologyInt.kroneckerInt_cup_capInt`, `SKEFTHawking.SingularCohomologyInt.kroneckerHInt_cupH24`, `SKEFTHawking.SingularCohomologyInt.interFormInt_eq_kroneckerHInt_capHInt`, `SKEFTHawking.SingularCohomologyInt.intPoincareDualityOfCapIso`, `SKEFTHawking.SingularCohomologyInt.interMatrix_isUnimodular_of_capIso`

### `intFundamentalClass_eval_datum`

**Statement.** For a closed oriented charted 4-manifold M, the integral fundamental class [M] ∈ H₄(M;ℤ) is carried (Phase 5q.H · E1) as the ℤ-linear evaluation functional it induces on top-degree integral cohomology: the single field `eval : Cohomology X 4 →ₗ[ℤ] ℤ` of the structure SKEFTHawking.SingularCohomologyInt.IntFundamentalClass, i.e. the integral Kronecker pairing ⟨·,[M]⟩.

- status `proven (5q.H arm-2, 2026-07-12: DISCHARGED at every consumed instance by SingularHomologyInt.intFundamentalClassOfHomology — eval := (kroneckerHInt 4).flip [M], kernel-pure — and its orientation form intFundamentalClassOfIntOrientation; the abstract IntFundamentalClass structure remains as the interface, its eval field no longer a free posit)` · eliminability `very_hard` · module `SingularIntersectionFormInt`
- **Posture.** The integral fundamental class [M] ∈ H₄(M;ℤ) of a closed oriented 4-manifold, carried as its induced evaluation functional ⟨·,[M]⟩ so the H⁴-valued integral cup product cupH24 descends to the ℤ-valued symmetric intersection form (Phase 5q.H · E1 Substrate-G; pre-matrix, orientation deferred).
- **Discharge path.** Discharge = build integral singular homology H₄(M;ℤ) (the on-main homology + Kronecker tower is entirely over ZMod 2 — SingularHomologyMod2/kroneckerH), the orientation-dependent fundamental class [M] ∈ H₄(M;ℤ) (the new ℤ ingredient the mod-2 blueprint SingularFundamentalClass does NOT need — every closed manifold is ℤ/2-orientable), and the integral cohomology↔homology Kronecker pairing kroneckerHInt; then instantiate eval := (kroneckerHInt 4).flip [M], exactly mirroring the mod-2 PoincareDualityConstruct.fundamentalFunctional = kroneckerH.flip fundamentalClass. Community-scale (integral homology + orientation are absent from Mathlib and on-main); tracked here so the intersection form itself (interFormInt + interFormInt_symm, kernel-pure) has exactly ONE unproved input.
- **Source.** Standard algebraic topology (Milnor–Stasheff; Hatcher §3.3): the fundamental class of a closed oriented n-manifold + the Kronecker (evaluation) pairing Hⁿ(M;ℤ) × Hₙ(M;ℤ) → ℤ.
- **Risk.** Very low mathematically (textbook); the cost is purely the from-scratch Lean construction of integral homology + orientation, deferred to a later E1 brick. The FORM assembled here is unconditional on `eval`.
- **Circularity.** None. The intersection form and its symmetry are proved for an ARBITRARY functional eval : H⁴ →ₗ[ℤ] ℤ; no property of the (future) geometric [M] is assumed, so wiring the real [M] later strictly discharges this datum without touching the form.
- **Consumers.** `SKEFTHawking.SingularCohomologyInt.interFormInt`, `SKEFTHawking.SingularCohomologyInt.interFormInt_symm`

### `intH2_basis_datum`

**Statement.** For a closed 4-manifold M, a finite free ℤ-basis of H²(M;ℤ) = Cohomology (TopCat.of M) 2 is carried (Phase 5q.H · E1 Substrate-G) as a disclosed datum: the structure SKEFTHawking.SingularCohomologyInt.IntH2Basis, holding a rank `n : ℕ` (= the free rank b₂(M)) and a field `basis : Module.Basis (Fin n) ℤ (Cohomology X 2)`. This is the finite-free-basis input that turns the ℤ-bilinear intersection form interFormInt into its Gram MATRIX interMatrix : Matrix (Fin n) (Fin n) ℤ.

- status `active` · eliminability `very_hard` · module `IntersectionMatrixInt`
- **Posture.** A finite free ℤ-basis of H²(M;ℤ) for a closed 4-manifold, carried as a disclosed datum so the symmetric ℤ-bilinear intersection form interFormInt descends to its integer Gram matrix interMatrix — the concrete arithmetic object the DONE lattice σ÷16 theorem consumes (Phase 5q.H · E1 Substrate-G; the final structural link integral-cohomology → cup → form → matrix → σ÷16).
- **Discharge path.** SHARPENED 2026-07-12 (arm-2, scout-verified vs FNOP arXiv:1910.07372 + Blass–Göbel math/9405206): the ℤ-analog of the mod-2 Erdős–Kaplansky self-duality forcing is PROVABLY BLOCKED (Specker: (⊕ℤ)⊕ℤ^ℕ is self-dual, not f.g.) — SETTLED_FORKS § 5qH-fg-ek-over-Z-blocked. Minimal published general-M route = Borsuk-ENR retract-of-finite-CW (FNOP Cor 3.18; community-scale; CW existence for compact TOP 4-manifolds is OPEN, FNOP Q3.15; smooth case = Morse, Mathlib-absent). PROJECT PATH: witness-level data — explicit finite free bases for the concrete carrier manifolds (ℝP⁴ chain etc.), + free-quotient descent where torsion appears. All results here hold for an ARBITRARY basis, isolating the free-module input as this one datum.
- **Source.** Standard algebraic topology (Hatcher §2.2/§3.1; Milnor–Stasheff): the integral cohomology of a closed manifold is finitely generated (finite CW structure), and over the PID ℤ a finitely-generated module splits as free ⊕ torsion, so its free part has a finite basis.
- **Risk.** Very low mathematically (textbook finite-generation + PID structure theorem); the cost is purely the from-scratch Lean construction of finite integral cohomology, deferred to a later E1 brick. The MATRIX, its symmetry, and the σ÷16 composition assembled here are unconditional on the choice of basis.
- **Circularity.** None. interMatrix and all its downstream results are built for an ARBITRARY IntH2Basis; no property of a specific (future) geometric basis is assumed. The genuinely-geometric inputs to the σ÷16 headline (IsEvenUnimodular interMatrix = even/Wu + unimodular/PD, and the topological factor 2∣σ/8 = Guillou–Marin) are left explicitly as hypotheses, NOT folded into this datum.
- **Consumers.** `SKEFTHawking.SingularCohomologyInt.interMatrix`, `SKEFTHawking.SingularCohomologyInt.interMatrix_isSymm`, `SKEFTHawking.SingularCohomologyInt.interMatrix_transpose`, `SKEFTHawking.SingularCohomologyInt.interMatrix_isSymmetricInt`, `SKEFTHawking.SingularCohomologyInt.eight_dvd_manifold_sig`, `SKEFTHawking.SingularCohomologyInt.sixteen_dvd_manifold_sig`

### `intLocalHomologyIso_datum`

**Statement.** For a topological space M and a point x : M, the integral LOCAL homology iso H₄(M, M∖x; ℤ) ≅ ℤ is carried (Phase 5q.H · E1 Substrate-G) as the disclosed structure SKEFTHawking.SingularRelHomologyInt.IntLocalHomologyIso M x, holding (i) iso : RelHomologyInt (localSub x) 4 ≃+ ℤ (the integral local group ≅ ℤ, two generators ±1), (ii) isoMod2 : the ON-MAIN mod-2 local group SingularRelativeHomologyMod2.RelativeHomology (localSub x) 4 ≃+ ZMod 2 (the shadow), and (iii) redCompat : ∀ z, isoMod2 (redRelHomology (localSub x) 4 z) = ((iso z : ℤ) : ZMod 2) — the mod-2 compatibility tying the integral iso to the on-main mod-2 local group via the (PROVED here, kernel-pure) ℤ→ℤ/2 relative-homology reduction bridge redRelHomology. This is the SHARED prerequisite for BOTH remaining E1 geometric cores: (A) orientation coherence (the two ±1 local generators force the coherent global sign-section that intOrientation_datum records as [M]), and (B) the PD local-global cap-iso (the local Euclidean model). Around it this brick BUILDS the full integral relative-homology / pair-LES substrate (RelHomologyInt = ker∂/im∂ over ℤ, the pair map homProjInt : Hₙ(X;ℤ) → RelHomologyInt, the connecting δ = connectingInt, the complex property δ∘j_* = 0, and redRelHomology) — the ℤ mirror of on-main SingularRelativeHomologyMod2 / SingularPairLES, ALL kernel-pure and unconditional; only the ℤ-generator identification of the local group is disclosed.

- status `proven (5q.H E1 brick 17b — hypothesis-free at charted 4-manifolds: SingularReducedGeneratorInt.intLocalHomologyIso_of_manifold' constructs the full 3-field datum (iso/isoMod2/redCompat), kernel-pure; the one residual ReducedGeneratorNonzero is discharged by reducedGeneratorNonzero via chartLocalIso_generator_reduces_ne_zero. Re-marked 2026-07-12 arm-2 after the atlas kept ranking it open)` · eliminability `very_hard` · module `SingularRelHomologyInt`
- **Posture.** The integral local homology iso H₄(M, M∖x; ℤ) ≅ ℤ of a 4-manifold at a point, carried as a disclosed datum (the local iso + its mod-2 compatibility with the on-main mod-2 local group via the reduction bridge) so that BOTH remaining E1 cores — orientation coherence and the PD local-global cap-iso — are discharged from this single shared geometric input. Around it the full integral relative-homology / pair-LES substrate (RelHomologyInt, homProjInt, connectingInt, δ∘j_*=0, redRelHomology) is built unconditionally and kernel-pure — the ℤ mirror of the on-main mod-2 blueprint (Phase 5q.H · E1 Substrate-G; the integral local-homology tower Mathlib/on-main lack).
- **Discharge path.** Discharge = the ℤ local reduction tower H₄(ℝ⁴,ℝ⁴∖0;ℤ) ≅ H₃(ℝ⁴∖0;ℤ) ≅ H₃(S³;ℤ) ≅ ℤ. The pair-LES connecting-iso step is provable from the integral pair LES built here (homProjInt / connectingInt / the exactness lemmas, mirroring SingularLocalHomology.connecting_bijective_of_acyclic) ONCE two from-scratch integral inputs land: (1) integral Euclidean acyclicity Hₖ(ℝⁿ;ℤ)=0 for k≥1 (the ℤ upgrade of on-main SingularEuclideanAcyclic, ZMod 2 only), and (2) integral sphere homology H₃(S³;ℤ) ≅ ℤ (the ℤ upgrade of on-main SphereHomology, ZMod 2 only) + the punctured retract ℝ⁴∖0 ≃ S³ (SingularPuncturedRetract, coefficient-independent). redCompat then holds by naturality of redRelHomology (PROVED unconditionally here) over the mod-2 tower (SingularLocalHomology.connecting_eucl_bijective). Community-scale (integral Euclidean acyclicity + integral sphere homology absent from Mathlib AND on-main — the on-main homology tower is entirely over ZMod 2); tracked so both E1 cores hold for an ARBITRARY such datum, isolating the ℤ local-generator identification as this one shared geometric input.
- **Source.** Standard algebraic topology (Hatcher §2.2/§3.3, Milnor–Stasheff §11): the local homology Hₙ(M, M∖x; ℤ) ≅ ℤ of an n-manifold, computed via the LES of the pair (ℝⁿ, ℝⁿ∖0) with ℝⁿ acyclic + the retract ℝⁿ∖0 ≃ Sⁿ⁻¹ + Hₙ₋₁(Sⁿ⁻¹;ℤ) ≅ ℤ; its two generators ±1 are the local orientations, whose mod-2 reduction is the (always-existing) unique mod-2 local generator. The ℤ→ℤ/2 relative reduction bridge redRelChain/redRelHomology is the relative dual of the absolute redChain/redHomology (brick 11).
- **Risk.** Very low mathematically (textbook local homology); the cost is purely the from-scratch Lean construction of integral Euclidean acyclicity + integral sphere homology, deferred to a later E1 brick. Everything else in the brick (the integral relative homology, the pair maps homProjInt/connectingInt, the complex property, the reduction bridge redRelHomology) is UNCONDITIONAL and kernel-pure; only the ℤ-generator identification of the local group is disclosed, and redCompat makes it non-vacuous (falsifiable against the on-main mod-2 local generator).
- **Circularity.** None. The integral relative homology, the pair LES core, and the reduction bridge are built UNCONDITIONALLY (kernel-pure); IntLocalHomologyIso and localGenerator/iso_localGenerator are stated for an ARBITRARY supplied datum, no property of a specific (future) geometric local iso is used beyond the disclosed redCompat. redRelHomology and its chain-map property redRelChain_relBoundary are proved unconditionally, so wiring the real local iso later strictly discharges this datum. This is the shared discharge-substrate for intOrientation_datum (A) and the PD local-global cap-iso (B) — it does not duplicate them, it isolates the ONE geometric input both share.
- **Consumers.** `SKEFTHawking.SingularRelHomologyInt.intLocalHomologyIso_redCompat`, `SKEFTHawking.SingularRelHomologyInt.localGenerator`, `SKEFTHawking.SingularRelHomologyInt.iso_localGenerator`, `SKEFTHawking.SingularRelHomologyInt.homProjInt`, `SKEFTHawking.SingularRelHomologyInt.connectingInt`, `SKEFTHawking.SingularRelHomologyInt.connectingInt_homProjInt`, `SKEFTHawking.SingularRelHomologyInt.redRelHomology`

### `intOrientation_datum`

**Statement.** For a closed charted 4-manifold M ([T2Space][CompactSpace][Nonempty][ChartedSpace (EuclideanSpace ℝ (Fin 4))]), the ORIENTATION-dependent input to the integral fundamental class is carried (Phase 5q.H · E1 Substrate-G) as the disclosed structure SKEFTHawking.SingularHomologyInt.IntOrientation M, holding (i) fundClass : Homology (TopCat.of M) 4 = the integral fundamental class [M] ∈ H₄(M;ℤ) produced by a coherent orientation of M, and (ii) redCompat : redHomology (TopCat.of M) 4 fundClass = SingularFundamentalClass.fundamentalClass (m:=2) — the mod-2 compatibility tying [M] to the ON-MAIN orientation-free mod-2 fundamental class [M]₂ via the ℤ→ℤ/2 reduction redHomology. This SHARPENS intFundamentalClass_eval_datum: the whole evaluation functional is now discharged from this single geometric datum (intFundamentalClassOfIntOrientation), and fundClass is not a free H₄ element — its mod-2 shadow must be the canonical [M]₂ (non-vacuous).

- status `active (HONEST geometric input — orientability. Constructor chain in-tree, kernel-pure: intOrientationDataOfOrientation (brick 18h; from a ±1 section + per-ball hasOrientedFundClassInt orientability input hballs, [PreconnectedSpace M]) → IntOrientationData → intOrientationOfData → IntOrientation; consumed at class level by SixteenDvdOfOrientation.sixteen_dvd_latticeSig_of_orientationData, arm-2 brick 10)` · eliminability `very_hard` · module `IntFundamentalClassOrientation`
- **Posture.** The orientation of a closed 4-manifold, carried as a disclosed datum (the integral fundamental class [M] ∈ H₄(M;ℤ) + its mod-2 compatibility with the on-main orientation-free [M]₂) so the integral intersection form is discharged from this single geometric input — the genuine new content over the mod-2 blueprint (Phase 5q.H · E1 Substrate-G; the orientation coherence Mathlib/on-main lack).
- **Discharge path.** Discharge = build integral relative/local singular homology RelativeHomologyInt Kᶜ n with the local iso H₄(M|x;ℤ) ≅ ℤ (the ℤ upgrade of the on-main mod-2 SingularRelativeHomologyMod2 / manifoldLocalIso, absent from Mathlib AND on-main — the on-main tower is entirely over ZMod 2), define restrictsToGeneratorInt/hasFundClassInt with a COHERENT choice of the ±1 local generators (= an orientation: the orientation local system trivial + a global section), and replay the on-main existence induction hasFundClass_chartBall/_union/_biUnion/_univ where the union step (SingularFundamentalClassExist.hasFundClass_union) now matches the two local ±1 generators via the orientation instead of the ℤ/2 collapse x+x=0 (ZModModule.add_self); extract fundClass. redCompat then holds by naturality of the ℤ→ℤ/2 reduction (redChain/redChain_chainBoundary/redHomology, PROVED unconditionally here) on the local-generator condition. Community-scale (integral homology + orientation absent from Mathlib and on-main); tracked here so intFundamentalClassOfIntOrientation and the whole intersection form hold for an ARBITRARY such datum, isolating orientation as this one input.
- **Source.** Standard algebraic topology (Milnor–Stasheff §11; Hatcher §3.3 Thm 3.26/3.27): a closed connected n-manifold has H_n(M;ℤ) ≅ ℤ iff it is orientable, and an orientation is a coherent choice of local generators of H_n(M, M∖x; ℤ) ≅ ℤ; its mod-2 reduction is the (always-existing) mod-2 fundamental class. The ℤ→ℤ/2 reduction on chains/homology (redChain/redHomology) is the dual of the on-main cochain reduction bridge IntersectionFormEvenInt.redC/redH.
- **Risk.** Very low mathematically (textbook orientation theory); the cost is purely the from-scratch Lean construction of integral relative/local homology + the coherent-generator gluing, deferred to a later E1 brick. Everything downstream of the datum (the intersection form, its symmetry) is unconditional on fundClass; the redCompat field makes the datum non-vacuous (falsifiable against the mod-2 [M]₂).
- **Circularity.** None. intFundamentalClassOfIntOrientation and the intersection form are built for an ARBITRARY IntOrientation; no property of a specific (future) geometric [M] is used beyond the disclosed redCompat. The ℤ→ℤ/2 comparison map redHomology and its chain-map property redChain_chainBoundary are proved UNCONDITIONALLY (kernel-pure), so wiring the real orientation later strictly discharges this datum. Refines (does not duplicate) intFundamentalClass_eval_datum: that carried the whole eval functional; this reduces it further to [M] : H₄(M;ℤ) + orientation coherence, the genuine residual.
- **Consumers.** `SKEFTHawking.SingularHomologyInt.intFundamentalClassOfIntOrientation`, `SKEFTHawking.SingularHomologyInt.intFundamentalClassOfIntOrientation_eval`, `SKEFTHawking.SingularHomologyInt.intOrientation_redHomology_fundClass`

### `intPoincareDuality_perfectPairing_datum`

**Statement.** For a closed ORIENTED 4-manifold M, the UNIMODULARITY (det = ±1) of the integer intersection matrix is carried (Phase 5q.H · E1 Substrate-G) as a disclosed datum: the structure SKEFTHawking.SingularCohomologyInt.IntPoincareDuality fc (tied to the integral fundamental class fc : IntFundamentalClass X), holding (i) toDualEquiv : Cohomology X 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology X 2) = the INTEGRAL Poincaré-duality perfect-pairing isomorphism (the curried intersection form a ↦ ⟨a∪·,[M]⟩ is a linear ISO onto the ℤ-dual; equivalently the integral cap map ·⌢[M] : H²(M;ℤ) → H₂(M;ℤ) is an iso, H₂ being ℤ-dual to H²); (ii) toDualEquiv_apply: ∀ a b, toDualEquiv a b = interFormInt fc a b — the compatibility fixing the equivalence to underlie the intersection form. This is the ONLY unproved input to interMatrix UNIMODULARITY. It is STRICTLY STRONGER than the on-main mod-2 injective non-degeneracy SingularPD4Instances.nondeg_of_closed (which gives only det ODD, not det = ±1).

- status `superseded_on_wiring_path (2026-07-12 arm-2: the live σ÷16 wiring is hcoreG_intrinsicInt → openDuality_univ_bij_of_hcoreGInt → capEquivInt → sixteen_dvd_latticeSig_of_capEquiv, and SingularSixteenDvdUnconditionalInt.sixteen_dvd_latticeSigInt consumes NO capIso/intPD datum; this datum remains a valid ALTERNATIVE interface for datum-supplied PD, off the critical path)` · eliminability `hard` · module `IntersectionFormUnimodularInt`
- **Posture.** The integral Poincaré-duality perfect-pairing input for a closed oriented 4-manifold, carried as a disclosed datum (the curried intersection form H²(M;ℤ) → Dual ℤ H²(M;ℤ) is a ℤ-linear iso) so the integer intersection matrix interMatrix is UNIMODULAR (det = ±1) — discharging the LAST conjunct of IsEvenUnimodular through LinearEquiv.isUnit_det + Int.isUnit_iff (Phase 5q.H · E1 Substrate-G). This completes the IsEvenUnimodular analysis: symmetric ✓ (graded-commutativity, proved) + even ✓ (SpinWuDatum) + unimodular ✓ (this datum) reduce IsEvenUnimodular interMatrix to exactly two clean disclosed geometric data. The integral iso is STRICTLY stronger than the on-main mod-2 injective nondeg_of_closed (det odd → det = ±1).
- **Discharge path.** Discharge = build the INTEGRAL homology H₂(M;ℤ) + the integral cap product ·⌢[M] : H²(M;ℤ) → H₂(M;ℤ) + the integral Kronecker pairing kroneckerHInt (the ℤ tower dual to the on-main SingularHomologyMod2 / kroneckerH), and prove the cap map an ISOMORPHISM (integral Poincaré duality). Then instantiate toDualEquiv from the composite H²(M;ℤ) ≃ H₂(M;ℤ) ≃ Dual ℤ H²(M;ℤ) and toDualEquiv_apply from the cap–cup adjunction ⟨a∪b,[M]⟩ = ⟨b, a⌢[M]⟩ (the integral mirror of the on-main fundamentalFunctional_cupH24 / kronecker_cup_cap). The char-2 shadow of this iso — INJECTIVITY of the mod-2 form — is ALREADY a theorem on main (nondeg_of_closed, via the capH-injectivity / P₄(univ) Bott–Tu tower); the integral upgrade (iso, not just injective; det = ±1, not just odd) is the community-scale core.
- **Source.** Standard 4-manifold topology (Poincaré duality; Milnor–Stasheff, Hatcher §3.3, Kirby–Taylor): the intersection form of a closed oriented 4-manifold is a PERFECT pairing on the free part of H²(M;ℤ), i.e. unimodular (det = ±1). The reduction perfect-pairing ⟹ det-unit uses the Mathlib bridges LinearEquiv.isUnit_det (a linear equivalence has unit determinant in any basis) + Int.isUnit_iff (IsUnit n ↔ n = 1 ∨ n = -1 over ℤ) + LinearMap.toMatrix_apply / Module.Basis.dualBasis_repr (the Gram matrix IS the matrix of the toDual map in the basis/dual-basis pair), all PROVED unconditionally here.
- **Risk.** Low mathematically (textbook: PD makes the intersection form unimodular); cost is the from-scratch Lean construction of integral homology H₂(M;ℤ) + the integral cap product + the iso proof, deferred to a later E1 brick. Every result in IntersectionFormUnimodularInt holds for an ARBITRARY such datum.
- **Circularity.** None. The unimodularity lemmas are built for an ARBITRARY IntPoincareDuality datum; no property of a specific (future) integral cap iso is assumed. The perfect-pairing ⟹ unit-det reduction (LinearEquiv.isUnit_det + Int.isUnit_iff + the Gram-matrix identification) is proved unconditionally. The evenness/Wu conjunct of IsEvenUnimodular is a SEPARATE disclosed datum (SpinWuDatum, spinWu_even_datum); this datum supplies ONLY unimodular. It is NOT the lattice-Arf route (nogo_lattice_arf_not_sigma8): unimodularity is a genuine PD fact, orthogonal to the banned σ/8 ≡ Arf congruence.
- **Consumers.** `SKEFTHawking.SingularCohomologyInt.interMatrix_eq_toMatrix_intPD`, `SKEFTHawking.SingularCohomologyInt.interMatrix_isUnit_det_of_intPD`, `SKEFTHawking.SingularCohomologyInt.interMatrix_isUnimodular_of_intPD`, `SKEFTHawking.SingularCohomologyInt.isEvenUnimodular_of_intPD`, `SKEFTHawking.SingularCohomologyInt.sixteen_dvd_manifold_sig_of_intPD`

### `niemeier_classification_exactly_24`

**Statement.** There are EXACTLY 24 even unimodular positive-definite lattices of rank 24 (the Niemeier lattices; Niemeier 1973). The Schellekens chain (Schellekens/*.lean, rebuilt genuine 2026-07-20) carries the falsifiable ARITHMETIC content this classification entails (24 = 8*3 = lcm(8,3) etc.); only the classification EXHAUSTIVENESS is this external hypothesis.

- status `proposed — an external-literature classification fact, disclosed in the module docstrings; the chain headline `schellekensChain_implies_24_divides_c_minus_iff_3_divides_N_gen` concludes its real arithmetic biconditional (via the kernel-checked GenerationConstraint) conditional at most on the named classification hypotheses.` · eliminability `very_hard` · module `Schellekens/NiemeierLattice.lean (docstring disclosure)`
- **Posture.** The 24 Niemeier lattices underpin the c=24 story; the chain encodes their arithmetic consequences and defers the exhaustiveness to this tracked external fact.
- **Discharge path.** Requires formalized lattice-classification machinery (even unimodular lattices, root systems, mass formulas / neighbor method) absent from Mathlib. A future Mathlib lattice-theory program; not project-critical (the arithmetic endpoint is proven independently).
- **Source.** Niemeier, J. Number Theory 5 (1973) 142; Conway-Sloane SPLAG Ch. 16.
- **Risk.** Effectively zero physically/mathematically (a settled 1973 classification); carried as an honest external-completeness landmark.

### `schellekens_c24_voa_classification_exactly_71`

**Statement.** There are EXACTLY 71 holomorphic vertex operator algebras of central charge 24 (Schellekens 1993 list; completeness proven by Moeller-Scheithauer 2024 and companions), each unique up to isomorphism. The chain carries the falsifiable count relations (24 <= 71; 71 = 70 + 1 with the Moonshine module); the classification EXHAUSTIVENESS/uniqueness is this external hypothesis.

- status `proposed — external-literature classification fact, disclosed in the module docstrings (see niemeier_classification_exactly_24 for the chain structure).` · eliminability `very_hard` · module `Schellekens/HolomorphicVOAc24.lean (docstring disclosure)`
- **Posture.** The 71 holomorphic c=24 VOAs anchor the Schellekens chain; the exhaustiveness is tracked here, the arithmetic consequences are proven in-tree.
- **Discharge path.** Requires formalized VOA theory (vertex algebras, characters, modular invariance, orbifold constructions) absent from Mathlib — a research-frontier formalization program.
- **Source.** Schellekens, Comm. Math. Phys. 153 (1993) 159; Moeller-Scheithauer arXiv:2112.12291 (Ann. Math. 2024) + companions.
- **Risk.** Very low (peer-reviewed completeness proof, Annals 2024); carried as an honest external-completeness landmark.

### `smith_inflow_z16`

**Statement.** The Smith homomorphism Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆ → Ω₄^{Pin⁺}, carried at the ℤ₁₆ level as an isomorphism `ZMod 16 ≃+ SKEFTHawking.SymTFT.Omega4PinPlusBordism` pinned to the canonical generator `smith 1 = Omega4PinPlusBordism.mk pinPlusRP4` (the structure SKEFTHawking.CommonOrigin.SmithInflow, consumed via the (S : SmithInflow) binder).

- status `superseded — RETIRED AS A STRATEGIC KEYSTONE (2026-07-21 atlas-integrity repair), formalizing the 2026-07-06 user-directed KT re-anchor which already DEMOTED this node to "an alternative route, not the required keystone" (SETTLED_FORKS § 5qH-injectivity-routes-all-equal-one-completeness-prop; PHASE5QH_EXECUTION_MAP: "the keystone is the KT GEOMETRIC exact-sequence close, NOT the spectral smith_inflow_z16 / ABP tower"). Retired for TWO independent reasons: (a) the Lean object named here is inhabited and canonical — not an open proposition (see atlas_typing_note); (b) the live 16-convergence keystone is the KT lane on the faithful `pinPlusCharPairData` carrier, whose open triple is {KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}. The entry is KEPT (not deleted) for provenance and because the geometric direct-Smith program (object 2 above) remains a real, genuinely very-hard ALTERNATIVE route should the KT lane ever be abandoned; if it is revived it must be re-entered as a NEW key naming the faithful dim-6 carrier explicitly, never on this thin-structure key. HISTORICAL RECORD FOLLOWS (unchanged, pre-2026-07-21): at the HYPOTHESIS level the W5 SmithInflow binder is now DISCHARGED by W6: the abstract iso is replaced by a CONSTRUCTED substrate Smith map (SymTFT.smithHom : Ω₅ → Ω₄^{Pin⁺}, SpinZ4Bordism5.lean), and sixteen_convergence_common_origin_via_constructed_smith takes no SmithInflow binder. This entry remains active because the GEOMETRIC FAITHFULNESS of the thin Ω₅/Ω₄ substrates + the genuine η-invariant are still tracked (a LARGER gap than the Pin⁺ side — the Dai–Freed invariant is ℤ₁₆-native; see elimination_path). The W5 binder form (SmithInflow) also survives, INHABITED by substrateSmithInflow and CANONICAL/unique by smithInflow_smith_unique. A hypothesis, NOT an axiom; all dependent theorems kernel-pure {propext, Classical.choice, Quot.sound}. W5+W8 UPDATE 2026-06-14 (Phase 5q.F finite discharge, PinPlusDischarge.lean): the SmithInflow ISO content (ZMod 16 ≃+ Ω₄^{Pin⁺}) is now DERIVED from the FINITE A(1)-Ext, not posited. The Pin⁺ Adams column t−s=4 height-4 cap is decidable F₂ linear algebra (PinPlusHeight4.col4_height_eq_four = 4, axioms:[], the Campbell δ=·h₀ cokernel), so |Ω₄^{Pin⁺}| = 2^4 = 16 from the finite Ext height; the old DeltaTruncationCap (16·[RP⁴]=0) is DERIVED (deltaCap_of_pin4). The single tracked input is REDUCED from the opaque SmithInflow to ONE precise disclosed Prop pin4_abutment = Pontryagin–Thom (Ω₄^{Pin⁺}=π₄MTPin⁺) + Adams convergence (E₂=E∞, no hidden ext); inhabited (pin4_abutment_substrate). sixteen_convergence_finite_discharge carries NO SmithInflow binder (takes pin4_abutment); the ℤ/16 is from finite content (criterion 8). The RESIDUAL tracked landmark is now just pin4_abutment (PT + convergence), Mathlib-absent (Thom-spectrum / stable-homotopy), per the axiom-stratified framework (Phase-5a chirality-wall l.57/100: the finite A(1)-Ext "partially discharges the cobordism axiom"). RETIREMENT 2026-06-15 (Phase 5q.F criterion 4): PinPlusDischarge §6 + Omega5FiniteIso re-pointed onto the GENUINE W4 bordism group DataBordismGrp ξ (real SingularManifolds over manifolds-with-boundary) — sixteen_convergence_genuine_carrier / omega5_quotient_iso_zmod16_genuine_carrier derive the ℤ/16 as the image of the genuine ABK/η grade (UNCONDITIONAL via the quotient dataBordism_quotient_abk_equiv_zmod16; full-carrier via the single disclosed PinPlusBordismLandmark = the OBJECTIVE-permitted Brown/ABK order-16 + height-4 ≤16 finite inputs). pin4_abutment / Omega4PinPlusBordism / the adamsAbutment modeling def are DEMOTED to finite-substrate corollaries; no load-bearing modeling DEFINITION remains for the geometric ℤ/16. The W5 geometric Smith map is the typed hom SmithIsomorphism.smithDataHom (DR Smith_sequence.md §5.2 scope) with the genuine manifold layer (SmithIsomorphism.smithImageSingularManifold, bricks 1-2: PD(a) a real codim-1 SingularManifold over arbitrary M). pin4_abutment remains CONSUMED by the demoted §1-§5 forms, hence still registered here.` · eliminability `very_hard` · module `CommonOrigin (Phase 5q.E W5 + W6); Pin⁺ half from SymTFT/PinPlusBordism4 (Phase 6r); Ω₅ substrate + constructed Smith from SymTFT/SpinZ4Bordism5 (W6); Kitaev reading from KitaevSixteenFold (W1)`
- **Posture.** The "16 convergence" common-origin theorem (CommonOrigin.lean) is honestly CONDITIONAL on this Smith-inflow input: GIVEN the Smith homomorphism (whose ℤ₁₆ iso-ness is established by García-Etxebarria–Montero 2018 and Wang 2024), the four occurrences of 16 — the Standard Model Weyl-fermion count, the ℤ₁₆ global anomaly, Rokhlin signature divisibility, and the Kitaev 16-fold way — are images of one genuine ℤ₁₆ (the Pin⁺ bordism group) under explicit maps, with Rokhlin and Kitaev reading it identically. The result still CONSTRAINS rather than DERIVES the Standard Model (the SM is the trivial class among 16). W6 (2026-06-14) builds a thin Ω₅^{Spin-ℤ₄} bordism substrate and a CONSTRUCTED Smith map, so the theorem can be stated with no abstract Lean hypothesis (sixteen_convergence_common_origin_via_constructed_smith) — but this is a HYPOTHESIS-LEVEL change only: the GEOMETRIC construction of the Smith map and the Ω₅ bordism group from manifolds + the η-invariant remain Mathlib-absent, and the thin substrates carry a tracked faithfulness gap (larger for Ω₅ than for the Pin⁺ side, as the Dai–Freed invariant is ℤ₁₆-native). So the convergence is a genuine ℤ₁₆-level map-composition; it must NOT be quoted as a geometric derivation or an unconditional unification.
- **Discharge path.** Build the GEOMETRIC inputs the structure stands in for: (i) the Ω₅^{Spin-ℤ₄} bordism group, (ii) the geometric Smith homomorphism Ω₅^{Spin-ℤ₄} → Ω₄^{Pin⁺}, and (iii) the Dai–Freed anomaly functor — all Mathlib-absent landmarks (Phase 5q.E roadmap §Walls + §Mathlib status, verified 2026-06-14 via semantic search). The Pin⁺ HALF (Ω₄^{Pin⁺} ≃+ ZMod 16) already exists as the Phase 6r SymTFT/PinPlusBordism4 substrate. W6 UPDATE 2026-06-14 (corrects an earlier overstatement): a thin Ω₅^{Spin-ℤ₄} SUBSTRATE IS now built (SpinZ4Bordism5.lean) — a genuine, kernel-pure `Quotient ≃+ ZMod 16` carrying `daiFreed : ℤ` with a 16∣Δ relation, plus a CONSTRUCTED Smith map `smithHom : Ω₅ → Ω₄^{Pin⁺}`. The earlier "NOT a thin-wrapper away / collapses to ZMod 16 (vacuous)" wording was wrong in one direction: the Quotient is NOT vacuous (it is a real ≃+ ZMod 16, like the Pin⁺ one). BUT it is a LESS-FAITHFUL stand-in for the geometric Ω₅ than the Pin⁺ signature is for Ω₄: the Dai–Freed invariant is ℤ₁₆-native (η/16 mod 1, no natural ℤ-lift), so carrying `daiFreed : ℤ` additionally tracks "the invariant takes ℤ values at all" — a tracked gap LARGER than the Pin⁺ side. So W6 discharges this input at the HYPOTHESIS level only (no abstract Lean binder in sixteen_convergence_common_origin_via_constructed_smith), NOT at the geometry/faithfulness level. The GEOMETRIC construction of Ω₅ from manifolds + the η-invariant (placeholder in APSEta) + the geometric Smith/Dai–Freed maps remain the Mathlib-absent landmark, trigger-gated per ADR-003 (shared frontier with Leg C/D). On the ADR-003 Leg D trigger (Mathlib ships spin-flavored bordism groups + the Dirac-operator/η machinery), build the geometric (i)+(ii)+(iii) to upgrade the chain from substrate-constructed to geometrically-faithful.
- **Source.** García-Etxebarria–Montero, JHEP 08 (2019) 003 [arXiv:1808.00009]; Wang (2024) Smith-homomorphism / string-bordism. NOTE: what the literature establishes is the ISO-NESS (the Smith hom is a generator-preserving isomorphism ℤ₁₆ ≅ ℤ₁₆) — that is cited-true; the SPECIFIC generator pin `smith 1 = [RP⁴]` is the canonical Kirby–Taylor normalization (a convention, not itself a cited theorem; the true Smith hom agrees up to a generator relabeling).
- **Risk.** Low. The carried fact (Smith hom is an iso ℤ₁₆ ≅ ℤ₁₆) is established in the literature (GEM 2018 / Wang 2024); only its geometric CONSTRUCTION is Mathlib-absent. Crucial contrast with the FALSE lattice-Arf bridge (RokhlinArfNoGo.lean): there a claimed identity was false; here the cited fact is TRUE and only the construction is absent. The conditional is inhabited (substrateSmithInflow) and canonical (smithInflow_smith_unique), so it is neither vacuous nor a choice-dependent artifact.
- **Circularity.** None. The common-origin theorem is honestly CONDITIONAL on this input — it does not assume its own conclusion. Verified by adversarial review (2026-06-14): the headline rokhlin_reads_kitaev is provably NOT rfl/simp/decide-able for an arbitrary SmithInflow, so the hypothesis does not smuggle the conclusion; it genuinely requires coherence of the independently-constructed Kitaev (KitaevSixteenFold) and Rokhlin (PinPlusBordism4) maps. Review verdict: "the legitimate opposite of the Arf-bridge failure mode."
- **Consumers.** `SKEFTHawking.CommonOrigin.sixteen_convergence_common_origin`, `SKEFTHawking.CommonOrigin.rokhlin_reads_kitaev`, `SKEFTHawking.CommonOrigin.kitaev_generator_is_bordism_generator`, `SKEFTHawking.CommonOrigin.sm_anomaly_trivial_in_bordism`, `SKEFTHawking.CommonOrigin.sm_spin10_count_trivial_in_bordism`, `SKEFTHawking.SixteenConvergenceDerived.sixteen_convergence_derived`

### `spinWu_even_datum`

**Statement.** For a closed ORIENTED Spin 4-manifold M, the mod-2 Wu / Spin input to the EVENNESS of the integer intersection matrix is carried (Phase 5q.H · E1 Substrate-G) as a disclosed datum: the structure SKEFTHawking.SingularCohomologyInt.SpinWuDatum fc (tied to the integral fundamental class fc : IntFundamentalClass X), holding (i) mu2 : Cohomology X 4 (ℤ/2) →ₗ[ZMod 2] ZMod 2 = the mod-2 fundamental-class functional ⟨·,[M]₂⟩; (ii) eval_compat: ((fc.eval ω : ℤ) : ZMod 2) = mu2 (redH X 4 ω), the ℤ→ℤ/2 compatibility of the two evaluations through the reduction bridge redH; (iii) wu_vanish: ∀ y : Cohomology X 2 (ℤ/2), mu2 (cupH24 y y) = 0 — the SPIN condition in functional form (⟨Sq² y,[M]₂⟩ = 0 for all y, which by the singular Wu relation is v₂ = 0; on an oriented 4-manifold v₁ = 0 so w₂ = v₂, hence v₂ = 0 ⟺ w₂ = 0 ⟺ M is Spin). This is the ONLY unproved input to interMatrix EVENNESS.

- status `proven (5q.H arm-2 brick 9, 2026-07-12: DISCHARGED at general closed oriented spin 4-manifolds — SpinWuDatumClosed.spinWuDatum_of_closed constructs the full datum from the two HONEST inputs (o : IntOrientation M, spin as wuClass2 poincareDual4Mid_of_closed = 0); mu2/PD frame = SingularPD4Instances (5q.G X6), eval_compat = KroneckerRedCompat + o.redCompat, wu_vanish DERIVED via the Wu relation (SpinWuFromPD). interMatrix evenness at general M: SpinWuDatumClosed.interMatrix_even_of_closed)` · eliminability `hard` · module `IntersectionFormEvenInt`
- **Posture.** The Spin/Wu evenness input for a closed oriented 4-manifold, carried as a disclosed datum (mod-2 fundamental functional + ℤ→ℤ/2 compatibility + the Spin condition v₂=0 as a Wu-functional vanishing) so the integer intersection matrix interMatrix is EVEN — discharging the last semi-mirror-able conjunct of IsEvenUnimodular through the from-scratch ℤ→ℤ/2 reduction bridge redH (Phase 5q.H · E1 Substrate-G). Symmetric ✓ (graded-commutativity) + even ✓ (this datum) leave unimodular/PD as the sole residual core.
- **Discharge path.** Discharge = build the ℤ/2 fundamental class + middle Poincaré-duality datum PoincareDual4Mid of the closed manifold (mod-2 orientability is automatic), take mu2 := P.mu, prove eval_compat from the fact that the integral and mod-2 fundamental classes agree under reduction, and derive wu_vanish from w₂(TM) = 0 (Spin) together with v₁ = 0 (oriented ⟹ w₁ = 0 ⟹ v₁ = 0) and the singular Wu relation ⟨v₂ ∪ y,[M]₂⟩ = ⟨Sq² y,[M]₂⟩ (PoincareDualityWu.wu_relation). The reduction bridge redH and its cup/coboundary compatibility (redH_cupH24, redC_coboundary, redC_cup) are PROVED unconditionally — the ℤ→ℤ/2 reduction of SingularCohomologyInt matches the on-main SingularCohomologyMod2 model definitionally (same functions on singular simplices; alternating signs (-1)^i reduce to 1 in char 2), so the bridge itself is NOT a hypothesis. Only the geometric Spin/PD datum is disclosed.
- **Source.** Standard 4-manifold topology (Wu formula w = Sq(v); Milnor–Stasheff §11; Kirby–Taylor): the intersection form of a Spin (equivalently w₂ = 0) 4-manifold is EVEN, because ⟨a∪a,[M]₂⟩ = ⟨Sq²(a),[M]₂⟩ = ⟨v₂∪a,[M]₂⟩ = 0 when v₂ = 0. On-main singular Wu substrate: PoincareDualityWu / PoincareDualityWuFormula (wuClass2, wu_relation, wuW2_eq_zero_iff).
- **Risk.** Low mathematically (textbook: Spin ⟹ even intersection form); cost is the from-scratch Lean construction of the ℤ/2 fundamental class + PD datum + the w₂=0 ⟹ v₂=0 derivation, deferred to a later E1 brick. Every result in IntersectionFormEvenInt holds for an ARBITRARY such datum.
- **Circularity.** None. The evenness lemmas are built for an ARBITRARY SpinWuDatum; no property of a specific (future) geometric fundamental class is assumed. The reduction bridge redH — the connective tissue to the mod-2 Wu side — is proved unconditionally (not part of this datum). The residual unimodular/Poincaré-duality conjunct of IsEvenUnimodular is left explicitly as a SEPARATE hypothesis (isEvenUnimodular_of_unimodular takes IsUnimodular as its remaining argument), NOT folded in here.
- **Consumers.** `SKEFTHawking.SingularCohomologyInt.interFormInt_diag_even`, `SKEFTHawking.SingularCohomologyInt.interMatrix_even_of_spinWu`, `SKEFTHawking.SingularCohomologyInt.isEvenUnimodular_of_unimodular`

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
