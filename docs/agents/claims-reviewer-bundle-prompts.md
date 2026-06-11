# Per-Bundle Stage-13 Review Anchor List

**Purpose:** The Phase 6i Wave 7 bundle architecture requires the
`physics-qa:claims-reviewer` and `physics-qa:figure-reviewer` agents to
operate at the bundle level rather than the per-paper level. Each
bundle has a different review profile (depth, scope, breadth, anchor
list). This document is the canonical per-bundle anchor list — the
specific load-bearing claims and citations the bundle's Stage-13 review
must verify.

**Companion to:** `docs/PAPER_STRATEGY.md` (canonical bundle
architecture) and `docs/PAPER_DRAFT_MAPPING.md` (per-draft → per-bundle
table).

**Created:** 2026-04-29 (Phase 6i Wave 7.2).

---

## How agents consume this document

The reviewer agents accept a `bundle_target` argument (one of the 17
bundle codes: `F`, `D1`–`D8`, `L1`–`L3`, `I1`–`I3`, `E1`, `E2`). Given
a bundle target, the agent:

1. Resolves the bundle's lifted source material via
   `scripts/bundle_clusters.py` and `docs/PAPER_DRAFT_MAPPING.md` §2
   ("Per-bundle source map").
2. Loads the bundle's per-section anchor list from this document.
3. Executes the bundle-appropriate review depth:
   - **Tier 2 (PRL splash):** stand-alone, single-paper depth.
   - **Tier 1 (deep):** intra-bundle consistency + cross-bundle
     consistency for cross-bridge claims.
   - **Tier 0 (flagship):** review-paper style, against published Tier 1
     bundles.
   - **Tier 3 (infrastructure):** software/methodology paper style,
     reproducibility-anchored.
   - **Tier 4 (experimental):** lightweight + device-parameter audit.
4. Produces a `papers/AutomatedReviews/<DATE>-bundle-stage13/<bundle>.md`
   review document.

The driver `scripts/review_runner.py --bundle <target>` orchestrates
this; see `scripts/review_runner.py --help`.

---

## Tier 0 — Flagship

### F. Fluid-Based Approaches to Fundamental Physics — A Formally Verified Survey

**Review profile:** review-paper style. Reviewer pulls published-version
DOIs / arXiv IDs from the citation cache (Phase 6i Wave 1 infrastructure)
and verifies each cited claim resolves correctly to the published Tier 1
bundle.

**Anchors (load-bearing, must verify):**
- Every published L1/L2/L3 Tier 2 bundle's central claim cited
  character-for-character.
- Every D1–D5 Tier 1 bundle's main result statement cited
  character-for-character.
- `RESEARCH_STATUS_OVERVIEW.md` proven-chains list current at the
  flagship-submission date.
- `ARCHITECTURE_SCOPE.md` §2 + §10 lifted verbatim and consistent with
  current state.
- Theorem / module / paper counts current per `docs/counts.tex`
  macros (no inline literals).

**Stage-13 BLOCKERs:**
- Any cited L*/D*/I*/E* claim drifts from its published form.
- Any inline numerical literal (per `validate.py --check
  numerical_literals` + `count_literals`).
- Any flagship section that cites a bundle still in preparation
  (`inprep: True` consistency must hold per the bundle's submission
  state).

---

## Tier 1 — Deep papers

### D1. Analog Hawking across three platforms

**Sources:** paper1, paper2, paper4, paper12 (BEC + polariton),
paper16_graphene_sk_eft.

**Anchors (load-bearing):**
- BEC analog Hawking dissipative correction `δ_diss = (1 + ξ²)⁻¹` at the
  fiducial parameters from `EXPERIMENTS['BEC_KIM_2014']`.
- Exact-WKB connection formula with the three non-perturbative effects
  (greybody factor, dispersive cut-off, sub-leading corrections).
- Polariton platform shot-count feasibility result from
  `feasibility.py:polariton_shot_count`.
- Graphene Dirac-fluid 92% Lean-theorem-reuse claim (verified against
  the Phase 5w cross-platform reuse counter).

**Stage-13 anchors specific to D1:**
- Cross-section consistency: the same dimensional analysis (linear
  density, [m⁻¹]) used across BEC, polariton, and graphene sections.
- The exact-WKB connection formula in §4 must match the Lean theorem in
  `WKBConnection.lean` (verified via `audit_paper_lean_refs.py`).

### D2. Anomaly constraints on SM particle content

**Sources:** paper7, paper8, paper9 (anomaly portion), paper10 (full
derivation as primary section).

**Anchors:**
- Z16 anomaly chain `dai_freed_spin_z4 ↔ Ω_5^{Spin×Z_4} ≅ Z_16` (pre-
  acknowledged Mathlib-bordism scope deferral; should be disclosed).
- Three-pillar synthesis: GS (Green-Schwarz) evasion, TPF (topological
  pivoting frame), modular generation `N_f ≡ 0 mod 3`.
- Drinfeld center cross-bridge to D4 §4 (the two D2 §3 + D4 §4
  occurrences must say the same thing).
- Quaternionic-spinor structure framing as motivation, not as a proven
  causal lemma.

**Stage-13 anchors specific to D2:**
- The `24 | c₋` chain claim (load-bearing for L2) must match between
  D2 §2 and L2 (see L2 below).
- "First quantum group / first rank-2 quantum group / first SU(3)
  fusion category in Lean 4" first-claim verifications via
  `qi-firstclaimverification` spot-check.

### D3. Emergent gravity through BH thermodynamics

**Sources:** paper3, paper5, paper6 (conditional), paper20–paper27 (gravity
chain), paper35 (cross-bridge), paper36–paper38 (QCD), paper39–paper43
(higher-curvature + nonlinear EFE + EC torsion).

**Anchors:**
- ADW gap equation + tetrad gap + bifurcation results.
- Emergent G_N: G_N^Sak = 12π/(N_f Λ_UV²) per Vassilevich Eq. (4.37)
  (already explicated in Wave 6 paper42b §3 expansion).
- Decision-Gate-E.2/E.3/E.4 biconditionals.
- Sakharov-Adler induced Newton constant ↔ heat-kernel a_2 coefficient.
- Stelle (α, β, γ) basis change at order a_4.
- Multi-channel PPN ratios (deflection α / precession (2α+1)/3 /
  ringdown α).
- Einstein-Cartan torsion |T_EC| ≃ 2.05×10⁻⁷⁷ GeV vs Kostelecky-
  Russell-Tasson 10⁻³¹ GeV bound — **not** the older `1.3×10⁻¹¹⁴ GeV`
  (Wave-6-fixed docstring drift).
- BCH four laws by regime (cross-bridge to L3 splash; same content).
- BH entropy from MTC counting + Kaul-Majumdar SU(2)_k -3/2 closed form.

**Stage-13 anchors specific to D3:**
- Cross-bridge to L1 (GW170817 / vestigial graviton) — D3 §6 + L1
  must report the same numerical Δc/c constraint.
- Cross-bridge to L3 (BCH four laws) — D3 §8 + L3 must agree.
- Cross-bridge to D4 §7 (QEC-Holography) — D3 §9 cross-bridge claim
  must match D4's framing.

### D4. Topological quantum computation foundations

**Sources:** paper9 (Drinfeld center), paper11 (primary kernel), paper14,
paper16_wrt_tqft, paper18, paper35 (QEC), note_rt_ch_bounds.

**Anchors:**
- First quantum-group formalization (`U_q(sl_2)`, `U_q(sl_3)`).
- Ising MTC complete + trefoil = −1 + figure-eight knot invariants.
- WRT TQFT partition functions + WRT surgery formula.
- Doublon SWAP gate + Berry-phase + first symmetry-protected gate.
- Hayden-Preskill structural QEC on horizon-MTC substrate.
- RT / Casini-Huerta knife-edge biconditional + tracked Props.

**Stage-13 anchors specific to D4:**
- Cross-bridge to D2 §3 (Drinfeld center) — D2 + D4 must say the same
  thing about the Drinfeld center construction.
- D4 §8 (RT/CH) must reference the W3 `H_HorizonBoundaryCondition`
  tracked Prop honestly.

### D5. Dark sector under substrate constraints

**Sources:** paper17, paper29, paper32, paper34, paper42b (CC-channel
secondary).

**Anchors:**
- Six Phase-5x DM mechanism classification.
- BBN classification (paper29) — N_eff bounds and BBN-conformant vs
  -violator partition.
- Zhitnitsky topological-DE absorption: ρ ~ Λ_QCD⁶/M_P² ≈ 6.71×10⁻⁹
  eV⁴.
- EP-violation matrix; vestigial-only verdict.
- CC-channel constraint: heat-kernel a_0 does not produce Λ_obs
  naturally.

**Stage-13 anchors specific to D5:**
- Cross-bridge to D3 §21 (paper42b CC reproduction) — D3 + D5 §7 must
  use the same heat-kernel a_0 coefficient.
- Cross-bridge to D2 (anomaly classification of DM candidates).

---

### D6. Formally Verified Fault-Tolerant Quantum Computation Substrate

(NEW BUNDLE — created 2026-05-26 at Phase 6v Wave 6v.1 ship.)

**Sources:** Phase 6v Waves 6v.1, 6v.2, 6v.5, 6v.6; Phase 6t Solovay-Kitaev
retroactive absorption.

**Anchors:**
- **§3 Williamson-Yoder gauging-QEC overhead bound** (Wave 6v.1, the
  bundle-creating wave): auxiliary-qubit overhead linear in operator
  weight W up to a polylogarithmic factor; substrate-level encoding
  `williamsonYoderAuxQubits W := W * (Nat.log 2 W + 1)`; falsifier
  `quadraticOverhead_not_linear` proves the polylog factor is unavoidable
  for any scheme that includes the W² baseline. Lean substrate:
  `lean/SKEFTHawking/FaultTolerance/GaugingQEC.lean`; PRL primary:
  `WilliamsonYoder2026GaugingLogicalOperators` (arXiv:2410.02213,
  Nat. Phys. 22, 598-603 (2026), DOI 10.1038/s41567-026-03220-8).
- **§2 Phase 6t Solovay-Kitaev tight-ε retroactive absorption**:
  `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight`
  (FKLW/SolovayKitaevPathA.lean) as the canonical universal-compilation
  primitive consumed by the remaining D6 sections.
- **§4 APM-LDPC + hashing bound** (Wave 6v.5, pending): affine-permutation-
  matrix LDPC code family over QCyc*.lean cyclotomic substrate +
  Shannon-capacity hashing bound from LDP/Cramér.lean.
- **§5 Shor T-gate counts** (Wave 6v.2, pending): T-gate compiler family
  applied to ECDLP-secp256k1 + RSA-2048, building on §2.
- **§6 W-state QFT decomposition in Q(ζ_N)** (Wave 6v.6, pending):
  Kyoto-Hiroshima 2025-09 single-shot projective measurement.

**Stage-13 anchors specific to D6:**
- Cross-bridge to D4 (sibling — TQC foundations): D6 retains
  fault-tolerant-computation focus; D4 retains Fibonacci/topological-
  foundations. Verify no double-counting of Phase 6t SK content between
  D4 §"Quantitative SK" appendix and D6 §2 (the retroactive absorption
  must move, not duplicate, the SK headline).
- Cross-bridge to I1 (verification methodology): the gauging-QEC
  falsifier-pattern (`quadraticOverhead_not_linear` as a class-separation
  witness) is methodology-class content that may sidebar into I1.
- Verify no project-local axioms introduced across D6 contributions
  (Pipeline Invariant #15); cross-check via `validate.py` axiom audit.

---

### D7. Classical Simulability and Quantum Advantage via Tensor Networks: A Formally Verified Demarcation

(NEW BUNDLE — created 2026-05-26 PM at Phase 6w Wave 6w.6/6w.7
spin-out trigger per user conditional-authorization on the
generality criterion.)

**Sources:** Phase 6w Waves 6w.1 through 6w.6; primary anchors
Tindall-Sels Science 392, 868 (2026) and Antão-Sun-Fumega-Lado
PRL 136, 156601 (2026).

**Anchors:**
- **HEADLINE demarcation theorem** `analog_hawking_quantum_advantage_demarcation`
  (Lean module `AnalogHawkingDemarcation.lean`): biconditional
  characterization of classical simulability via vanishing of the
  loop-correction rate function + Chern coefficient.
- **BP-LDP biconditional** `bp_convergence_iff_ldp_rate_zero`
  (Lean module `BPLDPSimulability.lean`, Wave 6w.3; review-2026-06-05
  D7-EV3 upgrade): `loopCorrectionRate` is the Cramér/Legendre
  transform at zero deviation of the Bernoulli loop-presence log-MGF
  over the graph's 4-cycle density; closed form `-log(1-p)` proven via
  IsLUB (`loopCorrectionRate_eq_neg_log`); zero-rate ⟺ tree proven,
  not definitional (`loopCorrectionRate_eq_zero_iff_tree`); strict
  positivity on loopy graphs, strict monotonicity in loop density,
  exact finite-n Cramér identity, KL bridge to the LDP suite
  (`loopCorrection_isCramerIIDUpperBound`), worked K_{2,2} value
  `log(4/3)`.
- **Categorical-Chern bridge** `categorical_chern_eq_real_space_chern_crystalline`
  and `_quasicrystalline` (Lean module `ChernBridge.lean`, Wave
  6w.5).
- **BP substrate** 24 substantive theorems in
  `BeliefPropagation.lean` (Wave 6w.2): factor graphs, BP messages,
  variable + factor updates + beliefs, Shannon entropy, factor
  energy, Bethe free energy, tree predicate.
- **Chebyshev-TN substrate** 10 substantive theorems in
  `ChebyshevTN.lean` (Wave 6w.4): first-kind Chebyshev polynomials
  via canonical recurrence + boundary-value identities `T_n(1) = 1`,
  `T_n(-1) = (-1)^n`, `T_{2k}(0) = (-1)^k`, `T_{2k+1}(0) = 0` +
  truncated expansion evaluation.
- **Aperiodic-lattice substrate** 7 substantive theorems in
  `AperiodicLattice.lean` (Wave 6w.4): `IsPeriodic2D` /
  `IsAperiodic2D` predicates, singleton-lattice aperiodicity,
  translation-invariance closures.
- **KZ-U application substrate** 8 substantive theorems in
  `KibbleZurekUnruh.lean` (Wave 6w.1): KZM exponent bounds, bridge
  identification, surface-gravity ↔ KZM-defect-rate strict
  inequality.
- Primary sources: Tindall-Mello-Fishman-Stoudenmire-Sels Science 392,
  868 (2026, DOI 10.1126/science.adx2728, arXiv:2503.05693) + Antão-
  Sun-Fumega-Lado PRL 136, 156601 (2026, DOI 10.1103/hhdf-xpwg,
  arXiv:2506.05230) — both cached at `Lit-Search/Phase-6w/primary-sources/`.

**Stage-13 anchors specific to D7:**
- Verify the HEADLINE biconditional's two-axis decomposition is
  substantively load-bearing in BOTH directions (forward and
  reverse): no P5 (mere unfolding of definition) on either side.
- Cross-bridge to D4 (TQC foundations sibling): D4 retains
  Fibonacci/topological-foundations focus; D7 covers the
  classical-simulability/tensor-network methodology. Verify no
  double-counting of categorical-Chern content between D4 and D7
  §"Chebyshev-TN Chern bridge".
- Cross-bridge to D6 (FT-QC substrate sibling): D6 covers fault-
  tolerant computation primitives; D7 covers classical-simulability
  demarcation. Verify the two bundles cite each other cleanly without
  overlap of the SK substrate.
- Verify the analog-Hawking application section (§"Kibble-Zurek-Unruh
  application") cites Phase 6w Wave 6w.1 substrate, NOT inserts new
  substrate.
- Verify no project-local axioms introduced across D7 contributions
  (Pipeline Invariant #15); axiom-audit cross-check via `validate.py`.
- Verify the substrate-generality claim (Phase 6w strategy synthesis
  decision-rule condition) is verifiable at the type level: the
  contributing Lean predicates take arbitrary type parameters.

---

### D8. Kernel-Verified Universal Quantum Gate Compilation — Alphabet-Agnostic Solovay-Kitaev across Dimensions

(NEW BUNDLE — authorized 2026-05-31 per Pipeline Invariant #14;
consolidates the verified-quantum-compilation corpus that had
outgrown the D4 §9.x showcase container.)

**Sources:** Phase 6p (Fibonacci density), 6t (quantitative SK +
reference-compiler skeleton), 6u (alphabet-agnostic substrate +
Clifford+T), 6x (Read-Rezayi k5/k7 + alphabet substrates + Mathlib
tracks), 6x′ (Mukhopadhyay channel-rep + Toffoli bounds), 6y (SU(d)
lift + SU(4)/SU(8) instances), 6z (T-free CCZ-essential SU(8)
density). All Lean-only / D.4-sourceless.

**Anchors:**
- **Alphabet-agnostic substrate** — generic `GeneratingSet`-parametrized
  quantitative Solovay-Kitaev (`GenericSolovayKitaevQuantitative.lean`);
  Clifford+T instance `solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight_unconditional`
  (`CliffordTQuantitative.lean`) + `cliffordT_density_unconditional`
  via Niven obstruction (`CliffordTInfiniteOrder.lean`).
- **SU(d) lift (HEADLINE)** `solovayKitaev_dawson_nielsen_quantitative_generic_sud_strict_constructive_tight`
  (`GenericSUdQuantitative.lean` / `GenericSUdSkHeadlineCascadeConcrete.lean`) —
  first kernel-verified quantitative SK at arbitrary dimension.
- **Concrete-radius matrix logarithm** `matrixMercatorLog` /
  `exp_matrixMercatorLog` (`GenericSUdMatrixMercatorLog.lean`) — the
  construction that eliminated the existential-radius regime blocker;
  Mathlib-PR-eligible.
- **Five-alphabet survey** — Fibonacci (`FibSU2Density.lean`,
  `SolovayKitaevQuantitative.lean`), Clifford+T, Read-Rezayi
  `SU(2)_5`/`SU(2)_7` (`ReadRezayiK5Quantitative.lean` /
  `ReadRezayiK7Quantitative.lean`), trapped-ion SU(4)
  `trappedIonSU4_solovayKitaev_headline_unconditional`
  (`TrappedIonSU4WitnessFull.lean`), Clifford+T SU(8)
  `cliffordCCZSU8_solovayKitaev_headline_unconditional`.
- **T-free CCZ-essential SU(8) density** `cliffordCCZLiteral_dense` +
  `cliffordCCZLiteral_solovayKitaev_headline_unconditional`
  (`CliffordCCZSU8LiteralHeadline.lean` /
  `CliffordCCZSU8LiteralGeneratingSet.lean` /
  `CliffordCCZSU8LiteralSeed.lean`).
- **Mukhopadhyay resource theory** — unconditional Toffoli lower
  bound `channelSde2_le_toffoliCost`
  (`MukhopadhyayToffoliUnconditional.lean` /
  `MukhopadhyayToffoliBound.lean`); dyadic-entry Lemma 3.10
  `channelRep_interp_isRat` (`MukhopadhyayChannelRep.lean` /
  `MukhopadhyayMatrixSde2.lean`); converse `cliffordOnly_not_dense`
  (`MukhopadhyayCliffordNotDense.lean`).
- Primary sources: Solovay-Kitaev; Dawson-Nielsen (arXiv:quant-ph/0505030);
  Kuperberg 2009; Boykin-Mor-Pulver-Roychowdhury-Vatan
  (arXiv:quant-ph/9906054); Read-Rezayi (arXiv:cond-mat/9809384);
  Brylinski-Brylinski (arXiv:quant-ph/0108062); Aaronson-Gottesman
  (arXiv:quant-ph/0406196); Mukhopadhyay (arXiv:2401.08950);
  Kliuchnikov-Maslov-Mosca (arXiv:1206.5236); Ross-Selinger
  (arXiv:1403.2975). Each must resolve to a primary-source cache file.

**Stage-13 anchors specific to D8:**
- **Honest scope — SU(8) duality (load-bearing).** The Phase 6y SU(8)
  instance achieves density from the `{H,T,CNOT}` sub-alphabet with CCZ
  **present-but-over-complete**; the Phase 6z literal instance is
  **T-free and CCZ-essential**. Verify the draft never conflates the
  two: CCZ-essentiality is a claim about the 6z literal route ONLY
  (backed by `cliffordOnly_not_dense`), not the 6y over-complete route.
- **Unconditional vs parametric Toffoli bound.** Verify the Toffoli
  lower bound is stated as **unconditional** (`channelSde2_le_toffoliCost`,
  with the `hC`/`hCCZ` hypotheses discharged in Phase 6x′), NOT the
  older parametric form. Full Toffoli minimality (Mukhopadhyay
  Conjecture 4.8) is explicitly OUT of scope — verify no overclaim.
- **Length exponent honesty.** Verify the word-length exponent is the
  honest `log 5 / log(3/2) ≈ 3.97`, NOT `log 5 / log 2 ≈ 2.32`
  (the latter would require an unproven quadratic contraction). Anchor:
  `skLengthExponent_sud` (`GenericSUdSkLengthExponent.lean`).
- **Cross-bridge to D4 (Fibonacci/topological anchor).** D4 retains
  the Fibonacci-universality + categorical-foundations focus; D8 cites
  D4 for the Fibonacci anchor and generalizes the universality
  machinery. Verify no double-counting of the Fibonacci density /
  quantitative-SK content between D4 §9.x and D8 §1–§2.
- **Cross-bridge to D6 (FT-QC substrate).** D6 *consumes* D8's
  quantitative SK as its universal-compilation primitive. Verify the
  two cite each other cleanly without duplicating the SK substrate
  content; the relationship D6 previously assigned to the Phase 6t
  Fibonacci headline is now served, more generally, by D8.
- **Public/private seam.** Verify the draft's scope statement keeps
  runtime-compiler implementation, vendor-specific tuning, certificate
  formats, and length-optimality engineering explicitly OUT of scope
  (D8 is the verified-existence / universality / lower-bound theory).
  The draft must not reference any private repository or commercial
  product.
- **No project-local axioms** across D8 contributions (Pipeline
  Invariant #15); axiom-audit cross-check via `validate.py`. All
  headlines kernel-pure `{propext, Classical.choice, Quot.sound}`.

### D9. Kernel-Verified Quantum-Network and Device-Characterization Certification Substrate

(NEW BUNDLE — authorized 2026-06-10 per Pipeline Invariant #14, commit
`edc18ce3`; consolidates the Phase 6AA–6AL QI-analytics/network corpus
plus the 6AM/6AN/6AP/6AQ envelope waves that had no bundle home.
Defensive-publication posture: textbook/published math at full
strength, honestly attributed.)

**Sources:** Phases 6AA–6AL (QI-analytics + network corpus), 6AM
W1–W4 + W6 (PhysLib adoption + quantum-FDT floor + sharp
Fannes–Audenaert), 6AN W2–W4 (NetworkCapacity, ComposedGateFidelity,
FDTNoiseFloor), 6AP W1/W2/W4 (expNeg_enclosure, KroneckerOpNorm,
ErasureRateBound), 6AQ (ReadoutRelaxationBound,
ThermalAssignmentFloor). All Lean-only / §3b-sourceless; seed material
`papers/phase6AA_qnetwork_preprint/preprint_draft.md` (verified
against current Lean state at lift time, 2026-06-10).

**Anchors (load-bearing):**
- **Diamond-norm program** — both Fuchs–van de Graaf bounds
  (`one_sub_sqrtFidelity_le_traceDist`, `FidelityBounds.lean`;
  `traceDist_le_sqrt_one_sub_sqrtFidelity_sq`,
  `FidelityUpperBound.lean`); the two-sided Choi sandwich
  `(1/2n)‖J₁−J₂‖₁ ≤ diamondDist ≤ n‖J₁−J₂‖_∞`
  (`diamondDist_ge_maxEntangled` / `diamondDist_ge_choi_traceNorm` /
  `diamondDist_le_choi_opNorm`); the full Watrous SDP duality
  `diamondDist_eq_choiSDP` (`DiamondSDPDuality.lean`) with primal
  attainment `exists_diamondDist_eq` and dual attainment
  `exists_choiDualValue_eq`; exact named-channel distances
  (`diamondDist_dephasing_eq` = γ, `diamondDist_depolarizing_eq` = p,
  `diamondDist_pauliKraus_eq` = 1−p₀,
  `diamondDist_errorBasisKraus_eq`, `diamondDist_spamBitFlip_eq` = q)
  vs honest two-sided BRACKETS for the non-covariant channels
  (`diamondDist_ampDamp_ge`/`diamondDist_ampDamp_le`,
  `diamondDist_genAmpDamp_bracket`) — verify the draft never claims
  exactness for amplitude damping or its thermal generalization.
- **Sharp Audenaert** `quantum_fannes_audenaert_sharp`
  (`SharpFannesAudenaert.lean`): sharp constant `log(d−1)`,
  UNCONDITIONAL for density operators on the monotone regime
  `T ≤ 1 − 1/d` — verify the regime hypothesis `hTV` is stated, and
  that the "first machine-checked discharge" claim is hedged with "to
  our knowledge" (per Phase 6AM W6 roadmap status).
- **Entropy corpus** — Klein (`relativeEntropy_nonneg`,
  `QuantumKlein.lean`), subadditivity
  (`vonNeumannEntropy_subadditive`), concavity
  (`vonNeumannEntropy_concave`), Gibbs variational
  (`vonNeumannEntropy_le_cross`), unconditional Mirsky
  (`mirsky_unconditional`); PhysLib ADOPTION (not re-derivation) for
  sandwiched-Rényi DPI / SSA via the faithful bridge
  (`toMState`/`toCPTPMap`/`krausMap_sandwichedRenyi_DPI`,
  `PhyslibBridge.lean`) — verify the bridge is described as an
  identification and the PhysLib citation (arXiv:2510.08672) is
  present.
- **Negativity/PPT ladder** — Werner thresholds
  (`negativityBellDiag_werner`: N = (2F−1)/2 for F ≥ ½;
  `ppt_werner_iff`: PPT ⟺ F ≤ ½, matching the BBPSSW/DEJMPS cutoff);
  trace-norm multiplicativity `traceNorm_kronecker`; log-negativity
  additivity `logNegativity_add`; n-copy regularized rate
  `logNegB_ncopy` + `logNegB_ncopy_localKraus_le`.
- **Network envelopes** — `swapChain_fidelity_envelope`
  (`Envelope.lean`, [¼,1] for k-swap Werner chains; "to our knowledge
  the first formally verified protocol-level fidelity bound for
  quantum networks" — hedged claim, verify hedge survives);
  decay-inclusive `decayInclusive_fidelity_envelope`; unconditional
  Horodecki teleportation
  `teleportAvgFidelity_horodecki_unconditional` ((2F+1)/3, the Haar
  integral `haarPauliZSqAverage_eq` PROVEN not assumed); BB84
  crossover `bb84_crossover_exists` (IVT root, the ≈11% decimal is
  NEVER asserted in the formal layer — verify the draft keeps this);
  DEJMPS non-monotonicity witness `dejmps_single_step_can_decrease`
  (Macchiavello asymptotics cited, NOT formalized); PLOB/erasure
  two-layer posture (`plobBound`, `erasureBound`,
  `erasureBound_le_plobBound` — formula layer Lean-verified, channel
  converse literature-cited); MFMC strong duality `maxFlow_eq_minCut`
  (`NetworkCapacityStrongDuality.lean`) — built in-project, Mathlib
  has no max-flow/min-cut at the pin (verify this absence claim is
  scoped to the pin).
- **Device envelopes** — `avgGateFidelity_eq`
  (F_avg = (dF_e+1)/(d+1), constructive sphere-moment proof);
  coherence ceiling `avgGateFidelity_coherenceChannel`
  (½ + ⅙e^{−t/T₁} + ⅓e^{−t/(2T₁)−t/T₂}, exact about the MODEL
  channel); RB-style two-sided certificate
  `avgGateFidelity_diamondDist_two_sided`; quantum FDT floor
  `qho_meanEnergy` ((ℏω/2)·coth(βℏω/2), DERIVED from the PhysLib
  canonical ensemble — verify "derived, not posited" framing); 6AQ
  readout envelopes `readoutDecayProb` (range/strict-mono/antitone/
  endpoints/`readoutDecayProb_enclosure`) and `thermalExcitedPop`
  (DERIVED via `twoState_excited_probability` from PhysLib twoState;
  StrictAnti; temperature/frequency monotonicity; rational
  enclosures); uniform-prior prefactor ½ floors
  (`avgAssignmentError_relaxation_floor`,
  `avgAssignmentError_thermal_floor`) and the max-capstone
  `avgAssignmentError_combined_floor`.
- **Rational-enclosure technique** — `expNeg_enclosure`
  (1−r ≤ e^{−r} ≤ 1/(1+r), `NumericalBounds.lean`) + degree-5 Taylor
  squeeze `expNeg046_tight` (0.631 ≤ e^{−0.46} ≤ 0.632) — verify the
  numerical bracket endpoints against the Lean statements.
- Primary sources: Watrous (Theory of Quantum Information, CUP 2018);
  Fuchs–van de Graaf (IEEE TIT 45, 1216 (1999)); Audenaert
  (J. Phys. A 40, 8127 (2007)); Fannes (CMP 31, 291 (1973)); Mirsky
  (Q. J. Math. 11, 50 (1960)); PLOB (Nat. Commun. 8, 15043 (2017));
  Bennett–Brassard 1984; Shor–Preskill (PRL 85, 441 (2000)); Deutsch
  et al. DEJMPS (PRL 77, 2818 (1996)); BBPSSW (PRL 76, 722 (1996));
  BDCZ (PRL 81, 5932 (1998)); Horodecki³ (PRA 60, 1888 (1999));
  Vidal–Werner (PRA 65, 032314 (2002)); Bennett–DiVincenzo–Smolin
  (PRL 78, 3217 (1997)); Ford–Fulkerson (Canad. J. Math. 8, 399
  (1956)); Nielsen (Phys. Lett. A 303, 249 (2002)); Magesan et al.
  (PRL 106, 180504 (2011)); Gambetta et al. (PRA 76, 012325 (2007));
  Walter et al. (PRApplied 7, 054020 (2017)); Geerlings et al.
  (PRL 110, 120501 (2013)); Jin et al. (PRL 114, 240501 (2015));
  Callen–Welton (Phys. Rev. 83, 34 (1951)); Caves (PRD 26, 1817
  (1982)); Meiburg–Lessa–Soldati PhysLib (arXiv:2510.08672). Each
  must resolve to a primary-source cache file.

**Stage-13 anchors specific to D9:**
- **The two-layer posture is load-bearing throughout.** Every floor /
  ceiling theorem must keep the formula layer (Lean-verified) and the
  device/channel-identification layer (literature-cited, explicit
  hypothesis) separate. Spot-verify the four canonical instances: the
  coherence ceiling (model-channel exactness vs physical-gate bound),
  `plobBound`/`erasureBound` (formula vs CV channel converse), the
  readout floors (decay-flips-outcome model hypothesis `he1`), and
  the RB certificate (fidelity-to-diamond conversion verified; RB
  model identification cited). Any sentence that reads a model
  theorem as an unconditional device fact is a BLOCKER.
- **The Caves wall ships as a HYPOTHESIS, never an axiom.** The
  amplifier added-noise bound A ≥ ℏω/2 is the explicit hypothesis
  `hcaves` of `fdt_noise_floor_amplifier` (`FDTNoiseFloor.lean`); the
  bosonic CCR ladder algebra is absent from PhysLib/Mathlib at the
  pin (documented wall, Phase 6AM/6AN roadmaps). Verify the draft
  says hypothesis-not-axiom, and that the zero-project-local-axiom
  claim is consistent with it.
- **Diamond convention.** The corpus uses the HALVED diamond norm
  (diamondDist = ½‖·‖_◇, [0,1]-valued). Verify every numerical
  diamond claim (γ, p, 1−p₀, q, brackets) is stated in this
  convention and no factor-of-2 drift exists against the cited
  literature values.
- **Formalization-first claims are hedged and enumerated.** Only
  four such claims are authorized, all "to our knowledge": the
  swap-chain protocol-level envelope, the sharp-Audenaert discharge,
  the in-project MFMC (a library-gap claim, not new mathematics),
  and the constructive sphere-moment derivation of the gate-fidelity
  identity being import-free. Any additional "first" is a BLOCKER.
- **Open items honestly excluded.** DEJMPS asymptotic basin
  (Macchiavello, cited); Fortescue–Lo asymptotic optimality (open
  conjecture, NOT claimed — verify `fortescueLoYield_tendsto_one` is
  not over-read); exact non-covariant diamond distances (brackets
  only); CV capacities (cited).
- **Cross-bridge to D8 (compiled-gate certificate).** D8 owns
  `diamondDist_cliffordTCompile_le` and the AKN conversion narrative;
  D9 owns the channel/measurement-certification layer and cites D8
  as sibling without restating its content. Verify no duplication of
  the compiled-gate chain (`UnitaryDiamond`/`MatrixNormBridge`
  content appears in D9 only as the consumed substrate note).
- **Cross-bridge to D6 (logical layer).** The QEC suppression
  theorems (`logicalErrorBound_antitone_distance`,
  `logicalErrorBound_tendsto_zero`) are D9's interface to D6's
  logical layer; verify D9 does not develop code/measurement/gauging
  content.
- **Cross-bridge to I3 (LDP foundations).** The FDT rare-event tail
  (`fdt_rare_event_tail`, `fdt_gallavotti_cohen`) consumes I3's
  large-deviation substrate; verify the citation direction.
- **Disclosure Variant B** (register-derived 2026-06-10): no
  ARISTOTLE_THEOREMS entry resolves to a QuantumNetwork module (S1)
  and the draft names no Aristotle-proved theorem (S2, whole-word
  sweep). Verify the standard Variant B block is the only
  manuscript-level disclosure (docs/DISCLOSURE_TEXT.md).
- **No project-local axioms** across D9 contributions (Pipeline
  Invariant #15); the QuantumNetwork corpus additionally carries no
  `native_decide`, no `sorry`, and no `maxHeartbeats` overrides
  (verified by source sweep 2026-06-10). All theorems kernel-pure
  `{propext, Classical.choice, Quot.sound}`.

---

## Tier 2 — PRL splashes

### L1. GW170817 / vestigial-graviton

**Source:** paper25.

**Anchors:**
- LIGO Δc/c bound from Abbott 2017 GW170817 detection paper.
- Vestigial-graviton dispersion forecast at the project's natural χ_vest
  range.
- GW170817 falsification factor ~7×10¹⁴ in the natural range.

**Stage-13 BLOCKERs:**
- The numerical Δc/c bound must match D3 §6 character-for-character
  (cross-bundle consistency check via Wave 7.3).
- Abbott 2017 detection paper bibitem must be cached and `doi_verified:
  True` (Wave 1+2 infrastructure).

### L2. Three generations from modular invariance

**Source:** paper10.

**Anchors:**
- Modular generation constraint `N_f ≡ 0 mod 3` derived from the
  generation-anomaly discriminant.
- The `24 | c₋` chain claim load-bearing in the discriminant
  computation.
- Ext computation over Steenrod subalgebra A(1) (first-formalization
  claim must be spot-checked against Agda/Coq registries).

**Stage-13 BLOCKERs:**
- L2 + D2 §2 must use the same Ext-computation chain.
- "First Ext computation over Steenrod subalgebra A(1)" first-claim
  verification per `qi-firstclaimverification`.

### L3. BCH four laws by regime

**Source:** paper27 (already submission-ready as of 2026-04-27).

**Anchors:**
- BCH four laws by regime partition (`H_RegimePartition` Prop bundle
  with M_c_form_consistent witness).
- Balbinot 2005 BEC-acoustic primary anchor (NOT the older
  3He-A heating analogy — `feedback_deep_research_analog_conflation.md`
  applies).
- Hawking 1975 Schwarzschild contrast as the secondary anchor.

**Stage-13 BLOCKERs:**
- L3 + D3 §8 must agree on the regime-partition definition.
- Balbinot 2005 must be cached and primary; not 3He-A heating.

---

## Tier 3 — Infrastructure

### I1. Verification methodology with worked cases

**Source:** paper15 (substantially expanded) + worked-case curated set.

**Anchors:**
- FirstOrderKMS Aristotle counterexample case (Phase 1).
- Gap-solution-bounded counterexample case (Phase 5d).
- Chirality-wall axiom decomposition case (Phase 5h).
- The 14-stage Wave Execution Pipeline.
- The supersession ledger pattern + Pipeline Invariant #13 (Wave 6).

**Stage-13 profile:** software/methodology paper style; each worked
case must trace to a reproducible Aristotle run ID OR commit-pinned
counterexample.

### I2. Verified statistical estimators + lean-tensor-categories

**Sources:** Phase 5c VerifiedJackknife; Phase 5o Wave 4
lean-tensor-categories.

**Anchors:**
- VerifiedJackknife test suite cross-references.
- lean-tensor-categories Mathlib upstream cycle (when a PR is in
  review).

**Stage-13 profile:** software paper style; each function must trace
to a passing test.

### I3. Verified Stochastic Calculus for Mathlib4

**Sources:** Phase 6o.ζ Lean module synthesis (no per-paper substrate;
analogous to I2's lean-tensor-categories framing). See
`temporary/working-docs/phase6n/i3_bundle_scoping.md` for the bundle
scoping document.

**Anchors:**

1. **First-of-its-kind formalization claims.** Each "first
   formalization in any proof assistant" claim (stochastic integral,
   quadratic variation, Itô's lemma, Novikov, Cramér, Sanov, Varadhan)
   must be supported by a literature search showing no prior
   Lean/Coq/Isabelle/HOL Light/Mizar formalization exists.
2. **Mathlib substrate consumed.** Claims about consuming Brownian
   motion (Degenne–Ledvinka–Marion–Pfaffelhuber, "Formalization of
   Brownian motion in Lean", arXiv:2511.20118, 2025), Doob martingales
   (Ying-Degenne 2022), Markov kernels (Degenne, "Markov kernels in
   Mathlib's probability library", arXiv:2510.04070, 2025;
   primary-source verified Phase 7 absorption Session 5
   2026-05-08 — supersedes carry-forward "Marion 2025"
   misattribution), sub-Gaussian variables, must trace to the named
   upstream Mathlib commits.
3. **Reproducibility.** Each Lean module must build (no sorry, except
   documented stubs registered in `SORRY_GAPS`); the Mathlib upstream
   coordination memo's PR list must be live and cite-able.
4. **`LDPCompatibleSKEFT` typeclass cross-bridge.** Claims about D3 /
   D5 / E1 downstream consumers must trace to specific Lean theorems
   in those modules that explicitly invoke the typeclass.
5. **Mathlib upstream coordination integrity.** Claims about
   coordination with Degenne et al. (Brownian motion authors:
   Degenne, Ledvinka, Marion, Pfaffelhuber) or any Mathlib maintainer
   must trace to actual Zulip / GitHub coordination artifacts (not
   unilateral assertions).

**Stage-13 profile:** software/methodology paper style (Tier 3 — same
profile as I1 / I2). Each first-of-its-kind claim must trace to a
reproducible Aristotle run ID OR commit-pinned counterexample where
applicable.

---

## Tier 4 — Experimental letters

### E1. Paris-LKB polariton letter

**Source:** paper12 (companion content) + Phase 5u Wave 21 cover letter.

**Anchors:**
- Polariton platform shot-count feasibility.
- LKB-specific device parameters (per the experimental team's published
  device specs).

**Stage-13 profile:** lightweight letter review + device-parameter
audit pass.

### E2. Dean-Kim-Lucas graphene letter

**Source:** paper16_graphene_sk_eft (companion content).

**Anchors:**
- Graphene Dirac-fluid SK-EFT prediction.
- Dean-Kim-Lucas device parameters.

**Stage-13 profile:** lightweight letter review + device-parameter
audit pass.

---

## Cross-bundle anchor summary table

| Cross-bridge | From | To | Anchor |
|---|---|---|---|
| GW170817 Δc/c | L1 | D3 §6 | Same numerical bound |
| BCH four laws | L3 | D3 §8 | Same regime partition |
| Modular generation | L2 | D2 §2 | Same Ext + 24 \| c₋ chain |
| Drinfeld center | D2 §3 | D4 §4 | Same construction |
| QEC ↔ horizon-MTC | D3 §9 | D4 §7 | Same cross-bridge |
| CC channel | D3 §21 | D5 §7 | Same heat-kernel a_0 |
| Polariton companion | D1 §6 | E1 | Same LKB device specs |
| Graphene companion | D1 §7 | E2 | Same Dean-Kim-Lucas specs |

The Wave 7.3 `validate.py --check bundle_consistency` walks each
cluster in `cluster_bundle_index.json` (built by Wave 7.1
`bundle_clusters.py`) and flags any `cross_bundle: true` cluster whose
member sentences disagree on the cross-bridge's numerical content.

---

*Document created 2026-04-29 (Phase 6i Wave 7.2). Companion to
`PAPER_STRATEGY.md` and `PAPER_DRAFT_MAPPING.md`. Loaded by
`physics-qa:claims-reviewer` and `physics-qa:figure-reviewer` when
invoked with `bundle_target=<target>`.*
