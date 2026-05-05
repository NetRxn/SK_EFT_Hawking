# SK-EFT Hawking — Paper Communication Strategy

**Status:** Active strategy document. Supersedes the per-wave-paper convention from Phases 1–6f for *external* communication; the per-wave drafting work in `papers/paperN_*` continues as internal source material that is then consolidated into the bundles defined here.

**Created:** 2026-04-28 from program-wide gap analysis (`temporary/Research-Overview/research_overview_analysis.md`) + paper-strategy reframing.

**Authority:** This document is the canonical reference for paper-deliverable structure and sequencing. Phase 6i Wave 7 (Paper Strategy Integration) wires this into the review pipeline. The per-paper drafts in `papers/paperN_*` remain in the repository as historical/source material; their consolidation into the bundles defined here is tracked in `PAPER_DRAFT_MAPPING.md`.

---

## 1. Diagnosis of the prior "one paper per wave" strategy

The project entered Phase 6 with thirty-two paper drafts and zero submissions. This is not a productivity issue — the per-wave drafting cadence has been an extremely effective *internal* discipline: each wave produces a paper-shaped deliverable, the Stage 13 adversarial reviewer keeps each draft honest, and the sentence-level provenance ties each claim to a Lean theorem. But the resulting paper map is inward-facing in three concrete ways:

**Headline results are buried.** "First quantum group in any proof assistant," "first formally verified four laws of black-hole mechanics partitioned by regime," "GW170817 falsifies the vestigial-second-sound graviton ID by 7 × 10¹⁴" — each of these is striking enough on its own to be the door into the program, but each currently sits inside a draft (Paper 11, Paper 27, Paper 25) that an external reader encounters as an isolated technical result. There is no flagship that says "here is what this research program is about" for them to land in.

**NO-GO theorems lose first-class status.** The program is unusual in that negative structural results are a deliberate output: Volovik q-theory dark energy, the vestigial-graviton GW170817 falsification, Fang-Gu torsion DM kinematic exclusion, fracton hydrodynamics → full GR, the BCS-branch seesaw lepton-number-violation requirement, perturbative Wen-ADW gravity, EW baryogenesis under crossover, abelian-MTC at the BH horizon. Distributed across many drafts, these read like incidental obstructions. Consolidated, they are a coherent statement about *which* parts of the standard map of physics are reachable from condensed-matter substrates and *why* — a genuine field-clearing contribution. Phase 5y already understands this internally (six closure rounds, formal scope memo, `ARCHITECTURE_SCOPE.md`). The paper strategy did not previously reflect it externally.

**Methodology is invisible to physicists.** The project's verification pipeline — Lean + Aristotle + adversarial review + sentence-level provenance + the 14-stage wave execution + the preemptive-strengthening discipline — is genuinely novel as a way to *do* theoretical physics, not just as a tool for proof-assistant developers. Critically, the verification has produced physics that wouldn't otherwise exist: Aristotle disproved the original FirstOrderKMS axiom (too weak); Aristotle disproved the gap-solution-bounded conjecture; the chirality-wall axiom decomposition surfaced hidden dependencies; the strengthening-pass discipline has caught dozens of structural-tautology theorems. Buried in a methods paper that only formal-verification people will read, this contribution is invisible to the physics audience that should hear it.

The paper strategy below is designed to fix all three.

---

## 2. Architecture — four-tier, falsifiability-led

The new structure is **fourteen publication targets**, organized as one flagship + five themed deep papers + three PRL-style headline letters + three infrastructure papers + two experimental letters. This is roughly a 2.3:1 collapse from the thirty-two drafts. Every existing draft maps cleanly into one of the fourteen targets (see `PAPER_DRAFT_MAPPING.md`). (Bundle architecture went 13 → 14 in Phase 6n Session 4 with the I3 authorization for "Verified Stochastic Calculus for Mathlib4"; original v1 figure of "eleven" headline drift was a long-standing miscount that this revision corrects in the same pass.)

Three principles drive the architecture:

1. **Falsifiability-led ordering.** The PRL-style headline letters (Tier 2) lead with the program's strongest falsifiable results — GW170817 vs vestigial-graviton (7 × 10¹⁴ falsification), three generations from modular invariance, BCH four laws by regime. These are the door-openers. Readers arrive through them.
2. **NO-GOs as first-class deliverables.** The dark-sector deep paper (Tier 1 #5) is built around the structural-NO-GO architecture. The flagship's Layer-3 scope statement makes the predictive-boundary explicit. The methodology paper documents specific cases where verification produced negative content the conventional process would have missed.
3. **The flagship is the citation anchor.** Tier 0 — one *Reviews of Modern Physics* / *Physics Reports* / *Annual Review* article — is the canonical entry point. Every other paper in the program cites it. It ships *last*, after the Tier 1 papers are out, so it can cite them and serve as the stable reference rather than a snapshot.

### 2.1 Tier 0 — flagship review (1 paper)

**Paper F: "Fluid-Based Approaches to Fundamental Physics — A Formally Verified Survey"**

Target journal: *Reviews of Modern Physics*, *Physics Reports*, or *Annual Review of Nuclear and Particle Science*.

Length: 80–150 pages.

Audience: the broad theoretical physics community plus mathematical physics and formal-verification readers.

Five jobs at once:
- Present the three-layer architecture (lattice → SK-EFT → emergent SM+GR) as the unifying frame.
- Index every machine-checked headline result and every formal NO-GO with cross-references to Tier 1 deep papers.
- Establish the verification methodology as a unifying thread (not a methods footnote).
- Lift `ARCHITECTURE_SCOPE.md` into the published literature: Layer 3 is in scope for SM+GR-sector emergent physics; the dark-energy sector is outside the tested predictive scope under Volovik mechanisms (and the Phase 6m verdict on causal-set / entropic-gravity / Jacobson-thermodynamic-GR routes, when shipped).
- Serve as the citation anchor that every other paper in the program references.

Outline (roughly 12 sections):
1. Introduction: the question and the methodology.
2. Three-layer architecture and predictive scope.
3. Emergent gauge fields: gauge erasure + topological-order routes.
4. Analog Hawking radiation across three platforms (summary; full content in Tier 1 #1).
5. Anomaly constraints on Standard-Model particle content (summary; full in Tier 1 #2).
6. Emergent gravity from microscopy (summary; full in Tier 1 #3).
7. Topological quantum computation foundations (summary; full in Tier 1 #4).
8. Dark sector under substrate constraints (summary; full in Tier 1 #5).
9. Verification methodology (summary; full in Tier 3 #1).
10. Architectural scope statement: what is and is not predicted.
11. Open program — Phase 6 forward roadmap.
12. Outlook: experimental access and future-work register.

This paper is *the* paper that says what the program is. Submitted last; built incrementally throughout the Tier 1 roll-out; final form benefits from ~12 months of accumulated cross-citation.

### 2.2 Tier 1 — themed deep papers (5 papers)

Each is a PRD/JHEP-style article aimed at one subcommunity. Each is the canonical reference for its slice. Each is 20–60 pages with full Lean theorem cross-references.

**Paper D1: Formally Verified Analog Hawking Radiation Across Three Platforms**

Target: *Physical Review D* (long article).

Audience: analog-gravity, condensed matter (BEC / polariton / Dirac-fluid graphene), gravitational-wave-adjacent.

Content: SK-EFT corrections to all orders; transport coefficient counting `count(N) = ⌊(N+1)/2⌋ + 1`; CGL FDR derivation; parity alternation theorem; exact WKB connection formula with the three non-perturbative effects (broken unitarity, FDR-mandated noise floor, spectral floor at ~6 T_H); positivity-forced relations at second order; KMS optimality; BEC predictions; polariton Tier-1 with stimulated-Hawking amplification; graphene Dirac-fluid 3×3 metric block-diagonalization, 92% Lean theorem reuse, Wiedemann-Franz violation, closed-form noise spectrum from Keldysh FDT + Landauer-Büttiker. Sidebar: how Aristotle's counterexample fixed the FirstOrderKMS axiom.

Sources: Papers 1, 2, 4, 12, 16a; Phase 5w + Phase 5d + Phase 5u material.

Companion: Tier 4 letters for Paris-LKB and Dean-Kim-Lucas experimental teams.

**Paper D2: Anomaly Constraints on Standard-Model Particle Content**

Target: *PRD* or *JHEP*.

Audience: high-energy theory, particle physics, lattice QFT, mathematical physics (anomaly classification, bordism).

Content: Three generations from Z₁₆ + modular invariance; the 16-convergence (SM Weyl, Z₁₆ classification, Rokhlin's 16, Kitaev DIII period — all from the quaternionic structure); the gravitational-anomaly argument for ν_R; the chirality-wall three-pillar synthesis (GS no-go evasion, GT positive construction, Z₁₆ algebraic anchor); the master TPF-evasion theorem; the 4+1D gapped-interface axiom and its 1+1D + 2+1D Fidkowski-Kitaev evidence; the change-of-rings discharge of topological hypothesis H2; the open H1/H3/H4 hypotheses pending Mathlib algebraic-topology infrastructure. The first machine-checked Ext^n_{A(1)}(F₂, F₂) computation in any proof assistant features as a section, not a separate paper.

Sources: Papers 7, 8, 9, 10; Phase 5b/5c/5q/5r/5h material.

**Paper D3: Emergent Gravity from Microscopy — Linearized EFE through Black-Hole Thermodynamics**

Target: *PRD* (long article), possibly *Annals of Physics*.

Audience: gravitational physics, BH thermodynamics, emergent-gravity community, holography-adjacent.

Content: ADW gap equation `G_c = 8π² / (N_f Λ²)`; the tetrad gap equation as the first explicit derivation in the literature; the bifurcation theorem; Vergeles unitarity Props; the gauge erasure selection rule (only U(1) survives the fluid layer; non-Abelian erased); the perturbative Wen-ADW deficit (G_Wen / G_c ≈ 1/6000 — route formally closed); fracton-hydrodynamics → full GR no-go; the linearized EFE result `G_N^emerg = α_ADW · 12π / (N_f Λ²)`; FLRW reduction with Friedmann I/II + Bianchi consistency; the GW170817 falsification of the vestigial-second-sound graviton identification (the headline negative result, reported in full); the Bekenstein-Hawking entropy from MTC state counting `S = A/(4G_N) − (3/2) log(A/(4G_N))` with Kaul-Majumdar SU(2)_k decomposition and the abelian-MTC F2 falsifier; the BCH four laws partitioned by regime at `M_c = (N_f Λ_UV) / (12π α_ADW)`; the Schwarzschild-vs-ADW-extremality regime criterion. Cross-bridges to QCD strong-coupling closure (Phase 6d Track A: confinement, χSSB GMOR, CFL ℤ_3 ≡ QCD center-ℤ_3) as a section.

Sources: Papers 3, 5, 22, 23, 25, 26, 27, 36, 37, 38; Phase 3 + Phase 5d + Phase 5f + Phase 5z W3 + Phase 6a + Phase 6d material.

**Paper D4: Topological Quantum Computation — First Machine-Verified Foundations**

Target: *PRD*, *PRX Quantum*, or split between mathematical-physics journal (*Communications in Mathematical Physics*) for the categorical content and *PRX Quantum* for the universality/gate content.

Audience: topological quantum computation, mathematical physics, formal verification (math-flavor).

Content: the longest verified mathematical chain in any proof assistant — Onsager-algebra → Inönü-Wigner contraction → U_q(sl₂) (first quantum group) → Hopf algebra (first non-trivial Hopf-algebra instance) → restricted u_q(sl₂) → SU(2)_k fusion at k=1,2,3 → S-matrix unitarity + Verlinde formula → algebraic number fields Q(√2), Q(√5), Q(ζ₅), Q(ζ₁₆) → F-symbols + R-matrices → hexagon equations → ribbon → trefoil = −1 (first verified knot invariant) → figure-eight knot → TQFT partition functions → WRT surgery invariants → Temperley-Lieb → Jones-Wenzl → Fibonacci universality (Lie-algebra spanning proof). Plus U_q(sl₃) (first rank-2 quantum group) → SU(3)_k fusion (first SU(3)_k formalization) → generic `QuantumGroup k A` → Kac-Walton fusion. Plus Muger center, Frobenius-Perron from fusion-matrix eigenvalues, dual-closure theorem, string-net. Plus the Fermi-Hubbard doublon SWAP + minimal Berry-phase theorem (first formally verified symmetry-protected two-qubit gate). Sidebar: industry relevance (Microsoft Majorana = our verified Ising; Google surface codes = our toric code via Vec_{ℤ/2} string-net; Fibonacci universality = our verified proof).

Sources: Papers 11, 14, 16b, 18; Phase 5b–5p material.

**Paper D5: The Dark Sector under Substrate Constraints**

Target: *PRD* or *Physics Reports* (review-flavored if the Phase 6m closure adds Tracks A/B/C verdicts).

Audience: cosmology, dark matter, dark energy, particle astrophysics.

Content: The structural NO-GO architecture for the dark-energy sector under tested mechanisms — Gibbs-Duhem locking `w_vac ≡ −1` for any single-scalar self-tuning emergent-vacuum framework; the q-theory realization-independent NO-GO across all four KV constructions; the four-factor orthogonality decomposition (Gibbs-Duhem ∩ c_s² ≥ 0 ∩ natural T_c ∩ MICROSCOPE); the closed-form vestigial EOS `w_vest(τ) = (1−τ²)/(5τ²−1)` and its catastrophic-c_s² gradient instability on the natural branch; the Zhitnitsky topological-DE absorption (within ≤ 3 orders of observed Λ, no free parameters); the combined-mechanism falsifier (Zhitnitsky + KV q-theory both active gives ×240 the observed value, forcing single-DE-mechanism commitment); the Phase 5y Layer-3 scope recalibration; the Phase 6m Tracks A/B/C closure for causal-set, entropic-gravity, and Jacobson-thermodynamic-GR routes (when those waves return). Plus the dark-matter classification: SFDM cluster-merger forecast at 3.5–5.7σ (Bullet, El Gordo, Pandora, A520, MACS J0025; Rankine-Hugoniot density-jump closed form; first 3σ detectable around 2028 with Euclid × Roman); fracton DM viability in p-wave dipole superfluid phase at MeV–TeV; Z₁₆-classified hidden-sector T-0 TQFT (invisible to all planned direct detection); Fang-Gu torsion DM kinematic exclusion at CDM level.

Sources: Papers 17, 32, plus the new Phase 6m verdict modules.

### 2.3 Tier 2 — PRL-style headline letters (3 papers)

Each is four pages, citing flagship + one Tier 1 paper. Each is a stand-alone news-attractor.

**Paper L1: GW170817 Falsifies the Vestigial-Second-Sound Graviton Identification by 7 × 10¹⁴**

Target: *Physical Review Letters*.

Length: 4 pages.

Lede: Volovik (JETP Lett. 119, 564, 2024) identified the vestigial second-sound mode as the spin-2 graviton, with leading-order propagation `c_GW = c · √χ_vest`. The natural susceptibility range χ_vest ∈ [0.1, 10] gives Δc/c ∈ [−0.68, +2.16], exceeding the LIGO-Virgo GW170817 cap of 3 × 10⁻¹⁵ by ~7 × 10¹⁴. Both endpoints proved as Lean falsifier theorems. Recovery requires either a derived-DOF mechanism for χ_vest = 1 or recognition that the metric-channel susceptibility is a separate UV input.

Why it ships first: clean falsification at LIGO precision, news-attractive, fits cleanly in 4 pages, doesn't require flagship to land. Strongest candidate for the arXiv-voucher first submission.

Source: Paper 25 + Phase 6a Wave 2 material.

**Paper L2: Three Generations of Standard-Model Fermions from Modular Invariance — A Machine-Checked Derivation**

Target: *Physical Review Letters*.

Length: 4 pages.

Lede: The number of Standard-Model fermion generations is forced to be a multiple of three by the combination of (i) the chiral central charge `c₋ = 8 N_f` from particle content and (ii) modular invariance `24 | c₋`. The smallest nontrivial solution is `N_f = 3`. The first machine-checked Ext^n_{A(1)}(F₂, F₂) computation through degree 5 (in any proof assistant) backs the algebraic core. Three textbook topology hypotheses (H1/H3/H4) remain pending Lean's algebraic-topology library; each is independently verifiable by a topologist.

Why it ships early: zero project-originated axioms in the algebraic layer; the headline "why three generations" question is broadly recognized; the proof-assistant first is news.

Source: Paper 10 + Phase 5b/5c/5q/5r material.

**Paper L3: Bardeen-Carter-Hawking Four Laws Partitioned by Regime in an Emergent-Gravity Substrate**

Target: *Physical Review Letters*.

Length: 4 pages.

Lede: We give the first machine-checked formulation of the four laws of black-hole mechanics partitioned by regime — Schwarzschild (heats up under accretion, finite-time evaporation) versus ADW-extremality (cools toward extremality, infinite-time near-extremal asymptote) — separated by `M_c = (N_f Λ_UV) / (12π α_ADW)`. The Jacobson-Koike form `T_H(v) = T_H(0) (1 − v²/c_⊥²)` is the structural anchor. The second law follows from Glorioso-Liu SK-EFT entropy-current monotonicity without invoking pointwise NEC. The third law preserves Israel's strong form in the natural Schottky branch but admits Kehle-Unger-style violation in BPS-violating matter sectors.

Why it ships early: Paper 27 is already submission-ready (cleared a 4-pass Stage 13 adversarial review); the regime-partition criterion is genuinely new; the formalization is a "first."

Source: Paper 27 + Phase 6a Wave 5 material.

### 2.4 Tier 3 — infrastructure papers (3 papers)

**Paper I1: Formal Verification at Scale in Theoretical Physics — A Methodology with Worked Cases**

Target: *Computer Physics Communications* or *Physics Reports*.

Audience: physicists *and* formal-verification researchers.

Content: Why machine verification changes what theoretical physics can do — by catching axioms that turn out to be false, by proving conjectures false, by forcing decomposition that surfaces hidden assumptions, by enabling adversarial-review automation. Three concrete worked cases: (1) Aristotle's counterexample to the original FirstOrderKMS axiom (constrained 4/9 components only; all 9 needed); (2) Aristotle's disproof of the gap-solution-bounded conjecture (explicit unbounded-in-G witness); (3) the chirality-wall axiom decomposition (1 opaque axiom → 4 focused topology hypotheses + 1 4+1D gapped-interface assumption with 1+1D and 2+1D evidence). Plus the 14-stage wave execution pipeline; the preemptive-strengthening discipline (six anti-patterns and their detection); sentence-level provenance with cross-paper consistency clusters; the three-layer Python ↔ Lean ↔ Aristotle architecture; the Stage 13 adversarial-reviewer pattern. Critically, this paper is aimed at the physics audience that needs to *believe* formal verification is worth the friction, not just at proof-assistant developers who already do.

Source: Paper 15 + WAVE_EXECUTION_PIPELINE.md + a curated trace of representative reviewer-driven corrections.

**Paper I2: Verified Statistical Estimators and the lean-tensor-categories Library**

Target: *Journal of Open Source Software* or *Computer Physics Communications* (software paper) plus companion Mathlib upstream PRs (Phase 5o Wave 5).

Audience: lattice physics, formal-verification community, mathematical-physics readers needing infrastructure.

Content: First verified jackknife and autocorrelation estimators (with the jackknife-variance-non-negative theorem); the 114-theorem lean-tensor-categories library covering the categorical hierarchy (Pivotal → Spherical → Balanced → Ribbon → Semisimple → Fusion → Modular), Hopf-algebra extensions (QuasitriangularBialgebra, RibbonHopfAlgebra), decidable algebraic number fields (Q(√2), Q(√5), Q(ζ₅), Q(ζ₁₆), Q(ζ₅) extensions, ComputableAdjoinRoot), and concrete instances (SU(2)_k fusion at k=1..5, Ising MTC, Fibonacci MTC, SU(3)_k k=1, 2). Mathlib upstream coordination memo. Reusable for any project needing verified MTC infrastructure (downstream: TPF construction, fault-tolerant-quantum-computing certification, anyonic-gate verification, conformal-field-theory partition functions).

Source: Phase 5c VerifiedJackknife + Phase 5o Wave 5 lean-tensor-categories work.

**Paper I3: Verified Stochastic Calculus for Mathlib4 — Stochastic Integral, Quadratic Variation, Itô's Lemma, and Large-Deviation Foundations**

Target: *Journal of Open Source Software* (primary) or *Computer Physics Communications* (fallback); tertiary fallback is upstream Mathlib4 PR series + community blog post.

Audience: the Mathlib probability working group (Degenne / Marion / Ledvinka / Pfaffelhuber); formal-verification community (Lean / ITP / CPP / FSCD); mathematical-probability-meets-formalization readers; the program's downstream physics consumers (D3 / D5 / E1) that will invoke the `LDPCompatibleSKEFT` typeclass.

Content: First formalization in any proof assistant of (i) the stochastic integral against semi-martingales (`StochasticIntegral`, `ItoIsometry`); (ii) quadratic variation and covariation (`QuadraticVariation`, `Semimartingale`); (iii) Itô's lemma for vector semimartingales (`ItoLemma`); (iv) Novikov's condition and Girsanov sketch (`Novikov`); (v) the foundational large-deviation framework — Cramér-iid + Sanov via method-of-types + contraction principle (`CramerIID`, `Sanov`, `Contraction`); (vi) Cramér lower bound via Esscher tilting + Varadhan-style upper bound (`CramerLowerBound`, `Varadhan`); plus (vii) the `LDPCompatibleSKEFT` typeclass that surfaces LDP-rate-function content in the program's existing SK-EFT Glorioso-Liu monotonicity statements (cross-bridge to D3 / D5 / E1). Companion Mathlib upstream coordination memo documents PR cadence and the Degenne / Marion coordination plan. Builds on the recently-completed Mathlib Brownian-motion (Degenne et al. arXiv:2511.20118), Doob martingales (Ying–Degenne 2022), and Markov kernels (Marion arXiv:2510.04070) substrates; closes the four-to-five-module gap (stochastic integral / semimartingale / Itô / Novikov / Stratonovich) those substrates leave.

Source: Phase 6n Session 4 I3 bundle authorization (Pipeline Invariant #14) + Phase 6o.ζ Lean module synthesis (no per-paper substrate; analogous to I2's lean-tensor-categories framing). Source manifest at `temporary/working-docs/phase6n/i3_bundle_scoping.md`.

### 2.5 Tier 4 — experimental letters (2 papers)

**Paper E1: A Falsifiable Hawking Spectrum for Polariton Microcavities at the Paris LKB Device Parameters**

Target: *Physical Review Letters* (Letter), *Physical Review Research*, or as an extended cover-letter document.

Length: 2–3 pages.

Audience: the Paris LKB polariton-Hawking experimental team (Falque / Bramati / Giacobino) primarily; broader analog-gravity-experimental community secondarily.

Content: The SK-EFT predicted Hawking spectrum and noise floor `n_noise = δ_k / 2` evaluated at the Paris-LKB device's published parameters. Signal-to-noise estimate for spontaneous detection at their cavity Q. Stimulated-Hawking amplification factor for stimulated-mode runs. The falsifiable frequency window where the SK-EFT noise-floor formula makes the cleanest prediction. A request for current device-parameter values to allow band-tightening.

Sources: Phase 5u Wave 21 (the new wave appended 2026-04-28); Paper 12 main material.

**Paper E2: Detecting Analog Hawking Radiation in the Bilayer-Graphene Dirac Fluid**

Target: *PRL* or *Physical Review Research*.

Length: 2–3 pages.

Audience: the Dean group (Columbia, sonic-horizon realization 2025); the Kim group (Harvard, noise thermometer); the Lucas group (theoretical noise-spectroscopy framework); broader graphene-electronic-Dirac-fluid community.

Content: T_H ≈ 2.4 K predicted for the Dean bilayer nozzle (10⁹× BEC). Negligible dissipative correction (δ_diss ~ 10⁻¹³, 11 orders below dispersive δ_disp ~ −3%). Wiedemann-Franz violation L/L₀ > 200× from two-channel transport. Closed-form noise-spectrum prediction `ΔS_I(ω) = 2ℏω σ_Q Γ(ω) n_H(ω)` from Keldysh FDT + Landauer-Büttiker. Bandwidth-cumulative SNR = 1 in ~1 minute at the Dean device. Principal device-specific uncertainty: greybody factor `Γ(ω)`.

Sources: Phase 5w material; Paper 16a main content.

---

## 3. Sequencing — order of submission and dependencies

The order matters. Three principles:

1. **Clear the arXiv-voucher gate with the easiest stand-alone PRL.** L1 (GW170817 vs vestigial-graviton) is the strongest candidate: clean negative result, fits in 4 pages, news-attractive, doesn't require any other paper to be out, doesn't depend on uncertain content.

2. **Tier 1 papers ship before Tier 0.** The flagship cites the Tier 1 papers; trying to write the flagship without them done is a snapshot. Tier 1 papers ship roughly in parallel after the voucher, with priority weighted toward shipping-ready material.

3. **Experimental letters ship paired with their Tier 1 anchor.** Tier 4 letters are most useful when the experimental team can simultaneously read the formal Tier 1 #1 paper (analog Hawking) for full backing.

Recommended sequence (approximate, conditional on user-authorization gates and Phase 6 closure of dependent waves):

- **Month 0:** L1 (GW170817 / vestigial-graviton). Voucher cleared.
- **Month 1–2:** L3 (BCH four laws by regime — Paper 27 already submission-ready), D3 (emergent gravity through BH thermo — absorbs L3's content as a section + adds the architectural context). These can ship in close succession; L3 as the splash, D3 as the deep companion.
- **Month 2–3:** L2 (three generations from modular invariance) + D2 (anomaly constraints on SM particle content). Same pattern: splash + deep.
- **Month 3–4:** D1 (analog Hawking across three platforms) + E1 (Paris LKB letter) + E2 (Dean-Kim-Lucas letter). Three publications same window because they reinforce each other and reach distinct experimental teams.
- **Month 4–5:** D4 (topological quantum computation foundations).
- **Month 4–6:** I1 (methodology) + I2 (lean-tensor-categories + verified statistics). Aligned with Phase 5o Wave 5 Mathlib upstream cycle.
- **Month 5–8:** D5 (dark sector). Ships after Phase 6m Tracks A/B/C return verdicts (estimated ~4–6 months from now). The paper is much stronger as a closed predictive-scope statement than as a partial Volovik-only closure.
- **Month 8–12:** F (flagship). Drafted incrementally throughout the roll-out; final form benefits from cross-citation of Tier 1 papers and the Phase 6m closure.

Twelve months from voucher to flagship is the rough envelope. The Phase 6 deep-research dispatches (six per Track in Phase 6m, plus the Phase 6j-6l Wave-1 dossiers) operate in parallel.

### Dependency graph (compressed)

- L1 has no dependencies; ships first.
- L3 ships after Paper 27 Stage-13 closure (already done) + arXiv voucher (from L1).
- L2 ships after L1 voucher; depends on no Phase-6 closure.
- D3 depends on L3 content + Phase 6d Track A closure (already shipped) + Phase 6a closure (already shipped). Ready.
- D2 depends on L2 content + the Phase 5b/5c chain (already shipped). Ready.
- D1 depends on Phase 5w closure (already shipped) + Phase 5d/5u closure (already shipped) + the WKB chain (already shipped). Ready.
- D4 depends on Phase 5b–5p categorical chain (already shipped) + Phase 5t doublon-gate (already shipped). Ready.
- D5 depends on Phase 5y closure (shipped) + Phase 6m Tracks A/B/C closure (in progress). Blocked on Phase 6m.
- F depends on D1–D5 + I1 + I2 + L1–L3 all shipped.
- I1 has no dependencies; can ship any time.
- I2 depends on Phase 5o Wave 5 Mathlib upstream cycle in progress; ships when first Mathlib PR is in review.
- E1 depends on D1 ready + Phase 5u Wave 21 cover-letter draft.
- E2 depends on D1 ready + Phase 5w material.

The critical path is L1 → voucher → everything else. The slowest path is Phase 6m → D5 → F. The flagship lands roughly when Phase 6m closes.

---

## 4. Cross-cutting principles

**NO-GOs are first-class.** Every Tier 1 deep paper that contains a structural NO-GO presents it as a result, not a footnote: D3 with vestigial-graviton + perturbative-Wen-ADW + non-Abelian-gauge-erasure + fracton-GR; D5 with q-theory + vestigial-graviton-cross-bridge + Fang-Gu + abelian-MTC-horizon. The flagship's §2 (architectural scope) and §10 (scope statement) explicitly section the predictive boundary. This is a deliberate communication choice; the program's negative content is unusually high-quality and deserves visibility.

**The methodology paper aims at physicists.** I1 is *not* primarily a formal-verification-community paper. The audience is the theorist who currently does not believe machine verification is worth the friction. The argument is empirical: here are three concrete cases where verification produced physics that would not otherwise exist. The formal-verification audience consumes I2 (the software paper) and the Mathlib upstream PRs.

**Every paper carries the scope statement.** Each paper includes (in the discussion or as a sidebar) the relevant slice of `ARCHITECTURE_SCOPE.md` — what this paper claims to predict, and what is explicitly outside the tested predictive scope under the mechanisms exercised here. This insulates each paper against implicit-overclaim review findings (e.g., "this paper says the substrate gives gravity but doesn't say anything about dark energy — is that an oversight?").

**Sentence-level provenance survives the rebundling.** The Phase 5v/Phase 6i sentence-state infrastructure (`prose_state.json`, `audit_log.jsonl`) tracks each sentence's claim cluster, primary source, and Lean theorem backing. When existing Paper 11 content lifts into D4, the sentence-level metadata moves with it — no claim becomes orphaned, no Lean reference rots. Phase 6i Wave 7 wires this re-mapping into the QI process.

**Adversarial review continues per bundle.** Stage 13 adversarial review applies to the new bundles, not just the old per-wave drafts. Each bundle gets at least one full-pass review before submission, with a pre-submission re-invocation pass after any substantive revision. The reviewer prompts are updated to know the bundle architecture.

**The flagship can be re-released.** RMP-style reviews are typically updated every few years. The flagship is designed for re-release: append-only sections covering Phase 7+ as the program continues, while the structural backbone (architecture, scope, methodology) stays stable.

---

## 5. Open questions and risks

**Will the experimental teams cooperate?** Tier 4 letters (E1, E2) are most useful when the experimental teams find them actionable. The Paris LKB group has the most engaged track record on polariton-Hawking; Dean-Kim-Lucas have the device but no announced Hawking-detection program. E1 has a higher probability of catalyzing measurement; E2 may end up more of a "Theory has the prediction; experimentalists have the device; here's how they meet" position paper. Both are worth shipping; the latter is hedged.

**Will Mathlib accept the lean-tensor-categories upstream?** I2's joint-paper structure assumes the Mathlib PR cycle (Phase 5o Wave 5) lands at least the first atomic PR (QSqrt2 + ComputableAdjoinRoot bridge) within the I2 timeline. If Mathlib's AI-content policy delays merging beyond ~6 months, I2 ships as a software-only paper without the Mathlib-acceptance hook; the upstream cycle becomes a separate JOSS update later.

**Will Phase 6m return all-NO-GO across Tracks A/B/C?** D5 (dark sector) is much stronger if it ships as a closed predictive-scope statement covering Volovik *and* the three new mechanism families. If any one of Tracks A/B/C returns PARTIAL-VIABLE, D5 still ships, but the framing changes from "dark-energy sector outside scope under tested mechanisms" to "dark-energy sector is a multi-mechanism landscape with one viable substrate-derived candidate." Both versions are publishable; the framing is determined by the closure outcome.

**Should D4 be split?** The longest-verified-mathematical-chain content has natural sub-audiences: the categorical-MTC/quantum-group content fits a *Communications in Mathematical Physics* split, while the Fibonacci-universality + doublon-gate content fits *PRX Quantum*. A single D4 paper is recommended for first publication (more impact unified), but a split into D4a (math-physics) + D4b (quantum computation) is acceptable if reviewer feedback during the bundle's Stage 13 strongly recommends it. The decision is deferred to the bundle's Stage 1 scoping.

**What about HepLean coordination for D2?** The anomaly-constraints paper (D2) and the latent Phase 6k Wave 4 (CKM apex substrate constraint) both touch HepLean's territory. Coordination is required: D2 should reference HepLean's CKM catalog where relevant, and Phase 6k Wave 4 will consume HepLean's CKM API once the Mathlib coordination work establishes the relationship-channel. D2 itself does not depend on Phase 6k.

**What if a striking new result lands during the roll-out?** The architecture is intentionally append-friendly. A new Tier 2 PRL splash can be added if a Phase 6 wave produces a 4-page-PRL-shaped headline (e.g., a Phase 6m Track returning VIABLE with a specific substrate-realization, or a Phase 6h activation if Gate Z.4 flips). The flagship's outline accommodates incremental additions.

---

## 6. Summary table

| Tier | Paper | Title (short) | Target | Length | Ships | Dependencies |
|---|---|---|---|---|---|---|
| 2 | L1 | GW170817 / vestigial-graviton | PRL | 4pp | Month 0 | (voucher gate) |
| 2 | L2 | Three generations from modular invariance | PRL | 4pp | Month 2–3 | L1 voucher |
| 2 | L3 | BCH four laws by regime | PRL | 4pp | Month 1–2 | L1 voucher |
| 1 | D1 | Analog Hawking across three platforms | PRD long | ~40pp | Month 3–4 | L1 voucher |
| 1 | D2 | Anomaly constraints on SM | PRD/JHEP | ~30pp | Month 2–3 | L1 voucher |
| 1 | D3 | Emergent gravity through BH thermo | PRD long | ~50pp | Month 1–2 | L1 voucher |
| 1 | D4 | Topological QC foundations | PRD/PRX-Q | ~40pp | Month 4–5 | L1 voucher |
| 1 | D5 | Dark sector under substrate constraints | PRD/Phys Rep | ~40pp | Month 5–8 | Phase 6m closure |
| 3 | I1 | Methodology | CPC/Phys Rep | ~25pp | Month 4–6 | (none) |
| 3 | I2 | Verified estimators + lean-tensor-categories | JOSS/CPC | ~15pp | Month 4–6 | Phase 5o W5 |
| 4 | E1 | Polariton experimental letter | PRL/PRR | 2–3pp | Month 3–4 | D1 ready + Phase 5u W21 |
| 4 | E2 | Graphene Dirac-fluid letter | PRL/PRR | 2–3pp | Month 3–4 | D1 ready |
| 0 | F | Flagship review | RMP/Phys Rep | 80–150pp | Month 8–12 | All above |

Eleven publication targets. Approximate twelve-month roll-out from voucher. The flagship is the citation anchor.

---

## 7. Cross-references

- **Draft mapping:** `PAPER_DRAFT_MAPPING.md` — explicit per-draft → per-bundle assignment for each of the 32 existing drafts.
- **Phase 6i Wave 7:** Paper Strategy Integration into the QI review process; updates Stage 13 reviewer prompts, sentence-level-provenance bundle assignment, and cross-paper consistency clusters.
- **Pipeline:** `WAVE_EXECUTION_PIPELINE.md` — the 14-stage process per wave; per-bundle Stage-13 adversarial-review re-invocation is defined in Phase 6i Wave 7.
- **Architecture scope:** `ARCHITECTURE_SCOPE.md` — Layer-3 predictive-boundary statement; lifted into the flagship's §2 + §10.
- **Research status:** `RESEARCH_STATUS_OVERVIEW.md` — the snapshot inventory of proven chains, open targets, and NO-GOs that the bundles consolidate.
- **Phase roadmaps:** `roadmaps/Phase{1..6}*_Roadmap.md` — per-wave execution plans whose deliverables flow into the bundles.
- **Inventory:** `SK_EFT_Hawking_Inventory_Index.md` and `SK_EFT_Hawking_Inventory.md` — module-level ground truth.
- **Knowledge graph:** `KNOWLEDGE_GRAPH.md` and the provenance dashboard's KG tab — the cross-paper claim-cluster infrastructure that survives the re-bundling.

---

*Created 2026-04-28. Active strategy document. Updates atomically as bundles ship and Phase 6 waves close.*
