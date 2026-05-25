# Strategic Positioning: Phase 6q — The Substrate-Bimodal-Outcome Phase

## How the Program Delivers Positive Uniqueness AND Sharpened NO-GO from the Same Theorem

**Date:** 2026-05-25
**Context:** This memo positions Phase 6q within the broader research program. Phase 6q substantively COMPLETE.

---

## Phase 6q's Strategic Value

Phase 6o Wave 1c closed with a structural NO-GO: the dissipative-SK-EFT bootstrap cannot produce uniqueness with the standard SK axiom set, blocked by three explicit obstructions (KMS replaces unitarity but breaks positivity; no SK-crossing analogue; SDP feasibility breaks on the complex contour). The NO-GO was useful — three explicit named obstructions — but left an open question: *is the dissipative-bootstrap programme structurally blocked, or does a different axiom set succeed?*

Phase 6q's Wave 1a deep research identified the answer: **the Chowdhury-Hartnoll DKM transport bootstrap (arXiv:2509.18255) is purely analytic** — no SDP, no crossing, no complex contour. It bypasses all three Phase 6o obstructions by design. Phase 6q ports CHHK to Lean and asks the natural follow-up: *does this analytic bootstrap succeed on the SK-EFT-Hawking substrate, or also fail?*

The strategic point: **the answer is BOTH — and that is the contribution**. CHHK succeeds on lattice platforms (graphene Dirac fluid; positive uniqueness with substantive numerical bound) and fails on continuum-bosonic platforms without UV regularization (BEC Bogoliubov; sharpened NO-GO with concrete super-factorial commutator-growth witness). Phase 6q is the first project deliverable where the *bimodal* nature of the outcome is itself the headline result.

For external positioning:

  - **Before Phase 6q:** "the dissipative SK-EFT bootstrap is structurally blocked (Phase 6o)."
  - **After Phase 6q:** "the only known analytic dissipative bootstrap (CHHK) succeeds on lattice platforms and fails on continuum-bosonic platforms — explicitly characterized, kernel-verified."

Like recent phases, Phase 6q produces no new standalone papers. The substantive content lifts into bundle L2 (PRL letter, positive uniqueness) and bundle D5 (NO-GO landscape, sharpened NO-GO) simultaneously, with a flagship-F split-entry cross-bridge paragraph.

---

## Two Strategic Track Pillars

### Track 1 — Generic DKM Transport-Bootstrap Substrate (Waves 1a, 1b, 1c)

Seven modules under `lean/SKEFTHawking/DKMBootstrap/` building the alphabet-agnostic CHHK transport-bootstrap substrate. Six axiom families (`Predicates.lean`), CHHK ↔ Crossley-Glorioso-Liu axiom bridge with F2/F3 orthogonality theorems (`AxiomSet.lean`), the three Phase 6o obstruction resolutions (`KMSConsistency.lean`, `NoCrossing.lean`, `SDPStructure.lean`), convex-cone substrate (`LinearFunctionals.lean`), and the highest-leverage cross-bridge to Phase 6n's `IsLDPRateFunction` framework (`LDPBridge.lean`).

**Audience:** Schwinger-Keldysh effective-field-theory researchers (Crossley, Glorioso, Liu, Akyuz, Penco); dissipative-bootstrap researchers (Chowdhury, Hartnoll, Hebbar, Khondaker); transport-coefficient theorists (Hartnoll, Mahajan, Punk, Sachdev); formal-methods researchers in the Lean/Coq/Agda communities targeting condensed-matter physics formalization.

**Re-use story:** Future dissipative-bootstrap formalization work inherits the entire Track 1 substrate. Adding a new bootstrap framework (e.g., KMS-bootstrap-on-QM arXiv:2511.08560, or a generalized Akyuz-Penco transport variant) is now an *instantiation problem* rather than a re-derivation. The biconditional `chhk_F4_existence_iff_LDP_rate_function_holds` is the substrate-level statement; new bootstrap frameworks slot in by establishing the appropriate analogue.

### Track 2 — SK-EFT-Hawking Specialization + Bimodal Substantive Outcome (Waves 2a, 2b, 2c)

Four modules + the 2026-05-25 strengthening-session new module specializing the Track 1 substrate to the SK-EFT-Hawking horizon-transport substrate and shipping the bimodal-outcome theorem.

  - `SKEFTSpecialization.lean` — the SK-EFT-Hawking platform-classifier substrate, three-way `PlatformKMSQuality` classifier (lattice/bosonic/intermediate).
  - `E1E2CrossBridge.lean` — three-platform cross-bridge (graphene-Dirac-fluid for the positive half, BEC-Bogoliubov for the sharpened-NO-GO half, polariton as substrate-level abstraction).
  - `HorizonTransportBootstrap.lean` — the substantive bimodal-outcome theorem wave. Positive headline `horizon_transport_uniqueness_graphene_witness_one_half`; sharpened-NO-GO headline `sharpened_no_go_super_factorial`.
  - `BECBogoliubovBosonicGrowth.lean` (Session 2 ship, ~341 LoC) — substantive concrete-substrate lift of the sharpened-NO-GO half. `becBogoliubovCommutatorNorm κ := (2 \cdot \kappa)!` super-factorial-unbounded commutator-norm sequence violating CHHK F3 operator-growth bound; companion theorem `bec_distinguishes_from_graphene_super_factorial` anchoring the syntactic platform-classifier distinctness to the substantive operator-growth divergence.

**Audience:** analog-gravity researchers (Volovik, Jannes, Visser, Schützhold); condensed-matter physicists working on Dirac-fluid Wiedemann-Franz violation (Crossno, Lucas, Fong, Kim, Sachdev); BEC-substrate analog-Hawking experimentalists (Steinhauer, Westbrook, Boiron-Westbrook-Clade); flagship-F readership.

**Re-use story:** the platform-classifier substrate and the substantive super-factorial-growth obstruction characterization extend naturally to future analog-gravity platforms. A new platform (cold-atom Floquet, optical-lattice-Hawking) instantiates by establishing its operator-growth scaling and platform-classifier-quality designation; the bootstrap succeeds-or-fails decision follows from the substrate.

---

## Bridge Map — How Phase 6q Connects to the Rest

| Bridge | Phase | Status | Cross-bridge to Phase 6q |
|---|---|---|---|
| Phase 6o Wave 1c NO-GO writeup | 6o W1c | shipped | The Phase 6q trigger result. Phase 6q sharpens "dissipative bootstrap fails with current axioms" to "the only known analytic dissipative bootstrap (CHHK) succeeds on lattice, fails on continuum-bosonic without UV reg." |
| Phase 6n Wave 2a Glorioso-Liu monotonicity | 6n W2a | shipped | Substrate dependency — `KMSConsistency.lean` cross-bridges to it. Any DKM-axiom replacement must respect `OnsagerReciprocity_from_KMS` + `SKEFTAxiomsExt_yields_parity_alternation`. |
| Phase 6n Wave 2c Crooks-on-analog-Hawking + `IsLDPRateFunction` | 6n W2c | shipped | The highest-leverage cross-bridge of Phase 6q. `LDPBridge.lean` instantiates `IsLDPRateFunction` on the DKM substrate; biconditional `chhk_F4_existence_iff_LDP_rate_function_holds` connects the dissipative-bootstrap-via-DKM and the LDP-rate-function-via-Crooks substrates as the same substrate up to category-theoretic biconditional. |
| CHHK arXiv:2509.18255 | upstream | published | Primary source — Wave 1a.1 DR pivot identified CHHK as the analytic-only dissipative bootstrap that bypasses all three Phase 6o obstructions. |
| Akyuz-Penco arXiv:2508.18346 | upstream | published | SK-EFT charge-transport substrate — provides the state-of-the-art statement of dissipative axioms that the DKM bootstrap structurally replaces. |
| Crossley-Glorioso-Liu arXiv:1511.03646 | upstream | foundational | The original SK-EFT axiom set — Phase 6q's `AxiomSet.lean` establishes the CHHK ↔ CGL bridge. |
| Yin-Lucas PRX 12, 021039 + Kuwahara-Saito PRL 127, 070403 | upstream | published | Lieb-Robinson-for-bosons substrate underwriting the sharpened-NO-GO half. Phase 6q's `BECBogoliubovBosonicGrowth.lean` anchors the super-factorial-growth obstruction to this literature. |
| Crossno et al. Science 351, 1058 (2016) | upstream | experimental | Graphene Wiedemann-Franz violation measurement — provides the real-world check on the positive-half headline. Crossno data satisfies the CHHK bound by margin ~4,300×. |

---

## Audiences and Outward-Facing Positioning

### Audience 1: Schwinger-Keldysh EFT and Dissipative-Bootstrap Researchers

The substantive message: **the dissipative-bootstrap programme is partially viable**. Phase 6o said "dissipative SK-EFT bootstrap uniqueness inaccessible with current axioms." Phase 6q now says "the only known analytic dissipative bootstrap (CHHK 2509.18255) succeeds on lattice platforms (graphene-Dirac-fluid) and fails on continuum-bosonic platforms without UV regularization (BEC Bogoliubov)."

For SK-EFT researchers, this is the operational guidance: target the lattice regime; the continuum-bosonic regime requires either a new F3-substitute axiom or explicit UV regularization. The Yin-Lucas + Kuwahara-Saito Lieb-Robinson-for-bosons literature is the predictive substrate.

### Audience 2: Transport-Coefficient Theorists (Holographic + Boltzmann + Hydrodynamic)

The Mott-Ioffe-Regel master-bound headline on graphene: **the SK-EFT-Hawking substrate admits a kernel-verified MIR-style transport-coefficient uniqueness bound on the graphene Dirac fluid**, with substantive numerical witness $(2\beta_2/4\pi)^{1/3} = 0.07562892800257…$ to 30 decimal places. The Crossno 2016 graphene measurement provides the experimental anchor (the experimental ratio satisfies the bound by ~4,300× margin).

This positions the project's transport-bootstrap work as a *quantitative theoretical-experimental bridge* on lattice-substrate analog-Hawking platforms. Holographic-bootstrap researchers using transport coefficients as observables for AdS/CMT have a kernel-verified comparison target.

### Audience 3: Analog-Gravity Experimentalists

The two-platform message: **on the lattice (graphene), the CHHK bootstrap uniquely constrains the transport coefficient; on the continuum-bosonic platform (BEC Bogoliubov without UV reg), the bootstrap fails by an explicit mechanism (super-factorial commutator growth)**. For experimentalists choosing between platforms, this is operational guidance for which analog-Hawking substrates admit clean transport-coefficient bootstrap analysis.

Polariton-Hawking is positioned as a substrate-level abstraction (`E1E2CrossBridge.lean`) waiting for E1 platform-specific data — the bootstrap applicability depends on the polariton platform's operator-growth scaling, which has not yet been characterized at the literature-substrate level.

### Audience 4: Lean / Mathlib Working Groups

Phase 6q demonstrates that Mathlib4 v4.29.0 + Phase 6n LDP infrastructure is *sufficient* for substantive dissipative-bootstrap formalization. No new Mathlib substrate was required (Cauchy integral formula, convex cones via `ProperCone`, `Matrix.PosSemidef`, `Mathlib.Analysis.SpecialFunctions.SuperpolynomialDecay`, central-binomial estimates via `FloorSemiring.tendsto_pow_div_factorial_atTop` — all present).

One Mathlib-PR-quality substrate did surface: the substantive biconditional architecture for "abstract LDP-class-instantiated-on-bootstrap-substrate" cross-bridges. The biconditional pattern is reusable for other LDP class instances; future Phase 6s Track 2 (community citizenship) work could surface it upstream.

---

## Comparison: Phase 6o Wave 1c vs Phase 6q

| Dimension | Phase 6o Wave 1c | Phase 6q |
|---|---|---|
| Outcome direction | Structural NO-GO | Bimodal — positive uniqueness AND sharpened NO-GO |
| Bootstrap framework | SK-EFT bootstrap (general) | CHHK 2025 DKM transport bootstrap (specific) |
| Obstructions identified | 3 structural (KMS-positivity, no crossing, SDP-on-complex-contour) | All 3 bypassed by CHHK; new obstruction identified for BEC Bogoliubov (super-factorial operator growth violates F3) |
| Substrate produced | NO-GO writeup memo | 11 Lean modules, 2,716 LoC, substantive theorems both directions |
| Practical resonance | "Don't try this approach with this axiom set" | "Try this approach on lattice platforms; expect failure on continuum-bosonic without UV reg" |
| Methodology contribution | Identifying the three structural obstructions explicitly | Bimodal-outcome design (positive AND NO-GO halves both witnessed by concrete substrates) |
| Bundle placement | D5 NO-GO landscape section (joint with Phase 6q) | L2 PRL letter (positive) + D5 NO-GO landscape (NO-GO) + F flagship split-entry |
| Sessions | One-session memo close | Two sessions — Session 1 (5 waves shipped) + Session 2 (strengthening + 3 substantive deferred lifts) |

The Phase 6q multiplier is striking: a single planning session + two implementation sessions shipped 11 substantive Lean modules with both bimodal halves witnessed by concrete substrates. The substrate work leveraged Phase 6n's `IsLDPRateFunction` infrastructure and Mathlib4's mature analytic-substrate (Cauchy integral, convex cones, super-factorial estimates) without any new project-local axiom additions.

---

## What's Next

### Immediate (Phase 6s+)

Phase 6s is the bootstrap-Itô-LDP foundational substrate phase (sibling to Phase 6q in the 2026-05-12 four-phase planning conversation). It carries the I3 bundle-initial-sourceless-lift work + downstream LDP infrastructure cleanup. Phase 6q's `LDPBridge.lean` is one consumer of the abstract `IsLDPRateFunction` class; Phase 6s shepherds the class itself.

### Medium-term: SDPB Extension Wave (B.5 deferred)

A future Phase 7+ research-frontier wave would consume `IsDKMFeasibleSDPCandidate` (Phase 6q scaffold) + Mathlib4's `ProperCone.hyperplane_separation` substrate to lift the substantive SDP-feasibility content per CHHK §6. This is genuinely research-frontier (the SDPB tooling itself does not formalize — the Lean content would be the structural framework + bounds-have-the-claimed-properties theorems).

### Medium-term: D1 Lift-to-Lean (B.4 deferred)

The D1 bundle's SK-EFT Wilson coefficient action-correlator link is currently in LaTeX prose only. Lifting it to Lean would unlock substantive "under action-correlator link" stricter forms for the Phase 6q biconditional (currently substrate-level) and substantive Gaussian-regime content for the strengthening pass §A.7. Multi-session multi-bundle work; tracked but not scheduled.

### Long-term: Polariton-Hawking Platform Specialization

The `E1E2CrossBridge.lean` polariton substrate is currently a substrate-level abstraction. Once E1 platform-specific data (operator-growth scaling, KMS-quality classification) lands at literature-substrate maturity, the polariton-Hawking platform can be classified into lattice or bosonic and the bootstrap-applicability decision follows.

### Long-term: Bundle Absorption

Phase 6q's L2 + D5 + flagship-F split-entry positioning is held for the unified user-authorized event. The closing-positioning working doc (`temporary/working-docs/phase6q/wave_2c_positioning.md`) is ready for Phase 7 absorption.

---

## Status

Phase 6q substantively CLOSED with bimodal outcome shipped BOTH halves. Positive uniqueness on graphene Dirac fluid (`horizon_transport_uniqueness_graphene_witness_one_half` + substantive Python numerical witness $(2\beta_2/4\pi)^{1/3} = 0.0756…$ with Crossno 2016 confirmation by margin ~4,300×). Sharpened NO-GO on BEC Bogoliubov-bosonic platform (`sharpened_no_go_super_factorial` + concrete super-factorial commutator-norm witness `becBogoliubovCommutatorNorm κ := (2·κ)!` violating CHHK F3).

Project axiom count UNCHANGED at 0; sorry count UNCHANGED at 0. Strengthening pass + B.1/B.2/B.3 substantive lifts complete. Bundle placement BOTH L2 (PRL letter) AND D5 (NO-GO landscape) with flagship-F split-entry positioning. Ready for Phase 7 absorption.
