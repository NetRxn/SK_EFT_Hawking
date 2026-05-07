# Phase 6o: Implications of the Substrate-Findings Compression Phase

## Technical and Real-World Implications

**Status:** Phase 6o substantively COMPLETE — 7 of 7 waves shipped end-to-end at Lean-substrate scope; Wave 4a (Sakharov verdict-(B) honest one-way closure) shipped 2026-05-08.
**Date:** 2026-05-07
**Classification:** Research Overview — For Technical and Non-Technical Stakeholders
**Prerequisite:** Phase 6n math-substrate closure (Sessions 1–29); the bundle architecture; LATE_PHASE6_ABSORPTION_PROTOCOL.

---

## Executive Summary

Phase 6o picks up the heavier substrate-finding tracks identified in the Session-1 conspicuous-gaps catalog and the Session-2 deep-research returns. Three Tracks ship 7 waves: emergent IR sector (boostless / Carrollian soft theorems + Kerr-Schild double-copy + dissipative-bootstrap NO-GO writeup), topological invariants on analog backgrounds (APS-η + Schellekens chain reframing), productive-value Aristotle wave (ETH-α refutation tableau) + I3 Itô + LDP community contribution, plus a Track 4 substrate-anchor refactor (Sakharov verdict-(B)).

The substantive findings are:

1. **Wave 1a — Boostless / Carrollian soft theorems on BEC + ADW + polariton.** Five SoftTheorems modules: `Boostless.lean` (IsBoostlessLeadingSoftFactor predicate); `Carrollian.lean` (Carrollian framework + Strominger-triangle closure on all three substrates); `EmergentGraviton.lean` (ADW graviton subleading factor); `DissipativeNoGo.lean` (Lindbladian S-matrix axiomatization NO-GO joining the program's NO-GO landscape); `NoiseFloorPrediction.lean` (universal $n_{\rm noise}$ / Hawking-flux Wilson-coefficient-independence — most concrete near-term Phase 7 deliverable per On-Shell Methods DR §7.2).

2. **Wave 1b — G4 Kerr-Schild double-copy on Petrov-D acoustic metric.** Five KerrSchild modules: `PetrovD.lean` (Petrov-D verification on draining-bathtub acoustic metric); `SingleCopy.lean` (Maxwell field on flat Minkowski via $A_\mu = \phi k_\mu$); `WeylSpinor.lean` (type-D vacuum reformulation $\Psi_{ABCD} = \Phi_{(AB} \Phi_{CD)} / S$); `BCJNoGo.lean` (3-obstruction strong-form BCJ NO-GO: Lorentz-frame breaking + gauge-erasure abelianization + UV-vs-IR scale-ordering mismatch); `PolaritonCrossBridge.lean` (E1 polariton ringdown signature). **First explicit classical double-copy on analog gravity in the literature.**

3. **Wave 1c — G1 NO-GO writeup** (~30 pages, no Lean novelty). Three structural obstructions to dissipative SK-EFT bootstrap-uniqueness with current axioms: unitarity → KMS replacement breaks EFT-positivity; crossing has no doubled-contour analog; SDP feasibility breaks on complex contour. NO-GO scope bounded to "current axioms" leaving room for future revision.

4. **Wave 2a — APS-η for analog horizons.** Six APSEta modules: `Predicate.lean` + `BECAcoustic.lean` + `ADWHorizon.lean` (parity-symmetric → η = 0) + `He3A.lean` (substantively non-zero η; Jackiw-Rebbi chiral edge mode at moving domain wall; ³He-A unique non-degenerate cell) + `SymTFTBridge.lean` (Witten-Yonekura η/16 mod 1 ↔ Z₁₆ + WittClass cross-bridges) + `RegimePartition.lean` (two-cell partition theorem). **First systematic substrate-side APS-η identification on a chirally-asymmetric analog Hawking horizon in the literature**, operationalized at substrate-data level.

5. **Wave 2b — G1 Schellekens chain reframing.** Six Schellekens modules: `SpinBordism.lean` extends existing `SpinBordism` + `Z16AnomalyComputation`; `AnomalyPolynomial.lean`; `ModularInvariance.lean` (modular invariance of edge CFT via Mathlib SL(2,ℤ)); `NiemeierLattice.lean` (predicate-level 24-dim Niemeier classification); `HolomorphicVOAc24.lean` (Möller-Scheithauer 2024 c=24 holomorphic-VOA classification predicate); `Chain.lean` (composed 5-step chain → $24 | c_-$ ⇔ $N_{\rm gen} \equiv 0 \pmod 3$ substantive theorem). **D.3 user-auth gate at D2 (substantive §2 reframing) + L2 (paired splash update)** closed in Phase 7 absorption Session 1. Per Modular Bootstrap DR §8 Tier 1(a) "the highest-leverage move."

6. **Wave 3a — G10 ETH-α productive-value refutation tableau.** Three ETH modules: `Predicates.lean` (5 candidate ETHAnsatz typeclass instances A1-A5 at finite-dimensional level: Srednicki + free-cumulant Pappalardi-Foini-Kurchan + Helbig-Hofmann-Thomale-Greiter Theory-of-ETH + Wang Eigenstate-Typicality-Principle + Inozemcev-Volovich-corrected); `ConcreteWitness.lean` (4-site Ising chain witness substrate); `RefutationTableau.lean` (3 concrete refutation theorems: T1 Inozemcev-Volovich gap via β-equation contradiction; T2 ETP doesn't imply Srednicki via n=16 zero-mean failure; T3 free-cumulant doesn't imply Srednicki via n=1 sum=1 violation). MCP-CLOSED — Aristotle batch deferred (zero residue after MCP).

7. **Wave 3b — I3 Itô + LDP-α + LDP-β substrate.** 12 modules: `Itô/StochasticIntegral` + `QuadraticVariation` + `Semimartingale` + `ItoIsometry` + `ItoLemma` + `Novikov`; `LDP/CramerIID` + `Sanov` + `Contraction` + `CramerLowerBound` + `Varadhan` + `LDPCompatibleSKEFT` typeclass connecting Wave 3b LDP infrastructure to Phase 6n Wave 2c.5c+ IsLDPRateFunction + Phase 6n Wave 2a Glorioso-Liu monotonicity. **I3 bundle initial sourceless lift via D.4 protocol** — analogous to I2's lean-tensor-categories sourceless pattern.

8. **Wave 4a — FLS BEC depletion-factor / Sakharov 4-criterion verdict (B).** Strict-extension `SakharovExtended` structure with load-bearing `depletion : ℝ` field + 5 substantive theorems JTGR16-JTGR20. Per Volovik-Jannes 2012 §VII forward-only argument and FLS BEC primary-source verification (arXiv:1103.4841 + 1204.3039 Eq. 71): the originally-claimed biconditional `_iff_` was honestly retired in favor of one-way (⇒) implication. Numerics refit `lambdaJ:=6.0e-14 / lambdaHK:=7.5e-12 / depletion:=8.0e-3` (consistency `8e-3 × 7.5e-12 = 6e-14` via `norm_num`). 3 new bibitems: FinazziLiberatiSindoni 2012 PRL/Proc + BelenchiaLiberatiMohd 2014. **Track 4 user-authorized at Phase 7 absorption Session 5 user-call C.**

The Phase 6o substrate-findings are COMPLETE. No new papers; all absorbed into existing bundles via the LATE_PHASE6_ABSORPTION_PROTOCOL D.2 / D.3 / D.4 branches during Phase 7 absorption Sessions 1–5.

---

## What Phase 6o Adds Beyond Phase 6n

Phase 6n compressed existing program content into deeper structural objects (resurgence, SymTFT, axiomatic skeletons). Phase 6o is the *first-mover substrate-discovery phase*: it produces results that didn't exist in the program before. The first explicit classical Kerr-Schild double-copy on an analog gravity background; the first systematic substrate-side APS-η identification on a chirally-asymmetric analog horizon; the Schellekens-chain reframing that elevates $24 | c_-$ from algebraic constraint to theorem-quality classification corollary of Möller-Scheithauer 2024 — none of these existed in the program before Phase 6o. Phase 6n was deepening; Phase 6o is *first-mover* substrate discovery.

---

## Result 1: Wave 1a — Soft-Theorem Program (Boostless / Carrollian / Emergent Graviton)

### What we found

The program's three analog-gravity substrates (BEC + ADW + polariton) all admit boostless / Carrollian soft-theorem structure. The Strominger-triangle closes on all three. The ADW graviton has a subleading soft factor. A *negative* substantive theorem: Lindbladian S-matrix axiomatization NO-GO joins the program's NO-GO landscape. Most concrete near-term experimentally-relevant prediction: universal $n_{\rm noise}$ / Hawking-flux Wilson-coefficient-independence. This is the most concrete falsifiable prediction Phase 6o produces; it lifts as cross-bridge content into E1 (Paris-LKB polariton experimental letter).

### Why it matters

The boostless / Carrollian soft-theorem program (Strominger triangle, on-shell methods, spinor-helicity) is one of the most active areas in modern amplitudes. Phase 6o ships the first machine-checked closure of the Strominger triangle on emergent (analog-gravity) substrates. The Wilson-coefficient-independence claim for $n_{\rm noise}$ is a falsifiable cross-bridge that the experimental teams can directly target.

---

## Result 2: Wave 1b — G4 Kerr-Schild Double-Copy

### What we found

The Petrov-D acoustic metric (draining-bathtub) admits a Kerr-Schild form. The Maxwell single-copy lives on flat Minkowski via $A_\mu = \phi k_\mu$. The Weyl spinor structure $\Psi_{ABCD} = \Phi_{(AB} \Phi_{CD)} / S$ is the type-D vacuum reformulation. The BCJ NO-GO is a 3-obstruction strong-form: Lorentz-frame breaking + gauge-erasure abelianization + UV-vs-IR scale-ordering mismatch.

**First explicit classical double-copy on analog gravity in the literature.**

### Why it matters

The classical double-copy program (Bern, Carrasco, Johansson, et al.) is one of the deepest structural results of modern gravity theory. Extending it to analog-gravity substrates is non-trivial because the substrates are dissipative (dispersive + Lorentz-violating). Wave 1b ships *both* the positive Kerr-Schild + single-copy + Weyl spinor content *and* the negative 3-obstruction BCJ NO-GO theorem. The pair is the structural payload: positive substrate + negative obstruction.

---

## Result 3: Wave 2a — APS-η for Analog Horizons

### What we found

The program's three analog-horizon substrates partition into a parity-symmetric cell (BEC + ADW: APS = bulk Atiyah-Singer; η = 0) and a chirally-asymmetric cell (³He-A: substantive APS boundary correction via Volovik chirality framework + Jackiw-Rebbi chiral edge mode at moving domain wall).

**First systematic substrate-side APS-η identification on a chirally-asymmetric analog Hawking horizon in the literature**, operationalized at substrate-data level.

### Why it matters

The APS-η invariant is the η-invariant boundary-correction in the Atiyah-Patodi-Singer index theorem. It's the right structural object for distinguishing parity-symmetric from chirally-asymmetric substrates. The Witten-Yonekura η/16 mod 1 cross-bridge to Z₁₆ via the SymTFTBridge module ties this to the Phase 5b/5c Z₁₆ anomaly classification chain. The two-cell regime partition is the substantive payload.

---

## Result 4: Wave 2b — G1 Schellekens Chain (D.3 GATE 3)

### What we found

The composed 5-step chain `SpinBordism → AnomalyPolynomial → ModularInvariance → NiemeierLattice → HolomorphicVOAc24` reframes $24 | c_-$ → $N_{\rm gen} \equiv 0 \pmod 3$ from algebraic constraint to *theorem-quality classification corollary* of Möller-Scheithauer 2024 c=24 holomorphic-VOA classification.

**D.3 user-auth gate at D2 (substantive §2 reframing) + L2 (paired splash update)** closed in Phase 7 absorption Session 1.

Per Modular Bootstrap DR §8 Tier 1(a): "the highest-leverage move."

### Why it matters

This is the single most substantive reframing of the project's "three generations of matter" central argument. The original $24 | c_-$ → $N_f = 3$ argument was algebraic (Dedekind eta function + chiral central charge). Wave 2b lifts this to a corollary of Möller-Scheithauer 2024's classification of c=24 holomorphic VOAs. The L2 PRL splash now points to this elevation: the central "Three Generations" claim is preserved, but the formal substrate is deeper. The reframing is Tier-1(a) "highest-leverage" because it ties the project's anomaly content to mainstream conformal-bootstrap / holomorphic-VOA classification literature.

---

## Result 5: Wave 3a — ETH-α Productive-Value Refutation Tableau

### What we found

5 candidate ETHAnsatz typeclass instances A1-A5 at finite-dimensional level (Srednicki + free-cumulant Pappalardi-Foini-Kurchan + Helbig-Hofmann-Thomale-Greiter Theory-of-ETH + Wang Eigenstate-Typicality-Principle + Inozemcev-Volovich-corrected). 4-site Ising chain witness substrate. 3 concrete refutation theorems: T1 Inozemcev-Volovich gap; T2 ETP doesn't imply Srednicki; T3 free-cumulant doesn't imply Srednicki.

MCP-CLOSED at Lean substrate; Aristotle batch deferred.

### Why it matters

The Eigenstate Thermalization Hypothesis (ETH) has at least five non-equivalent axiomatizations in the published literature. The refutation tableau formalizes the structural distinctions between them — what's an *implication* and what's a *strict-stronger* relation. This is the kind of productive-value Aristotle-driven case study that the I1 methodology paper consumes as a sidebar.

---

## Result 6: Wave 3b — I3 Itô + LDP Substrate (Bundle Initial Lift)

### What we found

12 modules: 6 Itô (StochasticIntegral, QuadraticVariation, Semimartingale, ItoIsometry, ItoLemma, Novikov) + 6 LDP (CramerIID, Sanov, Contraction, CramerLowerBound, Varadhan, LDPCompatibleSKEFT typeclass).

The `LDPCompatibleSKEFT` typeclass connects Wave 3b LDP infrastructure to Phase 6n Wave 2c.5c+ `IsLDPRateFunction` + Phase 6n Wave 2a Glorioso-Liu monotonicity. Concrete instance on linearResponseRateFunctionCentered Gaussian rate function.

**I3 bundle initial sourceless lift via D.4 protocol** — analogous to I2's lean-tensor-categories sourceless pattern. Pipeline Invariant #14 user-auth granted Phase 6n Session 4 (commit `a72ba68`).

### Why it matters

I3 ("Verified Stochastic Calculus for Mathlib4") is the program's third Tier-3 infrastructure-paper bundle. It targets the Mathlib probability working group (Degenne / Marion / Ledvinka / Pfaffelhuber) plus the formal-verification community. Phase 6o Wave 3b provides the bundle's initial sourceless lift — 12 modules covering stochastic integral / quadratic variation / Itô's lemma / Novikov / LDP foundations. The downstream cross-bridges to D3 / D5 / E1 are wired through the `LDPCompatibleSKEFT` typeclass.

---

## Result 7: Wave 4a — Sakharov Verdict (B) Honest One-Way Closure

### What we found

The originally-claimed biconditional `sakharov_induced_gravity_criterion_iff_lambda_j_eq_lambda_hk` was honestly retired in favor of a one-way (⇒) implication. The strict-extension `SakharovExtended` structure adds a load-bearing `depletion : ℝ` field. 5 substantive theorems JTGR16-JTGR20: depletion-factor unconditional + ³He-A unit + FLS strict bounds + asymmetry + composed honest-one-way closure.

Numerics refit per FLS BEC primary-source verification: `lambdaJ:=6.0e-14 / lambdaHK:=7.5e-12 / depletion:=8.0e-3` (consistency `8e-3 × 7.5e-12 = 6e-14` via `norm_num`).

Track 4 user-authorized at Phase 7 absorption Session 5 user-call C.

### Why it matters

This is a honest verdict-(B) downgrade pattern. The Volovik-Jannes 2012 §VII argument is forward-only; the FLS BEC primary-source check (arXiv:1103.4841 + 1204.3039 Eq. 71) confirms forward but doesn't test the converse. Rather than over-claiming a biconditional, the Lean module retires the biconditional and ships the substantive content that the literature actually supports — a one-way implication plus a load-bearing depletion factor. The 4-Boolean Sakharov layer (`SakharovConditions` + JTGR6-9) is preserved; the substantive new content is the depletion-factor asymmetry on ³He-A vs FLS BEC.

This is the kind of structural-tightening lesson the project's primary-source WebFetch + verify policy is designed to catch. Standing project policy as of Phase 7 absorption Session 5.

---

## By the Numbers (Phase 6o, post-CLOSED)

- **Lean theorems shipped:** very many — Phase 6o adds approximately 30+ new modules and ~200+ substantive theorems across the 7 waves.
- **First-formalization claims:** at least 3 distinct items (first explicit classical double-copy on analog gravity; first systematic APS-η on chirally-asymmetric analog horizon; Schellekens-chain reframing as Möller-Scheithauer 2024 corollary).
- **Bundle architecture changes:** I3 bundle (Tier-3 infrastructure paper) initial sourceless lift via D.4 protocol; Pipeline Invariant #14 user-auth granted Phase 6n Session 4.
- **D.3 user-auth gates:** GATE 3 (D2 §2 + L2 paired splash) closed in Phase 7 absorption Session 1.
- **Track 4 verdict-(B) honest closure:** Sakharov biconditional retired; load-bearing depletion factor added.

---

## Strategic Reading

Phase 6o is the *first-mover substrate-discovery phase*. Where Phase 6n compressed existing content, Phase 6o produces results that didn't exist before. The Kerr-Schild double-copy on analog gravity, APS-η on chirally-asymmetric analog horizons, and the Schellekens-chain reframing are all substrate-discovery firsts that lift directly into the bundle architecture as additive content + cross-bridge upgrades + (D.3) substantive section reframings.

The Phase 6o waves were dispatched in parallel where possible. Pre-flight Explore-agent dispatches (3-min substrate scouts) saved multi-session redirects. The MCP-loop default + Aristotle-as-fallback discipline shipped seven waves cleanly.

The verdict-(B) honest closure on Wave 4a is itself a methodology lesson: when the literature argues only one direction, the formal statement should reflect that. The project's standing primary-source WebFetch + verify policy is designed to catch this kind of over-claim before publication-grade prose relies on it.

The Phase 6o substrate-findings — combined with Phase 6n math substrate (`Phase6n_Implications.md`) and Phase 7 absorption (`Phase7_Implications.md`) — form the structural-deepening trio that the program executed between Phase 6m closure and the publication phase. The bundles that go to publication carry deeper formal content + first-mover substrate findings + honest-correction structural tightening, all absorbed via the LATE_PHASE6_ABSORPTION_PROTOCOL.
