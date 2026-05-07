# Architecture Scope — Three-Layer Predictive Boundary

**Last updated:** 2026-04-30 (Phase 6m closure — Lean formalization scope)

This document defines the **predictive scope** of the SK-EFT Hawking
research program's three-layer architecture — what the architecture
commits to predicting, and what is explicitly outside its tested scope.

---

## The three layers

The SK-EFT Hawking program is organized around a three-layer emergent-physics
architecture:

| Layer | Target physics                              | Canonical modules              |
|-------|---------------------------------------------|--------------------------------|
| 1     | Discrete lattice Hamiltonian + fermions     | `LatticeHamiltonian`, `FermionBag4D` |
| 2     | Coarse-grained effective field theory (SK)  | `AcousticMetric`, `SKDoubling`, `SecondOrderSK` |
| 3     | Emergent gauge fields + gravity (ADW+etc.)  | `ADWMechanism`, `GaugeErasure`, `ChiralityWall`, `VestigialGravity` |

---

## Predictive scope by layer

### Layer 3: SM + GR sector (IN SCOPE)

The architecture commits to **Standard Model + General Relativity
emergent physics** under the tested mechanisms:
- **ADW tetrad condensation** producing emergent gravity (Phase 3
  Wave 3)
- **Gauge erasure** producing `U(1)` from non-Abelian lattice
  (Phase 3 Wave 2)
- **Fracton hydrodynamics** producing subdiffusive emergent currents
  (Phase 4 Wave 2-3)
- **Vestigial gravity** as a distinct intermediate ordering
  (Phases 4, 5w, 5y; H4 structural content)

Layer-3 predictions in this sector are falsifiable, formalized
(currently ~3728 Lean theorems, zero sorry, 1 axiom), and actively
tested against laboratory platforms (BEC, polariton, graphene Dirac
fluid) in phases 5u/5w/5d.

### Dark-sector physics (OUT OF SCOPE under tested mechanisms)

**Phase 5y closure verdict (2026-04-23):** After six deep-research
rounds of Volovik-family dark-energy mechanisms (q-theory in four
realizations + vestigial gravity EOS + second-sound graviton), all
returned **NO-GO** for DESI DR2 compatibility. The structural obstruction
is formalized in:
- `GibbsDuhemTheorem.lean` — any single-scalar self-tuning emergent-vacuum
  framework with Gibbs-Duhem equilibrium locks `w_vac = −1`
- `QTheoryNoGoTheorem.lean` — the obstruction is realization-independent
  across the four tested KV q-theory constructions
- `DarkEnergyObstructionPrinciple.lean` — four-factor orthogonality
  (Gibbs-Duhem ∩ `c_s² ≥ 0` ∩ natural `T_c` ∩ MICROSCOPE) diagnoses
  why vestigial gravity also fails

**Predictive-scope recalibration:** Layer 3 is scoped to produce
SM+GR-sector emergent physics cleanly. The dark-energy sector is
**outside the architecture's tested predictive scope** under the
Volovik-family mechanisms explored in Phase 5y. This is a sharpening
of scope, not a retreat: the architecture remains intact for SM+GR
physics; it is explicit about not predicting cosmological-constant-type
physics under mechanisms currently tested.

### What this does NOT claim

Phase 5y's closure **does not** claim:
- q-theory is falsified as a vacuum-stability framework (only as a
  late-time dark-energy framework; q-theory as equilibrium or
  inflation-era framework remains untested / intact)
- Vestigial gravity is ruled out as a concept (the H4 framework
  PARTIAL verdict remains — the ordering and Z₄ structure are
  mathematically consistent and may find applications elsewhere)
- No emergent dark energy is possible (obstruction covers
  Volovik-family mechanisms specifically; entropic gravity,
  causal-set approaches, Jacobson-type thermodynamic GR were outside
  the Phase 5y tested scope and are now closed by Phase 6m — see
  Phase 6m closure block below)
- The three-layer architecture is falsified (only the dark-sector
  predictive claim is scoped out; Layer-3 SM+GR-sector claims are
  unaffected)

---

## Phase 6m closure (2026-04-30) — Three-track Phase 5y reframe

After three independent six-round deep-research probes of the
mechanism families flagged out-of-scope by Phase 5y (Tracks A, B, C
in `docs/roadmaps/Phase6m_Roadmap.md`), Phase 6m closes at the
Lean-formalization scope. Project totals: ~4944 substantive theorems
across 243 modules / 1 axiom / 0 sorry (verified `lake build` 8507
jobs PASS, 2026-04-30).

**Track-level verdicts (R5 + R6 Lean closure):**

- **Track A — Causal-set DE** (`CausalSetDarkEnergy.lean`, 15 thms):
  3 NO-GO-R5 phenomenological (Sorkin Models 1+2; BDG MYZ 2025) +
  causal-set d'Alembertian NO-GO-R2 reaffirmed via 4D gradient
  instability. **3 publishable structural caveats survive
  independent of DESI**: (i) GD-inapplicability robust under all 4
  sprinkling prescriptions; (ii) Barrow-bound prescription
  dependence (CQG/JCAP Letter short-note candidate); (iii)
  BDG σ_Λ = α_BDG/√V first-principles decomposition (CSDE7-8).

- **Track B — Entropic-gravity DE**
  (`EntropicGravityDarkEnergy.lean`, 14 thms): **8 NO-GO-R5
  unanimous — first complete-mechanism-family NO-GO closure in
  Phase 6m**. Verlinde 2017 / Padmanabhan-CosMIn /
  Hossenfelder-Verlinde post-Yoon-Guha / Cadoni-Tuveri DEC / Li
  2004 HDE / Tsallis HDE / Barrow HDE / Odintsov-D'Onofrio-Paul Ω_k
  all closed with quantitative |log 𝓑| / σ thresholds exceeding
  Jeffreys-decisive (5). 7-of-8 candidates have r_d-independent
  NO-GO mechanism. **Paper-45 publication-novelty claim.**

- **Track C — Jacobson-thermo-GR DE**
  (`JacobsonThermoGRDarkEnergy.lean`, 12 thms): **highest-survival
  track with 5+ R5 survivors**. M1 Jacobson 1995 + M2/M7
  Padmanabhan/CosMIn (epistemic flag) + M9 Volovik-Jannes
  PARTIAL-VIABLE under fixed-r_d Planck DR3 prior; M3 EGJ f(R)
  Exp + ArcTanh **strongest CLEARED-R5 of any track in Phase 6m**
  (Plaza-Kraiselburd 2504.05432: ΔAIC ≃ ΔBIC ≳ 20, Jeffreys "very
  strong"); M3 Starobinsky marginal CLEARED-R5; M3 Hu-Sawicki
  NO-GO-R5 via chameleon Solar-System constraint at b ≈ 0.21
  (best-fit b > 100× chameleon bound, encoded as norm_num
  inequality JTGR3); M4 Pure Lovelock NO-GO-R5 reaffirmed at
  1σ-box edge of Quintom-B (|w₀+1| < 0.05, |α̃₂|_max ≤ 0.15,
  encoded JTGR4); M8 KSS CLEARED-R5 conditional via R4 path-(a)
  Arata-Liberati-Neri 2603.28851, OPEN-R6+ via path-(c).
  Fixed-vs-floating r_d split = single empirical decider by ~2030.

**Phase 6e cross-bridge final closure** (Wave 3f JTGR6-JTGR8):
Sakharov four-condition criterion biconditional with Λ_J = Λ_HK
validated on Volovik-Jannes ³He-A; falsified on
Finazzi-Liberati-Sindoni acoustic-BEC (condition (ii) fails — only
phonons have BEC effective metric). **First systematic Λ_J vs Λ_HK
comparison on common substrate in literature** (CQG/PRD short-note
candidate).

**Wave 4 unified Phase 6m 7-class GD taxonomy**
(`DarkSectorClassificationExtension.lean`, 10 thms): consolidates
TA "combinatorial-vs-thermodynamic-scalar" + TB "a/b/c/d" + TC
"b/b'/b''/OPEN" into single classification namespace (Class 0 +
(a) + (b) + (b′) + (b″) + (c) + (d)) with 3-tier GD applicability
gradient (Tier I outside-domain / Tier II inapplicable / Tier III
applies / Tier S re-derive). M8 KSS uniquely populates Class (a).
Unimodular reformulation as Λ_HK escape route admits 5/6 Track-C
survivors except KSS (DSCE8).

**Predictive-scope recalibration after Phase 6m.** Layer 3 dark-
energy scope statement, sharpened from the Phase 5y formulation:
- **NO-GO (machine-checked):** Volovik-family mechanisms (Phase 5y);
  Track A causal-set DE phenomenological; Track B entropic-gravity
  DE complete-class; Track C M3 Hu-Sawicki + M4 Pure Lovelock;
  Track A causal-set d'Alembertian (R2 reaffirmed).
- **PARTIAL-VIABLE (R5 cleared, requires monitoring):** Track C
  M1 Jacobson 1995, M2/M7 Padmanabhan/CosMIn (epistemic flag),
  M9 Volovik-Jannes (under fixed-r_d).
- **CLEARED-R5 strongest (preferred over ΛCDM by ΔAIC ≳ 20):**
  Track C M3 EGJ f(R) Exponential + ArcTanh (Plaza-Kraiselburd
  2504.05432); Starobinsky marginal.
- **CONDITIONAL CLEARED-R5 / OPEN-R6+:** Track C M8 KSS via path-(a)
  PARTIAL closure; OPEN via path-(c) universal-horizon thermo.
- **3 publishable structural caveats** (Track A; independent of DESI):
  GD-inapplicability across prescriptions; Barrow-bound prescription
  dependence; BDG σ_Λ first-principles decomposition.

---

## Phase 6n / 6o math-substrate sub-phases (2026-05-04 → 2026-05-08)

Substrate-side findings; **no scope change**. The architectural-scope
boundary established by Phase 5y + Phase 6m is preserved. Phase 6n + 6o
sharpen the substrate operationalization at several integration points:

- **SymTFT PartiallyApplicable verdict** (Phase 6n.β): SymTFT
  audit substrate (`SymTFTAudit/WittClass.lean` + DrinfeldCenter +
  FreeKLinearCategory + DeligneTensor + PseudoUnitary + CrossBridges;
  ~100 substantive theorems) clears DMNO 2010 Witt-equivalence,
  Schellekens 24|c₋ chain, and pseudo-unitary substrate at the
  restricted-form layer. Verdict: SymTFT applicable to Layer-3 anomaly
  classification (D2 + D4 absorption); not load-bearing for dark sector.
- **Sakharov ↔ horizon-Crooks unification at β_H** (Phase 6n.ζ):
  ³He-A satisfies all 4 Sakharov conditions / FLS BEC violates
  condition (ii). Two classifications (Sakharov 4-criterion + horizon
  Crooks fluctuation theorem) shown to be independent program axes
  with Verlinde-vs-Jacobson distinction enforced at every claim site.
- **APS-η regime partition for analog horizons** (Phase 6o.δ):
  parity-symmetric branch → η = 0 (BEC + ADW); ³He-A carries
  substantively non-zero η via Jackiw-Rebbi chiral edge mode at moving
  domain wall (³He-A unique non-degenerate cell). First systematic
  substrate-side APS-η identification on chirally-asymmetric analog
  Hawking horizon in literature.
- **Schellekens chain 24|c₋ as Möller-Scheithauer 2024 corollary**
  (Phase 6o.ε): the 5-step Schellekens chain (Spin bordism + anomaly
  polynomial + modular invariance + Niemeier + holomorphic VOA c=24)
  is now formalized as a substantive theorem reframing 24|c₋ as a
  classification corollary of the Möller-Scheithauer 2024 c=24
  holomorphic-VOA classification.
- **G4 Kerr-Schild classical double-copy on Petrov-D analog gravity**
  (Phase 6o.β): Petrov-D verification on draining-bathtub acoustic
  metric + Maxwell single-copy on flat Minkowski + 3-obstruction
  strong-form BCJ NO-GO theorem. **First explicit classical double-copy
  on analog gravity in the literature.**

**Phase 6o Wave 4a Track 4 (2026-05-08) — verdict-(B) honest closure
of the Sakharov 4-criterion ↔ Λ_J = Λ_HK biconditional.** Per Volovik-
Jannes 2012 §VII forward-only argument and FLS BEC primary-source
verification (arXiv:1103.4841 + arXiv:1204.3039 Eq. 71), the
biconditional reading is honestly retired in favour of one-way (⇒)
implication + load-bearing `depletion : ℝ` field on `SakharovExtended`.
The `SakharovExtended` strict-extension structure wraps the unchanged
`SakharovConditions` 4-Boolean structure, preserving all downstream
callers. JTGR16-JTGR20 substantive theorems (depletion-factor
unconditional + ³He-A unit + FLS strict bounds + asymmetry + composed
honest-one-way closure) ship at refit numerics
`lambdaJ:=6.0e-14 / lambdaHK:=7.5e-12 / depletion:=8.0e-3`
(consistency `8e-3 × 7.5e-12 = 6e-14` via norm_num). The honest
downgrade from biconditional to one-way implication preserves the
substrate-physics content while correctly attributing to the
forward-only source argument. Architecture remains scoped: Layer 3
SM+GR-emergent IN; dark-sector OUT under all tested mechanism families.

---

## Cross-phase non-inheritance

Phase 5y's NO-GO verdicts do **not** propagate to the following
parallel/subsequent phases:

| Phase | Inheritance     | Status             |
|-------|-----------------|--------------------|
| 5u (polariton Hawking)   | No inheritance | Tier A, continues independently |
| 5d (RHMC ADW fermion)    | No inheritance | Orthogonal physics, continues |
| 5w (graphene Dirac fluid)| No inheritance | Orthogonal physics, continues |
| 5x (dark matter)         | No inheritance | Different mechanisms, continues |

Cross-phase impact memos are in `docs/stakeholder/Phase5y_Impact_on_*.md`
(Wave 9 deliverables).

---

## Architectural implications

1. **Program value preserved.** The Lean backbone of the program
   continues to build cleanly. 3728+ theorems (Phase 5t baseline) plus
   ~109 new theorems from Phase 5y closure across 7 new modules + 3
   extensions.

2. **Scope explicit.** The predictive-scope boundary is now
   formally stated in Lean (`ClassificationTableDark.lean`) and
   documented here. Future Phase 5/6 architectural conversations can
   reference this scope explicitly without ambiguity.

3. **GO/NO-GO methodology validated.** Phase 5y demonstrated that
   the program can execute a six-round deep-research probe, land a
   structural NO-GO, and harvest the result as formal content without
   reopening or re-scoping the underlying decision. This is a reusable
   methodology for future high-leverage bets.

4. **No publication overhead.** Phase 5y deliberately produces no
   papers (user-stated preference). The harvest is entirely Lean +
   architectural documentation + cross-phase memos. This keeps the
   program oriented around formal-verification output during the
   current period.

---

## References

- **Roadmap:** `docs/roadmaps/Phase5y_Roadmap.md` (terminal revision
  2026-04-24)
- **Classification:** `temporary/working-docs/phase5y_classification_table_dark.md`
  + `lean/SKEFTHawking/ClassificationTableDark.lean`
- **Deep research:** `Lit-Search/Phase-5y/` (6 rounds, all complete)
- **Wave execution:** `docs/WAVE_EXECUTION_PIPELINE.md`

---

*Phase 5y terminal closure artifact. Supersedes no prior architecture
document — this is the first explicit `ARCHITECTURE_SCOPE.md` for the
program.*
