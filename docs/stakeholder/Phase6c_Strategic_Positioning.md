# Strategic Positioning: Phase 6c within the Broader Program

## How Cross-Domain Bridges Reshape the Falsification Surface

**Date:** 2026-04-28
**Context:** This memo positions Phase 6c (Waves 1, 3, 4, 5) within the broader research program. Phase 6a built the project's emergent-gravity machinery; Phase 6c now exports that machinery to four foundational-physics open questions. Each export is a falsifiable bridge.

---

## Phase 6c's Strategic Value

Phase 6a delivered the project's internal machinery: emergent-gravity dynamics, GW170817 falsification of vestigial-second-sound graviton ID, BH-entropy microstate counting, and the horizon modular-tensor-category substrate. The framework was complete in the sense that internal predictions matched internal computations — but the *external* falsification surface was modest.

Phase 6c shifts the strategy: each wave constructs a *bridge* to a famous open problem (strong-CP, equivalence principle, Hayden-Preskill, Ryu-Takayanagi), encoded as a Lean module + Python mirror + paper, with *another community's* observable as the falsification target. Net effect: the project's empirical perimeter widens substantially, and each export comes with a concrete community partner.

---

## Four Strategic Bridges

### 1. Strong-CP / Cosmological-Constant Bridge (Wave 1)

**What:** Zhitnitsky's no-free-parameters $\rho_{DE} \sim \Lambda_{QCD}^6 / M_P^2$ formula evaluated at PDG values gives $6.7 \times 10^{-9}$ eV⁴, $\sim 240\times$ the observed value. The project's correctness-push theorem `combined_zhitnitsky_qtheory_exceeds_observation` proves a structural one-mechanism inconsistency.

**Why it matters strategically:** This is the broadest bridge — it ties two of physics's most stubborn fine-tuning puzzles to a single underlying mechanism (the QCD topological vacuum, already constrained by Pendlebury 2015 EDM data). The honest scope: the $\sim 240\times$ ratio is within Zhitnitsky's claimed precision but is not a tight match; cosmology can adjudicate via $w(z)$ measurements.

**Audience:** Cosmologists (DESI, Euclid, Roman teams), strong-CP / axion community, dark-energy modelers. The $w(z)$ adjudication is a near-term observational deliverable.

**Community partner:** the Volovik / Klinkhamer school (q-theory side); the Zhitnitsky group (proposal authors); Planck + DESI + Euclid analysis teams.

### 2. Equivalence-Principle Discriminator (Wave 3)

**What:** Out of six Phase-5x dark-matter mechanisms, exactly two violate the weak EP — both vestigial-phase. The other four satisfy all three EP levels. STEP-class precision tests at $\eta \sim 10^{-18}$ become *direct discriminators* of dark-sector classification within the project's substrate.

**Why it matters strategically:** EP precision experiments have moved toward $\eta \sim 10^{-18}$ for over a decade without a specific theoretical target in this framework. We now have one. A future detection / null result in the MICROSCOPE-to-STEP window has a clean yes-or-no interpretation against vestigial physics.

**Audience:** EP precision community (MICROSCOPE / STEP / SR-POEM teams), dark-matter phenomenology, Weak-EP test theorists (Will, Damour).

**Community partner:** ONERA / CNES (MICROSCOPE), Stanford / NASA (STEP); proxies through `PARAMETER_PROVENANCE` for Touboul 2017 PRL bound.

### 3. Hayden-Preskill on Horizon MTC (Wave 4)

**What:** Code distance and scrambling-time bound on the project's horizon-MTC substrate are linked by a clean biconditional — non-abelian anyon richness is *necessary and sufficient* for non-trivial code distance. Recovery is universally possible at the scrambling-time bound.

**Why it matters strategically:** The black-hole information paradox has matured into a quantum-error-correction picture (Almheiri-Dong-Harlow 2015; Pastawski-Yoshida-Harlow-Preskill 2015). Our framework provides the *substrate-only* contribution to the Hayden-Preskill scrambling time, mechanically tied to the anyon spectrum. Out of scope: AdS/CFT spectrum identification, Yoshida-Kitaev decoder, Page-curve quantitative reproduction — each tracked for future work.

**Audience:** Quantum-gravity / holographic-QEC researchers (Almheiri, Maldacena, Yoshida), topological-quantum-computation theorists (Kitaev, Preskill, Nayak-Stern groups).

**Community partner:** the holographic-QEC group at Caltech / IAS / KITP / Stanford / Princeton.

### 4. RT vs Kaul-Majumdar Structural Note (Wave 5)

**What:** Classical Ryu-Takayanagi ($A/(4 G_N)$, no log) and the project's microscopic Kaul-Majumdar ($-3/2 \log$) agree only on the knife-edge $A = 4 G_N$. Anywhere else, they differ by $(3/2)\log(A/(4 G_N))$. Sen's 4D Schwarzschild log coefficient ($+77/45$) is *different* from Kaul-Majumdar's ($-3/2$) — log universality is FALSE across regularizations.

**Why it matters strategically:** Quantum-gravity model-builders frequently quote classical RT without log corrections. This note is a small, rigorous reminder that the leading-order formula is provably *not* the full story for the project's substrate. The point isn't to refute RT; it's to make explicit that the *log coefficient* is a microscopic-theory signature, distinguishing competing approaches.

**Audience:** Holographic-entropy practitioners (Lewkowycz-Maldacena, RT/HRT community), microscopic BH-entropy counters (Kaul, Sen, Strominger-Vafa, Loop-Quantum-Gravity school).

---

## Updated Bridge Map

| Bridge | Phase 6a Status | Phase 6c Status | Next Step |
|--------|----------------|----------------|-----------|
| **Strong-CP / DE** | Z16 anomaly + framing-anomaly $c_- = 24$ formalized | Zhitnitsky $\rho_{DE}$ encoded; one-mechanism falsifier active | DESI DR3+ $w(z)$ adjudication |
| **Equivalence Principle** | Vestigial gravity infrastructure (W7) shipped | 6×3 classification matrix; STEP discriminator active | STEP / SR-POEM mission updates |
| **Hayden-Preskill QEC** | W3 horizon MTC substrate shipped | Code-distance / scrambling biconditional active | AdS/CFT spectrum identification (deferred) |
| **RT vs Kaul-Majumdar** | W3 Kaul-Majumdar derivation shipped | Knife-edge structural inconsistency formalized | Bulk minimal-surface construction (deferred) |

---

## Publication Strategy

### Paper 32: Strong-CP / Topological Dark Energy
- 8 Lean theorems + Python + paper, all submission-ready (claims + adversarial reviewers clean)
- Target: short paper venue (PRD short report, EPL, or JCAP letters)
- Novel contribution: machine-checked structural one-mechanism inconsistency
- Companion notebooks: `Phase6c1_StrongCPDarkEnergy_Technical.ipynb` + `_Stakeholder.ipynb`

### Paper 34: Equivalence Principle Classification
- 25 Lean theorems (13 original + 12 strengthening), 38 tests
- Target: PRD (mid-length) or Classical and Quantum Gravity
- Novel contribution: first formal classification of EP violation across multiple DM mechanisms; STEP discriminator
- Companion notebooks: `Phase6c3_EquivalencePrinciple_Technical.ipynb` + `_Stakeholder.ipynb`

### Paper 35: Hayden-Preskill on Horizon MTC
- 10 Lean theorems + 30 tests
- Target: short formalization note venue (PRD letter, JHEP letter, or arXiv as informal note)
- Novel contribution: structural identity tying anyon richness to code distance + scrambling time
- Companion notebooks: `Phase6c4_QECHolography_Technical.ipynb` + `_Stakeholder.ipynb`

### Note: RT vs Kaul-Majumdar
- 7 Lean theorems + 29 tests + 3-page note
- Target: arXiv informal note (not a full paper)
- Novel contribution: knife-edge biconditional + Sen non-universality witness
- Companion notebooks: `Phase6c5_RTCasiniHuerta_Technical.ipynb` + `_Stakeholder.ipynb`

---

## Experimental / Observational Engagement Priorities

1. **DESI / Euclid teams (Wave 1).** $w(z)$ measurements at high redshift can adjudicate Zhitnitsky-only vs combined-DE-mechanism scenarios. The project's correctness-push proof rules out the both-active scenario; observational confirmation either supports or falsifies the bridge.

2. **STEP / SR-POEM mission teams (Wave 3).** STEP-class $\eta \sim 10^{-18}$ projection now has a specific theoretical target: vestigial-relics signature. A null result at sub-$10^{-19}$ excludes vestigial gravity within the substrate.

3. **Holographic-QEC research groups (Wave 4).** Almheiri-Dong-Harlow / Pastawski-Yoshida-Harlow-Preskill / Yoshida-Kitaev frameworks. Our biconditional gives the substrate contribution; their decoder construction would close the loop.

4. **Microscopic-BH-entropy community (Wave 5).** Kaul-Majumdar and Sen approaches predict different log coefficients. The project's formalization of Kaul-Majumdar puts a stake in one camp without refuting the other.

---

## Program Maturity Assessment

Phase 6c marks a qualitative shift from *internal theoretical development* to *external falsification engineering*:

- **Phases 1–2:** SK-EFT corrections (δ_disp, δ_diss, δ²) and counting.
- **Phase 3:** Structural mapping (gauge erasure, WKB, ADW gap equation).
- **Phase 4:** Numerical validation + experimental bridge.
- **Phase 5:** Formal-verification firsts (chirality wall, fusion categories, Drinfeld double).
- **Phase 6a:** Emergent-gravity machinery (linearized EFE, FLRW, GW, BH microstates, horizon MTC).
- **Phase 6b:** BBN constraints (W1 shipped); cross-tension identification.
- **Phase 6c (this phase):** Cross-domain bridges; each wave is a falsifier targeting another community's observable.

The project now has direct numerical / structural contact with Pendlebury 2015 EDM, Touboul 2017 MICROSCOPE, Hayden-Preskill 2007, Almheiri-Dong-Harlow 2015, Ryu-Takayanagi 2006, Casini-Huerta 2009, Sen 2012, and Van Waerbeke-Zhitnitsky 2025 — substantially broadening the empirical / theoretical surface.

---

## Outstanding Work

- **W2 (EWBaryogenesisChiralityWall).** Pre-pipeline scoping done; not yet shipped. Will tie chirality-wall infrastructure (Phase 5a) to electroweak-baryogenesis bounds — closes the "chirality" leg of Phase 6c.
- **AdS/CFT spectrum identification (W4).** A concrete mapping from horizon MTC to a specific holographic CFT would tighten the Hayden-Preskill bridge.
- **Bulk minimal-surface and CH derivations (W5).** Constructive completion would convert the W5 tracked Props into derived theorems.
- **Phase 6c integration / closure.** Once W2 ships, a phase-closure summary (analogous to Phase 5y closure) will integrate all five bridges and identify cross-wave tensions if any.
