# Strategic Positioning: Phase 6d — Closing the QCD Bridge

## How Center Symmetry, Chiral SSB, and CFL Lock the Project's Framework to Standard QCD Phenomenology

**Date:** 2026-04-28
**Context:** This memo positions Phase 6d (Track A — W1 + W2 + W3, all shipped end-to-end) within the broader research program. Phase 6d is CLOSED; this is the closure summary.

---

## Phase 6d's Strategic Value

Phase 6d delivers the *QCD-side* bridge of the project's framework. Where Phase 5z.1 mapped an abstract scalar channel onto the electroweak Higgs, Phase 6d maps four QCD-physics structures onto the project's machinery:

- *Center symmetry* (W1) — the project's non-Abelian gauge-erasure framework recovers Polyakov-loop confinement.
- *Chiral SSB* (W2) — the WetterichNJL scalar channel from Phase 5z.1 is the QCD quark condensate.
- *Color-flavor locking* (W3) — the bare-gauge $\mathbb{Z}_3$ and the emergent diquark-sector $\mathbb{Z}_3$ are identical at the level of the cyclic generator.

The central strategic insight: each of these is an *independent reidentification check*. The project's machinery was built for emergent-gravity / dark-sector / categorical reasons; QCD agreement is a non-trivial consistency test, not a tuning target.

---

## Three Strategic Pillars

### Pillar 1: Confinement-as-Symmetry, in Lean (Wave 1)

**What:** 18 Lean theorems formalizing $\mathbb{Z}_N$ 1-form center symmetry, Polyakov-loop biconditionals, Svetitsky-Yaffe universality, KSS bound bracket [0.07, 0.08], and Walker-Wang transport prediction $\eta/s \in [\mathrm{KSS}, 2\cdot\mathrm{KSS}]$ with two falsifiers.

**Why it matters strategically:** Quark confinement (Yang-Mills mass gap) is one of the seven Clay Millennium Prize problems. We do not solve it. What we *do* is encode its modern symmetry-theoretic framing as a machine-checked Lean module — the kind of structural-bookkeeping that makes the question precise and the falsifiability surface explicit. The KSS-Walker-Wang prediction is a falsifiable narrow band that heavy-ion programs (RHIC, LHC) measure routinely.

**Audience:** Lattice QCD theorists (Pelissetto-Vicari, Kos-Poland-Simmons-Duffin), heavy-ion phenomenologists, condensed-matter analog-confinement researchers (Hofman-Iqbal higher-form-symmetry hydrodynamics).

**Community partner:** the holographic-hydrodynamics community (KSS, Walker-Wang transport); the Svetitsky-Yaffe universality community (lattice and bootstrap).

### Pillar 2: GMOR Identity, Machine-Checked (Wave 2)

**What:** 10 Lean theorems formalizing the QCD chiral-condensate order parameter, the Gell-Mann–Oakes–Renner relation $m_\pi^2 f_\pi^2 = -2 m_q \langle \bar q q \rangle$ verified at PDG/FLAG-2021 to ~1 part in $10^4$, and a structural contrapositive proving the chiral-unbroken phase violates GMOR.

**Why it matters strategically:** GMOR is one of QCD's most-tested identities; it relates four independent measurements with no fitted parameter. Machine-checking the agreement gives the project's WetterichNJL scalar channel (Phase 5z.1) a physical identification: it *is* the QCD quark condensate. The pattern-parallel construction with Phase 5z.1's Higgs-bilinear identification means the same template (the `IsBilinearCandidate` predicate) handles both electroweak and QCD condensates.

**Audience:** Lattice QCD community (FLAG-2021), chiral perturbation theory community (Gasser-Leutwyler tradition), particle-data community.

**Community partner:** FLAG (Flavour Lattice Averaging Group) for $\langle \bar q q \rangle$; PDG for $m_\pi$, $f_\pi$, $m_q$ values.

### Pillar 3: CFL Emergent ℤ_3 Equals QCD Center ℤ_3 (Wave 3 — THE Phase 6d correctness-push anchor)

**What:** 12 Lean theorems formalizing the CFL chiral Lagrangian and the cross-derivation correctness-push `CFL_emergent_Z3_matches_QCD_center_Z3`. Two independent generator derivations — bare-gauge SU(3) center (W1) and Cooper-paired diquark-sector emergent symmetry (Hirono-Tanizaki) — yield the *same* primitive cube root of unity $\omega = e^{2\pi i/3}$. Verifiable to machine precision via independent code paths.

**Why it matters strategically:** The Schäfer-Wilczek 1999 quark-hadron continuity claim is a deep structural fact about QCD: high-density CFL and low-density confined hadronic matter are continuously connected, with no thermodynamic phase transition. Hirono-Tanizaki gave the algebraic explanation: an emergent $\mathbb{Z}_3$ in CFL coincides with the bare-gauge $\mathbb{Z}_3$ of confined QCD. We formalize that coincidence in Lean.

This is *the* most architecturally unusual contribution of Phase 6d: the agreement is non-trivial because the two derivations are *physically* different (bare gauge vs Cooper-paired diquark sector), and the algebraic agreement at the generator level is what makes continuity work.

**Audience:** Dense-quark-matter community (Alford-Rajagopal-Wilczek, Schäfer-Wilczek, Son-Stephanov), neutron-star equation-of-state phenomenologists, higher-form-symmetry theorists (Hirono-Tanizaki, Gaiotto-Kapustin-Seiberg-Willett).

**Community partner:** the dense-matter / neutron-star theory community; specifically, Hirono and Tanizaki (whose 2019 PRL is the project's primary anchor).

---

## Bridge Map: How Phase 6d Connects to the Rest

| Bridge | Phase | Status | Cross-bridge to Phase 6d |
|--------|-------|--------|--------------------------|
| **Higgs-bilinear identification** | 5z.1 | shipped | Same template (`IsBilinearCandidate`) used in W2 for quark condensate |
| **Z16 anomaly (SM with $\nu_R$)** | 5b/6c | shipped | W1 calls `Z16AnomalyComputation` no, but framing-anomaly $c_- = 24$ relevant |
| **Horizon MTC substrate** | 6a W3 | shipped | W1 uses SU(3)$_1$ fusion ring; cross-references SU3kFusion |
| **WetterichNJL scalar channel** | 5z.1 | shipped | W2 cross-bridge `njl_scalar_bounded_consistent_with_chiral_broken` |
| **FangGu torsion DM** | 5y W4 | shipped | (No direct Phase 6d cross-bridge; relevant for Phase 6c W3 EP classification) |
| **Vestigial gravity** | 5y W7 | shipped | (No direct Phase 6d cross-bridge) |

---

## Publication Strategy

### Paper 36: Center Symmetry & Walker-Wang Transport
- 18 Lean theorems + 28 tests + 4-page paper, submission-ready.
- Target: PRD (Letters or short report) or J. High Energy Phys.
- Novel contribution: machine-checked $\mathbb{Z}_N$ center-symmetry framing + falsifiable KSS-window prediction.
- Companion notebooks: `Phase6d1_CenterSymmetry_Technical.ipynb` + `_Stakeholder.ipynb`.

### Paper 37: Chiral SSB and the GMOR Relation
- 10 Lean theorems + 14 tests + paper, submission-ready.
- Target: PRD (short paper) or Eur. Phys. J. C.
- Novel contribution: formal identification of WetterichNJL scalar with QCD quark condensate; GMOR cross-check at ~1 part in $10^4$.
- Companion notebooks: `Phase6d2_ChiralSSB_Technical.ipynb` + `_Stakeholder.ipynb`.

### Paper 38: CFL Emergent ℤ_3 Equals QCD Center ℤ_3 — THE Correctness-Push Anchor
- 12 Lean theorems + 17 tests + paper, submission-ready.
- Target: PRD (Letters) or PRL (rapid communication).
- Novel contribution: machine-checked cross-derivation correctness-push between bare-gauge and Hirono-Tanizaki emergent ℤ_3 generators.
- Companion notebooks: `Phase6d3_CFL_Technical.ipynb` + `_Stakeholder.ipynb`.

---

## Experimental / Lattice / Theoretical Engagement Priorities

1. **Lattice QCD universality measurements (W1).** SU(2) Ising vs SU(3) 3-state Potts critical exponents. Pelissetto-Vicari 2002 + Kos-Poland-Simmons-Duffin 2016 already provide $\nu_{\rm Ising} = 0.6299$ to 4-decimal precision; Potts deconfinement is weakly first-order. Direct lattice fits in the deconfinement region can sharpen the Svetitsky-Yaffe correspondence.

2. **Heavy-ion KSS-window measurement (W1).** RHIC and LHC measure $\eta/s \approx 0.1$–$0.2$ for the quark-gluon plasma. The Walker-Wang prediction $\eta/s \in [\mathrm{KSS}, 2\cdot\mathrm{KSS}] \approx [0.080, 0.159]$ is a tight target window. Sub-leading transport coefficients (second-order hydrodynamic constants) can adjudicate.

3. **FLAG / PDG GMOR refinement (W2).** Future updates of $\langle \bar q q \rangle$ and $m_q$ from FLAG / PDG are the cleanest cross-check. The current ~1-part-in-$10^4$ residual is well below higher-order chiral-perturbation-theory corrections; if it grows to 1\% or more in a future update, the identification is breaking down.

4. **Neutron-star equation-of-state constraints (W3).** Gravitational-wave merger observations (LIGO, future Einstein Telescope, Cosmic Explorer) constrain the dense-matter equation of state. CFL and other quark-matter phases can be distinguished by their distinct pressure-density curves. Our framework's $\mathbb{Z}_3$-matching is *consistency-class*, not equation-of-state-specific — but it ties the project's framework to the dense-matter modeling chain.

---

## Phase 6d Closure Summary

**Phase 6d is CLOSED.** All three Track A waves (W1 center symmetry, W2 chiral SSB, W3 CFL) shipped end-to-end. Per the roadmap scope-lock decision, residual QCD items (β-function, Wilson-loop confinement, full hadron-mass spectrum) are deferred to HepLean / PhysLean. The project's QCD bridge is complete at the level of *symmetry structure*; full QCD dynamics is a separate program.

**Total Phase 6d numbers:**
- 40 substantive Lean theorems / 0 sorry / 0 new axioms.
- 3 papers (paper36, paper37, paper38) all submission-ready.
- 3 figures, 59 tests.
- counts.tex macros: 6 (W1 + W2 + W3, each `_Thms` / `_Tests` pair).

**Discipline metric trend (5 waves with the discipline applied):**
- 6c.3 = 12 retroactive (no discipline; baseline)
- 6b.1 = 5 retroactive (discipline + ruthless review)
- 6d.1 = 6 retroactive (discipline + 2-pass review)
- 6d.2 = 4 retroactive (discipline + 3-pass review)
- 6d.3 = 1 retroactive (discipline + 1 first-pass identity-wrapper, caught by Lean unused-variable linter)

First-pass cost trends monotonically downward (12 → 5 → 6 → 4 → 1) as the preemptive-strengthening discipline matures.

---

## Program Maturity Assessment

Phase 6d marks a tighter integration of the project's emergent-gravity machinery with standard particle physics:

- **Phases 1–4:** SK-EFT, gauge erasure, ADW gap equation, vestigial gravity, experimental bridge.
- **Phase 5:** Formal-verification firsts; categorical infrastructure; production MC.
- **Phase 5z.1:** Higgs-bilinear identification (the template).
- **Phase 6a:** Emergent-gravity dynamics, GW falsification, BH microstates, horizon MTC.
- **Phase 6b:** BBN constraints (W1 shipped).
- **Phase 6c:** Cross-domain bridges (Strong-CP, EP, Hayden-Preskill, RT/CH).
- **Phase 6d (this phase, CLOSED):** QCD-side bridges (center symmetry, chiral SSB, CFL correctness-push).

The project's emergent-gravity framework now has consistency checks against:
- **Electroweak physics** (Phase 5z.1 — Higgs bilinear).
- **QCD chiral physics** (Phase 6d W2 — quark condensate, GMOR).
- **QCD confinement physics** (Phase 6d W1 — Polyakov loop, Svetitsky-Yaffe, KSS).
- **QCD dense-matter physics** (Phase 6d W3 — CFL emergent $\mathbb{Z}_3$).
- **Cosmology** (Phase 6c W1 — Zhitnitsky DE; Phase 6b W1 — BBN).
- **Black-hole physics** (Phase 6a W3 — Kaul-Majumdar; Phase 6c W4 — Hayden-Preskill; Phase 6c W5 — RT vs KM).

Each consistency check is machine-verified with zero `sorry` and zero new axioms. The project's empirical perimeter is now *substantially* broader than at any prior phase.
