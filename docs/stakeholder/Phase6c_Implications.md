# Phase 6c: Implications of Cross-Domain Bridges to Foundational Physics

## Technical and Real-World Implications

**Status:** Phase 6c Waves 1, 3, 4, 5 SHIPPED end-to-end (W2 EWBaryogenesisChiralityWall remains).
**Date:** 2026-04-28
**Classification:** Research Overview — For Technical and Non-Technical Stakeholders
**Prerequisite:** Phase 6a (Track A + Track B + Track C end-to-end shipped); Phase 6b Wave 1 (BBN)

---

## Executive Summary

Phase 6c took the project's emergent-gravity / dark-sector machinery and built four independent bridges to longstanding open problems in foundational physics. Each wave is a self-contained Lean module + Python mirror + paper, with figures and tests; each ships zero `sorry` statements and zero new axioms; each landed clean through claims-reviewer and adversarial-reviewer in a single submission cycle.

1. **Strong-CP / Topological Dark Energy bridge (Wave 1).** Formalizes the Van Waerbeke–Zhitnitsky 2025 proposal that the QCD topological vacuum naturally generates the observed cosmological-constant scale via $\rho_{DE} \sim \Lambda_{QCD}^6 / M_P^2$. At PDG values this gives $6.7 \times 10^{-9}$ eV⁴, within $\sim 240\times$ of the observed $2.8 \times 10^{-11}$ eV⁴ — a no-free-parameters match within the claimed three orders of magnitude. The project's Lean theorem `combined_zhitnitsky_qtheory_exceeds_observation` proves a structural one-mechanism inconsistency: Zhitnitsky and Klinkhamer–Volovik q-theory cannot simultaneously be active.

2. **Equivalence-Principle classification (Wave 3).** Classifies six Phase-5x dark-matter mechanisms by which level of the equivalence principle they violate. Two violate the weak EP ($\eta = 1$ for full vestigial phase, $\eta \sim 10^{-18}$ for vestigial relics); the other four (FangGu torsion, fracton subdiffusion, SFDM Thomas-Fermi, hidden-sector ℤ₁₆) satisfy all three EP levels. Conclusion: in this substrate, EP violation is *vestigial-only*, making STEP-class precision tests a unique discriminator.

3. **Hayden-Preskill QEC on the horizon MTC (Wave 4).** Formalizes the Hayden-Preskill information-recovery protocol on top of the Phase 6a Wave 3 horizon modular-tensor-category substrate. Code distance $d_C = \log d_{\max}$ and scrambling-time bound $t_{\rm scr} = \log D^2$ are tied by a clean biconditional: positive code distance iff non-abelian fusion. Fibonacci is the minimal admissible MTC ($d_C = \log\varphi \approx 0.481 < \log 2$); trivial-abelian falsifies admissibility.

4. **Ryu-Takayanagi vs Kaul-Majumdar structural inconsistency (Wave 5 / `note_rt_ch_bounds`).** Formalizes the structural conflict between classical Ryu-Takayanagi ($S = A/(4 G_N)$, no log term) and the project's Phase 6a Wave 3 microscopic Kaul-Majumdar entropy ($-\frac{3}{2}\log$ correction). They agree only at the knife-edge $A = 4 G_N$ (Planckian); everywhere else they differ by $(3/2)\log(A/(4 G_N))$.

---

## Result 1: Strong-CP / Topological Dark Energy Bridge

### What we found

Two of physics's most stubborn fine-tuning puzzles — the strong-CP $|\theta| \lesssim 10^{-9}$ bound and the cosmological-constant $\sim 10^{-120}$ hierarchy — may be a single phenomenon. Van Waerbeke and Zhitnitsky (arXiv:2506.14182) propose $\rho_{DE} \sim \Lambda_{QCD}^6 / M_P^2$, which at PDG $\Lambda_{QCD} = 0.1$ GeV gives $\rho_{DE} \approx 6.7 \times 10^{-9}$ eV⁴. Observed: $2.8 \times 10^{-11}$ eV⁴. Ratio: $\sim 240\times$. No fitted parameter.

The project encodes the QCD $\theta$-vacuum with the Pendlebury 2015 EDM bound as a structural invariant — any Lean construction at $\theta = 1$ raises a contradiction, mirroring the falsification at $\sim 9$ orders above bound.

The cross-mechanism inconsistency theorem `combined_zhitnitsky_qtheory_exceeds_observation` proves: if both Zhitnitsky's mechanism and a residual Klinkhamer-Volovik q-theory contribution operate, the combined dark energy strictly exceeds Zhitnitsky-alone at PDG scale, which already lies $\sim 240\times$ above observation. This is a falsifiable forced choice between two dark-energy mechanisms.

**Lean verification:** 8 theorems in `StrongCPTopologicalDE.lean` (zero sorry, zero new axioms). Cross-bridges to `Z16AnomalyComputation.sm_anomaly_with_nu_R` (right-handed-neutrino anomaly cancellation pillar) and `ModularInvarianceConstraint.framing_anomaly_constraint 24` (SM chiral central charge consistency).

### Why it matters

Two independent fine-tuning problems with one explanation, no anthropic selection, no new physics. The $\sim 3$-order match is honestly within the claimed precision of the no-free-parameters formula; it is not an exact fit, and competing one-parameter dark-energy models can match the observed value exactly. **The honest scope:** if future cosmology requires $w(z) \neq -1$ at high redshift via two distinct DE mechanisms, the bridge collapses.

---

## Result 2: Equivalence-Principle Classification

### What we found

Six dark-matter / hidden-sector mechanisms had been proposed in earlier Phase-5x work without explicit commitment to their EP status. This wave classifies them:

- **Vestigial differential coupling:** violates WEP at $\eta = 1$ (full vestigial phase, already excluded by MICROSCOPE).
- **Vestigial relics (STEP-class):** violates WEP at $\eta \sim 10^{-18}$ (sub-MICROSCOPE; at STEP design sensitivity).
- **FangGu torsion-trace:** satisfies all three EP levels. (Failure mode is kinematic — $w_{FG} = 1/3$ doesn't match observed CDM $w \approx 0$ — not EP-related.)
- **Fracton subdiffusion:** satisfies all three EP levels. (Universal mobility.)
- **SFDM Thomas-Fermi (Berezhiani-Khoury):** satisfies all three EP levels.
- **Hidden-sector ℤ₁₆ singlet:** satisfies all three EP levels.

The `violatesAt_mono` theorem encodes the subsumption hierarchy: any WEP violator violates EEP and SEP automatically. The structural conclusion `ep_violation_is_vestigial_only` shows that *exactly* the two vestigial mechanisms violate WEP — both of them, no others.

**Lean verification:** 25 theorems in `EquivalencePrinciple.lean` (13 original + 12 strengthening pass). Zero sorry, zero new axioms. Substantive cross-bridge `fangGu_failure_mode_is_kinematic_not_ep` calls `FangGuTorsionDM.fg_cdm_obstruction` to formally separate kinematic from EP failure modes.

### Why it matters

This makes precision EP experiments — MICROSCOPE (current $\eta < 10^{-15}$), STEP (projected $\eta \sim 10^{-18}$) — *direct discriminators* of dark-sector classification within the project's substrate. A future detection in the $\eta \in [10^{-18}, 10^{-15}]$ window with vestigial-relic signature would identify vestigial physics; a null result at sub-$10^{-19}$ excludes vestigial gravity (within the substrate). Strategically: the EP precision community now has a target that produces a clean yes-or-no answer.

---

## Result 3: Hayden-Preskill QEC on Horizon MTC

### What we found

Black-hole information recovery in the Hayden-Preskill protocol scrambles in $O(\log S_{BH})$ time. This wave formalizes the protocol on top of the project's Phase 6a Wave 3 horizon modular-tensor-category substrate, defining two information-theoretic observables:

- **Code distance** $d_C := \log d_{\max}$ — topological-shielding scale.
- **Scrambling-time bound** $t_{\rm scr} := \log D^2 = \log \sum_a d_a^2$ — substrate-only Hayden-Preskill bound.

The named correctness-push proves the biconditional $d_C > 0 \iff d_{\max} > 1$, plus the forward implication $d_C > 0 \Rightarrow t_{\rm scr} > 0$ (via $D^2 \geq d_{\max}^2$). Recovery is universally possible at the scrambling-time bound for any encoding choice. Concrete substrates: Fibonacci ($d_{\max} = \varphi \approx 1.618$, the *minimal* non-abelian admissible MTC), Ising ($d_{\max} = \sqrt{2}$), SU(3)$_{k=2}$ Fibonacci sub-sector, and trivial-abelian (the falsifier with $d_{\max} = 1$, $d_C = t_{\rm scr} = 0$).

**Lean verification:** 10 theorems in `QECHolographyBridge.lean` (zero sorry, zero new axioms). The substantive cross-bridge `horizon_BC_implies_HP_admissible` consumes the W3 hypothesis bundle `H_HorizonBoundaryCondition.areaLeading`, forcing $1 < d_{\max}$ and thus admissibility.

### Why it matters

Black-hole information theory has matured into a quantum-error-correction picture (Almheiri-Dong-Harlow 2015; Pastawski-Yoshida-Harlow-Preskill 2015; Yoshida-Kitaev 2017). This wave gives the project's substrate a clean structural identification: non-abelian anyon richness is *necessary and sufficient* for non-trivial code distance, which automatically gives non-trivial scrambling time. Topology and information move together. Out of scope for this wave (per Phase 6c roadmap §A): AdS/CFT spectrum identification, Yoshida-Kitaev decoder construction, Page-curve quantitative reproduction.

---

## Result 4: RT vs Kaul-Majumdar Structural Inconsistency

### What we found

Classical Ryu-Takayanagi (Phys. Rev. Lett. 96, 181602, 2006): $S_{\rm ent} = A / (4 G_N)$, no log term. Phase 6a Wave 3 microscopic Kaul-Majumdar derivation: $S = A/(4 G_N) - (3/2)\log(A/(4 G_N))$, with the universal $-3/2$ log coefficient. Sen 4D Schwarzschild (arXiv:1205.0971): $+77/45 \approx +1.71$ log coefficient — *different* microscopic answer, $|\Delta| = 289/90 \approx 3.21$.

Lean theorem `rt_eq_kaulMajumdar_iff_trivial_reduced_area`: classical RT and Kaul-Majumdar agree iff reduced area $A/(4 G_N) = 1$. Anywhere else, the gap is exactly $(3/2)\log(A/(4 G_N))$. At reduced area 2, the gap is $(3/2)\log 2 \approx 1.040$ exactly (Lean: `rt_kaulMajumdar_gap_at_reduced_area_two`).

**Lean verification:** 7 theorems in `RTCasiniHuertaBounds.lean` (zero sorry, zero new axioms). External hypotheses `H_RT_Formula_Valid` and `H_CasiniHuerta_Bound_Valid` are tracked Props (the bulk minimal-surface construction and CH derivation from modular Hamiltonian are out of scope per the roadmap).

### Why it matters

Quantum-gravity model-builders frequently invoke classical RT without explicit log corrections. This note is a small, rigorous reminder that the leading-order $A/4 G_N$ formula is provably *not* the full story for the project's substrate. The discrepancy is structural — not a perturbative correction at one specific scale but a logarithmic correction growing with horizon area. Different microscopic theories (Kaul-Majumdar vs Sen) give *different* log coefficients; this is a signature of the underlying microscopic theory, not a universal constant.

---

## What Phase 6c Adds Beyond Phase 6a

### Phase 6a (Tracks A, B, C — shipped): Emergent Gravity, GW, Horizon Microstates

Phase 6a built the project's emergent-gravity machinery: linearized Einstein equations, FLRW dynamics, gravitational-wave constraints (GW170817), and the horizon modular-tensor-category substrate with Kaul-Majumdar microscopic entropy.

### Phase 6c (Waves 1, 3, 4, 5 — shipped): Cross-Domain Bridges

Phase 6c takes that machinery and connects it outward to four independent open questions in foundational physics: strong-CP / dark energy, equivalence principle, black-hole information, and entropy bounds. Each wave is a *bridge*, not new internal infrastructure — they consume Phase 6a's outputs (e.g., W3 horizon BC, W3 Kaul-Majumdar entropy, FangGu torsion DM, Z16 anomaly) and translate them into other domains' language.

The result: the project's framework now has direct numerical / structural contact points with Pendlebury 2015 EDM, Touboul 2017 MICROSCOPE, Hayden-Preskill 2007, Almheiri-Dong-Harlow 2015, Ryu-Takayanagi 2006, Casini-Huerta 2009, and Sen 2012 — a substantial broadening of the project's empirical / theoretical surface area.

---

## Outstanding Phase 6c Items

- **Wave 2 (EWBaryogenesisChiralityWall).** Pre-pipeline scoping has occurred; not yet shipped. Will tie the project's chirality-wall infrastructure (Phase 5a) to electroweak-baryogenesis bounds.
- **Open question on dark energy.** The Zhitnitsky bridge's $\sim 240\times$ ratio is *not* a tight match. Resolution is gated on observational improvements ($w(z)$ dynamics from DESI DR3+, Euclid) that can distinguish Zhitnitsky-only from one-parameter-fit alternatives.
- **AdS/CFT spectrum identification (W4 deferred).** A concrete identification of the horizon MTC with a specific holographic CFT would tighten the Hayden-Preskill picture significantly. Tracked for future work.
- **Bulk minimal-surface and modular-Hamiltonian derivations (W5 deferred).** Constructive completion of $H_{RT}$ and $H_{CH}$ would convert the tracked Props into derived theorems.

---

## By the Numbers (Phase 6c, post-strengthening)

- **Lean theorems shipped:** 50 (W1: 8 + W3: 25 + W4: 10 + W5: 7) — substantive, all with zero sorry.
- **New Lean modules:** 4 (`StrongCPTopologicalDE`, `EquivalencePrinciple`, `QECHolographyBridge`, `RTCasiniHuertaBounds`).
- **New Python subpackages:** 4 (`src/strong_cp_de`, `src/equivalence_principle`, `src/qec_holography`, `src/rt_ch_bounds`).
- **New tests:** 111 (14 + 38 + 30 + 29).
- **New papers / notes:** 4 (paper32, paper34, paper35, note_rt_ch_bounds) — all submission-ready (claims + adversarial reviewers clean).
- **New figures:** 4 (`fig_zhitnitsky_de_theta_scan`, `fig_ep_violation_matrix`, `fig_code_distance_vs_fusion_spectrum`, `fig_rt_ch_bounds_mtc`).
- **New axioms introduced:** **0**.
- **New `sorry` statements:** **0**.
- **counts.tex macros added:** 14 (one pair `_Thms` / `_Tests` per wave, plus the W5 pair via the note).

---

## Strategic Reading

Phase 6c's waves were chosen *not* to extend the project's internal machinery but to *export* it. The emergent-gravity framework was already a complete theoretical apparatus; what it needed was external falsifiability surface. Each wave produces a falsifier the broader physics community can act on:

- **Wave 1** says: if both Zhitnitsky DE and KV q-theory operate, the combined density exceeds observation. Cosmology pinpoints this within DESI DR3+.
- **Wave 3** says: any MICROSCOPE-to-STEP $\eta$ detection signals vestigial physics. STEP-class missions act on it.
- **Wave 4** says: black-hole horizons must be non-abelian-MTC-like for information recovery. Quantum-gravity model-builders inherit this.
- **Wave 5** says: classical RT must be augmented with the microscopic log correction. Holographic-entropy practitioners act on it.

Phase 6c does not close the project's foundational program. It widens its empirical perimeter from *internal mechanisms compute their own observables* to *internal mechanisms specify external experiments / observations that could falsify them*.
