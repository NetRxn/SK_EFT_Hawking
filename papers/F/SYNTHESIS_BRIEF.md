# F (Flagship) Synthesis Brief — Fluid-Based Approaches to Fundamental Physics: A Formally Verified Survey

**Generated:** 2026-05-04 (Phase 7c F pre-draft survey, while D1/D2/D3/D4 reviewers run).
**Bundle target:** Tier 0 flagship review, ~80–150pp PRD-long-format.
**Source manifest:** `papers/F/source_manifest.md` (41 contributing source papers).
**Stage-13 anchor list:** `docs/agents/claims-reviewer-bundle-prompts.md` §F.
**Strategy frame:** `docs/PAPER_STRATEGY.md` §1 (Flagship target).

---

## Top-level synthesis paragraph (NEW to F, absent from any sibling bundle)

F is the only bundle that ships the **architectural-scope statement** of the
project as a coherent document. Twelve sibling bundles (D1–D5, L1–L3, I1–I2,
E1–E2) each report their own thread; F is where the substrate's predictive
content is exhibited as a single object across all twelve. The synthesis
claim NEW to F is:

> The same antisymmetric-tetrad-bilinear (ADW) substrate that drives the
> emergent-gravity content of Bundle~D3 (single Sakharov coefficient
> $G_N^{\mathrm{Sak}} = 12\pi/(N_f\,\Lambda_{\mathrm{UV}}^{2})$ propagating
> across six observables) also drives the SK-EFT analog-Hawking content of
> Bundle~D1 (across BEC, polariton, graphene; 92% Lean-theorem reuse), the
> chirality-wall + modular-invariance content of Bundle~D2 (Spin$^{\mathbb{Z}_4}$
> 5-bordism with $N_f = 16$ matching D3's Sakharov-coefficient $N_f$), the
> dark-sector NO-GO closures of Bundle~D5 (causal-set + entropic + Jacobson-thermo-GR
> with full Phase~6m closure), and the topological quantum-computation
> foundations of Bundle~D4 (one MTC, four faces — Drinfeld centre +
> WRT partition + HP-QEC + RT/CH knife-edge). The substrate is one object;
> its twelve faces are thirteen bundles' worth of predictive register.

This claim is structurally absent from any individual sibling bundle and is the F-unique
content. Sibling bundles report their threads; F reports the unification.

---

## Section structure (12 sections × ~7–12pp each = ~80–150pp)

### §1: Strategic frame
**Length:** 5pp | **Lift from:** new F-original synthesis (no single-source lift); cross-cite all 12 sibling bundles.
**Key claims to land:**
- 13-bundle publication architecture (1 flagship + 5 Tier-1 deep + 3 Tier-2 PRL + 2 Tier-3 infrastructure + 2 Tier-4 experimental).
- NO-GO results as first-class publishable content (per `PAPER_STRATEGY.md` §3.5).
- The substrate's predictive register lives at the boundary partition (cleared / falsified / structurally-blocked / reproduced).
- The unifying claim NEW to F is the substrate-identity claim above.
**Citations carried:** every 12 sibling bundles' headline citations.
**Cross-bundle bridge:** every section to every sibling bundle.

### §2: Architectural scope (lift verbatim from `ARCHITECTURE_SCOPE.md` §2 + §10)
**Length:** 6pp | **Lift from:** `docs/ARCHITECTURE_SCOPE.md` §2 + §10.
**Key claims to land:**
- The project's scope statement: what is and is not in scope.
- The 14-stage Wave Execution Pipeline (cross-ref Bundle~I1 §3).
- The 14 Pipeline Invariants (cross-ref Bundle~I1 §4).
- The Stage-13 adversarial-review architecture (cross-ref Bundle~I1 §5).
**Risks / open hypotheses:** Verify ARCHITECTURE_SCOPE.md is current at flagship-submission date; this is a Phase~7 Wave~14 obligation.

### §3: Gauge erasure (paper3)
**Length:** 4pp | **Lift from:** Bundle~D3 §3 + paper3.
**Key claims to land:** Only $U(1)$ survives the fluid layer; non-Abelian gauge fields persist only as discrete centre symmetries.
**Cross-bundle bridge:** D3 §3 + D4 §4 (Drinfeld centre carries the centre-symmetry data).

### §4: SK-EFT analog Hawking radiation across three platforms (D1 + E1 + E2)
**Length:** 12pp | **Lift from:** Bundle~D1 (full content) + companion summaries from E1, E2.
**Key claims to land:**
- Three SK-EFT axioms + KMS + FDR closure in `SKDoubling.firstOrder_KMS_optimal`.
- Three platforms (BEC, polariton, graphene) sharing 92% Lean theorem reuse.
- Exact WKB connection formula with three non-perturbative effects (modified unitarity / FDR-mandated noise floor / spectral floor at $\omega \sim 2 T_H$ for Heidelberg).
- Polariton stimulated-Hawking gain $G > 0.5$ at $\omega/\kappa = \ln 3 / (2\pi) \approx 0.175$ with $N_{\mathrm{probe}} = 100$ probe photons per mode (5σ).
- Graphene $T_H \approx 2.4\,\mathrm{K}$, $\delta_{\mathrm{disp}} \approx -2.8\%$, Wiedemann–Franz violation $L/L_0 > 200$.
**Cross-bundle bridge:** D1 + E1 + E2 (companion letters carry per-platform device-parameter audits).

### §5: Chirality wall + modular invariance (D2 + L2)
**Length:** 10pp | **Lift from:** Bundle~D2 (full content) + L2 splash summary.
**Key claims to land:**
- Spin$^{\mathbb{Z}_4}$ 5-bordism with $\mathbb{Z}_{16}$ anomaly classification.
- $N_f = 16$ as the unique SM consistency count (matches D3's Sakharov $N_f$).
- Three SM fermion generations from modular invariance ($N_f \in \mathrm{lcm}(16,3)\cdot\mathbb{Z}$).
- Three-pillar synthesis: Golterman-Shamir no-go (P1), Gioia-Thorngren positive construction (P2), Onsager + Witten anomaly + 4+1D gapped interface (P3).
- One axiom: `gapped_interface_axiom`.
**Cross-bundle bridge:** D2 + L2; D2 §3.4 (Drinfeld centre) ↔ D4 §4.

### §6: Emergent gravity through BH thermodynamics (D3 + L1 + L3)
**Length:** 30pp | **Lift from:** Bundle~D3 (full content, modulo the F-internal compression) + L1 splash summary + L3 splash summary.
**Key claims to land:**
- Single-coefficient identity $G_N^{\mathrm{Sak}} = 12\pi/(N_f\,\Lambda_{\mathrm{UV}}^{2})$ propagating across 6 observables.
- Three closures forcing ADW: Wen $\sim 1/6000$ deficit; fracton diff-inv no-go; GW170817 $\sim 7\times 10^{14}$ falsification.
- Four cleared decision gates: E.1 (linearised EFE), E.2 (heat-kernel calibration), E.3 (diff invariance through $a_4$), E.4 (multi-channel PPN).
- BCH four laws partitioned by regime mass $M_c = N_f\,\Lambda_{\mathrm{UV}}/(12\pi\,\alpha_{\mathrm{ADW}})$.
- Bekenstein–Hawking entropy $S = A/(4G_N) - (3/2)\log(A/(4G_N)) + O(1)$ with abelian-MTC falsifier.
- CC reproduced (not solved) at $\Lambda_{\mathrm{emerg}}/\Lambda_{\mathrm{obs}} \sim 10^{122}$.
- EC torsion $|T_{\mathrm{EC}}| \approx 2.05\times 10^{-77}\,\mathrm{GeV}$ ~46 orders below KRT.
- 5 algebraic-Lorentzian-geometry first-formalisation appendices (paper44 + Phase 6f-6g).
**Cross-bundle bridge:** D3 §6 ↔ L1 (GW170817 vestigial-graviton); D3 §8 ↔ L3 (BCH four laws); D3 §22.5 ↔ I1 sidebar (first-formalisation claims).

### §7: Topological QC foundations (D4)
**Length:** 10pp | **Lift from:** Bundle~D4 (full content).
**Key claims to land:**
- One MTC, four faces (Drinfeld centre + WRT partition + HP-QEC + RT/CH knife-edge).
- 5 first-formalisation claims: $U_q(\mathfrak{sl}_2)$, $U_q(\mathfrak{sl}_3)$, Ising MTC w/ all hexagons + ribbons, trefoil $= -\sqrt{2}$, WRT partition on $S^2 \times S^1$, HP code-distance biconditional.
- Doublon-SWAP gate as first SPT topological quantum gate (Berry phase $= \pi$).
- Cross-bridges: D4 §4 ↔ D2 §3.4 (Drinfeld centre); D4 §7 ↔ D3 §7 + §9 (HP-QEC); D4 §8 ↔ D3 §7 (knife-edge).
**Cross-bundle bridge:** D4; D2; D3.

### §8: Dark sector under substrate constraints (D5)
**Length:** 10pp | **Lift from:** Bundle~D5 (full content).
**Key claims to land:**
- Six Phase-5x DM mechanism classification with predictive-boundary partition.
- Phase 6m Track A: causal-set DE NO-GO + 3 publishable structural caveats.
- Phase 6m Track B: entropic-gravity unanimous NO-GO closure (8/8 mechanisms; first complete-mechanism-family-NO-GO publication).
- Phase 6m Track C: Jacobson-thermo-GR with M3 EGJ f(R) Exp + ArcTanh strongest CLEARED-R5 of any track.
- Sakharov 4-condition criterion: first systematic Λ_J vs Λ_HK comparison; substrate-dependent.
- Barrow-bound prescription dependence as embedded structural-caveat subsection (10.5).
- BBN classification (paper29); Zhitnitsky absorption (paper32); EP-violation matrix (paper34); CC-channel constraint (paper42b cross-link to D3 §21).
**Cross-bundle bridge:** D5 §7 ↔ D3 §21 (heat-kernel $a_0$).

### §9: Methodology and the verification stack (I1 + I2)
**Length:** 8pp | **Lift from:** Bundle~I1 (full content) + I2 software paper summary.
**Key claims to land:**
- 14-stage Wave Execution Pipeline (full description).
- 3-layer verification: Python numerics ↔ Lean 4 formal proofs ↔ Aristotle automated theorem prover.
- Worked cases from each pipeline stage.
- Phase 6f-6g substrate roster algebraic-Lorentzian-geometry first-formalisation claims (primary content here; D3 §22.5 supplement).
- VerifiedJackknife software paper content (I2).
- Lean tensor-categories Mathlib upstream cycle (I2).
**Cross-bundle bridge:** I1; I2; D3 §22.5 (algebraic-Lorentzian-geometry supplement).

### §10: Substrate predictive register: the boundary partition
**Length:** 8pp | **Lift from:** new F-original synthesis with cross-cites to D1–D5.
**Key claims to land:**
- The substrate's complete cleared/falsified/structurally-blocked/reproduced register.
- Cleared decision gates: E.1, E.2, E.3, E.4', PPN ratios, EC torsion, Stelle higher-curvature ceilings.
- Falsified: GW170817 vestigial graviton ~7e14; Wen-ADW ~1/6000; fracton no-go; abelian-MTC entropy falsifier; EWBG doubly-forbidden.
- Reproduced: CC problem at ~10^122.
- Open under tracked hypothesis: explicit one-loop α_ADW; RHMC L≥8 convergence; Higgs back-reaction; PMNS structure; figure-eight knot invariant; full WRT surgery formula.
**Cross-bundle bridge:** D3 + D5 (negative results); D1 (open hypotheses); D2 (axiom budget).

### §11: Open problems and Phase 8 outlook
**Length:** 6pp | **Lift from:** new F-original.
**Key claims to land:**
- 12-bundle Phase 7 close-out summary; submission roll-out per `PAPER_STRATEGY.md` §3.
- Cross-references to Phase 6 deferred targets that remain Phase 8+ work.
- Mathlib upstream cycle (cross-ref I2).
- Future Phase 6X waves anticipated; absorption protocol per `LATE_PHASE6_ABSORPTION_PROTOCOL.md`.
**Cross-bundle bridge:** all 12 siblings.

### §12: Conclusions
**Length:** 4pp | **Lift from:** new F-original.
**Key claims to land:**
- Restate the substrate-identity synthesis claim NEW to F.
- Substrate program scope: predictive register at the cleared/falsified/blocked/reproduced boundary partition.
- The 13-bundle architecture as a coherent submission package.

---

## Stage-13 anchor obligations (must verify at submission gate)

1. **Per-sibling-bundle headline-claim character match.** Every L1/L2/L3 PRL splash claim in F must match the published-form bundle's claim character-for-character (after sibling-bundle Stage 13 closes).
2. **Per-sibling-bundle main-result character match.** Every D1/D2/D3/D4/D5 main-result statement in F must match its Tier-1 deep paper's main result character-for-character.
3. **`RESEARCH_STATUS_OVERVIEW.md` proven-chains list current.** Verify at flagship-submission date.
4. **`ARCHITECTURE_SCOPE.md` §2 + §10 lifted verbatim.** Verify current state.
5. **All theorem / module / paper counts current per `docs/counts.tex`.** No inline literals.
6. **Citation cache complete.** Every cited bundle in `inprep: True` until that bundle's submission state changes.

---

## Cross-bundle bridge summary (per source-manifest insertion points)

| F section | Lifts from | Cross-bridges |
|---|---|---|
| §3 | paper3 | D3 §3 + D4 §4 |
| §4 | paper1+2+4+12+16_graphene_sk_eft | D1 + E1 + E2 |
| §5 | paper7+8+9+10 | D2 + L2 |
| §6 | papers 5/6/20/21/22/23/25/26/27/33/35/36/37/38/39/40/41/42/42b/43/44 | D3 + L1 + L3 + I1 sidebar |
| §7 | papers 9/11/14/16_wrt/18/35/note_rt_ch_bounds | D4 + D2 §3.4 + D3 |
| §8 | paper17/29/32/34/42b | D5 + D3 §21 |
| §9 | paper15+44 + Phase 6f-6g substrate roster + Phase 5o W4-5 | I1 + I2 + D3 §22.5 supplement |
| §10 | new F-original | All 12 siblings |
| §11 | new F-original | All 12 siblings + Phase 8 |
| §12 | new F-original | All 12 siblings |

---

## Biggest scope risks for the F substantive draft

1. **Sibling-bundle stability gate.** F cannot ship until all 12 sibling bundles reach Stage-13 GREEN. Drafting F now creates cross-bundle drift risk.
   *Mitigation:* this brief is fine; substantive draft awaits all-12-GREEN gate per Phase 7 Wave 13 sequencing.

2. **80–150pp scope.** F is the largest bundle by far. Pre-emptive strengthening discipline mandatory at every theorem statement.

3. **Citation registry coverage.** F lifts citations from all 12 siblings. Any registry gap surface across siblings during their Stage-13 closures must be back-propagated to F's bibliography.

4. **`ARCHITECTURE_SCOPE.md` currency.** F §2 lifts ARCHITECTURE_SCOPE verbatim; the document must be current at flagship-submission date.

5. **`RESEARCH_STATUS_OVERVIEW.md` proven-chains list.** Same currency requirement.

6. **Counts.tex freshness.** All counts in F must come from `docs/counts.tex` macros; no inline literals (Stage-13 BLOCKER per the F anchor list).

7. **`LATE_PHASE6_ABSORPTION_PROTOCOL.md` for any Phase 6X waves landing during F drafting.** F must absorb these via the Stage A–G branches before submission.

---

## Section count check

Target: ~12 sections × ~7–12pp each = ~80–150pp PRD long format. Section structure
above shows 12 sections (§1–§12) at 5+6+4+12+10+30+10+10+8+8+6+4 = 113pp. This
sits inside the target range.

If section §6 (D3 lift) compresses well to ~25pp, the document closes at ~108pp.
If §6 expands to handle full coverage, the document approaches 150pp at the upper
bound. **Recommendation:** target ~110pp on first draft; adjust §6 or §10
length on iteration.

---

*Synthesis brief generated 2026-05-04 by F pre-draft survey while sibling-bundle reviewers run. Drafting deferred until all 12 sibling bundles Stage-13 GREEN per Phase 7 Wave 13 sequencing.*
