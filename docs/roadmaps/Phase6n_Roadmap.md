# Phase 6n: SK-EFT Foundational Backing + Structural Compression — First-Mover Tracks

## Technical Roadmap — May 2026

*Prepared 2026-05-04 | **New phase, structurally parallel to Phase 6m.** Sources: `temporary/working-docs/brainstorm/20260504-GUToE/Phase6n-6z-GUToE-Brainstorm_1.md` (Session 1 + Session 2 + Session 3 synthesis); 8 deep-research returns at `Lit-Search/_Exploratory/`; the G10 Appendix at `Lit-Search/_Exploratory/Appendix- Re-assessment of Deferred Tracks for SK_EFT_Hawking Phase 6n+.md` reversing 3-of-4 deferred sub-tracks; Itô-explore agent findings on Mathlib4 + Degenne brownian-motion repo state.*

**Trigger condition (no gate — autonomous):** Phase 6n can dispatch any time. It is independent of Phase 6m closure and runs in parallel with active Phase 7a–7g bundle work.

**Status (2026-05-04):** **Roadmap initialized; first wave dispatch pending user confirmation of Shape D. No waves shipped yet.** Two D.3 user-authorization gates flagged in advance per `LATE_PHASE6_ABSORPTION_PROTOCOL.md` (waves 6n.γ and 6n.ζ refine prior published-claim profile and must not start before user-auth at Stage B of the absorption protocol).

**Entry state (2026-05-04 Inventory_Index snapshot):** ~5229 substantive theorems / ~243 modules / 0 sorry / 1 axiom. Phase 6m FULLY CLOSED at Lean-formalization scope (R1–R6 + strengthening + cross-module proof-chain). Phase 7 in flight: 8 of 13 bundles reviewer-triple-closed at GREEN (I1, I2, L1, L2, L3, D5, E1, E2); F + D1 + D2 + D3 + D4 in active drafting. Phase 7c session shipped 12 of 13 reviewer-triple-closed plus F flagship 12-section first pass at HEAD `9fabdc8`.

**Anchors carried forward into Phase 6n:**
- `FirstOrderKMS` (Phase 1) — Aristotle 4-of-9 productive-value disproof; the anchor case study Phase 6n.1 lifts to "axiom replaced by deeper structure that explains the disproof."
- Phase 6e Sakharov-criterion biconditional (Λ_J = Λ_HK on ³He-A; falsified on FLS BEC) — substrate for Phase 6n.7's horizon-Crooks reformulation.
- Phase 6m Track C JTGR survivors (M1, M2/M7, M3 Exp/ArcTanh, M4, M9; M8 conditional) — Sakharov-class assignment carries into 6n.7.
- Phase 5o Wave 5 lean-tensor-categories library (Pivotal → Spherical → Balanced → Ribbon → Semisimple → Fusion → Modular; 114 thms) — substrate for Phase 6n.γ G9 SymTFT lift.
- `δ_disp / δ_diss / δ^(2) / δ^(3)` SK-EFT gradient-expansion coefficients in `formulas.py` — substrate for Phase 6n.α G2 resurgence.
- Phase 6e a_n + Phase 6m Sakharov tr(I) + Phase 5z Goldstino zero modes — substrate for Phase 6n.η G8-W1 AS memo (the heat-kernel ↔ Atiyah-Singer dictionary already implicit).
- `WAVE_EXECUTION_PIPELINE.md` 14-stage process; `BUNDLE_LIFT_PROCEDURE.md`; `LATE_PHASE6_ABSORPTION_PROTOCOL.md` (D.2 / D.3 / D.4 branches).

**Thesis.** Phase 6n loads the program's deepest unification-leverage tracks identified in the Session-1 conspicuous-gaps catalog and refined by Session-2 deep-research returns. Two threads run in parallel:

1. **Structural unification leverage** (G2 resurgence; G9 SymTFT; G8-W1 AS reformulation memo) — compresses existing program content into deeper structural objects. First-mover where applicable.
2. **Foundational backing for fluctuation-theorem content** (G10-6n.1 Glorioso-Liu axiomatic; G10-6n.3 Crooks-on-analog-Hawking; G10-QCrooks-α productive-value Aristotle wave; G10-6n.7 Sakharov ↔ horizon-Crooks reformulation) — replaces FirstOrderKMS-class anchors with deeper axiomatic + adds new falsifiable IR constraints.

The phase ships 7 waves; downstream Phase 6o picks up the heavier tracks (G3 boostless-soft, G4-Kerr-Schild, G1 Schellekens chain + NO-GO writeup, G10-ETH-α, Itô + LDP-α/β as I3 community contribution pending user authorization).

**Project rule reaffirmed (Session-3 user direction 2026-05-04):** **No PM / time / phase-cost estimates anywhere in this roadmap.** Track readiness by content state (sorry count, reviewer-triple status, bundle absorption gate), not calendar.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap** per `CLAUDE.md` Mandatory References list. Read in order: WAVE_EXECUTION_PIPELINE → Inventory_Index → README → Lean Development Optimization → Aristotle reference doc.
> 2. **Read this roadmap end-to-end** before claiming any wave assignment.
> 3. **Critical predecessor modules — read source directly:**
>    - `lean/SKEFTHawking/FirstOrderKMS.lean` (Phase 1) — the productive-value anchor for 6n.1.
>    - `lean/SKEFTHawking/SakharovCriterion.lean` + Phase 6m Track C JTGR modules — substrate for 6n.7.
>    - `lean/SKEFTHawking/Substrate/HeatKernel.lean` + Phase 6e a_n / Phase 5z Goldstino content — substrate for 6n.η AS memo.
>    - `Lit-Search/_Exploratory/Phase 6n+ Foundational Backing Assessment- Non-Equilibrium Fluctuation Theorems and Stochastic Thermodynamics, Formally Verified.md` — the original G10 DR; §5 has the Glorioso-Liu theorem-signature sketch for 6n.1; §7 has the Crooks-on-analog-Hawking framing for 6n.3; §8 has the Sakharov ↔ horizon-Crooks structure for 6n.7.
>    - `Lit-Search/_Exploratory/Appendix- Re-assessment of Deferred Tracks for SK_EFT_Hawking Phase 6n+.md` — the calibration-rule appendix; QCrooks-α track structure §5; Itô deferral analysis §3.
>    - `Lit-Search/_Exploratory/Resurgence Theory and Schwinger–Keldysh EFT.md` — substrate for 6n.α.
>    - `Lit-Search/_Exploratory/SymTFT, Higher-Form, and Non-Invertible Symmetries Applied to the SK-EFT Hawking Program- A Structural Audit.md` — substrate for 6n.β; arXiv:2507.05350 (Schäfer-Nameki et al.) is the primary-source-audit target.
>    - `Lit-Search/_Exploratory/Atiyah–Singer Index Theorems as a Unifying Organizational Tool .md` — substrate for 6n.η.
>    - `Lit-Search/_Exploratory/On-Shell Methods, Soft Theorems, and Spinor-Helicity Amplitudes for Dissipative Emergent Gauge : Gravity Sectors.md` — out-of-scope for Phase 6n (deferred to Phase 6o); read only if the wave's natural extension brushes against it.
> 4. **`LATE_PHASE6_ABSORPTION_PROTOCOL.md` — load before any bundle-touching work.** Each Phase 6n wave's bundle absorption is pre-classified below as D.2 / D.3 / D.4 per the protocol's branch decision matrix. **Two waves carry mandatory user-authorization gates before drafting starts:** 6n.γ (Phase 1 FirstOrderKMS reframing in I1) and 6n.ζ (Phase 6e + 6m JTGR reformulation in D3 + L3).
> 5. **Apply preemptive-strengthening checklist** per `WAVE_EXECUTION_PIPELINE.md` Stage 3a + the five questions in `CLAUDE.md` "Preemptive-strengthening discipline" section. Do not skip the post-wave ruthless review either.
> 6. **Do not delegate Lean theorem proving to subagents.** MCP loop is the default tooling. Aristotle is fallback only after MCP-loop exhaustion + decomposition + user authorization.
> 7. **Bundle source freshness:** every wave that ships content into a drafted bundle must close with `validate.py --check bundle_source_freshness` re-run + Stage F reviewer-triple re-invocation per `LATE_PHASE6_ABSORPTION_PROTOCOL.md` Stage F.
> 8. **No PM / time estimates** anywhere — by user direction. Ship status by content state.

---

## Wave catalog — Shape D (Session-3 finalized)

Seven waves, two threads. Five core tracks run in parallel (no inter-dependencies until reformulation closures). Two reformulation closures run after their substrates close.

| Wave | Codename | Substrate gap | Bundle absorption | Branch | User-auth gate |
|---|---|---|---|---|---|
| **6n.α** | G2 Resurgence | Resurgence on SK-EFT gradient expansion | D1 §3-§4 (additive new section "Non-perturbative content of the SK-EFT") | **D.2** | none |
| **6n.β** | G9 SymTFT audit + GD-4-factor sketch | Categorical / higher-form / non-invertible symmetry compression | D2 + D3 + D5 + F (additive cross-bridge sections) | **D.2** | none |
| **6n.γ** | G10-6n.1 Glorioso-Liu axiomatic | SK-EFT axiomatic skeleton in Lean | D3 + L3 + I1 (refines FirstOrderKMS Phase 1 case study) | **D.3** | **YES — pre-draft I1 reframing for user review** |
| **6n.δ** | G10-QCrooks-α | Productive-value Aristotle wave on quantum-Crooks axiomatizations | D1 cross-bridge / D5 (additive refutation tableau) | **D.2** | none |
| **6n.ε** | G10-6n.3 Crooks-on-analog-Hawking | New falsifiable IR constraint on analog-Hawking spectrum | E1 + D1 (additive falsification window + cross-bridge) | **D.2** | none |
| **6n.ζ** | G10-6n.7 Sakharov ↔ horizon-Crooks | Phase 6e + 6m Track C JTGR reformulation as one fluctuation-theorem result | D3 + L3 (refines Phase 6e biconditional + Phase 6m Track C published claim profile) | **D.3** | **YES — pre-draft D3/L3 reframing for user review** |
| **6n.η** | G8-W1 AS memo (no Lean) | Heat-kernel ↔ Atiyah-Singer ↔ Bär-Strohmaier APS dictionary, physics-paper-grade memo | D2 + D3 + E1 appendix (re-reading; no prior verdict overturned) | **D.2** | none |

**Wave dependencies:**
- 6n.α / 6n.β / 6n.δ / 6n.ε / 6n.γ are independent — can run in any order, in parallel.
- 6n.ζ (Sakharov ↔ horizon-Crooks reformulation) depends on **6n.γ** (Glorioso-Liu axiomatic) closing first — its statement reads off the SKEFTAxioms typeclass.
- 6n.η (AS memo) is documentation-grade; it can run any time but is most coherent after 6n.β (which compresses anomaly content into SymTFT objects that the AS memo's index-theorem dictionary connects to).
- 6n.ε (Crooks-on-analog-Hawking) does not strictly depend on 6n.γ closing, but its theorem-statement form should follow 6n.γ's path-measure infrastructure to avoid divergent typeclass shapes.

Recommended start order (per Session-3 quality-priority criteria): **6n.γ + 6n.α + 6n.β in parallel**, since 6n.γ unblocks 6n.ζ and 6n.ε downstream. 6n.δ and 6n.η can join the parallel slate once their respective substrates are loaded into context.

---

## Wave 6n.α — G2 Resurgence on SK-EFT gradient expansion

**Three-question template (per `CLAUDE.md` Phase-6 wave format):**

- *Integrates with:* `formulas.py` SK-EFT gradient expansion (δ_disp, δ_diss, δ^(2), δ^(3)); D1 §3-§4 analog-Hawking spectrum content; the WKB chain (exact connection-formula machinery already shipped); Mathlib's existing analytic-continuation + asymptotic-series infrastructure.
- *New constraint adds:* (a) an all-orders bridge from EFT to substrate via Borel-transform singularity structure; (b) rigorous breakdown frequency for the analog Hawking spectrum (where the gradient expansion stops converging); (c) Λ_UV = κ√A from IR coefficients alone (Λ_UV from the Borel singularity at action A). First-mover on SK-EFT resurgence in any proof assistant. Optional small Mathlib4 PR for `borelTransform` if the proof-side cleanly factors.
- *Tension surfaces:* if the SK-EFT gradient expansion has Borel-summable structure with no non-perturbative singularities at the orders δ^(4)–δ^(7) the program can compute, the all-orders bridge produces no new substrate-level constraint and the wave degrades to "we computed two more orders of the gradient expansion." If genuine resurgence structure is present (expected per Aniceto-Başar-Schiappa physics canon), Λ_UV-from-IR is the deliverable.

**Substrate.** Resurgence theory (Écalle / Aniceto-Başar-Schiappa) applied to SK-EFT. δ^(4)–δ^(7) symbolic generation; Padé-Borel approximants; Borel-plane singularity extraction; Λ_UV identification.

**Stage 1 actions:**
- Generate δ^(4)–δ^(7) symbolic coefficients from `formulas.py` extension; add Lean theorem stubs in a new `SKEFTHawking/Resurgence/` module.
- State the Borel-transform predicate as a typeclass-parameterized predicate over the gradient-expansion coefficient sequence.
- Identify the Borel-plane singularity structure expected per Aniceto-Başar-Schiappa.
- Cross-check via the lattice RHMC infrastructure where applicable.

**Bundle absorption.** D.2 additive into D1 §3-§4 (new section: "Non-perturbative content of the SK-EFT — a resurgence reading"). Cross-bridge to E1 + E2 if the breakdown frequency lands inside experimental sensitivity windows.

**Risk axes.** Borel-summability assumption; Padé-Borel approximant ringing; Mathlib analytic-continuation gaps; Λ_UV identification ambiguity if multiple Borel singularities compete.

---

## Wave 6n.β — G9 SymTFT primary-source audit + GD-4-factor decomposition sketch

- *Integrates with:* Phase 5o W5 lean-tensor-categories library (114 thms; Pivotal → ... → Modular); the program's ℤ₁₆ + modular invariance (`24 | c₋ → N_f = 3`) anchor in D2 / L2; Phase 5y GD-orthogonality 4-factor decomposition in D5; arXiv:2507.05350 (Schäfer-Nameki et al., Choi-doubled mixed-state SymTFT, July 2025) as the load-bearing primary-source audit target; arXiv:1511.03646 Crossley-Glorioso-Liu (CGL).
- *New constraint adds:* (a) primary-source audit of arXiv:2507.05350 vs CGL — does the Choi-doubled mixed-state SymTFT framework apply to the dissipative SK-EFT contour, and if so, which Z₂ in the IR effective theory does the SymTFT pick out; (b) lift Z₁₆ / θ̄ + 24|c₋ + topological-order content into one categorical object via the audit's framework; (c) **GD-orthogonality 4-factor → SymTFT decomposition sketch** — the highest-leverage open structural problem flagged by the DR. If the GD 4 factors decompose cleanly inside one SymTFT, the program's anomaly content compresses into a single object instead of four parallel orthogonality-decomposition factors.
- *Tension surfaces:* if the Choi-doubled mixed-state SymTFT does NOT apply to dissipative SK-EFT (e.g., the Choi-doubling assumes unitary evolution at higher categorical level), the audit returns a structural NO-GO that joins the program's no-go landscape — also publishable. If the GD 4-factor decomposition does NOT lift cleanly into one SymTFT, the wave produces a sketch + identified obstruction; partial result.

**Substrate.** SymTFT / higher-form / non-invertible symmetry literature (Bhardwaj-Schäfer-Nameki line). Primary-source target arXiv:2507.05350. Existing program's lean-tensor-categories library as the formalization substrate.

**Stage 1 actions:**
- Read arXiv:2507.05350 in full; extract the categorical structure (3-category? Choi-doubled tensor category?).
- Audit applicability to CGL SK-EFT contour. Decision: applicable / not-applicable / partially-applicable.
- If applicable: state the SymTFT predicate in `SKEFTHawking/SymTFT/Audit.lean`; lift Z₁₆ + 24|c₋ + topological-order naturally.
- GD-4-factor decomposition sketch (paper-math first; Lean stubs as scoping permits).

**Bundle absorption.** D.2 additive into D2 (Z₁₆ + modular content recompressed) + D3 (cross-bridges to gravity content) + D5 (GD-4-factor sketch) + F (single-categorical-object framing for the flagship's §2 architecture statement).

**Risk axes.** Choi-doubled mixed-state SymTFT may be too new to apply confidently; primary-source audit may flip applicability under deeper read; GD-4-factor decomposition sketch may surface obstruction rather than compression.

---

## Wave 6n.γ — G10-6n.1 Glorioso-Liu axiomatic skeleton

**🚨 USER AUTHORIZATION GATE (D.3 absorption — Stage B of `LATE_PHASE6_ABSORPTION_PROTOCOL.md`):**

I1's Phase 1 FirstOrderKMS case study is the program's anchor productive-value example. The 6n.γ reframing converts "Aristotle disproved 5/9" → "Aristotle disproved 5/9; deeper Glorioso-Liu axiomatic was formalized; the 5/9 disproof became a theorem of first/second-order separation." This substantially strengthens the case study but changes I1's framing. **Pre-draft the I1 reframing language for user review BEFORE shipping 6n.γ.**

D3 + L3 also absorb under D.3 (citation form on Glorioso-Liu monotonicity now points to the formalized `Glorioso_Liu_local_second_law` rather than the published derivation alone). D3 + L3 absorption is incremental enough that user-auth at the I1 review point covers all three.

**Three-question template:**

- *Integrates with:* Phase 1 FirstOrderKMS productive-value case study (Aristotle disproof of 5 of 9); existing program SK-EFT modules (`KMSCompatible`, `FDTCompatible`, `GloriosoLiuMonotoneCompatible` typeclasses); Glorioso-Crossley-Liu II classical-limit axiomatic (arXiv:1701.07817) as the cleanest target.
- *New constraint adds:* a clean axiomatic statement of the SK-EFT primitive (six axioms: SK-1 closed-time-path + SK-2 largest-time/unitarity + SK-3 reflection positivity / Im S ≥ 0 + SK-4 hermiticity + KMS-dyn dynamical KMS Z₂ symmetry + LE local equilibrium); typeclass-parameterized `DynamicalKMS [uv : UVRealization]` per Jain-Kovtun arXiv:2309.00511 UV-ambiguity; the local second-law theorem as `∂_μ J^μ_S ≥ 0 pointwise`; recovery of the FirstOrderKMS 4-of-9 partition as first-order/second-order separation of the dynamical-KMS axiom. Lifts Phase 1 productive-value finding from "axiom disproof" to "axiom replaced by deeper structure that explains the disproof."
- *Tension surfaces:* if the 4-of-9 partition does NOT recover cleanly (the disproof was deeper than first-order/second-order separation), the failure mode is itself a publishable productive-value finding. If the LE axiom does not admit a sharp Lean predicate that aligns with existing program hydrodynamic typeclasses, the formalization either trivializes the main theorem (LE too weak) or excludes legitimate program content (LE too strong); both are recoverable via predicate-design iteration.

**Substrate.** Glorioso-Crossley-Liu axiomatic (arXiv:1511.03646 / 1612.07705 / 1701.07817). Classical-limit form recommended (Glorioso-Crossley-Liu II) — significantly easier than the full quantum form. Discrete-time / formal-power-series scope (continuous-time corollaries deferred to post-Phase-6o-Itô).

**Stage 1 actions:**
- Read Glorioso-Crossley-Liu I + II + Jain-Kovtun arXiv:2309.00511 in full directly (do not delegate to subagents — per CLAUDE.md rule on Phase-5 deep-research depth-reading).
- Draft `SKEFTAxioms` structure in `lean/SKEFTHawking/GloriosoLiu/Axioms.lean` with six fields.
- Draft `DynamicalKMS [uv : UVRealization]` typeclass-parameterized family.
- Sharp Lean predicate for `LocalEquilibrium` parameterized over conservation pattern.
- Aristotle-probe the conjunction of the six axioms for inconsistency before stating the main theorem.

**Module decomposition (proposed):**
```
SKEFTHawking/GloriosoLiu/
  Axioms.lean              -- the 6-field SKEFTAxioms structure
  DynamicalKMS.lean        -- typeclass + UV-realization-indexed family
  LocalEquilibrium.lean    -- LE axiom + slow-mode infrastructure
  EntropyCurrent.lean      -- existence + Noether construction
  LocalSecondLaw.lean      -- ∂_μ J^μ_S ≥ 0 main theorem
  OnsagerReciprocity.lean  -- off-diagonal-symmetry derivation
  FirstOrderProjection.lean -- recovers FirstOrderKMS as first-order theorem
  Phase1Reconciliation.lean -- 4-of-9 partition recovery proof
```

**Bundle absorption.** D.3 into I1 (anchor case study reframe — user-auth REQUIRED pre-draft). D.3 incidentally into D3 + L3 (Glorioso-Liu citation form upgraded). All three covered by the same user-auth gate at I1.

**Risk axes** (numbered per Session-3 walkthrough):
1. Axiom inconsistency surfaced by Aristotle (low / high if hits — but publishable as productive-value).
2. Jain-Kovtun UV-ambiguity deeper than typeclass handles (medium / medium).
3. LE axiom too vague (medium / medium — predicate-design iteration).
4. SK-3 reflection positivity edge cases at IR (low / low-to-medium — measure-theoretic carve-out via "a.e." weakening).
5. Onsager reciprocity hides implicit assumption (medium / low-to-medium — surfaces as a finding either way).
6. 4-of-9 partition fails to recover cleanly (medium / medium-to-high — most directly publishable failure mode).
7. Sign-convention drift (low / low — pick GCL II convention explicitly).
8. Continuous-time framing limited until Itô lands (high / low — scope explicitly to discrete-time / formal-power-series).
9. D.3 absorption cascade across D3 + L3 + I1 (high / medium — pre-draft mitigates).
10. Published commitment to the axiom set (certain / medium long-term — name "Glorioso-Crossley-Liu axiomatic" not "the SK-EFT axiomatic").

---

## Wave 6n.δ — G10-QCrooks-α productive-value Aristotle wave

- *Integrates with:* Phase 1 FirstOrderKMS template (parallel-axiomatization Aristotle refutation tableau); the program's MTC / quantum-group / fusion-category infrastructure (operator-algebra typing for TPM, work distributions, Petz recovery, quasiprobabilities); QCyc16 / QCyc5Ext / native_decide finite-dimensional sandboxes; existing `KMSCompatible` / `FDTCompatible` / `GloriosoLiuMonotoneCompatible` typeclasses; Perarnau-Llobet-Bäumer-Hovhannisyan-Huber-Acín no-go theorem (Phys. Rev. Lett. 118, 070601, 2017).
- *New constraint adds:* (a) parallel-axiomatization tableau across at least four candidate quantum-Crooks axiomatizations — Tasaki-Crooks (Talkner-Hänggi 2007 arXiv:0705.1252) + Åberg fully-quantum (Phys. Rev. X 8, 011019, 2018) + Kafri-Deffner (Phys. Rev. A 86, 044302, 2012) + a quasiprobability axiomatization (Levy-Lostaglio or Francica); (b) Aristotle-driven concrete-witness search for finite-dimensional Hilbert-space counterexamples to each candidate's claimed equivalence with classical Crooks on diagonal states + average energy reproduction (the Perarnau-Llobet et al. no-go scheme); (c) the surviving axiomatizations connected to existing `KMSCompatible` / `FDTCompatible` content via typeclass hypothesis-bundle compatibility lemmas. **FirstOrderKMS² template** — the literature is more axiomatically unstable for quantum-Crooks than for first-order KMS; the program's Phase 1 productive-value methodology applies directly.
- *Tension surfaces:* if Aristotle finds zero refutations across the four candidate axiomatizations, the wave degrades to "we mapped the axiom space and stated the consistency relations" — still publishable but at lower yield. The Perarnau-Llobet et al. no-go theorem guarantees that *at least one* candidate must fail in any unified framework, so the expected refutation count is ≥ 1.

**Substrate.** Quantum-thermodynamics literature (Tasaki-Crooks / Åberg / Kafri-Deffner / Levy-Lostaglio quasiprobability). Perarnau-Llobet et al. no-go theorem as the structural anchor. Program's MTC / quantum-group infrastructure as the linear-algebra / operator-algebra typing.

**Stage 1 actions:**
- State Tasaki-Crooks for finite-dim discrete-spectrum H in `SKEFTHawking/QuantumCrooks/Tasaki.lean`.
- State Perarnau-Llobet et al. no-go as a parameterized obstruction in `SKEFTHawking/QuantumCrooks/PerarnauLlobet.lean`.
- State Åberg, Kafri-Deffner, and one quasiprobability axiomatization in parallel (one module each).
- Aristotle-probe each candidate's claimed equivalence with classical Crooks on diagonal states using QCyc16 / native_decide finite-dimensional sandboxes.
- Publish the refutation tableau as a productive-value paper at the FirstOrderKMS scale.

**Bundle absorption.** D.2 additive into D1 cross-bridge / D5 (refutation tableau as a section).

**Risk axes.** Aristotle returns no refutation (low — Perarnau-Llobet bounds ≥ 1); quasiprobability axiomatization choice (Levy-Lostaglio vs Francica) may not span the literature's full axiom-space (medium — name it explicitly + flag); the productive-value paper venue varies on whether the refutation tableau is "FirstOrderKMS template" or "novel". Aristotle is *not* the load-bearing tool for 6n.γ but IS for 6n.δ — submission gating per CLAUDE.md "User gets first & last call on Aristotle submissions."

---

## Wave 6n.ε — G10-6n.3 Crooks-on-analog-Hawking on polariton SK-EFT substrate

- *Integrates with:* E1 polariton paper; D1 §3-§4 analog Hawking content; Carusotto-Gerace polariton analog black-hole literature (arXiv:1206.4276 + follow-ups); Steinhauer BEC analog black holes; Tettamanti-Parola-Cacciatori arXiv:1703.05041 exactly-solvable BEC; **Loganayagam-Martin Exterior EFT for Hawking Radiation arXiv:2403.10654** (JHEP 2025) — the cleanest substrate for trajectory-Crooks at the horizon; Banerjee et al. fluctuation-dissipation horizon-temperature derivation (Eur. Phys. J. C 80, 411, 2020) as the FDT-level prior art.
- *New constraint adds:* an inequality on the analog-Hawking spectrum derived from trajectory-level Crooks detailed-balance, **beyond what FDT / Kubo gives**. Specifically: the LDP rate function I(σ) for entropy production must satisfy the GC/LS symmetry I(-σ) - I(σ) = -σ, which translates into specific bounds on the spectrum's higher cumulants of work / entropy-production fluctuations. Falsifiable on existing experimental platforms (Steinhauer BEC, Weinfurtner Vancouver surface-wave, Carusotto polariton). Comparable in character to Phase 6e Sakharov biconditional — third "Sakharov-style" biconditional in the program if non-trivial.
- *Tension surfaces:* the DR's main flag — "if the inequality is satisfied trivially given the existing thermal spectrum, the contribution is FDT-level only and not novel." The work itself is *deriving* what trajectory-Crooks structure constrains beyond FDT; the output of the derivation determines (a) trivial = formalization-only contribution, or (b) non-trivial = third Sakharov-style biconditional + falsifiable predictions.

**Substrate.** Two viable framings:
- (a) Glorioso-Crossley-Liu SK-EFT effective action as the path measure (closer to existing program infrastructure; uses 6n.γ as substrate).
- (b) Loganayagam-Martin exterior EFT for Hawking radiation (cleanest framework for trajectory-Crooks at the horizon specifically).

DR recommends (b) on top of (a): state the trajectory-Crooks predicate on Loganayagam-Martin exterior EFT; derive the inequality; verify it specializes correctly to the program's existing SK-EFT polariton content.

Discrete-time / Markov-jump-process scope (Falasco-Esposito 2025 RMP framework) — sufficient for falsifiability on Steinhauer / Weinfurtner / Carusotto. Continuous-time form deferred to post-Phase-6o-Itô.

**Stage 1 actions:**
- Read Loganayagam-Martin arXiv:2403.10654 in full directly.
- Draft `AnalogHawkingSubstrate` typeclass + `TrajectoryCrooksAtHorizon` predicate.
- Derive the inequality on the spectrum (paper math first; Lean theorem statement second).
- Specialize to Steinhauer / Weinfurtner / Carusotto device parameters; check against published spectrum + noise data.
- Add E1 falsification-window section.

**Bundle absorption.** D.2 additive into E1 (new section: "Trajectory-level Crooks constraint at the analog horizon"). D.2 cross-bridge into D1 only after 6n.γ closes (theorem-statement form follows 6n.γ's path-measure infrastructure).

**Risk axes.** Triviality risk (DR's main flag); continuous-vs-discrete-time framing (Markov-jump sufficient for falsifiability; cleaner version waits for Itô); Verlinde-Nagle contamination (Lean statements must invoke only Glorioso-Liu / Loganayagam-Martin substrate, not Verlinde — analogous discipline to 6n.ζ); open-vs-closed-system framing (Loganayagam-Martin exterior EFT is open; CGL is closed; cross-walk lemma needed); substrate-specific verifiability variance.

---

## Wave 6n.ζ — G10-6n.7 Sakharov ↔ horizon-Crooks reformulation

**🚨 USER AUTHORIZATION GATE (D.3 absorption — Stage B of `LATE_PHASE6_ABSORPTION_PROTOCOL.md`):**

D3 + L3 currently express the Phase 6e Sakharov-criterion biconditional and the Phase 6m Track C JTGR survivors as separate results. The 6n.ζ reformulation unifies them as one fluctuation-theorem result (`Sakharov_iff_horizon_Crooks` biconditional). This refines D3 + L3's published-claim profile — same content, deeper structural framing. **Pre-draft the D3 + L3 reframing language for user review BEFORE shipping 6n.ζ.**

**Wave dependency:** 6n.ζ blocks on 6n.γ (Glorioso-Liu axiomatic) closing first.

- *Integrates with:* Phase 6e Sakharov-criterion biconditional (Λ_J = Λ_HK on ³He-A; falsified on FLS BEC); Phase 6m Track C JTGR survivors (M1, M2/M7, M3 Exp/ArcTanh, M4, M9; M8 conditional); Eling-Guedens-Jacobson f(R) (gr-qc/0602001) entropy-production term; Chirco-Eling-Liberati gravitational-dissipation (PRD 81, 024016) heat decomposition; Alonso-Serrano + Liška unimodular-from-Clausius (arXiv:2008.04805); 6n.γ Glorioso-Liu axiomatic substrate.
- *New constraint adds:* Sakharov criterion expressed as horizon-Crooks-detailed-balance (`P_F[γ] / P_R[γ̄] = exp(σ[γ])` at the local Rindler horizon); unifies Phase 6e biconditional + Phase 6m Track C JTGR survivors as one fluctuation-theorem result; **explicitly distinguishes Jacobson-allowed (equilibrium-Clausius-on-Rindler-horizon) from Verlinde-falsified (gravity-as-entropic-force) entropic-gravity readings**. Cleanest non-trivial deliverable in any Phase 6n track per the original DR.
- *Tension surfaces:* if the reformulation requires assumptions stronger than what Phase 6e + Phase 6m JTGR currently invoke, those extra assumptions become candidate sites for elimination-tournament probing. The Verlinde caveat is real: "fluctuation-theorem structure is present at the horizon (Jacobson level), not gravity *is* an entropic force (Verlinde level)" — this distinction must be carried through every Lean statement and bundle citation.

**Substrate.** Phase 6e Sakharov + Phase 6m Track C JTGR + Glorioso-Liu axiomatic (6n.γ). Re-reading: not new derivation. Sakharov-class assignment from Phase 6m R5 (M1 + M9 in Sakharov-class; M2/M7 with epistemic flag; M3 in class-(b′); M4 in class-(b″); M8 OUTSIDE Sakharov-class).

**Stage 1 actions (after 6n.γ closes):**
- State `HorizonDetailedBalance` predicate parameterized over the substrate.
- State `Sakharov_iff_horizon_Crooks` biconditional theorem.
- Specialize to Phase 6e biconditional witnesses (³He-A holds; FLS BEC fails).
- Specialize to Phase 6m Track C JTGR survivors (verifies which class-(b/b′/b″) survivor admits horizon-Crooks reading).
- Pre-draft D3 + L3 reframing language for user-auth gate.

**Bundle absorption.** D.3 into D3 + L3 (refines biconditional + JTGR survivors' published-claim profile). User-auth REQUIRED pre-draft.

**Risk axes.** Reformulation may surface stronger-than-current assumption (publishable as elimination-tournament target either way); Verlinde-vs-Jacobson distinction must not slip in any single Lean theorem statement (compositional discipline); 6n.γ blocks delays 6n.ζ start; D.3 absorption cascade across D3 + L3.

---

## Wave 6n.η — G8-W1 Atiyah-Singer reformulation memo (no Lean)

- *Integrates with:* Phase 6e a_n Seeley-DeWitt heat-kernel coefficients (Λ_HK derivation); Phase 6m Sakharov tr(I) ≠ 0 (the McKean-Singer supertrace nonvanishing condition); Phase 5z Goldstino zero modes (the APS boundary kernel `h(Σ)`); Bär-Strohmaier APS-index-theorem framework; Witten-Yonekura η-invariant content.
- *New constraint adds:* a physics-paper-grade memo (no Lean) restating Phase 6e a_n + Phase 6m Sakharov tr(I) + Phase 5z Goldstino zero modes in Atiyah-Singer / Bär-Strohmaier APS / Witten-Yonekura η-invariant language. The heat-kernel ↔ Atiyah-Singer dictionary is **already implicit** in the program; the memo makes it explicit. Free Tier-1 deliverable. Unlocks D2 / D3 / E1 appendix narratives at zero Lean cost.
- *Tension surfaces:* if the reformulation surfaces a *new* topological-invariant statement that is not implicit in the existing program content, the memo upgrades to a Lean-formalization wave (deferred to Phase 6o or later as G8-Lean-refactor opening). Likely: the memo stays as a memo. The *full* Mathlib Atiyah-Singer formalization is a multi-year community-coordination effort and stays deferred indefinitely.

**Substrate.** Existing program a_n + tr(I) + Goldstino content. Bär-Strohmaier *Index Theorems and Spectral Geometry* + Witten-Yonekura η-invariant literature as the reformulation framework.

**Stage 1 actions:**
- Draft memo at `temporary/working-docs/phase6n_AS_reformulation_memo.md` (~10-15 pages physics-paper-grade).
- Cross-reference Phase 6e a_n / Phase 6m Sakharov / Phase 5z Goldstino sections.
- Identify any *new* topological-invariant statement (if surfaces, deferred to Phase 6o).
- Add D2 / D3 / E1 appendix sections that reference the memo.

**Bundle absorption.** D.2 additive into D2 + D3 + E1 appendix (re-reading; no prior verdict overturned, no published-claim profile change). No user-auth required.

**Risk axes.** Memo format vs Lean-formalization split (low — explicitly scoped as memo); reformulation surfaces new content (low — known dictionary, low novelty risk); Lean refactor temptation (high — discipline against scope creep).

---

## User authorization gates — consolidated

Two D.3 user-auth gates per `LATE_PHASE6_ABSORPTION_PROTOCOL.md` Stage B:

| Wave | Bundle(s) refined | Pre-draft deliverable for user review |
|---|---|---|
| **6n.γ** Glorioso-Liu axiomatic | I1 (anchor case study reframe) + D3 + L3 (citation form upgrade) | I1 reframing language; specifically: "FirstOrderKMS as Phase 1 anchor → first-order projection of Glorioso-Liu axiomatic; the 4-of-9 partition is now a theorem, not an Aristotle-empirical observation." |
| **6n.ζ** Sakharov ↔ horizon-Crooks | D3 + L3 (Phase 6e + Phase 6m Track C JTGR survivors unified) | D3 + L3 reframing language; specifically: "Phase 6e Sakharov biconditional + Phase 6m Track C JTGR survivors as parallel results → unified `Sakharov_iff_horizon_Crooks` biconditional. Verlinde-vs-Jacobson distinction explicit at every Lean statement." |

**Additional gates (standard per `WAVE_EXECUTION_PIPELINE.md`):**
- Stage 4 Aristotle submission (6n.δ QCrooks-α specifically) — user gets first and last call.
- Stage 13 adversarial review per absorbed bundle — fresh-context reviewer per `BUNDLE_LIFT_PROCEDURE.md` §11.
- I3 bundle authorization (Phase 6o, deferred to that roadmap) — Pipeline Invariant #14 user-auth for new bundle target.

---

## Phase 6o handoff (preview — full detail in `Phase6o_Roadmap.md` stub)

Tracks deferred to Phase 6o per Session-3 quality-priority:
- **G3 boostless / Carrollian soft-theorem program** for emergent post-erasure U(1) + ADW graviton (Tier 1).
- **G4-Kerr-Schild** classical double-copy on Petrov-D analog metrics (the draining-bathtub acoustic metric IS Petrov D; Tier 2).
- **G1-Schellekens chain** (spin-bordism → anomaly polynomial → modular invariance → Niemeier → Schellekens c=24 holomorphic-VOA classification corollary; Tier 1).
- **G1-NO-GO writeup** (dissipative SK-EFT bootstrap can't produce uniqueness with current axioms; Tier 4 NO-GO).
- **G10-ETH-α** productive-value Aristotle wave on Inozemcev–Volovich gap (Tier 2).
- **G10-Itô + LDP-α + LDP-β as I3 community contribution** (pending Pipeline Invariant #14 user-auth for new bundle target).

Phase 6o framing locks at the next user-input gate (after Phase 6n closes, or earlier if Phase 6n waves run in parallel and Phase 6o needs to start before Phase 6n closure).

---

## Cross-references

- `temporary/working-docs/brainstorm/20260504-GUToE/Phase6n-6z-GUToE-Brainstorm_1.md` — full session record (Sessions 1, 2, 3); decisions log; deep-research dispatch table.
- `Lit-Search/_Exploratory/` — 8 deep-research returns (Sessions 2 inputs).
- `Lit-Search/_Exploratory/Appendix- Re-assessment of Deferred Tracks for SK_EFT_Hawking Phase 6n+.md` — calibration rule + 3-of-4 reversal recommendations on G10 deferred tracks.
- `docs/PAPER_STRATEGY.md` — 13-bundle architecture (note: §2 headline says "eleven publication targets" while the rest treats 13; minor doc drift to be corrected at I3 authorization or earlier).
- `docs/PAPER_DRAFT_MAPPING.md` — per-source → per-bundle mapping; new rows added per Phase 6n wave at Stage 12.
- `docs/BUNDLE_LIFT_PROCEDURE.md` — frozen 14-step canonical lift workflow.
- `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` — frozen Stage A–G robustness protocol; D.2 / D.3 / D.4 branch decision matrix.
- `docs/WAVE_EXECUTION_PIPELINE.md` — 14-stage process (canonical).
- `docs/agents/claims-reviewer-bundle-prompts.md` — per-bundle Stage-13 anchor list (consumed by Stage F reviewer-triple re-invocation).
- `docs/ARCHITECTURE_SCOPE.md` — predictive-scope boundary; Phase 6n updates the SK-EFT-axiomatic section + the Crooks-on-analog-Hawking falsifiability content.
- `docs/roadmaps/Phase7_Roadmap.md` — Phase 7 umbrella (16 waves; 7 sub-phases 7a–7g).
- `docs/roadmaps/Phase7a_Roadmap.md` — Phase 7a sub-roadmap (Phase 6m closure + Phase 7 Wave 0 + I1 + I2 + robustness infrastructure).
- `docs/roadmaps/Phase6m_Roadmap.md` — predecessor phase; format reference.
- `docs/roadmaps/Phase6o_Roadmap.md` — successor phase stub.

---

*Created Phase 6n initialization (2026-05-04). Roadmap initialized; first wave dispatch pending user confirmation of Shape D + I1 reframing pre-draft for 6n.γ user-auth gate. Updates atomically as waves close.*
