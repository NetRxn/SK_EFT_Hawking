# Phase 6n: SK-EFT Foundational Backing + Structural Compression — First-Mover Tracks

## Technical Roadmap — May 2026

*Prepared 2026-05-04 | **New phase, structurally parallel to Phase 6m.** Sources: `temporary/working-docs/brainstorm/20260504-GUToE/Phase6n-6z-GUToE-Brainstorm_1.md` (Session 1 + Session 2 + Session 3 synthesis); 8 deep-research returns at `Lit-Search/_Exploratory/`; the G10 Appendix at `Lit-Search/_Exploratory/Appendix- Re-assessment of Deferred Tracks for SK_EFT_Hawking Phase 6n+.md` reversing 3-of-4 deferred sub-tracks; Itô-explore agent findings on Mathlib4 + Degenne brownian-motion repo state.*

**Trigger condition (no gate — autonomous):** Phase 6n can dispatch any time. It is independent of Phase 6m closure and runs in parallel with active Phase 7a–7g bundle work.

**Status (2026-05-05 Session 9 close):** Sessions 4–9 have shipped substantive Lean lifts across Wave 1a (Lean substrate + Path B numerical verdict + δ⁴–δ⁷ formulas + Path A Stage 1), Wave 1b (primary-source SymTFT audit + 4 stages of discrete-sector predicates and cross-bridges + **Session 9 cross-track unification via SecondOrderProjection**), Wave 1c (AS reformulation memo working doc), Wave 2a (Glorioso–Liu Lean skeleton + Stage 2–3 + Stage 2–3b KMS framework + R1 LIFTED + Session 7 load-bearing deepening + **Session 9 SecondOrderProjection extending SKEFTAxioms to second derivative order via SKEFTAxiomsExt**), Wave 2b (7 QuantumCrooks/ modules + parametric + concrete quantum no-go), Wave 2c (3 modules + Stage 2-3 substantive biconditional + **Stage 4 substrate-level GC bridge SHIPPED Session 8**), Wave 2d (substrate bundle + Bool-projection biconditional + **Stage 4 SKEFTHorizonBridge SHIPPED Session 7**), and I3 bundle infrastructure. **Session 9 (2026-05-05) — Wave 2a × Wave 1b cross-track unification SHIPPED:** new module `lean/SKEFTHawking/GloriosoLiu/SecondOrderProjection.lean` (9 substantive theorems + `SKEFTAxiomsExt` structure + 7 predicate defs) bridges Track 2 foundational (`SKEFTAxioms` on `SKAction`) to Track 1 structural (`KMSParityAlternationCompatible` on `SKActionExt`) via the substantive proof-body chain `SKEFTAxiomsExt → fullSecondOrder_uniqueness (Aristotle run c4d73ca8) → combined_positivity_constraint (Aristotle run c4d73ca8) → γ_{2,1}+γ_{2,2}=0 → KMSParityAlternationCompatible stage2Verdict`. Headline theorems: `combined_positivity_of_parity_zero` (converse of Aristotle's combined_positivity_constraint, establishing the biconditional `positivity_ext ↔ γ_{2,1}+γ_{2,2}=0`); `SKEFTAxiomsExt_for_combined_parity_zero` (substantive non-trivial existence witness with explicit 14-entry FullSecondOrderCoeffs embedding); `SKEFTAxiomsExt_yields_combined_uniqueness` (load-bearing projection); `SKEFTAxiomsExt_yields_parity_alternation` (load-bearing parity-alternation theorem); `SecondOrderProjection_bridges_to_KMSParityAlternation` (cross-track unification statement). Verlinde-vs-Jacobson distinction preserved at every Lean statement. Lake build 8535 → 8536 jobs clean (+1 SecondOrderProjection module). MCP-driven, zero Aristotle. Zero new axioms (only `propext, Classical.choice, Quot.sound`). **Session 8 (2026-05-05) — TWO substantive lifts:** (i) **Wave 2c Stage 4 GC bridge** new module `SKEFTGallavottiCohen.lean` (7 substantive theorems); (ii) **Wave 1b Stage 4c third cross-bridge** extending `SymTFTAudit/CrossBridges.lean` from 2 to 3 substantive bridges (closing Stage-4 asymmetry).

**User direction reaffirmed (2026-05-04 Session 5 close):** **Push forward on math/physics/infrastructure (6n + likely 6o) before drafting manuscripts or integrating into ≤ Phase 6m work.** Writing/verification overhead is non-trivial; the ≤ Phase 6m product surface is fairly stable. Bundle absorption (the D.2 / D.3 events listed below) is **deferred until the full Phase 6n + 6o picture lands**, at which point the absorption work runs as one coherent pass rather than incrementally per wave. The two D.3 user-auth pre-drafts (Wave 2a I1 reframing, Wave 2d D3+L3 reframing) **exist as working docs** at `temporary/working-docs/phase6n/` but are **on-hold for user review** — neither blocks further math/Lean work in Phase 6n.

**Entry state (2026-05-04 Inventory_Index snapshot):** ~5229 substantive theorems / ~243 modules / 0 sorry / 1 axiom. Phase 6m FULLY CLOSED at Lean-formalization scope (R1–R6 + strengthening + cross-module proof-chain). Phase 7 in flight: 13 of 13 bundles reviewer-triple-closed at GREEN (I1, I2, L1, L2, L3, D1, D2, D3, D4, D5, E1, E2, F); flagship F all-12-section draft shipped HEAD `9fabdc8` (Phase 7c close). Phase 7 in stable hold pending Phase 6n + 6o math closure per user direction.

**Anchors carried forward into Phase 6n:**
- `FirstOrderKMS` (Phase 1) — Aristotle 4-of-9 productive-value disproof; the anchor case study Phase 6n.1 lifts to "axiom replaced by deeper structure that explains the disproof."
- Phase 6e Sakharov-criterion biconditional (Λ_J = Λ_HK on ³He-A; falsified on FLS BEC) — substrate for Phase 6n.7's horizon-Crooks reformulation.
- Phase 6m Track C JTGR survivors (M1, M2/M7, M3 Exp/ArcTanh, M4, M9; M8 conditional) — Sakharov-class assignment carries into 6n.7.
- Phase 5o Wave 5 lean-tensor-categories library (Pivotal → Spherical → Balanced → Ribbon → Semisimple → Fusion → Modular; 114 thms) — substrate for Phase Wave 2a G9 SymTFT lift.
- `δ_disp / δ_diss / δ^(2) / δ^(3)` SK-EFT gradient-expansion coefficients in `formulas.py` — substrate for Phase Wave 1a G2 resurgence.
- Phase 6e a_n + Phase 6m Sakharov tr(I) + Phase 5z Goldstino zero modes — substrate for Phase Wave 1c G8-W1 AS memo (the heat-kernel ↔ Atiyah-Singer dictionary already implicit).
- `WAVE_EXECUTION_PIPELINE.md` 14-stage process; `BUNDLE_LIFT_PROCEDURE.md`; `LATE_PHASE6_ABSORPTION_PROTOCOL.md` (D.2 / D.3 / D.4 branches).

**Thesis.** Phase 6n loads the program's deepest unification-leverage tracks identified in the Session-1 conspicuous-gaps catalog and refined by Session-2 deep-research returns. **Two parallelizable Tracks ship 7 waves:**

- **Track 1 — Structural unification leverage** (3 waves): **Wave 1a** G2 Resurgence; **Wave 1b** G9 SymTFT audit; **Wave 1c** G8-W1 Atiyah-Singer reformulation memo. Compresses existing program content into deeper structural objects. First-mover where applicable.
- **Track 2 — Foundational backing for fluctuation-theorem content** (4 waves): **Wave 2a** G10-6n.1 Glorioso-Liu axiomatic; **Wave 2b** G10-QCrooks-α productive-value Aristotle wave; **Wave 2c** G10-6n.3 Crooks-on-analog-Hawking; **Wave 2d** G10-6n.7 Sakharov ↔ horizon-Crooks reformulation. Replaces FirstOrderKMS-class anchors with deeper axiomatic + adds new falsifiable IR constraints.

Downstream Phase 6o picks up the heavier tracks (G3 boostless-soft, G4-Kerr-Schild, G1 Schellekens chain + NO-GO writeup, G10-ETH-α, Itô + LDP-α/β as I3 community contribution pending user authorization).

**Naming-convention note (Session-5 rename).** Earlier working docs, brainstorm sessions, and memory entries refer to the same waves by Greek-letter labels. The Tracks/Waves convention here matches Phase 6m and is keyboard-friendly; the historical Greek labels remain in working docs at `temporary/working-docs/phase6n/` and in the MEMORY.md index. Cross-reference table:

| New label | Historical (Greek) | Codename |
|---|---|---|
| Wave 1a | 6n.α | G2 Resurgence |
| Wave 1b | 6n.β | G9 SymTFT audit + GD-4-factor |
| Wave 1c | 6n.η | G8-W1 Atiyah-Singer memo |
| Wave 2a | 6n.γ | G10-6n.1 Glorioso-Liu axiomatic |
| Wave 2b | 6n.δ | G10-QCrooks-α |
| Wave 2c | 6n.ε | G10-6n.3 Crooks-on-analog-Hawking |
| Wave 2d | 6n.ζ | G10-6n.7 Sakharov ↔ horizon-Crooks |

Sub-wave numbering (e.g., Wave 1a.1, 1a.2, 1a.3, 1a.4) replaces the Greek sub-wave labels (6n.α.1, etc.).

**Project rule reaffirmed (Session-3 user direction 2026-05-04):** **No PM / time / phase-cost estimates anywhere in this roadmap.** Track readiness by content state (sorry count, reviewer-triple status, bundle absorption gate), not calendar.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap** per `CLAUDE.md` Mandatory References list. Read in order: WAVE_EXECUTION_PIPELINE → Inventory_Index → README → Lean Development Optimization → Aristotle reference doc.
> 2. **Read this roadmap end-to-end** before claiming any wave assignment.
> 3. **Critical predecessor modules — read source directly:**
>    - `lean/SKEFTHawking/FirstOrderKMS.lean` (Phase 1) — the productive-value anchor for 6n.1.
>    - `lean/SKEFTHawking/SakharovCriterion.lean` + Phase 6m Track C JTGR modules — substrate for 6n.7.
>    - `lean/SKEFTHawking/Substrate/HeatKernel.lean` + Phase 6e a_n / Phase 5z Goldstino content — substrate for Wave 1c AS memo.
>    - `Lit-Search/_Exploratory/Phase 6n+ Foundational Backing Assessment- Non-Equilibrium Fluctuation Theorems and Stochastic Thermodynamics, Formally Verified.md` — the original G10 DR; §5 has the Glorioso-Liu theorem-signature sketch for 6n.1; §7 has the Crooks-on-analog-Hawking framing for 6n.3; §8 has the Sakharov ↔ horizon-Crooks structure for 6n.7.
>    - `Lit-Search/_Exploratory/Appendix- Re-assessment of Deferred Tracks for SK_EFT_Hawking Phase 6n+.md` — the calibration-rule appendix; QCrooks-α track structure §5; Itô deferral analysis §3.
>    - `Lit-Search/_Exploratory/Resurgence Theory and Schwinger–Keldysh EFT.md` — substrate for Wave 1a.
>    - `Lit-Search/_Exploratory/SymTFT, Higher-Form, and Non-Invertible Symmetries Applied to the SK-EFT Hawking Program- A Structural Audit.md` — substrate for Wave 1b; arXiv:2507.05350 (Schäfer-Nameki et al.) is the primary-source-audit target.
>    - `Lit-Search/_Exploratory/Atiyah–Singer Index Theorems as a Unifying Organizational Tool .md` — substrate for Wave 1c.
>    - `Lit-Search/_Exploratory/On-Shell Methods, Soft Theorems, and Spinor-Helicity Amplitudes for Dissipative Emergent Gauge : Gravity Sectors.md` — out-of-scope for Phase 6n (deferred to Phase 6o); read only if the wave's natural extension brushes against it.
> 4. **`LATE_PHASE6_ABSORPTION_PROTOCOL.md` — load before any bundle-touching work.** Each Phase 6n wave's bundle absorption is pre-classified below as D.2 / D.3 / D.4 per the protocol's branch decision matrix. **Two waves carry mandatory user-authorization gates before drafting starts:** Wave 2a (Phase 1 FirstOrderKMS reframing in I1) and Wave 2d (Phase 6e + 6m JTGR reformulation in D3 + L3).
> 5. **Apply preemptive-strengthening checklist** per `WAVE_EXECUTION_PIPELINE.md` Stage 3a + the five questions in `CLAUDE.md` "Preemptive-strengthening discipline" section. Do not skip the post-wave ruthless review either.
> 6. **Do not delegate Lean theorem proving to subagents.** MCP loop is the default tooling. Aristotle is fallback only after MCP-loop exhaustion + decomposition + user authorization.
> 7. **Bundle source freshness:** every wave that ships content into a drafted bundle must close with `validate.py --check bundle_source_freshness` re-run + Stage F reviewer-triple re-invocation per `LATE_PHASE6_ABSORPTION_PROTOCOL.md` Stage F.
> 8. **No PM / time estimates** anywhere — by user direction. Ship status by content state.

---

## Wave catalog — Shape D (Session-3 finalized; Session-5 status)

Seven waves across two parallelizable Tracks. Five core waves run in parallel (no inter-dependencies until reformulation closures); two reformulation closures (Wave 2c, Wave 2d) sequence after Wave 2a closes.

**Status legend:**
- ✅ **SHIPPED** — Lean / numerical / memo deliverables committed; bundle absorption deferred per Session-5 user direction.
- 🟡 **IN-PROGRESS** — partial deliverables shipped; remaining sub-stages identified.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft exists; no Lean yet.
- ⏳ **NOT STARTED** — substrate ready; awaiting dispatch.

| Wave | Codename | Status | Bundle absorption | Branch | User-auth gate |
|---|---|---|---|---|---|
| **Track 1 — Structural unification leverage** | | | | | |
| **Wave 1a** | G2 Resurgence | 🟡 **IN-PROGRESS** (1a.1 + 1a.2 + 1a.4 SHIPPED; 1a.3 Path-B verdict shipped; **1a.3 Path-A AUTHORIZED + Stage 1 skeleton SHIPPED Session 6**: `src/resurgence/bdg_self_energy.py` module + 9 tests (4 pass, 5 Stage-2+ skip-marked with literature-anchor citations) + working doc with Stage 2-5 sub-stage decomposition. Stage 2 next-up: γ_1 derivation via Beliaev 1958 LO scheme + cross-validation against literature anchor.) | D1 §3-§4 (additive) — **DEFERRED** | **D.2** | none |
| **Wave 1b** | G9 SymTFT audit + GD-4-factor sketch | 🟡 **IN-PROGRESS** (Stage 1+2+3+4 SHIPPED Session 6 + **Stage 4c third cross-bridge SHIPPED Session 8 (2026-05-05)**. Stage 4 ships 3 substantive predicate-level cross-bridges (was 2 of 3 in Session 6, now 3 of 3 — Session 8 closes the asymmetry): KMSParityAlternation ↔ SecondOrderSK γ_{2,1}+γ_{2,2}=0; Z16AnomalyEta ↔ Z16AnomalyCancels; **chiralCentralCharge ↔ GenerationConstraint.generation_constraint_iff** project-local Schellekens chain (sidesteps absent Mathlib Witt-group infrastructure via biconditional `3 ∣ n ↔ 24 ∣ 8·n`). Updated `stage4_discrete_sector_bridges_partition` from 2-of-3 to 3-of-3 substantive bridges. Stage 5 chiralCentralChargeMod24 ↔ full Witt-class **candidate Mathlib upstream-PR opportunity** retained per program's track record of in-program Mathlib-grade infrastructure builds.) | D2 + D3 + D5 + F (additive) — **DEFERRED** | **D.2** | none |
| **Wave 1c** | G8-W1 AS memo (no Lean) | ✅ **SHIPPED** (memo at `temporary/working-docs/phase6n/6n_eta_AS_reformulation_memo.md`; APS-η for analog horizons flagged as Phase 6o follow-up) | D2 + D3 + E1 appendix — **DEFERRED** | **D.2** | none |
| **Track 2 — Foundational backing for fluctuation-theorem content** | | | | | |
| **Wave 2a** | G10-6n.1 Glorioso-Liu axiomatic | ✅ **SHIPPED** (Stage-1 skeleton + Stage 2–3 substantive refactor + Stage 2–3b KMS framework refactor + R1 LIFTED; 8 GloriosoLiu/ modules. **Session 7 (2026-05-05) Stage 2-3b load-bearing deepening:** `entropy_current_exists` upgraded from trivial-discharge `⟨zeroEntropyCurrent, rfl⟩` to substantive Noether construction via `A.dynamical_KMS` extraction; `OnsagerReciprocity_from_KMS` upgraded from trivial-discharge `⟨0⟩` to substantive 9×9 diagonal embedding of the FDR-pinned 2×2 conductivity. Both make `A : SKEFTAxioms` parameter load-bearing. New cross-bridges: `noetherEntropyDensity_eq_beta_imL` + `firstOrderConductivity_isSymm_of_FirstOrderKMS`.) | D3 + L3 + I1 — **DEFERRED** (I1 reframing pre-draft EXISTS, on-hold) | **D.3** | **HELD** — I1 pre-draft at `temporary/working-docs/phase6n/6n_gamma_I1_reframing_predraft.md` (on-hold per Session-5 user direction) |
| **Wave 2b** | G10-QCrooks-α | ✅ **SHIPPED** (Stage 1: 6 QuantumCrooks/ modules + parametric no-go theorem; Stage 2-3: 7th module Concrete.lean ships substantive quantum no-go via canonical 2-level Perarnau-Llobet counterexample on `Matrix (Fin 2) (Fin 2) ℝ`. All MCP-proven, zero Aristotle escalation, zero sorry.) | D1 cross-bridge / D5 — **DEFERRED** | **D.2** | none |
| **Wave 2c** | G10-6n.3 Crooks-on-analog-Hawking | ✅ **SHIPPED** (Stage 1 + Stage 2-3 SHIPPED Session 6: 3 CrooksAnalogHawking/ modules. **Session 8 (2026-05-05) Stage 4 substrate-level GC bridge:** new module `CrooksAnalogHawking/SKEFTGallavottiCohen.lean` ships 7 substantive theorems lifting Wave 2c rate-function content to substrate level paralleling Session-7 Wave 2d Stage 4. Headline: `WFormGallavottiCohen β I := ∀ W, I(W) - I(-W) = -β·W` (Crooks-form W-variable GC); `linearResponseRateFunction β σ² W := (W - β·σ²/2)² / (2·σ²)` FDT-pinned Gaussian; `linearResponseRateFunction_satisfies_WFormGC` proves W-form GC algebraically; `WFormGallavottiCohen.to_σForm` cross-bridge to existing σ-form via change of variable; **`skeft_substrate_yields_WFormGC`** load-bearing-A theorem destructuring `A.dynamical_KMS`; **`firstOrderDissipative_yields_WFormGC`** concrete substantive witness (γ₂ > 0 ⇒ c.i₂ = γ₂/β > 0 ⇒ W-form GC unconditionally); **`firstOrderDissipative_yields_horizon_crooks_with_GC`** composed Stage-4 substrate (FDR-pinned σ = β·W + Noether-density positivity + W-form GC together via single c). Verlinde-vs-Jacobson distinction preserved. MCP-driven, zero Aristotle. Stage 5+ LDP infra retained as Mathlib upstream-PR candidate.) | E1 + D1 — **DEFERRED** | **D.2** | none |
| **Wave 2d** | G10-6n.7 Sakharov ↔ horizon-Crooks | ✅ **SHIPPED** (Stage 1 + Stage 2-3 SHIPPED Session 6: substrate bundle + substantive biconditional `sakharov_iff_horizon_crooks` proved at Bool-projection level + ³He-A and FLS BEC compatibility theorems + horizon-Crooks-language unification of Phase 6e + Phase 6m Track C substrate-classification. **Stage 4 substrate-level bridge SHIPPED Session 7 (2026-05-05)**: new module `CrooksAnalogHawking/SKEFTHorizonBridge.lean` ships 6 substantive theorems linking Wave 2a's `SKEFTAxioms` machinery at horizon temperature β_H to Wave 2c's `HorizonDetailedBalance` predicate. Headline theorems: `noetherEntropyDensity_nonneg_of_SKEFTAxioms` (entropy density ≥ 0 via `A.dynamical_KMS` + `A.reflection_pos`); `skeft_yields_horizon_crooks_witness` (FDR-pinned σ = β_H · W); `sakharov_skeft_substrate_jacobsonConsistent` (substrate-level Sakharov + SKEFTAxioms ⇒ Jacobson-consistent); `helium3A_skeft_substantive_jacobsonConsistent` (³He-A concrete instance under any SKEFTAxioms); `horizonCrooks_substantive_partition` (substantive partition vs. FLS BEC). Verlinde-vs-Jacobson distinction preserved.) D3+L3 reframing pre-draft on-hold per Session-5. | D3 + L3 — **DEFERRED** (pre-draft on-hold) | **D.3** | **HELD** — D3+L3 pre-draft on-hold per Session-5 user direction |

**Wave dependencies (Session-5 status):**
- Wave 1a / Wave 1b / Wave 2b / Wave 2c / Wave 2a are independent — can run in any order, in parallel.
- Wave 2a ✅ closed at Lean-substrate level (Stage-1 + Stage-2–3 + Stage-2–3b shipped). This unblocks Wave 2d Lean module work AND Wave 2c's path-measure theorem-statement form.
- Wave 2d Lean module work is now **unblocked** by Wave 2a closure; only the bundle absorption is deferred.
- Wave 1c ✅ memo shipped; the AS-side translation of SymTFT anomaly content (Witten–Yonekura η-invariant) cross-references Wave 1b when Wave 1b closes.
- Wave 2c does not strictly depend on Wave 2a closing for the substrate audit, but for theorem-statement form, Wave 2a's `SKEFTAxioms` typeclass is now available.

**Recommended next-up order (Session 9+ reset, per user direction "push forward on math, build in leverage order"):**

**Session 9 close add:** Wave 2a × Wave 1b cross-track unification gap CLOSED. The post-Session-9 picture is more uniformly load-bearing — the highest-leverage residual deficits all live in either upstream-PR-scope (Wave 1b Stage 5 full Witt-class) or multi-session physics (Wave 1a Stage 2 γ_1 Beliaev derivation). For lower-cost incremental work: Wave 2b ℂ-extension (~30 min mechanical).

1. ~~**Wave 2b**~~ — ✅ Stage 1 + Stage 2-3 SHIPPED (Session 6): 7 QuantumCrooks/ modules + substantive quantum Perarnau-Llobet no-go (canonical 2-level counterexample, MCP-proven, zero Aristotle).
2. ~~**Wave 2c**~~ — ✅ Stage 1 + Stage 2-3 SHIPPED (Session 6) + ✅ **Stage 4 SHIPPED Session 8 (2026-05-05)**: substrate-level Gallavotti-Cohen bridge in `SKEFTGallavottiCohen.lean` (7 substantive theorems; W-form GC predicate; FDT-pinned Gaussian rate function; load-bearing-A theorem extracting `c : FirstOrderCoeffs` from `A.dynamical_KMS`; concrete `firstOrderDissipativeAction` witness; composed Stage-4 substrate combining Session-7 horizon-Crooks witness + W-form GC). Verlinde-vs-Jacobson distinction preserved. Stage 5+ LDP infra retained as Mathlib upstream-PR candidate.
3. ~~**Wave 2d Lean substrate**~~ — ✅ Stage 1 + Stage 2-3 SHIPPED (Session 6) + ✅ **Stage 4 SHIPPED Session 7**: substrate bundle + substantive biconditional `sakharov_iff_horizon_crooks` proved at Bool-projection level + ³He-A and FLS BEC compatibility theorems + horizon-Crooks-language unification of Phase 6e + Phase 6m Track C substrate-classification + Stage 4 SKEFTHorizonBridge substrate-level form (6 substantive theorems). Verlinde-vs-Jacobson distinction preserved.
4. ~~**Wave 1b**~~ — ✅ Stage 1+2+3+4 SHIPPED (Session 6) + ✅ **Stage 4c SHIPPED Session 8 (2026-05-05)**: primary-source audit verdict + 3 discrete-sector candidate predicates + **3 substantive cross-module bridges** (was 2 in Session 6; Session 8 closes asymmetry). Bridges: KMSParityAlternation ↔ SecondOrderSK γ_{2,1}+γ_{2,2}=0; Z16AnomalyEta ↔ Z16AnomalyCancels; chiralCentralCharge ↔ GenerationConstraint.generation_constraint_iff (project-local Schellekens chain via biconditional `3 ∣ n ↔ 24 ∣ 8·n`). Stage 5+ full Witt-class form remains in-program-build candidate (Mathlib upstream-PR target).
5. **Wave 2b Stage 2-3 extension targets** — generalize the concrete substrate to `Matrix (Fin n) (Fin n) ℂ` for arbitrary n; add reservoir-coupled forms; KMSCompatible/FDTCompatible typeclass connections.
6. **Wave 1a.3 Path A precision** — ✅ AUTHORIZED + Stage 1 SHIPPED Session 6 (`src/resurgence/bdg_self_energy.py` module skeleton + Stage 2-5 sub-stage decomposition working doc). Stage 2 next-up: γ_1 via Beliaev 1958 LO scheme + cross-validation against literature anchor (Pitaevskii-Stringari §4.4 / Liu-Fukuyama PRB 31, 175). Stages 3-5 planned in working doc.
7. **Phase 6o opening** — APS-η analog-horizons sub-wave + the deferred-track items (G3 Carrollian, G4 Kerr-Schild, G1 Schellekens, G10-ETH-α, I3 community contribution).

---

## Wave 1a — G2 Resurgence on SK-EFT gradient expansion 🟡 IN-PROGRESS

**Sub-wave status (Session-5 close):**
- ✅ **Wave 1a.1 SHIPPED** (commit `769ecc6`): `formulas.py` extended with δ⁴–δ⁷ symbolic coefficient generators (16 new coefficients across orders 4–7 per `count(N) = ⌊(N+1)/2⌋ + 1`).
- ✅ **Wave 1a.2 SHIPPED** (commit `2eb461a`): Padé-Borel numerical infrastructure at `src/resurgence/borel.py` (ratio test, Padé approximant, Borel-singularity extraction, Λ_UV closed-form predictor).
- 🟡 **Wave 1a.3 PARTIALLY CLOSED**: Path B (numerical run on Steinhauer-class BEC parameters via `borel.py`) **executed**; verdict shipped at `temporary/working-docs/phase6n/6n_alpha_3_VERDICT.md` + script at `6n_alpha_3_path_B_numerical_run.py` (uncommitted working docs). **Verdict: BEC SK-EFT in weak-coupling regime is geometrically convergent, NOT Gevrey-1** (super-geometric per Beliaev-style prefactors); comparable to GKST holographic linear-response. The Path B counterfactual Gevrey-1 model recovers Λ_UV = κ√A = 2500 Hz exactly via [1/1] Padé–Borel — pipeline validated; physical verdict is "no resurgence content for weak-coupling BEC." Path A precision (multi-session BdG self-energy through order 7) deferred pending user decision (VERDICT §7).
- ✅ **Wave 1a.4 SHIPPED** (commit `0abd7d3`): Lean substrate at `lean/SKEFTHawking/Resurgence/{Basic,BorelAction,StokesBound}.lean` + count theorems at `HigherOrderSK.lean`. Formalizes `IsGevrey1` predicate, `StokesData` infrastructure, `lambdaUV_from_borelAction` conditional theorem, `deltaNP_pos_of_stokes_pos` non-perturbative-content existence statement.

**Substantive math finding (Session 5):** the BEC SK-EFT geometric-convergence verdict is a substrate-structural classification result paralleling the Phase 6e Sakharov-criterion finding. A "third Sakharov-style biconditional" candidate framing flagged for user review at next bundle-absorption pass.

**Open question for user:** ship Path B verdict alone (closes Wave 1a at substrate-level finding) vs. authorize Path A precision (multi-session BdG self-energy enumeration through order 7; would convert "suggestive" → "definitive" structural-classification claim of the same scale as Phase 6e Sakharov biconditional).

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

## Wave 1b — G9 SymTFT primary-source audit + GD-4-factor decomposition sketch 🟡 IN-PROGRESS

**Sub-wave status (Session 6 close):**
- 📝 **Stage 1 audit working doc** at `temporary/working-docs/phase6n/6n_beta_symtft_audit.md`: substrate analysis + Choi-doubled SymTFT applicability decision matrix + cross-bridge audit + GD-4-factor decomposition sketch + risk register.
- ✅ **Stage 2 audit verdict SHIPPED** (Session 6) at `temporary/working-docs/phase6n/wave_1b_symtft_audit_verdict.md`: direct primary-source fetch of arXiv:2507.05350 (Schäfer-Nameki et al., "SymTFT Approach for Mixed States with Non-Invertible Symmetries," July 2025). **Verdict: PARTIALLY APPLICABLE** — discrete dynamical-KMS Z₂ embeds in the Choi-doubled framework as a "weak symmetry" analog of the paper's Kramers-Wannier example; continuous entropic U(1)_T does NOT embed (paper does not handle continuous symmetries) and requires fusion with Brennan-Sun arXiv:2407.07951 BF technology — multi-wave research project per DR §6.2, deferred to Phase 6o.
- ✅ **Stage 3 discrete-sector Lean substrate SHIPPED** (Session 6): `lean/SKEFTHawking/SymTFTAudit/Applicability.lean`:
  - `SymTFTApplicability` inductive (Applicable / PartiallyApplicable / NotApplicable)
  - `stage2Verdict := PartiallyApplicable` (the audit outcome)
  - 3 ship-able discrete-sector candidate predicates: `chiralCentralChargeMod24Compatible`, `Z16AnomalyEtaCompatible`, `KMSParityAlternationCompatible`
  - Substantive instantiation theorems for each (Stage-2 verdict instantiates each non-vacuously)
  - `stage2_partition` substantive partition theorem
- ⏳ **Stage 4+ (substantive cross-module bridges to existing program threads) NOT STARTED**: connect each of the 3 discrete-sector predicates to existing program content (`SpinBordism.Z16`, `SecondOrderSK.gamma_2_1+gamma_2_2=0`, modular-invariance / Schellekens content). Multi-wave research project; full Lean Witt-group / Anderson dual / Lagrangian algebra infrastructure absent in Mathlib (Stage 1 §6 risk register).
- ⏳ **Continuous-sector follow-on**: `gauge_erasure` (Phase 3 W2) and `GD_orthogonality` (4-factor decomposition) candidates deferred per Stage 2 verdict §3 — speculative connections that need Brennan-Sun fusion or substantive (-1)-form work.

**Lake build state**: 8529 → 8530 jobs (+1 module = SymTFTAudit), all clean, zero sorry.

**Substantive Stage-1+2+3 finding:** the Stage 2 audit verdict is the load-bearing deliverable — direct primary-source fetch confirmed the framework handles discrete non-invertible symmetries in closed quantum systems but does NOT handle continuous, KMS, thermal, or Schwinger-Keldysh content. The PARTIALLY APPLICABLE verdict is the middle of three branches (per Stage 1 §2.2 matrix) and is the honest assessment — neither overconfident nor pessimistic. The Stage 3 Lean substrate operationalizes this verdict at the predicate level (zero sorry).

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

## Wave 2a — G10-6n.1 Glorioso-Liu axiomatic skeleton ✅ SHIPPED (Lean substrate); ⏳ HELD (bundle absorption)

**Sub-wave status (Session-5 close):**
- ✅ **Stage-1 Lean module skeleton SHIPPED** (commit `fa2f54c`): all 8 modules (`Axioms.lean`, `DynamicalKMS.lean`, `LocalEquilibrium.lean`, `EntropyCurrent.lean`, `LocalSecondLaw.lean`, `OnsagerReciprocity.lean`, `FirstOrderProjection.lean`, `Phase1Reconciliation.lean`) under `lean/SKEFTHawking/GloriosoLiu/`.
- ✅ **Stage-1 close** (commit `522155e`): 8 sorries trivial-discharge + root integration into `lean/SKEFTHawking.lean`.
- ✅ **Stage 2–3 substantive refactor SHIPPED** (commit `1b87c4a`): all 7 modules parameterized over `SKDoubling.SKAction`; substantive content beyond placeholders.
- ✅ **R1 LIFTED** (commit `bbb34ce`): substantive partition recovery via `SKDoubling.KMSSymmetry` projection + Aristotle counterexample + linarith. The 4-of-9 partition is now a **theorem** (`Phase1Reconciliation.four_of_nine_partition_recovered`) rather than an Aristotle-empirical observation.
- ✅ **Stage 2–3b KMS framework refactor SHIPPED** (commit `d344c33`): non-trivial existence witness `SKEFTAxioms_zero_action` for the zero action; `dynamical_KMS := ⟨kmsForZeroAction β⟩` substantive witness shipped.
- 📝 **KMS framework finding (working doc)** at `temporary/working-docs/phase6n/6n_gamma_kms_framework_finding.md`: structural finding that strict-invariance `KMSSymmetry` is generically incompatible with non-trivial dissipative SK-EFT actions (canonical KMS shift generates new monomials whose only cancellation requires γ_1 = γ_2 = 0). Recommends extending Stage 2–3b with the algebraic FDR form (`hasDynamicalKMS_algebraic`) for non-trivial existence witness `SKEFTAxioms_for_dissipative` — small-scope follow-up refactor (~50 lines Lean) flagged for next-session attention.
- ⏳ **D.3 bundle absorption HELD per Session-5 user direction**: I1 reframing pre-draft EXISTS at `temporary/working-docs/phase6n/6n_gamma_I1_reframing_predraft.md` (drop-in §3 replacement prose for `papers/I1/paper_draft.tex` lines 282–340 + D3+L3 incidental citation upgrades). On-hold for user review until Phase 6n + 6o math closure complete; absorption then runs as one coherent pass per user direction.

**🚨 USER AUTHORIZATION GATE (D.3 absorption — Stage B of `LATE_PHASE6_ABSORPTION_PROTOCOL.md`) — HELD:**

I1's Phase 1 FirstOrderKMS case study is the program's anchor productive-value example. The Wave 2a reframing converts "Aristotle disproved 5/9" → "Aristotle disproved 5/9; deeper Glorioso-Liu axiomatic was formalized; the 5/9 disproof became a theorem of first/second-order separation." This substantially strengthens the case study but changes I1's framing. **Pre-draft EXISTS for user review when bundle-absorption pass begins.**

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

## Wave 2b — G10-QCrooks-α productive-value Aristotle wave ✅ SHIPPED (Stage 1 + Stage 2-3)

**Sub-wave status (Session 6 close):**
- ✅ **Stage 1 SHIPPED** (Session 6): 6 modules under `lean/SKEFTHawking/QuantumCrooks/` (Setup, Tasaki, Aberg, KafriDeffner, Quasiprobability, PerarnauLlobet) all imported into root. Substantive content includes:
  - `IsCrooksRatio` predicate + `IsCrooksRatio.symm` symmetry theorem (forward/reverse roles symmetric — load-bearing for trajectory-Crooks downstream Wave 2c/2d).
  - 4 candidate axiomatization predicates (Tasaki-TPM, Åberg-coherent, Kafri-Deffner-unital, Kirkwood-Dirac quasiprobability) at the Crooks-ratio-compatibility level. (Distinguishing structural content lives in Stage 2-3 schemes.)
  - **Parametric Perarnau-Llobet no-go theorem** `perarnau_llobet_no_go_parametric`: proves that under `h_disagree : ∃ β, trueAverage β ≠ firstMoment (canonicalTPM β)`, no MS satisfies `ReproducesAverageEnergy ∧ RecoversTPMOnDiagonal`. The load-bearing physics content (TPM averages disagree with true averages on coherent states) is the `h_disagree` hypothesis; the algebraic obstruction is proved fully via direct rewriting.
  - Contrapositive forms: `reproduces_avg_implies_fails_TPM` (Åberg-class result) + `recovers_TPM_implies_fails_avg` (Tasaki-class result).
- 📝 **Stage 1 working doc** at `temporary/working-docs/phase6n/wave_2b_QCrooks_stage1.md`: substrate analysis + module decomposition + risk register + primary-source bibitems.
- ✅ **Stage 2-3 SHIPPED** (Session 6, same session): 7th module `Concrete.lean` ships the canonical 2-level Perarnau-Llobet counterexample as concrete `Matrix (Fin 2) (Fin 2) ℝ` matrices (ρ_+ = !![1/2, 1/2; 1/2, 1/2], ρ_diag, H_i = diag(0,1), H_f = σ_x). Substantive theorems:
  - `trueAverage_perarnau ρ_plus = +1/2` (matrix-trace computation: Tr[H_f · ρ_+] − Tr[H_i · ρ_+])
  - `tpmAverage_perarnau ρ_plus = -1/2` (TPM projects coherences away → uses ρ_diag)
  - `perarnau_llobet_disagreement` — they differ
  - `perarnau_h_disagree` — disagreement witness specialized to the parametric framework
  - **`perarnau_llobet_no_go_quantum`** — the substantive quantum no-go theorem, derived from the parametric no-go + h_disagree witness
  All proved via direct Lean tactics (`simp` + `norm_num` + `Fin.sum_univ_two`); zero Aristotle escalation; zero sorry.
- ⏳ **Stage 2-3 extension targets (deferred)**: ℂ-valued density matrices for general states; multi-level systems (`Matrix (Fin n) (Fin n) ℂ`); reservoir-coupled and unitary-evolution forms; KMSCompatible/FDTCompatible typeclass connections.

**Lake build state**: 8519 → 8526 jobs (+7 modules), all clean, zero sorry across new modules.

**Substantive Stage-1+2-3 finding:** The Perarnau-Llobet no-go is proved fully via MCP (no Aristotle dependency). The parametric form decouples the algebraic obstruction from the quantum substrate; the substantive form specializes via a concrete numerical witness for `h_disagree` on a 2-level Hilbert space. This validates the "MCP-first" discipline — the program's existing infrastructure + Mathlib's matrix machinery were sufficient for the substantive lift without requiring an Aristotle batch.

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

**Risk axes.** Aristotle returns no refutation (low — Perarnau-Llobet bounds ≥ 1); quasiprobability axiomatization choice (Levy-Lostaglio vs Francica) may not span the literature's full axiom-space (medium — name it explicitly + flag); the productive-value paper venue varies on whether the refutation tableau is "FirstOrderKMS template" or "novel". Aristotle is *not* the load-bearing tool for Wave 2a but IS for Wave 2b — submission gating per CLAUDE.md "User gets first & last call on Aristotle submissions."

---

## Wave 2c — G10-6n.3 Crooks-on-analog-Hawking on polariton SK-EFT substrate 🟡 IN-PROGRESS

**Sub-wave status (Session 8 close):**
- ✅ **Stage 1 SHIPPED** (Session 6): 2 modules under `lean/SKEFTHawking/CrooksAnalogHawking/`:
  - `HorizonDetailedBalance.lean` — predicate `HorizonDetailedBalance P_F P_R σ := ∀ W, P_F.P W = exp(σ W) · P_R.P (-W)` generalizes `IsCrooksRatio` (Wave 2b substrate) to nonlinear entropy-production functional `σ : ℝ → ℝ`. Substantive theorems: `specialize_to_Crooks` (cross-module bridge: `σ(W) = β·W` ⇒ HDB ↔ IsCrooksRatio), `symm_neg` (forward/reverse symmetry under σ ↦ −σ ∘ neg, generalizing `IsCrooksRatio.symm`), `horizonDetailedBalance_zero` (well-posedness witness).
  - `GallavottiCohen.lean` — predicate `GallavottiCohenSymmetry I := ∀ σ, I(-σ) - I(σ) = -σ` is the LDP rate-function symmetry (long-time / NESS limit of Crooks). Substantive theorems: `gallavottiCohen_linear_witness` (linear `I(σ) := σ/2` satisfies GC), `shift_invariant` (GC is gauge-invariant under constant shifts).
- ✅ **Stage 4 substrate-level GC bridge SHIPPED** (Session 8, 2026-05-05): new module `lean/SKEFTHawking/CrooksAnalogHawking/SKEFTGallavottiCohen.lean` ships 7 substantive theorems lifting Wave 2c rate-function content to substrate level paralleling Session-7 Wave 2d Stage 4. Headline content:
  - **W-form GC predicate** `WFormGallavottiCohen β I := ∀ W, I(W) - I(-W) = -β·W` — Crooks-form W-variable analog of σ-form `GallavottiCohenSymmetry`, the natural form to pair with `HorizonDetailedBalance`.
  - **FDT-pinned linear-response Gaussian rate function** `linearResponseRateFunction β σ² W := (W - β·σ²/2)² / (2·σ²)` with mean β·σ²/2 (FDT-pinning) and variance σ²; `linearResponseRateFunction_satisfies_WFormGC` proves W-form GC algebraically for any σ² ≠ 0 (`field_simp; ring`).
  - **Cross-bridge `WFormGallavottiCohen.to_σForm`** — change of variable σ = β·W + sign flip `J := -I ∘ (·/β)` converts W-form to σ-form GC (substantive cross-module identity between this module's predicate and the existing `GallavottiCohenSymmetry`).
  - **Substantive load-bearing-A theorem** `skeft_substrate_yields_WFormGC` — under SKEFTAxioms at β > 0, the proof body destructures `A.dynamical_KMS` to extract `c : FirstOrderCoeffs` with `FirstOrderKMS c β`, and the W-form GC clause activates conditionally on c.i₂ ≠ 0 (non-trivial noise; the conditional form is structural — degenerate substrates with c.i₂ = 0 don't carry meaningful rate functions).
  - **Concrete substantive witness** `firstOrderDissipative_yields_WFormGC` — for `firstOrderDissipativeAction(coeffs, β)` with γ₂ > 0 and β > 0, the explicit witness c = ⟨γ₁+γ₂, -γ₁, 0,0,0,0, γ₁/β, γ₂/β, 0⟩ has c.i₂ = γ₂/β > 0 and the W-form GC unconditionally holds. Parallel of Session-7 `helium3A_skeft_substantive_jacobsonConsistent`.
  - **Composed Stage-4 substrate** `skeft_yields_horizon_crooks_with_GC` + `firstOrderDissipative_yields_horizon_crooks_with_GC` — full composed substrate-level bridge: FDR-pinned σ = β·W (Session 7 Wave 2d) + Noether-density positivity (Session 7) + W-form GC (Session 8) ALL with the same single c extracted from `A.dynamical_KMS`. The strongest substantive Stage-4 statement of Wave 2c that does not require LDP infrastructure (Stage 5+ is the in-program build candidate per the Mathlib-upstream-PR pattern).

  Verlinde-vs-Jacobson distinction preserved at every Lean statement. MCP-driven, zero Aristotle.
- ⏳ **Stage 5+ NOT STARTED**: derive the third Sakharov-style biconditional
    ```
    AnalogHawkingSubstrate.satisfies_GLU_monotonicity (Wave 2a substrate)
      ↔ EmissionSpectrum.LDP_rate_function.satisfies_GallavottiCohen
    ```
  Requires the analog-Hawking spectrum substrate (Loganayagam–Martin or CGL-EFT) + LDP infrastructure. Buildable in-program via discrete-time / Markov-jump LDP per Falasco–Esposito 2025 RMP framework — **candidate Mathlib upstream-PR opportunity** per the program's track record (lean-tensor-categories, RingQuot, repl pinning).

**Lake build state**: 8534 → 8535 jobs (+1 module = SKEFTGallavottiCohen, Session 8), all clean, zero sorry.

**Substantive Stage-1 finding:** `HorizonDetailedBalance` is definitionally a generalization of `IsCrooksRatio` — the linear case σ(W) = β·W IS the classical Crooks ratio. This makes Wave 2c a substantive *generalization* of Wave 2b's classical-Crooks structure rather than a separate framework. The substantive analog-Hawking content is the constraint on σ from GLU monotonicity (Stage 2-3).

- *Integrates with:* E1 polariton paper; D1 §3-§4 analog Hawking content; Carusotto-Gerace polariton analog black-hole literature (arXiv:1206.4276 + follow-ups); Steinhauer BEC analog black holes; Tettamanti-Parola-Cacciatori arXiv:1703.05041 exactly-solvable BEC; **Loganayagam-Martin Exterior EFT for Hawking Radiation arXiv:2403.10654** (JHEP 2025) — the cleanest substrate for trajectory-Crooks at the horizon; Banerjee et al. fluctuation-dissipation horizon-temperature derivation (Eur. Phys. J. C 80, 411, 2020) as the FDT-level prior art.
- *New constraint adds:* an inequality on the analog-Hawking spectrum derived from trajectory-level Crooks detailed-balance, **beyond what FDT / Kubo gives**. Specifically: the LDP rate function I(σ) for entropy production must satisfy the GC/LS symmetry I(-σ) - I(σ) = -σ, which translates into specific bounds on the spectrum's higher cumulants of work / entropy-production fluctuations. Falsifiable on existing experimental platforms (Steinhauer BEC, Weinfurtner Vancouver surface-wave, Carusotto polariton). Comparable in character to Phase 6e Sakharov biconditional — third "Sakharov-style" biconditional in the program if non-trivial.
- *Tension surfaces:* the DR's main flag — "if the inequality is satisfied trivially given the existing thermal spectrum, the contribution is FDT-level only and not novel." The work itself is *deriving* what trajectory-Crooks structure constrains beyond FDT; the output of the derivation determines (a) trivial = formalization-only contribution, or (b) non-trivial = third Sakharov-style biconditional + falsifiable predictions.

**Substrate.** Two viable framings:
- (a) Glorioso-Crossley-Liu SK-EFT effective action as the path measure (closer to existing program infrastructure; uses Wave 2a as substrate).
- (b) Loganayagam-Martin exterior EFT for Hawking radiation (cleanest framework for trajectory-Crooks at the horizon specifically).

DR recommends (b) on top of (a): state the trajectory-Crooks predicate on Loganayagam-Martin exterior EFT; derive the inequality; verify it specializes correctly to the program's existing SK-EFT polariton content.

Discrete-time / Markov-jump-process scope (Falasco-Esposito 2025 RMP framework) — sufficient for falsifiability on Steinhauer / Weinfurtner / Carusotto. Continuous-time form deferred to post-Phase-6o-Itô.

**Stage 1 actions:**
- Read Loganayagam-Martin arXiv:2403.10654 in full directly.
- Draft `AnalogHawkingSubstrate` typeclass + `TrajectoryCrooksAtHorizon` predicate.
- Derive the inequality on the spectrum (paper math first; Lean theorem statement second).
- Specialize to Steinhauer / Weinfurtner / Carusotto device parameters; check against published spectrum + noise data.
- Add E1 falsification-window section.

**Bundle absorption.** D.2 additive into E1 (new section: "Trajectory-level Crooks constraint at the analog horizon"). D.2 cross-bridge into D1 only after Wave 2a closes (theorem-statement form follows Wave 2a's path-measure infrastructure).

**Risk axes.** Triviality risk (DR's main flag); continuous-vs-discrete-time framing (Markov-jump sufficient for falsifiability; cleaner version waits for Itô); Verlinde-Nagle contamination (Lean statements must invoke only Glorioso-Liu / Loganayagam-Martin substrate, not Verlinde — analogous discipline to Wave 2d); open-vs-closed-system framing (Loganayagam-Martin exterior EFT is open; CGL is closed; cross-walk lemma needed); substrate-specific verifiability variance.

---

## Wave 2d — G10-6n.7 Sakharov ↔ horizon-Crooks reformulation 🟡 IN-PROGRESS

**Sub-wave status (Session 6 close):**
- ✅ **Stage 1 Lean substrate SHIPPED** (Session 6): `lean/SKEFTHawking/CrooksAnalogHawking/SakharovHorizonCrooks.lean`:
  - `HorizonCrooksSubstrate` structure bundles existing `JacobsonThermoGRDarkEnergy.SakharovConditions` (Phase 6m Track C substrate) with the new `HorizonDetailedBalance` predicate (Wave 2c) into a single substrate type.
  - `jacobsonConsistent` predicate captures the Jacobson reading (NOT Verlinde — distinction preserved at every Lean statement per Phase 6n DR §7).
  - Concrete witnesses: `helium3A_horizon_crooks` (Sakharov true via JTGR7 → Jacobson-consistent) and `flsBEC_horizon_crooks` (Sakharov-(ii) fails via JTGR8 → not Jacobson-consistent).
  - `horizonCrooks_substrate_partition` theorem: substantive partition combining both witnesses — extends the existing Phase 6e+6m biconditional witnesses to the horizon-Crooks substrate type. Proof invokes `JacobsonThermoGRDarkEnergy.volovik_jannes_he3a_satisfies_sakharov_criterion` (JTGR7) and `flsBEC.universalCoupling = false` (JTGR8) — substantive cross-module bridge per P6 discipline.
- 📝 **D3+L3 reframing pre-draft EXISTS (uncommitted)** at `temporary/working-docs/phase6n/6n_zeta_D3_L3_reframing_predraft.md`. On-hold for user review per Session-5 user direction (bundle absorption deferred until full Phase 6n + 6o picture lands).
- ✅ **Wave dependency Wave 2a closed** at Lean-substrate level (Stage 1 + 2-3 + 2-3b shipped). Wave 2d Lean module work was unblocked, now Stage 1 SHIPPED.
- ⏳ **Stage 2-3 NOT STARTED**: full `Sakharov_iff_horizon_Crooks` biconditional derivation requires the GLU monotonicity bridge from Wave 2a's `SKEFTAxioms`/`hasDynamicalKMS_algebraic` substrate applied at the substrate-level Rindler horizon. Per `6n_gamma_kms_framework_finding.md` §6.2, the bridge MUST use the algebraic-FDR form (`hasDynamicalKMS_algebraic`), not strict-invariance.

**Lake build state**: 8528 → 8529 jobs (+1 module), all clean, zero sorry.

**Substantive Stage-1 finding:** the existing Phase 6e biconditional witnesses (³He-A satisfies / FLS BEC fails) extend cleanly to the horizon-Crooks substrate type via the `HorizonCrooksSubstrate` bundle. The partition theorem is a substantive cross-module statement preserving the Verlinde-vs-Jacobson distinction.

**🚨 USER AUTHORIZATION GATE (D.3 absorption — Stage B of `LATE_PHASE6_ABSORPTION_PROTOCOL.md`) — HELD:**

D3 + L3 currently express the Phase 6e Sakharov-criterion biconditional and the Phase 6m Track C JTGR survivors as separate results. The Wave 2d reformulation unifies them as one fluctuation-theorem result (`Sakharov_iff_horizon_Crooks` biconditional). This refines D3 + L3's published-claim profile — same content, deeper structural framing. **Pre-draft EXISTS for user review when bundle-absorption pass begins.**

**Wave dependency:** Wave 2d blocks on Wave 2a (Glorioso-Liu axiomatic) closing first. ✅ **SATISFIED** (Session 5 close).

- *Integrates with:* Phase 6e Sakharov-criterion biconditional (Λ_J = Λ_HK on ³He-A; falsified on FLS BEC); Phase 6m Track C JTGR survivors (M1, M2/M7, M3 Exp/ArcTanh, M4, M9; M8 conditional); Eling-Guedens-Jacobson f(R) (gr-qc/0602001) entropy-production term; Chirco-Eling-Liberati gravitational-dissipation (PRD 81, 024016) heat decomposition; Alonso-Serrano + Liška unimodular-from-Clausius (arXiv:2008.04805); Wave 2a Glorioso-Liu axiomatic substrate.
- *New constraint adds:* Sakharov criterion expressed as horizon-Crooks-detailed-balance (`P_F[γ] / P_R[γ̄] = exp(σ[γ])` at the local Rindler horizon); unifies Phase 6e biconditional + Phase 6m Track C JTGR survivors as one fluctuation-theorem result; **explicitly distinguishes Jacobson-allowed (equilibrium-Clausius-on-Rindler-horizon) from Verlinde-falsified (gravity-as-entropic-force) entropic-gravity readings**. Cleanest non-trivial deliverable in any Phase 6n track per the original DR.
- *Tension surfaces:* if the reformulation requires assumptions stronger than what Phase 6e + Phase 6m JTGR currently invoke, those extra assumptions become candidate sites for elimination-tournament probing. The Verlinde caveat is real: "fluctuation-theorem structure is present at the horizon (Jacobson level), not gravity *is* an entropic force (Verlinde level)" — this distinction must be carried through every Lean statement and bundle citation.

**Substrate.** Phase 6e Sakharov + Phase 6m Track C JTGR + Glorioso-Liu axiomatic (Wave 2a). Re-reading: not new derivation. Sakharov-class assignment from Phase 6m R5 (M1 + M9 in Sakharov-class; M2/M7 with epistemic flag; M3 in class-(b′); M4 in class-(b″); M8 OUTSIDE Sakharov-class).

**Stage 1 actions (after Wave 2a closes):**
- State `HorizonDetailedBalance` predicate parameterized over the substrate.
- State `Sakharov_iff_horizon_Crooks` biconditional theorem.
- Specialize to Phase 6e biconditional witnesses (³He-A holds; FLS BEC fails).
- Specialize to Phase 6m Track C JTGR survivors (verifies which class-(b/b′/b″) survivor admits horizon-Crooks reading).
- Pre-draft D3 + L3 reframing language for user-auth gate.

**Bundle absorption.** D.3 into D3 + L3 (refines biconditional + JTGR survivors' published-claim profile). User-auth REQUIRED pre-draft.

**Risk axes.** Reformulation may surface stronger-than-current assumption (publishable as elimination-tournament target either way); Verlinde-vs-Jacobson distinction must not slip in any single Lean theorem statement (compositional discipline); Wave 2a blocks delays Wave 2d start; D.3 absorption cascade across D3 + L3.

---

## Wave 1c — G8-W1 Atiyah-Singer reformulation memo (no Lean) ✅ SHIPPED

**Status (Session-5 close):**
- ✅ **Stage-1 memo SHIPPED (uncommitted working doc)** at `temporary/working-docs/phase6n/6n_eta_AS_reformulation_memo.md`: heat-kernel ↔ AS dictionary written explicitly for the program's a₀, a₂, a₄ content; Sakharov tr(I) ≠ 0 identified as McKean–Singer supertrace nonvanishing condition; instanton zero modes identified as ker(D); Z₁₆ anomaly identified as Witten–Yonekura η/16 mod 1 (cross-bridge to Wave 1b SymTFT).
- 🚩 **One potentially-new structural item flagged for Phase 6o**: APS eta-invariant for analog-horizon backgrounds (BEC-acoustic, ADW, ³He-A) — first systematic substrate-side APS-η computation on analog Hawking horizons would be publishable. Promoted to Phase 6o follow-up sub-wave per memo §6.3.
- ⏳ **Bundle absorption (D2 + D3 + E1 appendix) DEFERRED** per Session-5 user direction. Memo is non-load-bearing for any current bundle; absorption runs as part of unified Phase 6n + 6o bundle-absorption pass.

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

## User authorization gates — consolidated (Session-5 status)

**Two D.3 user-auth gates HELD pending unified Phase 6n + 6o bundle-absorption pass** (Session-5 user direction: "push forward on math/physics/infrastructure first; bundle absorption runs as one coherent pass once full picture lands"):

| Wave | Bundle(s) refined | Pre-draft deliverable | Status |
|---|---|---|---|
| **Wave 2a** Glorioso-Liu axiomatic | I1 (anchor case study reframe) + D3 + L3 (citation form upgrade) | `temporary/working-docs/phase6n/6n_gamma_I1_reframing_predraft.md` — drop-in §3 replacement prose for `papers/I1/paper_draft.tex` lines 282–340; "FirstOrderKMS as Phase 1 anchor → first-order projection of Glorioso-Liu axiomatic; the 4-of-9 partition is now a theorem, not an Aristotle-empirical observation." | 📝 **HELD** — pre-draft EXISTS; on-hold for unified absorption pass |
| **Wave 2d** Sakharov ↔ horizon-Crooks | D3 + L3 (Phase 6e + Phase 6m Track C JTGR survivors unified) | `temporary/working-docs/phase6n/6n_zeta_D3_L3_reframing_predraft.md` — D3 + L3 reframing language; "Phase 6e Sakharov biconditional + Phase 6m Track C JTGR survivors as parallel results → unified `Sakharov_iff_horizon_Crooks` biconditional. Verlinde-vs-Jacobson distinction explicit at every Lean statement." Per KMS framework finding §6.2: technical-accuracy footnote needed referencing algebraic-FDR `FirstOrderKMS` rather than strict-invariance `KMSSymmetry`. | 📝 **HELD** — pre-draft EXISTS; on-hold for unified absorption pass |

**Additional gates (standard per `WAVE_EXECUTION_PIPELINE.md`):**
- Stage 4 Aristotle submission (Wave 2b QCrooks-α specifically) — user gets first and last call. **Triggers when Wave 2b Lean substrate is decomposed and ready for batch.**
- Stage 13 adversarial review per absorbed bundle — fresh-context reviewer per `BUNDLE_LIFT_PROCEDURE.md` §11. **Triggers in unified bundle-absorption pass at end of Phase 6n + 6o.**
- ✅ **I3 bundle authorization GRANTED** (Session 4, 2026-05-04) — Pipeline Invariant #14 user-auth for new bundle target. Bundle architecture 13 → 14. Infrastructure shipped commit `a72ba68`: `papers/I3/{bundle_metadata.json, source_manifest.md, change_log.md, append_log.json}` + bundle-count test assertion fix commit `82e9aba` + PAPER_DRAFT_MAPPING.md row 69 fix commit `70f0dea`. Scoping doc at `temporary/working-docs/phase6n/i3_bundle_scoping.md` (working doc; substantive scoping pending Phase 6o opening).

---

## Phase 6o handoff (preview — full detail in `Phase6o_Roadmap.md` stub)

Tracks deferred to Phase 6o per Session-3 quality-priority (and additions surfaced in Sessions 4–5):
- **G3 boostless / Carrollian soft-theorem program** for emergent post-erasure U(1) + ADW graviton (Tier 1).
- **G4-Kerr-Schild** classical double-copy on Petrov-D analog metrics (the draining-bathtub acoustic metric IS Petrov D; Tier 2).
- **G1-Schellekens chain** (spin-bordism → anomaly polynomial → modular invariance → Niemeier → Schellekens c=24 holomorphic-VOA classification corollary; Tier 1).
- **G1-NO-GO writeup** (dissipative SK-EFT bootstrap can't produce uniqueness with current axioms; Tier 4 NO-GO).
- **G10-ETH-α** productive-value Aristotle wave on Inozemcev–Volovich gap (Tier 2).
- **G10-Itô + LDP-α + LDP-β as I3 community contribution** — ✅ Pipeline Invariant #14 user-auth GRANTED (Session 4); bundle infrastructure shipped; substantive scoping at `temporary/working-docs/phase6n/i3_bundle_scoping.md` awaits Phase 6o opening.
- **APS-η for analog-horizon backgrounds** (NEW, surfaced by Wave 1c memo §6.3): first systematic substrate-side APS-η computation on BEC-acoustic / ADW / ³He-A horizons; would (a) sharpen L3 regime-partition with topological-invariant distinction, (b) connect to Wave 1b SymTFT via Witten–Yonekura η-invariant identification, (c) be publishable as first such calculation on analog Hawking horizons.
- **Wave 1a.3 Path A precision** (multi-session BdG self-energy through order 7) — pending user decision per VERDICT §7. If authorized, runs as a Phase 6o sub-wave delivering definitive Gevrey-1-or-geometric verdict + numerical Λ_UV (or absence thereof) + structural-finding writeup.
- **Unified Phase 6n + 6o → Phase 7 bundle-absorption pass** — runs at end of Phase 6o per Session-5 user direction. Absorbs all D.2/D.3 events from Phase 6n (Wave 1a + Wave 1b + Wave 2a I1 + Wave 2a D3+L3 + Wave 2b + Wave 2c + Wave 2d + Wave 1c) and Phase 6o (TBD) as one coherent pass per `LATE_PHASE6_ABSORPTION_PROTOCOL.md` Stages A–G. Two D.3 user-auth gates (Wave 2a I1, Wave 2d D3+L3) trigger at start of this pass.

Phase 6o framing locks at the next user-input gate (after Phase 6n math closes — i.e., after Wave 2b + Wave 2c + Wave 2d Lean ship, plus optionally Wave 1b Stage-2 Lean and Wave 1a.3 Path A).

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

*Created Phase 6n initialization (2026-05-04). Sessions 1–5 closed 2026-05-04. Session 5 close: 12 commits ahead of origin/main; Wave 1a IN-PROGRESS (1a.1+1a.2+1a.4 SHIPPED, 1a.3 Path B verdict working doc, 1a.3 Path A pending user decision); Wave 1b WORKING DOC (Stage-1 audit); Wave 2a SHIPPED (Lean substrate, R1 LIFTED, KMS framework refactor); Wave 2b NOT STARTED (next-up #1); Wave 2c NOT STARTED (next-up #2, unblocked by Wave 2a); Wave 2d working doc + Lean NOT STARTED (next-up #3); Wave 1c SHIPPED (memo); I3 bundle infrastructure SHIPPED. **Bundle absorption HELD per Session-5 user direction** — runs as unified Phase 6n + 6o → Phase 7 absorption pass once full math/Lean picture lands. Updates atomically as waves close.*
