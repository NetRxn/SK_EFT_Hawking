# Phase 6v: External Substrate Alignment & D6 Bundle Creation

## Technical Roadmap — May 2026

*Prepared 2026-05-25, following the External Quantum Findings opportunity-scan synthesis. Approved 2026-05-25 PM.*

**Trigger condition:** External opportunity-scan dispatch (April–May 2026 quantum-computing literature) surfaced 11 candidate research threads with strong overlap with the project's existing substrate. Pareto ranking selected 7 actionable waves for Phase 6v + 1 wave (former 6v.7) lifted into Phase 6w as a separate multi-wave program. Full synthesis lives in the private decision-record repo (cross-cutting public+private strategy artifact); this public roadmap is self-contained for Phase 6v public-side execution.

**Headline goal:** ship the FT-QC frontier alignment (gauging QEC + Shor T-gate count + APM-LDPC + W-state QFT) under a **new bundle D6 — "Formally Verified Fault-Tolerant Quantum Computation Substrate"** (15th publication target), plus resolve the Phase 6q polariton open question, plus deliver an authoritative NbRe SOTA classification, plus add Penn TMD demarcation to E1.

**Predecessor work assumed clean before Phase 6v starts:**
- Phase 6q strengthening pass (in flight in separate session; tracked in memory entry `next_session_phase6q_strengthening_pass.md`).
- Phase 6r / 6s / 6t / 6u status — independently scoped; do NOT depend on Phase 6v.

**Project rule applied:** No new project-local axioms (Pipeline Invariant #15 RESPECTED). No `maxHeartbeats` overrides in proof bodies (Invariant #10). Tracked-Prop posture for any irreducible gap with discharge plan in the wave roadmap.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY PHASE 6v WAVE WORK:**
>
> 1. **Mandatory project bootstrap** per workspace `CLAUDE.md` Mandatory References list.
> 2. **Read this roadmap end-to-end** before any wave-level claim.
> 3. **Read the canonical strategy synthesis** at `temporary/working-docs/phase6v/Phase6v_Strategy_Synthesis.md` — that document is the source of truth for Phase 6v / 6w decisions (§0 decisions log D-1 through D-8; §3.5 D6 bundle rationale; §8 follow-up list).
> 4. **External opportunity-scan source docs** at `temporary/working-docs/phase6v/External-Recs-Opportunity-scan/`:
>    - `Quantum Computing — Past 30 Days Ranked Opportunities for SK-EFT Hawking.md`
>    - `SK-EFT Hawking × Recent Quantum Breakthroughs Overlap & Opportunity Analysis.md`
>    - `Perplexity-Screen-Capture.md`
> 5. **Per-wave roadmap docs** at `docs/roadmaps/Phase6v/Wave_6v.<N>_Roadmap.md` are created at Stage 1 of each wave (compaction-survivability protocol). Do NOT pre-create them; let each wave's Stage 1 establish its constants + Lean targets first.
> 6. **Do not delegate Lean theorem proving to subagents.** MCP loop default; Aristotle is fallback.
> 7. **No PM / time estimates anywhere** — by user direction.

---

## Wave catalog — Phase 6v (7 waves; D6 bundle creation thread)

**Status legend:**
- ✅ **SHIPPED** — Lean / numerical deliverables committed and kernel-verified.
- 🟡 **IN-PROGRESS** — partial deliverables shipped.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft only.
- ⏳ **NOT STARTED**.

| Wave | Title | Status | Bundle absorption | LoE |
|---|---|---|---|---|
| **Wave 6v.4** | Penn TMD polariton regime demarcation (E1 lift) | ✅ SHIPPED 2026-05-26 | E1 §2 paragraph + Lean theorem | 0.5–1 sess |
| **Wave 6v.3** | DKM F3 polariton occupancy bound (Phase 6q follow-on) | ✅ SHIPPED 2026-05-26 | D5 §13 + E1 §2 (Wave 6v.4 cite chain) | 1–2 sess |
| **Wave 6v.1** | Williamson/Yoder gauging QEC formalization — **CREATES D6 BUNDLE** | ✅ SHIPPED 2026-05-26 | D6 §3 (CREATED) + I1 cross-bridge | 1.5 sess |
| **Wave 6v.2** | Google/Oratomic T-gate counts for Shor circuits | ⏳ NOT STARTED | D6 §5 + D4 cross-bridge | 2–3 sess |
| **Wave 6v.5** | APM-LDPC code substrate + hashing-bound LDP sub-wave | ⏳ NOT STARTED | D6 §4 + I1 | 4 sess |
| **Wave 6v.6** | W-state QFT decomposition in Q(ζ_N) | ⏳ NOT STARTED | D6 §6 | 2 sess |
| **Wave 6v.8** | NbRe triplet superconductor full SOTA BdG + SPT classification | ⏳ NOT STARTED | D2 + D4 | 3–5 sess (heaviest in 6v) |

**Total estimated effort:** ~14–19 sessions across 7 waves.

**Phase 6v.7 NOTE:** the KZM-Unruh bridge (former Wave 6v.7) has been **lifted into Phase 6w as Wave 6w.1** to give the Tindall/Sels + Aalto material proper multi-wave scoping rather than forcing a consolidation. See `docs/roadmaps/Phase6w_Roadmap.md`.

**Wave dependencies:**
- Wave 6v.1 creates the D6 bundle skeleton; Waves 6v.2, 6v.5, 6v.6 each LIFT INTO D6 — so 6v.1 must precede them.
- Wave 6v.3 (DKM F3 polariton) consumes Phase 6q substrate (already shipped); no Phase 6v dependency.
- Wave 6v.4 (Penn TMD) is independent of all other 6v waves; can ship first as warmup.
- Wave 6v.8 (NbRe) is independent of D6; can ship at any point but is heaviest.
- D6 Stage-13 bundle-level review runs after Wave 6v.6 ship (last D6-contributing wave); precedes D6 arXiv preprint preparation.

---

## Wave-by-wave detail

Each wave's headline goal + bundle-target + key substrate is summarized below. Per-wave roadmaps (`docs/roadmaps/Phase6v/Wave_6v.<N>_Roadmap.md`) are created at each wave's Stage 1 and become the canonical compaction-survivability handoff. Full Pareto/synthesis rationale lives in the private cross-cutting decision-record repo.

### Wave 6v.4 — Penn TMD polariton regime demarcation

**Goal:** Lift the UPenn 2026 TMD-polariton 4 fJ switching demonstration into E1 by adding Penn-TMD parameters to `EXPERIMENTS` + provenance + shipping `polariton_tier1_fails_tmds` theorem (validity-ratio threshold).

**Bundle target:** E1 §2 (Paris-LKB polariton paper).
**Key substrate:** `PolaritonTier1.lean`, `src/core/constants.py`, `src/core/provenance.py`.
**Cross-cutting outputs:** new bibkey `UPennTMD2026Polariton` + cached primary source.

### Wave 6v.3 — DKM F3 polariton occupancy bound (Phase 6q follow-on)

**Goal:** Resolve the open Phase 6q question of where polariton platforms fall on the DKM positive/NO-GO bimodal outcome. Compute pump-power → mode-occupation upper bound from UPenn-style femtojoule switching; ship `polariton_dkm_f3_holds_at_pump_below_threshold` Lean theorem; close the polariton case as inheriting the graphene positive uniqueness result.

**Bundle target:** D5 + E1 (per Phase 6q absorption protocol Branch D.2 if already drafted).
**Key substrate:** `DKMBootstrap/SKEFTSpecialization.lean`, `DKMBootstrap/HorizonTransportBootstrap.lean`, `PolaritonTier1.lean`.

### Wave 6v.1 — Williamson/Yoder gauging QEC formalization (creates D6 bundle)

**Goal:** Formalize the Williamson/Yoder *Nature Physics* April 2026 gauging-of-symmetry construction; ship `gaugingQEC_auxQubit_overhead_le` theorem (W·polylog(W) auxiliary-qubit overhead). **Wave 6v.1 also creates the D6 bundle infrastructure** per strategy synthesis §3.5.3 (Stage 12 task list).

**Bundle target:** D6 §3 (new) + I1 cross-bridge.
**D6 creation tasks (Stage 12 of this wave):**
1. `papers/D6/` directory + `bundle_metadata.json` per `docs/BUNDLE_DIRECTORY_SCHEMA.md`.
2. `docs/PAPER_STRATEGY.md` update: 14 → 15 bundles.
3. `docs/PAPER_DRAFT_MAPPING.md` update: D6 section assignments.
4. `docs/BUNDLE_READINESS_HEATMAP.md`: D6 readiness tracking added.
5. `SK_EFT_Hawking_Inventory_Index.md` §7: bundle table 14 → 15.
6. `docs/agents/claims-reviewer-bundle-prompts.md`: D6 bundle-anchor entry.
7. F-bundle FT-QC chapter checklist entry (formerly follow-up B1; see strategy synthesis §3.5.3 task #8).

**Key substrate:** `GaugeErasure.lean`, `GaugeEmergence.lean`, `SymTFTAudit/Drinfeld*.lean`, `VillainHamiltonian.lean`, `FKGappedInterface.lean`, `FaultTolerance/`.

### Wave 6v.2 — Google/Oratomic T-gate counts for Shor circuits

**Goal:** Apply the project's T-gate compiler (`scripts/phase6p_tgate_compiler.py` family) to Shor ECDLP-secp256k1 + Shor RSA-2048 arithmetic circuits; ship `shor_ecc256_tgate_count_le` Lean theorem building on the Phase 6t tight-ε SK headline; produce formally verified independent confirmation of the Google/Oratomic estimates.

**Bundle target:** D6 §5 (primary) + D4 + I1 cross-bridges.
**Key substrate:** `FKLW/SolovayKitaevPathA.lean` (Phase 6t tight-ε SK), `QCyc40Ext.lean`, T-gate compiler scripts.

### Wave 6v.5 — APM-LDPC code substrate + hashing-bound LDP sub-wave

**Goal:** Formalize affine-permutation-matrix LDPC code family over the project's cyclotomic substrate; prove encoding rate `k/n > 1/2` lower bound. **Hashing-bound sub-wave (ships inside 6v.5 per ship-hard D-3):** derive Shannon-capacity hashing bound from `LDP/Cramér.lean` applied to noise process.

**Bundle target:** D6 §4 + I1.
**Key substrate:** `QCyc*.lean` cyclotomic infrastructure, `FaultTolerance/`, `LDP/`, `VerifiedJackknife.lean`, `VerifiedStatistics.lean`.

### Wave 6v.6 — W-state QFT decomposition in Q(ζ_N)

**Goal:** Formalize the Kyoto/Hiroshima 2025-09 W-state single-shot projective-measurement circuit as a Q(ζ_N) cyclotomic decomposition; bridge to Phase 6t SK quantitative synthesis bounds.

**Bundle target:** D6 §6.
**Key substrate:** `QCyc*.lean` family, `FKLW/SolovayKitaevPathA.lean`, `ETH/`, `RTCasiniHuertaBounds.lean`.

### Wave 6v.8 — NbRe triplet superconductor full SOTA BdG + SPT classification (heaviest wave)

**Goal:** Ship full SOTA BdG model for NbRe (3D non-centrosymmetric lattice + SOC + d-vector triplet pairing + singlet-triplet mixing), classify topological phase under broken-inversion + (preserved or broken) time-reversal subgroup, bridge to MTC anyon edge theory, ship inverse-spin-valve-effect theorem in toy S/F/S analog. Sub-wave structure: 8.A (parameters + provenance) → 8.B (toy BdG toe-hold) → 8.C (full SOTA) → 8.D (D2 + D4 paper lifts).

**Bundle targets:** D2 §"SPT classification — material exhibits" (primary) + D4 §"topological-qubit substrate candidates" (cross-bridge).
**Key substrate:** `SPTClassification.lean`, `Z16Classification.lean`, `SpinBordism.lean`, `BdGHamiltonian.lean`, `FKGappedInterface.lean`, `PauliMatrices.lean`, `MajoranaKramers.lean`, `FermiPointTopology.lean`, `IsingBraiding.lean`.
**No-new-axioms discipline:** any irreducible gap (e.g., 3D-winding-number identity Mathlib lacks) lands as tracked Prop with discharge plan in the wave roadmap, NOT a new project-local axiom.

---

## Recommended sequencing

Phase 6v wave order (per strategy synthesis §6):

1. **6v.4** Penn TMD — warmup
2. **6v.3** DKM F3 polariton — resolves Phase 6q open question
3. **6v.1** Williamson/Yoder gauging QEC — **creates D6 bundle**
4. **6v.2** T-gate counts for Shor — D6 §5
5. **6v.5** APM-LDPC + hashing-bound — D6 §4
6. **6v.6** W-state QFT in Q(ζ_N) — D6 §6
7. **6v.8** NbRe SOTA — D2 + D4

**Compaction-survivability protocol:** Each wave's per-wave roadmap (`docs/roadmaps/Phase6v/Wave_6v.<N>_Roadmap.md`) is the canonical handoff document; created at Stage 1, updated at Stage 12. Resist letting the synthesis doc become a substitute for per-wave roadmaps — the strategy synthesis is the decision artifact, NOT the operational document for each wave.

**Stage 13 bundle-level review:** D6 bundle-level Stage-13 adversarial review runs after Wave 6v.6 ships (last D6-contributing wave); precedes D6 arXiv preprint preparation.

**D6 arXiv preprint:** prepared at Phase 6v close (post-Wave-6v.6 Stage-13 bundle review). Downstream coordination handled separately.

---

## Cross-phase coordination

- **Phase 6q strengthening pass** (separate session, in flight): should land before Phase 6v.3 (which builds on Phase 6q substrate).
- **Phase 6r / 6s / 6t / 6u**: independently scoped; do NOT block Phase 6v. Phase 6u is a planning skeleton with "(likely Phase 6w)" track references that should be **re-slotted to a later phase letter** since Phase 6w is now claimed for Tindall/Sels + Aalto material per D-8.
- **Phase 6w** (Classical Simulability & Quantum Advantage in Analog Hawking — Tensor-Network Substrate): follows Phase 6v or runs in parallel if substrate work permits. See `docs/roadmaps/Phase6w_Roadmap.md`.

---

## References

- **External opportunity-scan source docs (raw external research; workspace-level, not in repo):** `temporary/working-docs/phase6v/External-Recs-Opportunity-scan/`
- **Wave Execution Pipeline:** `docs/WAVE_EXECUTION_PIPELINE.md`
- **Paper Strategy (14 → 15 bundles at Wave 6v.1 ship):** `docs/PAPER_STRATEGY.md`
- **Bundle Readiness Heatmap:** `docs/BUNDLE_READINESS_HEATMAP.md`
- **Phase 6w sibling roadmap:** `docs/roadmaps/Phase6w_Roadmap.md`
- **Predecessor Phase 6q close:** memory entry `project_phase6q_complete_2026_05_23`
- **Predecessor Phase 6t close:** `docs/PHASE6T_QUANTITATIVE_SK_COMPLETE.md`
