# Phase 6w: Classical Simulability & Quantum Advantage in Analog Hawking — Tensor-Network Substrate

## Technical Roadmap — May 2026

*Prepared 2026-05-25 PM. Approved 2026-05-25 PM per strategy synthesis decision D-8.*

**Trigger condition:** The Phase 6v strategy synthesis (`temporary/working-docs/phase6v/Phase6v_Strategy_Synthesis.md`) initially packed the Tindall/Sels + Aalto material into a single Phase 6v wave (former 6v.7 "KZM-Unruh bridge") plus parked the deeper sub-claims (A1a, A1b, A1c) in the follow-up list. Second-pass LoE review surfaced that the combined ambition is genuinely a multi-wave program (~16–21 sessions) — too large for a single Phase 6v wave but too coherent to scatter across the follow-up list. User direction D-8 authorized a separate Phase 6w to fully scope the material.

**Headline goal:** ship a formally verified framework for **classical simulability of analog Hawking radiation**: when do belief-propagation tensor-network methods (à la Tindall/Sels) and Chebyshev tensor-network methods (à la Aalto) classically simulate analog-Hawking observables, and by contrapositive — when does a quantum processor genuinely have an advantage? Deliverables span new substrate (BP-on-TN + Chebyshev-TN + aperiodic-lattice formalization) and headline theorems (LDP-controlled BP convergence + categorical-Chern ↔ real-space-Chern bridge + combined quantum-advantage demarcation).

**Predecessor work assumed clean:**
- Phase 6v Wave 6v.1 (D6 bundle creation) AND Wave 6v.6 (W-state QFT in Q(ζ_N)) preferred-but-not-required. Phase 6w can technically run in parallel with Phase 6v after Phase 6v.1 ships, but the cleaner cadence is sequential.
- LDP/ substrate (Cramér / Sanov / Varadhan / contraction principle) — already shipped pre-Phase 6v.
- `HawkingUniversality.lean` + `WKBConnection.lean` — already shipped.

**Project rule applied:** No new project-local axioms (Pipeline Invariant #15 RESPECTED). No `maxHeartbeats` overrides in proof bodies (Invariant #10). **Substrate-heavy phase:** several waves build Mathlib-PR-quality substrate (BP on factor graphs, Chebyshev TN contraction, aperiodic lattices) that the project does not currently have. Each substrate-building wave should be scoped with explicit Mathlib-upstream-PR option from Stage 1.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY PHASE 6w WAVE WORK:**
>
> 1. **Mandatory project bootstrap** per workspace `CLAUDE.md` Mandatory References list.
> 2. **Read this roadmap end-to-end** before any wave-level claim.
> 3. **Read the canonical strategy synthesis** at `temporary/working-docs/phase6v/Phase6v_Strategy_Synthesis.md` — particularly §8 (former A1a/A1b/A1c follow-up cluster, now constituting Phase 6w).
> 4. **External opportunity-scan source docs** at `temporary/working-docs/phase6v/External-Recs-Opportunity-scan/` — especially the Perplexity capture (Tindall/Sels coverage) + the Quantum Computing 30-day list (Aalto entry #5).
> 5. **Primary literature must be cached before Stage 3 substrate work:**
>    - **Tindall/Sels et al.** *Science* 392, 868 (2026), DOI 10.1126/science.adx2728 — disordered TFIM tensor networks; KZM exponent extraction.
>    - **Aalto group quasicrystal-Chern-mosaic paper** *PRL* Apr 2026 (Editor's Suggestion) — Chebyshev TN methods on 268M-site quasicrystal Hamiltonians.
>    - **Kibble-Zurek-Unruh correspondence** — locate the canonical theoretical references (Hu et al.; Anglin & Zurek; etc.).
> 6. **Per-wave roadmap docs** at `docs/roadmaps/Phase6w/Wave_6w.<N>_Roadmap.md` are created at Stage 1 of each wave.
> 7. **Do not delegate Lean theorem proving to subagents.** MCP loop default; Aristotle is fallback.
> 8. **No PM / time estimates anywhere** — by user direction.
> 9. **Substrate-PR-quality scoping:** for each substrate-building wave (6w.2 BP on TN; 6w.4 Chebyshev TN + aperiodic lattices), evaluate at Stage 1 whether the substrate should be (a) developed in-project under `lean/SKEFTHawking/`, (b) developed as an explicit Mathlib upstream-PR pre-effort, or (c) developed in a hybrid mode with an in-project Lean module that proxies Mathlib API. Default: option (c).

---

## Wave catalog — Phase 6w (7 waves; Tindall/Sels + Aalto thread)

**Status legend:** ✅ SHIPPED / 🟡 IN-PROGRESS / 📝 WORKING DOC / ⏳ NOT STARTED.

| Wave | Title | Status | Bundle absorption | LoE |
|---|---|---|---|---|
| **Wave 6w.1** | Kibble-Zurek-Unruh bridge (foundation; lifted from former Phase 6v.7) | ✅ SHIPPED 2026-05-26 PM | D1 + E1 + E2 reinforcement | 1 sess |
| **Wave 6w.2** | Belief propagation on tensor networks — Mathlib substrate | ⏳ NOT STARTED | I1 substrate; later D7 candidate | 3–4 sess |
| **Wave 6w.3** | LDP-controlled classical-simulability sub-claim (former A1a) | ⏳ NOT STARTED | D1 cross-bridge to LDP/ + I-bundle section | 2 sess |
| **Wave 6w.4** | Chebyshev tensor-network + aperiodic-lattice substrate | ⏳ NOT STARTED | I1 substrate; later D7 candidate | 3–4 sess |
| **Wave 6w.5** | Categorical-Chern ↔ real-space-Chern bridge theorem (former A1b) | ⏳ NOT STARTED | D4 extension + SPTClassification | 2–3 sess |
| **Wave 6w.6** | Combined classical-simulability demarcation for analog Hawking (former A1c) | ⏳ NOT STARTED | D1 + E1 + E2 + possibly new D7 | 2–3 sess |
| **Wave 6w.7** | D1 / E1 / E2 absorption + (optional) D7 bundle spin-out + Stage-13 review | ⏳ NOT STARTED | Bundle lift + adversarial review | 2 sess |

**Total estimated effort:** ~16–21 sessions across 7 waves.

**Wave dependencies:**
- 6w.1 (foundation) is independent of all other waves; can ship first or any time.
- 6w.2 → 6w.3 (substrate → headline) must be sequential.
- 6w.4 → 6w.5 (substrate → headline) must be sequential, independent of 6w.2/6w.3.
- 6w.6 (combined demarcation) depends on both 6w.3 AND 6w.5.
- 6w.7 (absorption) depends on 6w.6.

**Recommended sequencing:** 6w.1 → 6w.2 → 6w.3 → 6w.4 → 6w.5 → 6w.6 → 6w.7 (linear); OR 6w.1 → (6w.2 || 6w.4 in parallel sessions) → (6w.3 || 6w.5) → 6w.6 → 6w.7 (parallel branches; faster but harder to coordinate).

---

## Bundle architecture decision — D7 spin-out vs D1/E1/E2 absorption

**Open at phase start:** does Phase 6w's content warrant a new bundle **D7 — "Classical Simulability and Quantum Advantage in Analog Hawking"** (Tier 1 deep, 16th publication target), or does it absorb into existing D1 + E1 + E2 as cross-bundle additions?

**Decision rule:** if the combined demarcation theorem (Wave 6w.6) lands as a substantive headline result with broad applicability beyond analog Hawking (e.g., applicable to general LDP-controlled-BP classical-simulability classification), spin out D7. If the content is naturally absorbed as "quantum-advantage demarcation" sections within D1 + E1 + E2, keep it as cross-bundle absorption.

**Decision timing:** evaluate at Wave 6w.6 close (Stage 10 of that wave). User authorization required to add a 16th bundle target per Pipeline Invariant #14.

**Default posture if undecided:** absorb into D1 §"quantum-advantage demarcation" cross-bridge + E1 §"classical-simulability boundary" cross-bridge + E2 §"classical-simulability boundary" cross-bridge. Keep D7 as a Phase 7+ option.

---

## Wave-by-wave detail

### Wave 6w.1 — Kibble-Zurek-Unruh bridge (foundation)

**Goal:** Lift the former Phase 6v.7 Tindall/Sels KZM-Unruh bridge into Phase 6w as the foundation wave. Ship `surface_gravity_bounds_kzm_exponent` Lean theorem: the SK-EFT surface gravity κ at the analog horizon bounds the KZM exponent extracted by tensor-network methods on disordered spin glasses, via the WKB connection formula's modified unitarity. Cite Tindall/Sels as independent classical-simulation validation.

**Bundle target:** D1 + E1 + E2 reinforcement; light foundation for the deeper 6w.3 + 6w.5 + 6w.6 waves.
**Key substrate:** `HawkingUniversality.lean`, `WKBConnection.lean`, `LDP/`, `QuantumCrooks/`, `CrooksAnalogHawking/`, `ETH/`.
**Deliverables:**
1. New module `lean/SKEFTHawking/KibbleZurekUnruh.lean` with the foundation theorem.
2. Bibkey `TindallSels2026Science392` + cached primary source PDF.
3. D1/E1/E2 paper-draft citation passes.

**This wave does NOT build new tensor-network substrate** — that lives in Waves 6w.2 + 6w.4. 6w.1 is the existing-substrate-only foundation.

### Wave 6w.2 — Belief propagation on tensor networks (Mathlib substrate)

**Goal:** Build Lean substrate for belief propagation on tensor-network factor graphs. Define BP message-passing iteration; prove convergence criteria via Bethe-lattice / loopy-graph analysis; characterize BP convergence as an LDP saddle-point condition on the Bethe free energy.

**Bundle target:** I1 substrate (verification methodology); later D7 candidate.
**Key substrate (existing):** `LDP/Cramér.lean`, `LDP/Sanov.lean`, `LDP/Varadhan.lean`.
**Key substrate (NEW):** new module `lean/SKEFTHawking/BeliefPropagation.lean` (or `lean/SKEFTHawking/TensorNetworks/BeliefPropagation.lean` if a TensorNetworks subdirectory is warranted).
**Mathlib-PR potential:** HIGH — factor graphs + BP message-passing iteration is generic infrastructure not currently in Mathlib. Consider whether sub-claims should be extracted as Mathlib PRs.

**Stage 1 scoping output:** working doc at `temporary/working-docs/phase6w/wave_6w_2_bp_tensor_network_substrate_plan.md`.

### Wave 6w.3 — LDP-controlled classical-simulability sub-claim (former A1a)

**Goal:** Headline theorem from Wave 6w.2 substrate: **BP convergence on a PEPS tensor network is governed by the LDP rate function of the loop-correction terms; classical simulability of the underlying dynamics holds when this rate function is below a computable threshold.** Connect to Tindall/Sels's empirical D-Wave-Advantage2 comparison; identify the threshold parameter regime.

**Bundle target:** D1 cross-bridge to LDP/ + new I-bundle section (later D7 candidate).
**Key substrate:** Wave 6w.2 BP substrate + existing LDP/.
**Deliverables:**
1. Theorem `bp_convergence_iff_ldp_below_threshold` (precise statement TBD at Stage 1).
2. Numerical cross-check against Tindall/Sels-extracted KZM exponent.
3. Paper-draft section (target bundle TBD per D7 spin-out decision).

### Wave 6w.4 — Chebyshev tensor-network + aperiodic-lattice substrate

**Goal:** Build Lean substrate for Chebyshev tensor-network contraction methods (Aalto-style) and for aperiodic/quasicrystal lattices. Define Chebyshev polynomial expansion of TN contraction; define quasicrystal lattice via cut-and-project method (canonical Penrose tiling + generalizations); prove convergence + complexity bounds.

**Bundle target:** I1 substrate; later D7 candidate.
**Key substrate (NEW):** new modules `lean/SKEFTHawking/TensorNetworks/ChebyshevTN.lean` + `lean/SKEFTHawking/Lattices/AperiodicLattice.lean` (or similar; precise module structure decided at Stage 1).
**Mathlib-PR potential:** HIGH for both Chebyshev TN + aperiodic-lattice infrastructure.

**Stage 1 scoping output:** working doc at `temporary/working-docs/phase6w/wave_6w_4_chebyshev_aperiodic_substrate_plan.md`.

### Wave 6w.5 — Categorical-Chern ↔ real-space-Chern bridge theorem (former A1b)

**Goal:** Bridge theorem: **categorical Chern class (from fusion-category data) coincides with real-space Chern marker (from tensor-network density matrices) in the crystalline limit.** Extend to quasicrystal limit using Wave 6w.4 substrate.

**Bundle target:** D4 extension + SPTClassification extension.
**Key substrate:** Wave 6w.4 Chebyshev TN + aperiodic-lattice substrate + existing `StringNet.lean`, `FusionCategory.lean`, `FPDimension.lean`, `SPTClassification.lean`, `FermiPointTopology.lean`.
**Deliverables:**
1. Theorem `categorical_chern_eq_real_space_chern_crystalline`.
2. Theorem `categorical_chern_eq_real_space_chern_quasicrystalline` (extension).
3. D4 paper-draft addition + SPTClassification cross-bridge.

### Wave 6w.6 — Combined classical-simulability demarcation (former A1c)

**Goal:** Combine 6w.3 (BP-LDP simulability) + 6w.5 (categorical-real-space Chern bridge) into a unified demarcation theorem: **for an analog Hawking system on a (possibly aperiodic) lattice, the parameter regime in which BP-LDP simulability holds AND the categorical Chern marker is well-defined is exactly the regime where classical simulation is competitive with a quantum processor.** By contrapositive: outside that regime, quantum processors have genuine advantage.

**Bundle target:** D1 + E1 + E2 + (possibly D7 if spin-out triggers).
**Key substrate:** Waves 6w.3 + 6w.5.
**Deliverables:**
1. Theorem `analog_hawking_quantum_advantage_demarcation` (precise statement TBD at Stage 1 of this wave).
2. **D7 spin-out decision** per "Bundle architecture decision" section above.

### Wave 6w.7 — D1/E1/E2 absorption + (optional) D7 bundle spin-out + Stage-13 review

**Goal:** Bundle lift across D1 + E1 + E2 (and D7 if spun out per Wave 6w.6 decision). Stage-13 adversarial review of Phase 6w content per `physics-qa:claims-reviewer` agent. Stage-14 QI sweep at Phase 6w close.

**Deliverables:**
1. D1 §"quantum-advantage demarcation" addition.
2. E1 §"classical-simulability boundary" addition.
3. E2 §"classical-simulability boundary" addition.
4. (If D7 spins out) `papers/D7/` bundle skeleton + PAPER_STRATEGY.md 15 → 16 bundle update + downstream-doc updates per BUNDLE_LIFT_PROCEDURE.md.
5. Stage-13 adversarial review report.
6. Stage-14 QI register update.

---

## Cross-phase coordination

- **Phase 6v** (sibling phase): D6 bundle creation runs in Phase 6v; D6 ships before Phase 6w substantively closes. Phase 6w can begin in parallel with Phase 6v after Phase 6v.1 (D6 bundle creation) ships, but the cleaner cadence is sequential.
- **Phase 6u** (Generic-Alphabet SK substrate, planning skeleton): Phase 6u's Wave catalog references "(likely Phase 6w)" for Track T-A2 (Clifford+CCZ) and Track T-B (Read-Rezayi). **These references should be re-slotted to a later phase letter (Phase 6x or beyond)** since Phase 6w is now claimed for Tindall/Sels + Aalto material per D-8. See update note in `docs/roadmaps/Phase6u_Roadmap.md`.

---

## References

- **External opportunity-scan source docs (raw external research; workspace-level, not in repo):** `temporary/working-docs/phase6v/External-Recs-Opportunity-scan/`
- **Wave Execution Pipeline:** `docs/WAVE_EXECUTION_PIPELINE.md`
- **Paper Strategy:** `docs/PAPER_STRATEGY.md`
- **Bundle Lift Procedure:** `docs/BUNDLE_LIFT_PROCEDURE.md`
- **Phase 6v sibling roadmap:** `docs/roadmaps/Phase6v_Roadmap.md`
- **Phase 6u roadmap (Track T-A2 / T-B re-slot note):** `docs/roadmaps/Phase6u_Roadmap.md`
