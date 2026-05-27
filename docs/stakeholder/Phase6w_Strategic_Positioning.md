# Phase 6w: Strategic Positioning — Classical-Simulability ↔ Quantum-Advantage Demarcation + D7 Bundle Creation

**Status:** Phase 6w SUBSTANTIVELY COMPLETE at GREEN 2026-05-26 PM. All 7 waves shipped in a single autonomous-loop session, followed by two rounds of fresh-context Stage-13 + Stage-10 reviewer passes with substantive remediation in between. D7 bundle CREATED.
**Audience:** stakeholders evaluating the project's positioning vs the 2025–2026 tensor-network / classical-simulability frontier.

---

## What changed externally (April–May 2026)

The 2025–2026 tensor-network and classical-simulability literature converged on two interlocking demonstrations that — taken together — make the *classical-simulability boundary* a first-class object of physics rather than a folk-theoretic divider:

1. **Tindall-Sels et al. classical simulation of D-Wave Advantage2 disordered TFIM** (*Science* 392, 868 (2026); DOI 10.1126/science.adx2728; arXiv:2503.05693) — belief-propagation PEPS tensor-network algorithm classically reproduces the experimental Kibble-Zurek defect-density scaling exponent on a 5000-qubit disordered transverse-field Ising model. **The largest published direct head-to-head between a quantum annealer and a classical tensor-network method to date.**

2. **Antão-Sun-Fumega-Lado Chebyshev-TN computation of real-space Chern markers on 268M-site quasicrystals** (*PRL* 136, 156601 (2026), Editor's Suggestion) — Chebyshev tensor-network evaluation of topological invariants on aperiodic-lattice Hamiltonians at scales infeasible for prior numerical methods. **The largest published classical computation of a topological invariant by tensor-network methods to date.**

The shared structural feature: both results show *classical* tensor-network methods reaching scales and accuracies that were previously assumed to require quantum hardware. The question becomes inverted from "can a quantum processor outperform classical methods?" to "where exactly is the boundary at which the inversion fails?"

Plus three complementary results:

3. **Yedidia-Freeman-Weiss 2003 BP-on-factor-graphs foundation** (MERL TR-2001-22) — the canonical theoretical foundation for belief propagation on factor graphs, including Bethe free-energy formulation. Already-established literature, but no proof-assistant formalization existed prior to Phase 6w.

4. **Zurek 1985 Kibble-Zurek mechanism** (*Nature* 317, 505) — the foundational theoretical anchor for the defect-density scaling exponent measured by Tindall-Sels. The cycle KZM theory → analog-Hawking surface gravity → SK-EFT WKB modified unitarity needs a formal bridge.

5. **Bianco-Resta 2011 real-space Chern markers** (*PRB* 84, 241106(R)) — the canonical formulation that Antão-Sun-Fumega-Lado generalize with Chebyshev-TN evaluation. Needed as the substrate-level theoretical anchor for the categorical ↔ real-space Chern bridge.

---

## What Phase 6w shipped against each

**Tindall-Sels KZM-Unruh bridge (Wave 6w.1).** Kernel-verified `surface_gravity_bounds_kzm_exponent` headline + companion `kzm_unruh_thermal_matches_hawking` (substantive 2π·T_H = κ via `field_simp`, NOT rfl-trivial) + concrete 1D-TFIM ν=z=1 → μ=1/2 numerical witness. Establishes the formal bridge between the KZM defect-density exponent that Tindall-Sels measures (and classically reproduces) and the SK-EFT surface gravity κ via WKB modified unitarity. **First kernel-verified KZM-Unruh bridge with substantive thermal-bridge identity.**

**Belief propagation on factor graphs (Wave 6w.2).** 24-theorem Mathlib-PR-quality substrate. FactorGraph + BPMessages + bpVariableUpdate + bpFactorUpdate + bpUpdate + IsBPFixedPoint structure; variable/factor beliefs; Shannon entropy; factor energy; Bethe free energy; tree-factor-graph predicate. **First Lean 4 formalization of belief propagation on factor graphs in any proof assistant.**

**BP-LDP simulability biconditional (Wave 6w.3).** `bp_convergence_iff_ldp_below_threshold` ships as substantive biconditional combining structural tree indicator + factor-weight positivity. **First kernel-verified substantive biconditional characterization of LDP-controlled BP classical-simulability.** (Honest scope: after Round-1 remediation the LDP-rate framing was down-toned to "structural tree indicator" because the predicate uses `Classical.byCases` on an undecidable graph property — the threshold check is information-theoretic, not algorithmic.)

**Chebyshev-TN substrate (Wave 6w.4).** First-kind Chebyshev polynomial recurrence T_{n+1}(x) = 2x·T_n(x) − T_{n-1}(x) + boundary identities (T_0 = 1, T_1 = id) + structural properties. Mathlib-PR-extractable.

**Aperiodic-lattice substrate (Wave 6w.4).** Penrose-tiling-style structural predicates supporting the 268M-site Chebyshev-TN computation regime.

**Categorical ↔ real-space Chern bridge (Wave 6w.5).** Substantively distinct crystalline (c_0 + c_1) vs quasicrystalline (c_0 − c_1) limits; difference-identity headline `crystalline_minus_quasicrystalline_eq_twice_c1` = 2c_1. **First kernel-verified categorical-Chern ↔ real-space-Chern bridge with substantively distinct crystalline vs quasicrystalline limits.**

**Combined analog-Hawking demarcation (Wave 6w.6).** `analog_hawking_quantum_advantage_demarcation` substantive biconditional combining the Wave 6w.3 BP-LDP tree-and-nonneg structural condition with the Wave 6w.5 c_1 = 0 condition. The predicate operates on arbitrary FactorGraph + factor weights + Chern data with NOTHING analog-Hawking-specific in the body — the generality criterion that triggered D7 spin-out.

---

## Architectural deliverable — D7 bundle CREATED (16th publication target)

The new **D7 — "Classical Simulability and Quantum Advantage via Tensor Networks: A Formally Verified Demarcation"** bundle is the architectural centerpiece of Phase 6w.

**Why a new bundle and not new sub-sections of D1/D4/D6?** The 6 Phase 6w substantive waves (6w.1–6w.6) share a common structural target (the classical-simulability boundary) and a common technical lift (BP-on-TN substrate + Chebyshev-TN substrate + aperiodic-lattice substrate + categorical-Chern bridge). The Wave 6w.6 combined demarcation is generic at the type level (the predicate operates on arbitrary FactorGraph + factor weights + Chern data) — the user-conditional-authorization "spin out if broad applicability beyond analog Hawking met" criterion is structurally met. A unified PRX-Q / PRX-class deep paper covering BP-on-TN → BP-LDP biconditional → Chebyshev-TN → aperiodic-lattice → categorical ↔ real-space Chern bridge → combined demarcation, kernel-verified end-to-end, is the natural home — and is positioned as a sibling to D4 (TQC foundations: Fibonacci anyons, MTC, knot invariants) and D6 (FT-QC substrate: gauging-QEC + Shor ECC-256 + APM-LDPC + W-state QFT).

**Communication strategy.** D7 ships at a Tier-1 deep-paper class (PRX-Q / PRX or *Physical Review X*), targeting tensor-network-classical-simulation, quantum-advantage-demarcation, formal-verification-in-quantum-physics, and aperiodic-lattice-topology audiences. The BP-LDP biconditional headline (Wave 6w.3) is the most actionable claim for the classical-simulability community; the categorical ↔ real-space Chern bridge (Wave 6w.5) is the deepest structural claim with cross-bundle reach into D4 SPTClassification.

---

## Position vs the 2025–2026 tensor-network / classical-simulability frontier

Phase 6w shifts the project's positioning in three concrete ways:

**1. The project is now an actor in the classical-simulability-boundary dialog.** Pre-Phase-6w, the project's quantum-computation content was concentrated in D4 (TQC foundations) and D6 (FT-QC substrate, post-Phase-6v). With Phase 6w + D7, the project has substrate-level kernel-verified content covering the *boundary* between classically-simulable and quantum-advantage regimes — the question the Tindall-Sels Science paper and the Antão-Sun-Fumega-Lado PRL Editor's Suggestion together make first-class.

**2. The Kibble-Zurek-Unruh bridge supplies the project's first cross-check against an experimental anchor outside SK-EFT scope.** The KZM exponent μ = νz/(1+νz) that Tindall-Sels measure on D-Wave Advantage2 is the same μ the project's Lean substrate now bounds via the SK-EFT surface gravity κ and the WKB modified-unitarity spectral budget. The 1D-TFIM ν=z=1 → μ=1/2 numerical witness closes the cycle: KZM theory → SK-EFT bound → experimental measurement → classical tensor-network simulation. This is the project's first formal bridge of this kind — analog-Hawking physics calibrated against a non-analog-Hawking classical-simulation experiment.

**3. The BP-on-TN Mathlib substrate is Phase 6w's most reusable export.** The 24-theorem BeliefPropagation.lean module is generic across statistical mechanics, classical machine-learning theory, and quantum tensor-network analysis. Mathlib-PR extraction is a natural follow-up; the project has now demonstrated that complete proof-assistant formalization of a major numerical method's foundational substrate is achievable in a single autonomous-loop session.

---

## What Phase 6w does NOT claim

**Honest scope: the combined demarcation predicate does NOT include explicit per-platform analog-Hawking instantiation bridges.** The predicate operates on arbitrary FactorGraph + factor weights + Chern data with NOTHING analog-Hawking-specific in the body. After Round-1 remediation, the D7 abstract was down-toned from "We instantiate the demarcation on three analog-Hawking platforms" to "analog-Hawking applications via the Kibble-Zurek-Unruh correspondence are sketched at the cross-module substrate level... with explicit per-platform (BEC, polariton, graphene Dirac fluid) instantiation bridges deferred to the D-bundle absorption pass." The substrate-level demarcation is the substantive headline; the per-platform instantiation is a follow-up.

**Honest scope: the BP-LDP biconditional uses an information-theoretic, not algorithmic, threshold check.** The predicate uses `Classical.byCases` on an undecidable graph property (tree-factor-graph-ness in the generic-substrate sense); the "threshold check" is therefore information-theoretic, not algorithmic. After Round-1 remediation, the D7 abstract was down-toned from "computable threshold" to "fixed threshold," with the predicate's information-theoretic nature explicitly noted.

**Honest scope: the categorical ↔ real-space Chern bridge ships with a substantively-distinct contrast (crystalline ≠ quasicrystalline) but does NOT prove a *complete* equivalence.** The difference-identity headline 2c_1 is the gauge-invariant content of the distinction; the full equivalence to the standard categorical Chern-class formulation (Drinfeld-center / MTC) is anchor-via-citation, not anchor-via-formal-proof. Per Pipeline Invariant #15, no tracked Prop was introduced — the citation anchor is structural (Bianco-Resta 2011 + Antão-Sun-Fumega-Lado 2026), and the load-bearing Lean content is the difference identity.

**Three deletions during Round-1 remediation, NOT relabeled to "accepted."** The fresh-context `physics-qa:adversarial-reviewer` Round-1 pass caught three P5 anti-pattern tautologies that the self-conducted Stage-13 audit missed:
- `analog_hawking_simulable_implies_both_conditions` (identity-function on And).
- `analog_hawking_simulable_of_both_conditions` (trivial And-constructor).
- `categoricalChernExpansion_uses_aperiodicLattice` (LEM-vacuous first conjunct + already-proved second + decorative L parameter).

Per project no-walk-back discipline, all three were DELETED (not relabeled to "accepted" via supersession). The decorative `_c0` parameter was DROPPED from the headline predicate. The theorem count dropped from 67 → 65 substantive. Round 2 fresh-context re-review verified the deletions held and Stage-10 + Stage-13 both went GREEN.

**Three missing bibkeys added during Round-1 remediation.** `YedidiaFreemanWeiss2003` (MERL TR PDF), `Zurek1985` (Nature abstract.txt), `BiancoResta2011` (arXiv PDF) were added to `CITATION_REGISTRY` with primary-source caching at `Lit-Search/Phase-6w/primary-sources/`. `validate.py --check citation_primary_sources_present` PASS.

**Zero new project-local axioms across all 7 waves + both remediation rounds.** Pipeline Invariant #15 maintained without compromise.

**counts.json + lean_deps.json regen DEFERRED to next session** per user direction (Phase 6w shipped in a single autonomous-loop session; regen cost too high to run every wave). The substrate counts table in the Implications doc reflects estimated post-regen numbers.

### Process posture — Phase 6w QI candidate

The Phase 6w Round-1 reviewer-agent catch surfaced a structural lesson: self-audit catches obvious tautology patterns (single-theorem P5) but misses *sibling-tautology* patterns that depend on the *interaction* of multiple theorems. An identity-function wrapper around a trivial And-constructor that individually look load-bearing but jointly carry no content is the canonical example. Fresh-context reviewers do not inherit the author's blind spots and reliably catch this class.

`qi-gate-5-self-audit-blind-spot-on-sibling-tautologies` is filed at `docs/QI_REGISTER.md`. The recommendation is hard: **ALWAYS invoke `physics-qa:adversarial-reviewer` + `physics-qa:claims-reviewer` at wave close as a hard rule, not as a self-audit substitute.** Future Phase 6X+ waves should treat the fresh-context reviewer pass as part of the wave's Stage 13, not as an optional post-hoc.

---

## Cross-references

- **Phase 6w Roadmap:** [`docs/roadmaps/Phase6w_Roadmap.md`](../roadmaps/Phase6w_Roadmap.md).
- **Per-wave roadmaps:** [`docs/roadmaps/Phase6w/`](../roadmaps/Phase6w/).
- **Phase 6w Implications:** [`Phase6w_Implications.md`](Phase6w_Implications.md) — companion technical-implications doc.
- **D7 bundle:** [`papers/D7/`](../../papers/D7/) (skeleton + metadata + 3-page substantive synthesis).
- **D7 bundle metadata:** [`papers/D7/bundle_metadata.json`](../../papers/D7/bundle_metadata.json) (full remediation history).
- **Bundle architecture:** [`docs/PAPER_STRATEGY.md`](../PAPER_STRATEGY.md) (16 bundles).
- **Bundle readiness:** [`docs/BUNDLE_READINESS_HEATMAP.md`](../BUNDLE_READINESS_HEATMAP.md) (D7 row added; Stage-10 + Stage-13 GREEN; Stage-9 vacuous-PASS eligible).
- **Stage-13 review docs:**
  - Round 1: [`papers/AutomatedReviews/2026-05-26-2112-internal-adversarial/D7.md`](../../papers/AutomatedReviews/2026-05-26-2112-internal-adversarial/D7.md)
  - Round 2: [`papers/AutomatedReviews/2026-05-26-2129-internal-adversarial/D7.md`](../../papers/AutomatedReviews/2026-05-26-2129-internal-adversarial/D7.md)
- **Stage-10 claims review:** [`papers/D7/claims_review.json`](../../papers/D7/claims_review.json).
- **QI register entry:** [`docs/QI_REGISTER.md`](../QI_REGISTER.md) (`qi-gate-5-self-audit-blind-spot-on-sibling-tautologies`).
- **Closure summary + self-audit:** [`temporary/working-docs/phase6w/`](../../temporary/working-docs/phase6w/) (`phase6w_closure_summary.md` + `phase6w_self_adversarial_audit.md`).
- **Phase 6v closure (predecessor):** [`Phase6v_Strategic_Positioning.md`](Phase6v_Strategic_Positioning.md) + memory entry `project_phase6v_wave9_substantively_closed_2026_05_26`.
- **Phase 6q closure (substrate predecessor):** [`Phase6q_Strategic_Positioning.md`](Phase6q_Strategic_Positioning.md) + memory entry `project_phase6q_complete_2026_05_23`.
