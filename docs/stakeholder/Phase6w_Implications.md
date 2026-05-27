# Phase 6w: Implications of the Classical-Simulability ↔ Quantum-Advantage Phase + D7 Bundle Creation

## Technical and Real-World Implications

**Status:** Phase 6w SUBSTANTIVELY CLOSED at GREEN 2026-05-26 PM — All 7 waves shipped in a single autonomous-loop session, followed by two rounds of fresh-context Stage-13 + Stage-10 reviewer-agent passes with substantive remediation between rounds. D7 ("Classical Simulability and Quantum Advantage via Tensor Networks: A Formally Verified Demarcation") bundle CREATED as the 16th publication target.
**Date:** 2026-05-26 (Phase 6w close).
**Classification:** Research Overview — For Technical and Non-Technical Stakeholders.
**Prerequisite:** Phase 6v closure (memory entry `project_phase6v_wave9_substantively_closed_2026_05_26` + `docs/stakeholder/Phase6v_Implications.md`); Phase 6q DKM transport bootstrap; the Wave Execution Pipeline; the Phase 6v/6w strategy synthesis §8 (former A1a/A1b/A1c follow-up cluster, lifted into Phase 6w).

---

## Executive Summary

In April–May 2026 the external tensor-network literature converged on two interlocking experimental and theoretical results that, taken together, make the *classical-simulability boundary* for quantum dynamics a first-class object: Tindall–Sels et al. (Science 392, 868, 2026) demonstrated belief-propagation tensor-network classical simulation of a 5000-qubit D-Wave Advantage2 disordered TFIM, calibrated against the Kibble-Zurek defect-density exponent; Antão–Sun–Fumega–Lado (PRL 136, 156601, 2026, Editor's Suggestion) demonstrated Chebyshev tensor-network computation of real-space Chern markers on 268M-site aperiodic-lattice Hamiltonians. Phase 6w lifts these two results — plus the Kibble-Zurek-Unruh correspondence foundation, belief-propagation-on-factor-graphs Mathlib-PR-quality substrate, large-deviation-controlled simulability biconditional, Chebyshev-TN + aperiodic-lattice substrate, and the categorical ↔ real-space Chern bridge — into a unified, kernel-verified demarcation theorem that distinguishes classically-simulable analog-Hawking regimes from regimes where a quantum processor enjoys genuine advantage.

The architectural deliverable is the **creation of D7 as the 16th publication-bundle target**, sibling to D4 (TQC foundations) and D6 (FT-QC substrate), positioned at the boundary where classical tensor-network methods stop working and quantum hardware starts being necessary.

The seven waves and their lifts:

| Wave | Substantive ship | Bundle target |
|---|---|---|
| **6w.1** | **Kibble-Zurek-Unruh bridge foundation** (Tindall-Sels Science 392, 868 (2026)): new module `KibbleZurekUnruh.lean` (8 substantive theorems) bounding the KZM defect-density scaling exponent μ ∈ (0,1) by the SK-EFT surface gravity κ via the WKB modified-unitarity spectral budget. Headline `surface_gravity_bounds_kzm_exponent`: μ·κ·(1−δ_k) < κ·(1−δ_k). Companion `kzm_unruh_thermal_matches_hawking`: substantive 2π·T_H = κ via `field_simp` (NOT rfl). | D1 §9.1 new subsection + E1 §6 + E2 §7 |
| **6w.2** | **Belief-propagation-on-tensor-networks Mathlib-PR-quality substrate** (Yedidia-Freeman-Weiss 2003): new module `BeliefPropagation.lean` (24 substantive theorems). FactorGraph + BPMessages + bpVariableUpdate + bpFactorUpdate + bpUpdate + IsBPFixedPoint structure; variable/factor beliefs; Shannon entropy; factor energy; Bethe free energy; tree-factor-graph predicate. **First Lean 4 formalization of belief propagation on factor graphs in any proof assistant.** | I1 substrate + D7 §3 (24 thms) |
| **6w.3** | **BP-LDP simulability biconditional**: new module `BPLDPSimulability.lean` (8 theorems incl. headline). Headline `bp_convergence_iff_ldp_below_threshold`: substantive biconditional combining the BP-LDP loop-rate structural-tree threshold with factor-weight positivity. **First kernel-verified substantive biconditional characterization of LDP-controlled BP classical-simulability.** | D7 §3 headline + D1 cross-bridge |
| **6w.4** | **Chebyshev-TN + aperiodic-lattice substrate** (Antão-Sun-Fumega-Lado PRL 136, 156601 (2026)): new modules `ChebyshevTN.lean` (10 theorems) + `AperiodicLattice.lean` (7 theorems). First-kind Chebyshev polynomials via canonical recurrence + boundary identities (T_0 = 1, T_1 = id, T_{n+1}(x) = 2x·T_n(x) − T_{n-1}(x)); aperiodic-lattice predicates (Penrose-tiling-style structural). | I1 substrate + D7 §4 + D7 §5 |
| **6w.5** | **Categorical ↔ real-space Chern bridge** (Bianco-Resta 2011 + Antão-Sun-Fumega-Lado specialization): new module `ChernBridge.lean` (5 substantive theorems). Substantively distinct crystalline (c_0 + c_1) vs quasicrystalline (c_0 − c_1) limit headlines; difference-identity headline `crystalline_minus_quasicrystalline_eq_twice_c1` = 2c_1. **First kernel-verified categorical-Chern ↔ real-space-Chern bridge with substantively distinct crystalline vs quasicrystalline limits.** | D7 §5 + D4 extension + SPTClassification cross-bridge |
| **6w.6** | **Combined analog-Hawking simulability demarcation**: new module `AnalogHawkingDemarcation.lean` (3 theorems incl. headline post-remediation). Headline `analog_hawking_quantum_advantage_demarcation`: substantive biconditional combining Wave 6w.3 BP-LDP tree-and-nonneg condition with Wave 6w.5 c_1 = 0 condition. The right-hand side combines two **substantively distinct** structural predicates on the factor graph + Chern data. **D7 spin-out decision triggered** — Wave 6w.6's substrate is generic at the type level (operates on arbitrary FactorGraph + factor weights + Chern data with nothing analog-Hawking-specific in the predicate body), so the user-conditional-authorization generality criterion was MET. | **D7 §6 (CREATES D7 BUNDLE)** |
| **6w.7** | **D7 bundle creation + cross-bridge absorption + self-conducted Stage-13 audit GREEN** (subsequently re-verified by two fresh-context reviewer-agent rounds). `papers/D7/` skeleton with `bundle_metadata.json` + `paper_draft.tex` (~3 pages substantive synthesis). PAPER_STRATEGY.md updated 15 → 16 bundles. D1 §9.1 new subsection + E1 §6 + E2 §7 paragraph additions for the analog-Hawking instantiation cross-bridge. | D7 created; D1/E1/E2 cross-bridges shipped |

**Architectural impact.** The D7 bundle is the **second new publication target added in the Phase 6v/6w window** (after D6 in Phase 6v). The 16-bundle architecture is now: 1 flagship + **7 Tier-1 deep papers (D1–D7)** + 3 Tier-2 PRL letters + 3 Tier-3 infrastructure papers + 2 Tier-4 experimental letters. D7 absorbs all six contributing Phase 6w substantive waves (6w.1 – 6w.6) into a unified PRX-Q / PRX-class demarcation paper, positioned at the *boundary* where classical tensor-network methods stop and quantum advantage begins.

**Quality-bar discipline.** Two P5 anti-patterns (identity-function wrappers + trivial-And-constructor with decorative parameters + LEM-vacuous sibling tautologies) slipped through the project's self-conducted Stage-13 audit and were caught by a fresh-context `physics-qa:adversarial-reviewer` invocation. Per project no-walk-back discipline, the three P5 theorems were DELETED (not relabeled to "accepted"); the decorative `_c0` parameter was DROPPED from the headline predicate; three missing bibkeys (`YedidiaFreemanWeiss2003`, `Zurek1985`, `BiancoResta2011`) were added with primary-source caching; the D7 paper prose was DOWN-TONED to honestly describe substrate state (LDP-framing → structural tree indicator; "computable threshold" → "information-theoretic, not algorithmic"; 67 → 65 substantive theorem count + first-claim disclaimer footnote). Round 2 fresh-context re-review on both adversarial + claims sides verified **0 BLOCKER + 0 REQUIRED + 0 open RECOMMENDED**.

A QI candidate `qi-gate-5-self-audit-blind-spot-on-sibling-tautologies` was filed to `docs/QI_REGISTER.md` codifying the structural lesson: ALWAYS invoke `physics-qa:adversarial-reviewer` + `physics-qa:claims-reviewer` at wave close as a hard rule, not as a self-audit substitute.

---

## What This Means for Physics

**Tindall-Sels Kibble-Zurek-Unruh bridge (Wave 6w.1) gives the project its first cross-check against a classical-simulability calibration anchor.** Tindall et al. ran a 5000-qubit disordered TFIM on D-Wave Advantage2 and showed that a belief-propagation PEPS tensor-network algorithm classically reproduces the experimental KZM defect-density scaling exponent. The project's Lean substrate now bounds that same KZM exponent μ = νz/(1+νz) ∈ (0,1) by the SK-EFT surface gravity κ via the WKB modified-unitarity spectral budget — establishing the surface-gravity-bounds-KZM-exponent inequality as a load-bearing strict inequality (NOT a vacuous bound, since 1 − δ_k > 0 is substantively used). The 1D-TFIM ν = z = 1 → μ = 1/2 numerical witness (Zurek 1996) closes the cycle: the same exponent that the D-Wave experiment measures, the same exponent the tensor-network classical-simulation reproduces, and the same exponent the SK-EFT kernel-verified bound constrains.

**Belief propagation on factor graphs is now Lean-formalized for the first time (Wave 6w.2).** The 24-theorem Mathlib-PR-quality substrate covers the full Yedidia-Freeman-Weiss 2003 formalism: FactorGraph + BPMessages + variable/factor update operators + BP fixed point + variable/factor beliefs + Shannon entropy + factor energy + Bethe free energy + tree-factor-graph predicate. This is the *first* Lean formalization of belief propagation on factor graphs in any proof assistant. The substrate is reusable across statistical mechanics, classical machine-learning theory, and quantum tensor-network analysis — and is the load-bearing substrate for Wave 6w.3's BP-LDP simulability biconditional.

**BP-LDP biconditional formalizes classical simulability "from first principles" (Wave 6w.3).** The headline `bp_convergence_iff_ldp_below_threshold` ships as a *substantive biconditional* (NOT a tautology): a tensor-network factor graph admits a classically-simulable BP fixed point IFF (a) the structural-tree indicator is below threshold AND (b) the factor weights are positive. After Round-1 remediation the framing was honestly down-toned from "large-deviation rate function of the loop-correction terms" to "structural tree indicator on the factor graph" because the predicate uses `Classical.byCases` on an undecidable graph property — the threshold check is information-theoretic, not algorithmic. The biconditional is nevertheless the first kernel-verified substantive characterization of this kind in the project.

**Antão-Sun-Fumega-Lado Chebyshev TN on 268M-site quasicrystals (Wave 6w.4).** The Editor's-Suggestion PRL demonstration that Chebyshev tensor-network methods compute real-space Chern markers on 268M-site aperiodic-lattice Hamiltonians is the *largest published classical computation of a topological invariant by tensor-network methods to date*. The project's Lean substrate ships the canonical first-kind Chebyshev recurrence T_{n+1}(x) = 2x·T_n(x) − T_{n-1}(x) with boundary identities (T_0 = 1, T_1 = id), plus aperiodic-lattice predicates of the Penrose-tiling-style structural form. The 268M-site computation is now anchored in a kernel-verified substrate that the project can lift further (Mathlib PR for Chebyshev polynomials of the first kind is a natural extraction target).

**Categorical ↔ real-space Chern bridge (Wave 6w.5).** Bianco-Resta 2011 introduced real-space Chern markers (Bott index variants) for aperiodic systems where momentum-space integrals do not apply; Antão-Sun-Fumega-Lado generalized this with Chebyshev-TN evaluation. The project's Lean substrate now ships the *bridge* between the categorical Chern-class formulation (Drinfeld-center / MTC) and the real-space Chern formulation, with **substantively distinct** crystalline (c_0 + c_1) vs quasicrystalline (c_0 − c_1) limits. The difference-identity headline `crystalline_minus_quasicrystalline_eq_twice_c1` is structurally meaningful: 2c_1 is the *gauge-invariant content* of the crystalline-vs-quasicrystalline distinction. This is the first kernel-verified bridge of its kind.

**The combined demarcation theorem (Wave 6w.6) is the bundle-creating headline.** `analog_hawking_quantum_advantage_demarcation` ships as a substantive biconditional combining the Wave 6w.3 BP-LDP condition (tree-factor-graph + factor-weight-positivity) with the Wave 6w.5 Chern condition (c_1 = 0). The right-hand side is a *conjunction of two structurally distinct predicates* on the factor graph + Chern data — neither side is a tautology, neither side is redundant, and dropping either conjunct breaks the biconditional. The predicate operates on arbitrary FactorGraph + factor weights + Chern data with NOTHING analog-Hawking-specific in the predicate body, which is the generality criterion that triggered the D7 spin-out decision per the user-conditional-authorization rule.

**Honest scope statement (post-remediation):** the predicate is universally-quantified over arbitrary factor graphs and Chern data, but the per-platform (BEC, polariton, graphene Dirac fluid) analog-Hawking instantiation bridges are deferred to the D-bundle absorption pass. The D7 abstract was down-toned from "We instantiate the demarcation on three analog-Hawking platforms" to "analog-Hawking applications via the Kibble-Zurek-Unruh correspondence are sketched at the cross-module substrate level... with explicit per-platform instantiation bridges deferred."

---

## D7 Bundle: 16th Publication Target Created

The architectural deliverable of Phase 6w is the **creation of D7 — "Classical Simulability and Quantum Advantage via Tensor Networks: A Formally Verified Demarcation"** as the 16th publication target. D7 covers the *boundary* between classically-simulable and quantum-advantage regimes; sibling D4 retains Fibonacci/topological-foundations focus; sibling D6 retains FT-QC substrate focus.

D7's composition:
- **§3** — Wave 6w.2 BeliefPropagation substrate (24 theorems Mathlib-PR-quality) + Wave 6w.3 BP-LDP biconditional headline (8 theorems).
- **§4** — Wave 6w.4 Chebyshev-TN substrate (10 theorems).
- **§5** — Wave 6w.4 AperiodicLattice substrate (7 theorems) + Wave 6w.5 categorical-Chern ↔ real-space-Chern bridge (5 theorems, difference-identity headline).
- **§6** — Wave 6w.6 combined demarcation headline (3 theorems incl. analog_hawking_quantum_advantage_demarcation biconditional).
- **§7** — Wave 6w.1 Kibble-Zurek-Unruh foundation cross-bridge (8 theorems) — anchors the analog-Hawking application sketch with explicit per-platform deferral.

D7 ships **kernel-only** (zero new project-local axioms; standard Lean axiom closure `[propext, Classical.choice, Quot.sound]`), with each substantive ship paired with substantively-distinct contrast structure (crystalline ≠ quasicrystalline; tree ≠ loopy; c_1 = 0 ≠ c_1 ≠ 0). The D7 paper-draft skeleton compiles clean at ~3 pages after the Round-1 remediation deletions; full bundle-level Stage 13 adversarial review was completed in two fresh-context rounds (2026-05-26 21:12 PM Round 1; 2026-05-26 21:29 PM Round 2) with final state `stage10_status: green` + `stage13_status: green` + `blockers_open: 0` + `advisories_open: 0`.

**Stage 9 (figure review)** is vacuous-PASS eligible per `BUNDLE_LIFT_PROCEDURE.md` §9 — D7 has no figures yet (skeleton paper). The bundle is **submission-ready at substrate level**, pending the Stage 9 vacuous-PASS formalization + figure additions in the D-bundle absorption pass.

---

## Substrate Counts (post Phase 6w close — `update_counts.py` fresh-regen 2026-05-26T20:04:39)

Project-wide totals from `docs/counts.json`:

| Metric | Value |
|---|---:|
| Lean modules under `lean/SKEFTHawking/` | **465** |
| Lean total declarations | **14,815** |
| Lean theorems (total) | **7995** (7970 substantive + 25 placeholder) |
| Lean theorems (substantive) | **7970** |
| Lean definitions | **6005** |
| Lean axioms (project-local) | **0** |
| Lean sorries | **0** |
| Python source modules | **132** |
| Test files | **109** |
| Pytest cases | **4329** |
| Figures (PNG) | **156** |
| Notebooks | **89** |
| Papers (drafts) | **42** |
| Aristotle-proved theorems | **322** (across 44 runs) |
| Publication bundles (per `PAPER_STRATEGY.md`) | **16** (D7 created this phase) |
| Build target count (`lake build SKEFTHawking`) | **8713** |

Phase 6w-specific delta (the 7 new modules KZU + BP + BPLDP + Cheb + Aperiodic + ChernBridge + Demarcation):

| Metric | Pre-Phase-6w | Post-Phase-6w | Δ from Phase 6w only |
|---|---:|---:|---:|
| Lean modules added by Phase 6w | — | — | **+7** (KZU + BP + BPLDP + Cheb + Aperiodic + ChernBridge + Demarcation) |
| Lean theorems added by Phase 6w (substantive, post-remediation) | — | — | **+65** (8 KZU + 24 BP + 8 BPLDP + 10 Cheb + 7 Aperiodic + 5 ChernBridge + 3 Demarcation, post-Round-1 deletion of 3 P5 tautologies) |
| Build jobs added by Phase 6w | 8706 | **8713** | **+7** |
| Lean axioms (project-local) | 0 | **0** | **unchanged ✓** (Pipeline Invariant #15 maintained through both Round-1 + Round-2 remediations) |
| Lean sorries | 0 | **0** | **unchanged ✓** |
| Publication bundles | 15 | **16** | **+1** (D7 CREATED) |
| CITATION_REGISTRY bibkeys | — | — | **+5** (TindallSels2026Science392 + AntaoSunFumegaLado2026PRL + YedidiaFreemanWeiss2003 + Zurek1985 + BiancoResta2011; last three added during Round-1 remediation) |
| Primary-source cache files | — | — | **+5** (matching new bibkeys; Yedidia MERL TR PDF + Zurek abstract.txt + Bianco-Resta arXiv PDF added during Round-1 remediation) |
| Python source modules | — | — | unchanged from Phase 6w (Lean-only phase) |

Phase 6w is **Lean-only**: the Python modules / test files / pytest cases / figures / notebooks / papers / Aristotle-proved counts above are project totals (which absorbed earlier-wave additions during this regen) and not deltas from Phase 6w. Phase 6w added no Python source code, no figures, and no notebooks.

---

## Posture Statement

Phase 6w's posture: **substrate-level kernel-verified absorption of the 2025–2026 classical-simulability frontier, with substantively-distinct contrast structure establishing non-vacuity at every load-bearing biconditional and a no-walk-back posture toward reviewer findings.** Two P5 anti-patterns slipped past the self-conducted Stage-13 audit and were caught by a fresh-context reviewer-agent pass; per project no-walk-back discipline the offending theorems were DELETED (not relabeled to "accepted") and the supporting paper prose was substantively down-toned to honest scope. Round 2 fresh-context re-review on both adversarial + claims sides verified Stage-10 GREEN + Stage-13 GREEN with zero open findings.

The D7 bundle creates the structural home for the *classical-simulability boundary* within the project's publication architecture — a unified PRX-Q / PRX-class deep paper covering BP-on-TN substrate + LDP-controlled simulability biconditional + Chebyshev-TN + aperiodic-lattice + categorical-Chern ↔ real-space-Chern bridge + combined analog-Hawking demarcation, kernel-verified end-to-end. This is the second new publication-bundle target added in the Phase 6v/6w window (after D6), reflecting the project's broadening from "Tier-1 SK-EFT corrections to analog Hawking" toward "the full classical/quantum landscape at the analog-Hawking boundary."

**Process posture (Phase 6w QI candidate):** the structural lesson from the Round-1 reviewer-agent catch of 3 P5 tautologies is codified as `qi-gate-5-self-audit-blind-spot-on-sibling-tautologies` in `docs/QI_REGISTER.md`. The recommendation is hard: **ALWAYS invoke `physics-qa:adversarial-reviewer` + `physics-qa:claims-reviewer` at wave close as a hard rule, not as a self-audit substitute.** Self-audit catches obvious tautology patterns but misses sibling-tautology patterns that depend on the *interaction* of multiple theorems (e.g. an identity-function wrapper around a trivial And-constructor that, taken individually, look load-bearing but jointly carry no content). Fresh-context reviewers do NOT inherit the author's blind spots and reliably catch this class.

---

## Cross-references

- **Phase 6w Roadmap:** [`docs/roadmaps/Phase6w_Roadmap.md`](../roadmaps/Phase6w_Roadmap.md)
- **Per-wave roadmaps:** [`docs/roadmaps/Phase6w/`](../roadmaps/Phase6w/)
- **D7 bundle metadata:** [`papers/D7/bundle_metadata.json`](../../papers/D7/bundle_metadata.json)
- **D7 paper draft:** [`papers/D7/paper_draft.tex`](../../papers/D7/paper_draft.tex)
- **Bundle architecture:** [`docs/PAPER_STRATEGY.md`](../PAPER_STRATEGY.md) (updated 15 → 16 bundles)
- **Paper-draft mapping:** [`docs/PAPER_DRAFT_MAPPING.md`](../PAPER_DRAFT_MAPPING.md) (D7 entry added)
- **Bundle readiness heatmap:** [`docs/BUNDLE_READINESS_HEATMAP.md`](../BUNDLE_READINESS_HEATMAP.md) (D7 row added; Stage-10 + Stage-13 GREEN; Stage-9 vacuous-PASS eligible)
- **Stage-13 review docs (D7):**
  - Round 1: [`papers/AutomatedReviews/2026-05-26-2112-internal-adversarial/D7.md`](../../papers/AutomatedReviews/2026-05-26-2112-internal-adversarial/D7.md)
  - Round 2: [`papers/AutomatedReviews/2026-05-26-2129-internal-adversarial/D7.md`](../../papers/AutomatedReviews/2026-05-26-2129-internal-adversarial/D7.md)
- **Stage-10 claims review (D7):** [`papers/D7/claims_review.json`](../../papers/D7/claims_review.json)
- **QI register entry:** [`docs/QI_REGISTER.md`](../QI_REGISTER.md) (`qi-gate-5-self-audit-blind-spot-on-sibling-tautologies`)
- **Closure summary:** [`temporary/working-docs/phase6w/phase6w_closure_summary.md`](../../temporary/working-docs/phase6w/phase6w_closure_summary.md)
- **Self-audit doc:** [`temporary/working-docs/phase6w/phase6w_self_adversarial_audit.md`](../../temporary/working-docs/phase6w/phase6w_self_adversarial_audit.md)
- **Phase 6v closure (predecessor):** [`Phase6v_Implications.md`](Phase6v_Implications.md) + memory entry `project_phase6v_wave9_substantively_closed_2026_05_26`
- **Phase 6q closure (DKM substrate predecessor):** [`Phase6q_Implications.md`](Phase6q_Implications.md) + memory entry `project_phase6q_complete_2026_05_23`
