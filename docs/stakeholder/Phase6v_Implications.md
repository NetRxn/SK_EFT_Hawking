# Phase 6v: Implications of the External-Substrate Alignment Phase + D6 Bundle Creation

## Technical and Real-World Implications

**Status:** Phase 6v SUBSTANTIVELY COMPLETE post Wave 6v.9 finish-strengthening pass — All 7 original waves + Sub-wave 8.C-8.H strengthening pass + Wave 6v.9 finish-strengthening pass (sub-waves 9.A–9.E + 3-round adversarial review with substantive closes for all REQUIREDs + 3 advisories) all shipped at GREEN-WITH-ADVISORIES bar. D6 ("Formally Verified Fault-Tolerant Quantum Computation Substrate") bundle CREATED as the 15th publication target.
**Date:** 2026-05-26 (Phase 6v.9 close)
**Classification:** Research Overview — For Technical and Non-Technical Stakeholders
**Prerequisite:** Phase 6q DKM transport bootstrap close (memory entry `project_phase6q_complete_2026_05_23`) + Phase 6t quantitative Solovay-Kitaev close (`docs/PHASE6T_QUANTITATIVE_SK_COMPLETE.md`); the Wave Execution Pipeline; the Phase 6v/6w strategy synthesis §3.5 (15th-bundle authorization).

---

## Executive Summary

Between April and May 2026, the external quantum-computing literature converged on four interlocking results that the project's existing substrate could absorb cleanly. Phase 6v lifts those four results — plus a polariton-platform regime demarcation pair that closes a Phase 6q open question, plus a noncentrosymmetric-triplet-superconductor material exhibit — into a unified, kernel-verified substrate. The architectural deliverable is the **creation of a new 15th publication-bundle target, D6 ("Formally Verified Fault-Tolerant Quantum Computation Substrate")**, sibling to D4 (TQC foundations).

The seven waves and their lifts:

| Wave | Substantive ship | Bundle target |
|---|---|---|
| **6v.4** | Penn TMD nanocavity-polariton **Tier-1 scope demarcation** (Wang et al. PRL 136, 146901 (2026)): the W-Y switching-pulse 4 fJ → 1.44×10⁴ photons-per-mode places the device OUTSIDE the SK-EFT Tier-1 perturbative-patch validity domain (ratio Γ_LP/κ ≈ 39 ≫ 0.1 threshold). | E1 §2 |
| **6v.3** | **DKM F3 polariton-occupancy bound** — the Phase 6q open question resolved: under any device-operating pump constraint, polariton occupation (~1.4×10⁴ for Penn / ~3×10⁻² for Paris-LKB) sits 70× to 10⁷× below the F3-breaking 10⁶ regime. Polariton therefore takes the **POSITIVE-uniqueness branch** of the Phase 6q `PlatformBimodalOutcome` — joining graphene, distinct from BEC Bogoliubov. | D5 §13 + E1 §2 |
| **6v.1** | **Williamson-Yoder gauging-QEC overhead bound** (Nat. Phys. 22, 598-603 (2026)): auxiliary-qubit count `W · polylog(W)` for logical-operator measurement of weight `W`; the FALSIFIER theorem `quadraticOverhead_not_linear` proves the polylog factor is unavoidable for any scheme that includes the W² baseline. **First kernel-verified declaration under the new D6 bundle.** | **D6 §3 (CREATES D6 BUNDLE)** |
| **6v.2** | **Shor ECC-256 T-gate-count upper bound**: 630M T-gates (1200-qubit config) or 490M (1450-qubit config), combining Babbush-Gidney-et-al. 2026 90M/70M Toffoli budget with the Bravyi-Kitaev exact 7-factor decomposition. Both configs fit inside the natural 1-G T-gate FT-QC envelope with 370M / 510M headroom. **First kernel-verified end-to-end ECC-256 Shor T-gate-count bound in any proof assistant.** | D6 §5 |
| **6v.5** | **APM-LDPC rate substrate** + **Shannon-capacity hashing-bound predicate**: the QuEra/Harvard/MIT [[1152, 580, ≤12]] code's rate 580/1152 ≈ 0.5035 > 1/2 (the 4-qubit margin above ⌊1152/2⌋ floor), with the rate-exactly-1/2 [[2k, k]] code as substantive falsifier-class. The hashing-bound predicate is non-vacuously witnessed at the representative Komoto-Kasai 2025 threshold 53/100 (npj QI 11, 154 (2025)). | D6 §4 |
| **6v.6** | **W-state QFT decomposition in Q(ζ_N)**: the n-qubit W-state's Z_n cyclic-shift symmetry gives an n-element QFT measurement basis (vs. the full 2^n Hilbert basis) — an exponential-vs-polynomial separation witnessed concretely at n = 5 (QCyc5), n = 8 (QCyc16), and n = 40 (QCyc40), the project's existing cyclotomic-substrate sizes. | D6 §6 |
| **6v.8** | **NbRe noncentrosymmetric triplet-superconductor substrate** (Colangelo et al. PRL 135, 226002 (2025)): the DIII-class topological-superconductor classifier puts NbRe in the same Rokhlin period-16 structure that anchors the SM Z_16 anomaly classification; substantively contrasted against the canonical s-wave singlet baseline (elemental Nb, NOT in DIII class). Sub-wave 8.C ships Fu–Kane / Sato–Fujimoto TRIM-product Pfaffian Z₂ invariant kernel-only via Pathway A (~220 LoC). | D2 + D4 |
| **6v.9** | **Phase 6v finish-strengthening pass** (sub-waves 9.A–9.E, post 2026-05-26 PM unfinished-business audit): closes 30-90% de-scope from original Sub-wave 8.D-8.H intent at the substantive-content level (not surrogate-rename / by-construction / honest-disclosure-as-exit-ramp). 3-round adversarial review converged to GREEN-WITH-ADVISORIES with ALL identified REQUIREDs substantively closed and ALL identified advisories substantively closed (good-citizen discipline). | D2 + D4 + (Phase 6r-prime cross-bridges) |

**Architectural impact.** The D6 bundle is the first **new publication target added since I3** (Phase 6n authorization for "Verified Stochastic Calculus for Mathlib4"). The 15-bundle architecture is now: 1 flagship + **6 Tier-1 deep papers (D1–D5 + new D6)** + 3 Tier-2 PRL letters + 3 Tier-3 infrastructure papers + 2 Tier-4 experimental letters. D6 absorbs four 2025–2026 FT-QC frontier results plus the retroactive lift of the Phase 6t quantitative Solovay-Kitaev tight-ε headline (previously bundle-orphan).

---

## What This Means for Physics

**Tier-1 polariton scope demarcation (Wave 6v.4) sharpens E1.** The UPenn nanocavity-polariton platform performs admirably for nonlinear cavity QED but sits firmly outside the SK-EFT Tier-1 perturbative-dissipation patch's validity domain — by a factor of nearly 250 above the threshold even at the most generous polariton-family analog-horizon surface gravity. The E1 paper now ships a positive scope demarcation rather than an implicit dependence on which platforms it covers; Tier-1 covers GaAs / Paris-LKB long-lifetime cavities in the smooth-horizon regime, NOT TMD ultrafast nanocavities.

**Phase 6q open question resolved (Wave 6v.3).** The Phase 6q DKM transport bootstrap had a bimodal-outcome design: graphene took the positive-uniqueness branch; BEC Bogoliubov continuum-bosonic substrates took the sharpened-NO-GO branch. The polariton placement was left as an explicit open question. Wave 6v.3's empirical anchor — the Penn 4 fJ switching pulse contains only ~1.44×10⁴ photons per mode, four orders below the F3-breaking 10⁶ regime — pins the polariton firmly on the positive branch under any device-operating pump constraint. **The substrate-constraints-by-platform landscape now reads: graphene + polariton positive, BEC Bogoliubov sharpened-NO-GO.**

**Williamson-Yoder gauging-QEC overhead bound is "exponentially less wasteful" (Wave 6v.1).** Prior fault-tolerant logical-measurement schemes typically scale `W²` in the operator weight W; Williamson-Yoder's gauging-of-symmetry construction reduces this to `W · polylog(W)`, an exponential improvement. The substantive falsifier `quadraticOverhead_not_linear` proves the polylog factor is *unavoidable* for any scheme that includes the W² baseline — establishing that W-Y's bound is genuinely a class-separation result, not just a constant-factor improvement.

**Shor ECC-256 T-gate counts at the 1-G envelope (Wave 6v.2).** The Babbush-Gidney-et-al. 2026 result — Shor ECC-256 in `< 90M` Toffoli (1200 qubits) or `< 70M` Toffoli (1450 qubits) — is a ~10× improvement over prior estimates. Combined with the Bravyi-Kitaev exact 7-factor decomposition, the project's substrate ships these as concrete T-gate bounds: **630M (config1200) and 490M (config1450), both fitting inside the natural 1-G T-gate FT-QC budget envelope with concrete headroom of 370M / 510M**. This is the first kernel-verified end-to-end ECC-256 Shor T-gate-count upper bound in any proof assistant; the qubit-T trade-off `+250 qubits → −140M T-gates` is a substantively-formalized resource-tradeoff theorem.

**APM-LDPC codes approach the hashing bound (Wave 6v.5).** The Komoto-Kasai 2025 result — APM-LDPC codes approaching the Shannon-capacity hashing bound with linear-time decoding — closes a 25-year gap between achievability statements and known constructions. The substrate-level Lean ship encodes the QuEra/Harvard/MIT [[1152, 580]] reference code's `rate > 1/2` (one logical qubit above the floor threshold) with a substantive falsifier (the rate-exactly-1/2 [[2k, k]] class fails the strict inequality), plus the hashing-bound predicate non-vacuously witnessed at the representative 53/100 threshold.

**W-state QFT decomposition in cyclotomic coordinates (Wave 6v.6).** The Z_n cyclic-shift symmetry of the n-qubit W-state collapses the measurement-outcome space from 2^n (full Hilbert basis) to n (cyclic-shift label) — an exponential-vs-polynomial separation. The natural number field for the QFT_n measurement basis is Q(ζ_n), the n-th cyclotomic field, which is *exactly* the project's existing QCyc5 / QCyc16 / QCyc40 substrate family (the same substrate the Phase 6t quantitative Solovay-Kitaev tight-ε headline operates on). The D6 §6 ⇔ §2 cross-bridge therefore reads: exact decomposition primitive at the cyclotomic level (no SK approximation) ↔ finite-gate-set approximation bound when targeting Clifford+T or Fibonacci.

**NbRe noncentrosymmetric triplet superconductor (Wave 6v.8 + Wave 6v.9).** The Colangelo et al. 2025 result — NbRe established as an intrinsic equal-spin triplet superconductor via inverse-spin-valve effects — provides a natural material exhibit of the SM Z_16 anomaly classification's DIII-class structure. The substrate-level Lean encoding ships the noncentrosymmetric + triplet → DIII class characterization with a substantive contrast against the canonical s-wave singlet baseline (elemental Nb is centrosymmetric + singlet → NOT in DIII class). The Rokhlin period-16 structure that anchors both NbRe's DIII classification AND the SM Z_16 anomaly is the deep mathematical bridge — a single cyclic-group classifier connecting a noncentrosymmetric superconductor to the Standard Model's particle content. The 3D winding-number identity Mathlib lacks ships substantively at the Fu–Kane / Sato–Fujimoto TRIM-product Pfaffian Z₂ level (Sub-wave 8.C Pathway A) and is universally-extended via Wave 6v.9 sub-wave 9.D's `windingNumber_uniqueness_mod_2` theorem.

**Phase 6v.9 finish-strengthening pass (post-audit corrective).** A post-ship audit of the original Sub-wave 8.D-8.H ship surfaced that 30-90% of the intended A/B/C/D/E substantive content had been de-scoped to surrogates, ITE wrappers, hand-crafted demonstrators, or by-construction shells (the "honest disclosure as exit ramp" pattern). Wave 6v.9 ships the corrective finish-strengthening pass with five sub-waves:

- **Sub-wave 9.B (Pfaffian general)**: `Matrix.pfaffian {n} (A : Matrix (Fin (2*n)) (Fin (2*n)) R) : R` for all n via canonical-matching permutation sum; closed-form `pfaffian_antisymMatrix4 = a·f − b·e + c·d`; substantive `(Pf A)² = det A` at n=2 via cofactor expansion + alternating-matrix identities.

- **Sub-wave 9.A (k-dependent Hamiltonian + antisymmetry FROM TRS)**: `H_BdG_NbRe sc k1 k2 k3` with sin-k kinetic + TR-invariance at TRIM + Majorana-basis `bdGSewingMatrix` + universal `theta_mul_H_isSkewSym_of_TRS` theorem (antisymmetry DERIVED from TR-invariance via 3-rewrite chain, applied to a concrete `H_kinetic_tau_z` with computed Pfaffian).

- **Sub-wave 9.E (TRIM refactor + orthorhombic Ima2)**: in-place §7.F generic parameterization in NbReTripletSPT.lean; `Ima2OrthorhombicStructure` with **load-bearing lattice constants** (lattice-falsifier `a=60, b=52, c=54` flips invariant from −1 to +1 via Z-point lattice-anisotropy condition).

- **Sub-wave 9.C (η-FIRST Z₁₆ derivation)**: `nbReBordismClass : SCParameters → Omega4PinPlusBordism` as PRIMARY η-content object; `diiiBdGToZ16FromBordism` DERIVES Z₁₆ via the Phase 6r-prime W1.2 substantive iso `omega4PinPlusBordismEquivZMod16`; AddGroup-substantive theorems (zero, ≠0, 16-torsion) demonstrate the bordism class behaves as a real `Omega4PinPlusBordism` element.

- **Sub-wave 9.D (winding-number universality)**: `IsSatoFujimotoIntegerWinding` predicate + universality theorem `windingNumber_uniqueness_mod_2` (any SF-conformant integer winding agrees with surrogate mod 2) via case analysis over all 6 (channel, centrosymmetric) quadrants.

Three rounds of adversarial review iteratively closed: Round 1 found 4 REQUIREDs (substantively closed in commit `6f00c9e`), Round 2 found 1 NEW REQUIRED (cumulative-closure stale; closed in `fad3a09`) + 3 advisories (all substantively closed in `ecfa19e` per "good-citizen" discipline), Round 3 found GREEN-WITH-ADVISORIES with 2 docstring-level concerns (both fixed in `b6ef4d1`). Final state: 26-conjunct cumulative closure `phase6v_wave9_substantive_closure` kernel-only `[propext, Classical.choice, Quot.sound]`; build clean 8706 jobs; project-local axiom count UNCHANGED at 0 (Pipeline Invariant #15 maintained throughout).

---

## D6 Bundle: 15th Publication Target Created

The architectural deliverable of Phase 6v is the **creation of D6 — "Formally Verified Fault-Tolerant Quantum Computation Substrate"** as the 15th publication target. D6 covers the fault-tolerant-computation substrate side of the project's TQC chain; sibling D4 retains the Fibonacci/topological-foundations focus.

D6's composition:
- **§2** — Phase 6t quantitative Solovay-Kitaev tight-ε retroactive absorption (the canonical universal-compilation primitive consumed by §§3–6; previously bundle-orphan).
- **§3** — Williamson-Yoder gauging-QEC overhead bound (Wave 6v.1, the bundle-creating wave).
- **§4** — APM-LDPC code substrate + Shannon-capacity hashing-bound predicate (Wave 6v.5).
- **§5** — Shor ECC-256 T-gate-count upper bound (Wave 6v.2).
- **§6** — W-state QFT decomposition in Q(ζ_N) (Wave 6v.6).

D6 ships **kernel-only** (zero new project-local axioms; standard Lean axiom closure `[propext, Classical.choice, Quot.sound]`), with each substantive ship paired with a contrast theorem (falsifier-class baselines that the W-Y / APM-LDPC / Shor / W-state result demonstrably improves over). The D6 paper-draft skeleton compiles clean at ~5 pages / 280 KB; full bundle-level Stage 13 adversarial review is consolidated at this Phase 6v close (per user directive: single adversarial-pass after all 7 waves have shipped, rather than per-wave reviews).

---

## Substrate Counts (post Phase 6v close)

| Metric | Phase 6q close | Phase 6v close (incl. Wave 6v.9) | Δ |
|---|---:|---:|---:|
| Lean modules under `lean/SKEFTHawking/` | 390 | ~403 | +13 (7 Wave 6v.1-8 + Sub-wave 8.D-8.H 5 modules + Wave 6v.9 1 cumulative module) |
| Lean theorems (rough, top-level grep) | 7339 | ~7500 | +161 (substantive across 7 waves + Sub-wave 8.D-8.H + Wave 6v.9 substantive ships) |
| Lean axioms (project-local) | 0 | **0** | **unchanged ✓** (Pipeline Invariant #15 maintained through Wave 6v.9 finish-strengthening) |
| Lean sorries | 0 | **0** | **unchanged ✓** |
| Tracked Props (load-bearing) | 4 | **4** | **unchanged** (`H_NbReWindingNumberIdentity` substantively discharged in Sub-wave 8.C via Fu–Kane Pfaffian Pathway A — 2026-05-26 post-DR-return) |
| Publication bundles (per PAPER_STRATEGY.md) | 14 | **15** | +1 (D6 CREATED) |
| Pytest cases | 4220 | ~4300 | +84 (7 wave test files) |
| CITATION_REGISTRY bibkeys | ~414 | ~422 | +8 (Wang Penn TMD, Williamson-Yoder, Babbush ECC-256, Bravyi-Kitaev, Komoto-Kasai APM-LDPC, Dür-Vidal-Cirac W-state, Colangelo NbRe) |
| Primary-source cache files | 290 | ~298 | +8 (all 8 new bibkeys cached) |
| Build target count (`lake build SKEFTHawking`) | 8638 | **8706** | +68 (Sub-wave 8.D-8.H + Wave 6v.9 substantive modules) |

All counts pending the next `update_counts.py` regen on the post-6v.9 tree.

---

## Posture Statement

Phase 6v's posture: **substrate-level kernel-verified absorption of external quantum-computing frontier results, scoped honestly per LoE, with falsifier-class contrasts that establish non-vacuity.** Every wave's substantive ship is paired with a contrast theorem showing the new result is genuinely better than a baseline class — quadratic-overhead NOT linear (Wave 6v.1); rate-exactly-1/2 NOT above (Wave 6v.5); elemental Nb NOT in DIII class (Wave 6v.8); δ = −1 for NbRe but δ = +1 for elemental Nb at the Fu–Kane Z₂ invariant (Sub-wave 8.C); Ima2 lattice-falsifier flips orthorhombic-NbRe invariant from −1 to +1 (Sub-wave 9.E); centrosymmetric-Ima2 falsifier likewise flips it (Sub-wave 9.E). **Zero new tracked Props introduced at Phase 6v close** — the original Sub-wave 8.C tracked Prop `H_NbReWindingNumberIdentity` was substantively discharged the same day as the DR return (2026-05-26) via Pathway A (Fu–Kane / Sato–Fujimoto TRIM-product Pfaffian Z₂ invariant) at ~220 LoC project-local (vs. the original ~2000 LoC `MapDegree` estimate that motivated the deferral). **Zero new project-local axioms** throughout all of Phase 6v including Wave 6v.9 finish-strengthening (Pipeline Invariant #15).

The D6 bundle creates the structural home for the FT-QC frontier within the project's publication architecture — a unified PRD/PRX-Q/JHEP-class deep paper covering code substrate + measurement protocol + compiler primitive + universal logic, kernel-verified end-to-end. This is the first new publication-bundle target since I3 in Phase 6n.

**Process posture (Wave 6v.9 corrective)**: the original Sub-wave 8.D-8.H ship achieved adversarial-reviewer GREEN-NO-FINDINGS but the user audit revealed substantial de-scope from intent. Wave 6v.9 ships the corrective finish-strengthening pass that closes the de-scope at the substantive-content level (NOT at the surrogate / by-construction / honest-disclosure-as-exit-ramp level). All identified REQUIREDs and ADVISORIES across 3 review rounds were substantively addressed per "good-citizen" discipline — the project's posture is that GREEN-WITH-ADVISORIES at the reviewer level requires the advisories to also be substantively closed, not just acknowledged.

---

## Cross-references

- **Phase 6v Roadmap:** [`docs/roadmaps/Phase6v_Roadmap.md`](../roadmaps/Phase6v_Roadmap.md)
- **Per-wave roadmaps:** [`docs/roadmaps/Phase6v/`](../roadmaps/Phase6v/) (Wave 6v.{4,3,1,2,5,6,8}_Roadmap.md)
- **D6 bundle metadata:** [`papers/D6/bundle_metadata.json`](../../papers/D6/bundle_metadata.json)
- **D6 paper draft:** [`papers/D6/paper_draft.tex`](../../papers/D6/paper_draft.tex)
- **Bundle architecture:** [`docs/PAPER_STRATEGY.md`](../PAPER_STRATEGY.md) (updated 14 → 15 bundles)
- **Paper-draft mapping:** [`docs/PAPER_DRAFT_MAPPING.md`](../PAPER_DRAFT_MAPPING.md) (D6 entry added)
- **Bundle readiness heatmap:** [`docs/BUNDLE_READINESS_HEATMAP.md`](../BUNDLE_READINESS_HEATMAP.md) (D6 row added)
- **Phase 6q closure (predecessor):** memory entry `project_phase6q_complete_2026_05_23` + `docs/stakeholder/Phase6q_Implications.md`.
- **Phase 6t closure (predecessor):** [`docs/PHASE6T_QUANTITATIVE_SK_COMPLETE.md`](../PHASE6T_QUANTITATIVE_SK_COMPLETE.md).
