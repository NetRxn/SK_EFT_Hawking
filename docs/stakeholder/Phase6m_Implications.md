# Phase 6m: Implications of the Three-Track Dark-Energy Closure

## Technical and Real-World Implications

**Status:** Phase 6m TERMINALLY CLOSED at the Lean-formalization scope. All three tracks (Causal-set DE, Entropic-gravity DE, Jacobson-thermodynamic-GR DE) plus the Wave 4 unified taxonomy SHIPPED.
**Date:** 2026-05-07
**Classification:** Research Overview — For Technical and Non-Technical Stakeholders
**Prerequisite:** Phase 5y closure (Volovik q-theory NO-GO; the methodology template Phase 6m mirrors); Phase 6e (heat-kernel chain — Wave 5 CC-reproduced verdict cross-references Track C); ARCHITECTURE_SCOPE.md.

---

## Executive Summary

Phase 6m is the largest and most consequential dark-energy probe the project has ever executed. Its purpose: take the three mechanism families that Phase 5y explicitly flagged as outside the tested predictive scope — causal-set dark energy, entropic-gravity dark energy, Jacobson-thermodynamic-GR dark energy — and apply the same six-round deep-research-plus-Lean-formalization methodology that Phase 5y used for Volovik q-theory. After R1 through R6 plus the Lean-formalization closure plus a ruthless strengthening pass plus a cross-module proof-chain pass, **all three tracks have returned verdicts**. The combined statement, taken with Phase 5y, is: **Layer-3 dark-energy-scale physics is outside the architecture's tested predictive scope under all four major mechanism families**.

The headline findings are:

1. **Track A (Causal-set DE):** 3 NO-GO-R5 phenomenological verdicts (Sorkin Models 1+2; BDG MYZ 2025) plus the causal-set d'Alembertian NO-GO-R2 reaffirmed. **3 publishable structural caveats survive independent of DESI**: Gibbs–Duhem inapplicability robust across all 4 admissible sprinkling prescriptions; Barrow-bound prescription dependence (CQG/JCAP Letter candidate); BDG $\sigma_\Lambda = \alpha_{\rm BDG}/\sqrt{V}$ first-principles decomposition.

2. **Track B (Entropic-gravity DE):** **8 of 8 unanimous NO-GO-R5 — first complete-mechanism-family NO-GO closure in Phase 6m**. Verlinde 2017 / Padmanabhan-CosMIn / Hossenfelder-Verlinde / Cadoni-Tuveri DEC / Li 2004 HDE / Tsallis HDE / Barrow HDE / Odintsov-D'Onofrio-Paul $\Omega_k$ all closed with quantitative thresholds. *Honest correction (Phase 7 absorption Session 5):* the original Tsallis/Barrow figures were AIC/BIC-based, not Bayes-factor-based. The aggregator was updated to a mixed-threshold form acknowledging this — Verlinde / Tsallis (decisive Bayes) / Odintsov (decisive) remain decisive; Barrow is moderate-AIC (ΔAIC = 4.7 < Jeffreys-decisive 5). The 8/8 NO-GO closure at the *disfavoured* level survives the correction; the misnamed `barrow_log_bayes := 5.5` was retired and replaced with `barrow_aic_delta := 4.7`.

3. **Track C (Jacobson-thermodynamic-GR DE):** **Highest-survival track in Phase 6m with 5+ R5 survivors.** M3 EGJ f(R) Exponential + ArcTanh is the **strongest CLEARED-R5 of any track** (Plaza-Kraiselburd 2504.05432: ΔAIC ≃ ΔBIC ≳ 20 = Jeffreys "decisive" preference *in favor* over ΛCDM). M3 Hu-Sawicki NO-GO via chameleon Solar-System constraint at $b \approx 0.21$ (~100× too large for chameleon screening). M4 Pure Lovelock NO-GO at the 1σ-box edge. M8 KSS conditional path-(a) CLEARED. M1 Jacobson 1995 / M2/M7 Padmanabhan-CosMIn (epistemic flag) / M9 Volovik-Jannes PARTIAL-VIABLE under fixed-$r_d$ Planck DR3 prior.

4. **Phase 6e cross-bridge — Sakharov 4-criterion ↔ $\Lambda_J = \Lambda_{\rm HK}$.** First systematic comparison in literature: ³He-A satisfies all four conditions and $\Lambda_J = \Lambda_{\rm HK}$ holds; Finazzi–Liberati–Sindoni acoustic BEC violates condition (ii) (only phonons have a BEC effective metric). *Phase 6o Wave 4a verdict (B):* the originally-claimed biconditional was retired in favor of an honest one-way implication (Volovik–Jannes 2012 §VII argues only forward; FLS BEC primary-source verification confirms forward, doesn't test ⇐) plus a load-bearing depletion factor `depletion : ℝ` field on a strict-extension `SakharovExtended` structure. The 4-Boolean Sakharov layer is preserved; the substantive new content is the depletion-factor asymmetry.

5. **Wave 4 unified Phase 6m 7-class GD taxonomy** (`DarkSectorClassificationExtension.lean`, 10 substantive theorems) consolidates Track A "combinatorial-vs-thermodynamic-scalar" + Track B "a/b/c/d" + Track C "b/b'/b''/OPEN" into a single classification namespace (Class 0 + (a) + (b) + (b′) + (b″) + (c) + (d)) with a 3-tier GD applicability gradient. Unimodular reformulation as $\Lambda_{\rm HK}$ escape route admits 5 of 6 Track-C survivors except KSS.

The architectural-scope statement — Layer 3 dark-energy outside predictive scope under all tested mechanism families — is now machine-checked across all four families.

---

## Result 1: Track A — Causal-Set Dark Energy

### What we found

Five candidate causal-set DE mechanisms were surveyed (Sorkin 1989; Sorkin-Surya 2004; Ahmed-Dowker-Surya 2017; BDG MYZ 2025; causal-set d'Alembertian). After six rounds of deep research:

- Sorkin Model 1, Sorkin Model 2, BDG: **NO-GO-R5 phenomenological** at $f_{\rm DESI} < 10^{-5}$ at 95% C.L. post-Tier-(4) conditioning (raw / SN / ISW / σ₈).
- Causal-set d'Alembertian: NO-GO-R2 reaffirmed via 4D gradient instability — gives DM, not DE.

**Three publishable structural caveats survive independent of DESI:** (i) Gibbs–Duhem inapplicability robust under all 4 admissible prescriptions (local stochastic Barrow/Zuntz; covariant nonlocal ZAS 2018; spatially homogeneous ADGS 2004 Model 1; per-PLC fluctuating Barrow branch); (ii) Barrow-bound prescription dependence (per-PLC gives $\alpha \lesssim 3 \times 10^{-6}$; ZAS-2018 covariant lifts ~3 orders) — *publishable structural caveat at CQG/JCAP Letter scope*; (iii) BDG $\sigma_\Lambda = \alpha_{\rm BDG}/\sqrt{V}$ first-principles decomposition with $\alpha_{\rm BDG} = \sqrt{K(M)/V}$ computable from MYZ 2025 bi-action integrals.

`CausalSetDarkEnergy.lean`: 15 substantive theorems / 0 sorry / 0 new axioms.

### Why it matters

Causal-set theory is one of the dominant non-string approaches to quantum gravity, and Sorkin's everpresent-Λ proposal is a serious candidate for explaining $\Lambda_{\rm obs}$. Phase 6m closes the dark-energy phenomenological window for the most-tested causal-set mechanisms while preserving the three structural caveats that have publication value independent of DESI.

---

## Result 2: Track B — Entropic-Gravity Dark Energy

### What we found

Nine entropic-gravity DE candidates were enumerated. After six rounds:

- **8 of 8 unanimous NO-GO-R5.** Verlinde 2017, Padmanabhan-CosMIn, Hossenfelder-Verlinde, Cadoni-Tuveri DEC, Li 2004 HDE, Tsallis HDE, Barrow HDE, Odintsov-D'Onofrio-Paul $\Omega_k$. 7-of-8 candidates have $r_d$-independent NO-GO mechanisms (CMB Boltzmann + Bullet-Cluster falsifiers).

This is the **first complete-mechanism-family NO-GO closure in Phase 6m**. The Tier-1 deep paper bundle D5 §9 carries this as a publication-novelty claim.

**Honest correction (Phase 7 absorption Session 5, 2026-05-08):** primary-source pdfminer extraction of Luciano arXiv:2506.03019 Table II yielded max ΔAIC = +4.7 for Barrow Entropy SN+BAO — methodology AIC-only, not BIC/Bayes-factor. The historical project number `barrow_log_bayes := 5.5` was unsourced. The Lean module was updated: `barrow_aic_delta := 4.7` + `aic_moderate_threshold := 4.0` (Burnham-Anderson). Theorem renamed `barrow_hde_no_go_bayes_factor_*` → `barrow_hde_disfavoured_information_criteria_*`. The §6 aggregator was refactored to a mixed-threshold form: `all_three_decisive_bayes_bounds_exceed_jeffreys_decisive` (Verlinde + Tsallis + Odintsov, all genuinely Bayes-decisive at |log𝓑| > 5) plus `all_quantitative_bounds_disfavoured` (4-of-4 mixed-threshold). The 8/8 NO-GO closure at the *disfavoured* level survives the correction. The Phase 7 absorption discipline ("primary-source WebFetch and verify before relying on registry-anchored magnitudes") is now standing project policy.

`EntropicGravityDarkEnergy.lean`: 14 substantive theorems / 0 sorry / 0 new axioms.

### Why it matters

Verlinde-style entropic gravity has been a serious dark-energy candidate for fifteen years. The unanimous NO-GO closure is the strongest possible structural verdict — a complete mechanism family closed. The Phase 7 honest correction (AIC vs Bayes; mixed-threshold aggregator) is itself a methodology contribution, illustrating that primary-source WebFetch + verification catches misattribution before publication-grade prose relies on it.

---

## Result 3: Track C — Jacobson-Thermodynamic-GR Dark Energy

### What we found

Nine Jacobson-thermodynamic-GR mechanisms were enumerated. After six rounds:

- **5+ R5 survivors — highest-survival track in Phase 6m.**
- M3 EGJ f(R) Exponential + ArcTanh: **strongest CLEARED-R5 of any track** (Plaza-Kraiselburd ΔAIC ≃ ΔBIC ≳ 20, Jeffreys "decisive" preference over ΛCDM).
- M3 Starobinsky: marginal CLEARED-R5.
- M3 Hu-Sawicki: NO-GO-R5 via chameleon Solar-System constraint at $b \approx 0.21$ (best-fit > 100× too large for chameleon screening).
- M4 Pure Lovelock: NO-GO-R5 at 1σ-box edge of Quintom-B, $|\tilde\alpha_2|_{\max} \leq 0.15$.
- M8 KSS: CLEARED-R5 conditional via path-(a) (Arata–Liberati–Neri 2603.28851); OPEN-R6+ via path-(c).
- M1 Jacobson 1995, M2/M7 Padmanabhan-CosMIn (epistemic flag), M9 Volovik-Jannes: PARTIAL-VIABLE under fixed-$r_d$ Planck DR3 prior.

`JacobsonThermoGRDarkEnergy.lean`: 12 substantive theorems / 0 sorry / 0 new axioms (later extended in Phase 6o W4a with 5 new theorems JTGR16–JTGR20 for the verdict-(B) honest one-way closure).

### Why it matters

Track C is the *only* track in Phase 6m with a strongly-cleared survivor (M3 EGJ f(R) Exponential + ArcTanh at ΔAIC ≃ ΔBIC ≳ 20). The Track-C survivors are not project-originated theories — they're mainstream Jacobson-thermodynamic mechanisms that the project has *correctly identified* as the only Phase-6m-tested family with substrate-realized DE candidates that stand up to DESI DR2. Future DESI DR3 + Roman (~2030) will adjudicate: pure-Λ class (M1, M2/M7, M9) floating-$r_d$ disfavor reaches ≳5σ at DR3 + >7σ at Roman; fixed-$r_d$ remains <3σ throughout.

---

## Result 4: Phase 6e Sakharov Cross-Bridge (Wave 3f + Phase 6o W4a Verdict (B))

### What we found

The Sakharov four-criterion (fermionic-node existence, universal coupling, $\text{tr}(I) \neq 0$, IR Lorentz-invariance recovery) is validated on Volovik–Jannes ³He-A (all four conditions hold, $\Lambda_J = \Lambda_{\rm HK} \sim \Delta_0^4 / (6\pi^2 \hbar^3)$); falsified on Finazzi–Liberati–Sindoni acoustic BEC (condition (ii) fails — only phonons have a BEC effective metric).

This was the **first systematic $\Lambda_J$ vs $\Lambda_{\rm HK}$ comparison on common substrate in literature**.

**Phase 6o W4a verdict (B), 2026-05-08:** the originally-claimed biconditional `sakharov_induced_gravity_criterion_iff_lambda_j_eq_lambda_hk` was honestly retired in favor of a one-way implication. Reason: the Volovik–Jannes 2012 §VII argument is forward-only; the FLS BEC primary-source check (arXiv:1103.4841 + 1204.3039 Eq. 71) confirms forward but doesn't test the converse. A strict-extension `SakharovExtended` structure was added with a load-bearing `depletion : ℝ` field. The 4-Boolean Sakharov layer (`SakharovConditions` + JTGR6–9) is preserved; the substantive new content is JTGR16–JTGR20 (depletion-factor asymmetry on ³He-A vs FLS BEC). Numerics refit: `lambdaJ := 6.0e-14 / lambdaHK := 7.5e-12 / depletion := 8.0e-3` (consistency `8e-3 × 7.5e-12 = 6e-14` via `norm_num`).

### Why it matters

This is the *substrate-physics* anchor for Track C. ³He-A is the first concrete substrate where Sakharov-induced gravity is rigorously realizable; FLS BEC is the first concrete substrate where the Sakharov condition (ii) demonstrably fails. The verdict-(B) honest downgrade — biconditional → one-way + depletion factor — is itself a methodology lesson: when the literature argues only one direction, the formal statement should reflect that, not over-claim.

---

## Result 5: Wave 4 — Unified 7-Class Phase 6m GD Taxonomy

### What we found

`DarkSectorClassificationExtension.lean` consolidates the per-track classifications into a single namespace covering Class 0 + (a) + (b) + (b′) + (b″) + (c) + (d), with a 3-tier GD applicability gradient (Tier I outside-domain / Tier II inapplicable / Tier III applies / Tier S re-derive). Per-track class assignments + cross-class instantiation witnesses to the Phase 5y orthogonality principle.

10 substantive theorems / 0 sorry / 0 new axioms.

### Why it matters

The unified taxonomy ties Phase 5y's Volovik-only orthogonality decomposition (Gibbs–Duhem ∩ $c_s^2 \geq 0$ ∩ natural $T_c$ ∩ MICROSCOPE) into a four-mechanism-family-spanning structural framework. M8 KSS uniquely populates Class (a). Unimodular reformulation as $\Lambda_{\rm HK}$ escape route admits 5 of 6 Track-C survivors except KSS.

---

## By the Numbers (Phase 6m, post-CLOSED)

- **Lean theorems shipped:** 50 substantive across 4 modules (CausalSetDarkEnergy 15 + EntropicGravityDarkEnergy 14 + JacobsonThermoGRDarkEnergy 12 + DarkSectorClassificationExtension 10), plus +5 from Phase 6o W4a (JTGR16–JTGR20). Phase 6m-flavor total: 55+ substantive theorems / 0 sorry / 0 new axioms.
- **Deep-research rounds:** 18 (6 per track) + R6 Lean closure + R7 strengthening + R8 cross-module proof-chain.
- **Publishable structural caveats:** 3 (Track A) + 1 (Track-C M3 cross-cutting) + 1 (Sakharov verdict-(B) one-way) — all embedded as D5 sections per `PAPER_DRAFT_MAPPING.md` per Pipeline Invariant #14 default (no new bundle targets spawned).
- **Bundle destinations:** D5 §8–§12 + §10.5 + §11.5 (with Phase 6o W4a addition to §11) + F §8 + flagship architectural-scope statement.
- **Architectural-scope update:** Layer 3 dark-energy is *outside the architecture's tested predictive scope under all four major mechanism families* (Volovik-q-theory + causal-set + entropic-gravity + Jacobson-thermodynamic-GR).

---

## Strategic Reading

Phase 6m is the *terminal closure* of the dark-energy probe program. Combined with Phase 5y, the four major mechanism families have all been exercised against DESI DR2 + standard cosmological constraints. The combined verdict is honest and clear: **the project's substrate produces Layer-3 SM+GR-sector emergent physics; dark-energy-scale physics requires either (i) a mechanism family the project hasn't tested, (ii) a CLEARED Track-C survivor like M3 EGJ f(R) Exponential which is *not* a project-originated theory but a mainstream Jacobson-thermodynamic mechanism, or (iii) acceptance that the architecture's predictive scope doesn't reach the dark-energy sector under the substrates currently exercised.** All three options are explicitly named in the architectural-scope statement.

The methodology contributions from Phase 6m are themselves substantive:

- **Track B's complete-family unanimous NO-GO closure** is the strongest possible structural verdict and the publication-novelty kernel of D5 §9.
- **The Phase 7 absorption Session 5 honest correction** (AIC vs Bayes; mixed-threshold aggregator) demonstrates that primary-source WebFetch + verify catches misattribution before publication-grade prose relies on it. This is now standing project policy.
- **Phase 6o W4a verdict (B) honest downgrade** (biconditional → one-way + depletion factor) is a structural-tightening lesson: when the literature argues only one direction, the formal statement should reflect that.
- **The unified 7-class GD taxonomy** is a reusable framework for future dark-sector classification work.

Phase 6m ships *no per-wave standalone papers*. All content lifts into bundle D5 (§8–§12 + §10.5 + §11.5) with the F flagship §8 + §10 architectural-scope summary.
