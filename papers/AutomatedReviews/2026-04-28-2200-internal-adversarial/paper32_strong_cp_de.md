---
paper: paper32_strong_cp_de
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-28T22:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper32_strong_cp_de

## Summary

Cost-bounded review (Classes 1, 3, 4, 5, 6 only). Citation bibitems are
clean by inspection (Class 1 cache-skip — no wrong-author / wrong-title
smell). The Lean module `StrongCPTopologicalDE.lean` carries 8
substantive theorems with no `rfl`-on-non-trivial-claim placeholders and
no structural-tautology bodies. Two REQUIRED issues: (a) abstract
narrative claims a "structural inconsistency theorem" forcing the
project to commit to one DE mechanism, but `combined_zhitnitsky_qtheory_exceeds_observation`
only shows `H_BothActiveGivesInconsistency (rho > 1e-10)` — i.e. it
asserts the combined density exceeds 1e-10, which is the observed
density itself, not a "factor of three" excess as the prose claims;
the inequality is also unconditionally true by Zhitnitsky alone, the
q-theory term is decorative; (b) the prose claim `\rhoDE^{\mathrm{pred}}
\approx 6.7e-9 eV^4` contradicts the abstract's own number `6.71 eV^4
... within roughly 240×` — the ratio 6.71e-9 / 2.8e-11 ≈ 240 is
self-consistent, but `\theta = 1` is referred to as the "Planck-natural"
value which is not the standard usage in the strong-CP literature
(Planck-natural usually means a generic `O(1)` value, often `θ = π`).

## Findings

### 3.1 — 🟡 REQUIRED — `combined_zhitnitsky_qtheory_exceeds_observation` does not establish the prose "factor-of-three excess" claim

- **Gate:** LeanProofSubstance (Gate 5) / NarrativeGrounding (Gate 7)
- **Location:** `paper32_strong_cp_de/paper_draft.tex:222-230`; `lean/SKEFTHawking/StrongCPTopologicalDE.lean:196-206`
- **Observed:** Paper prose: "the theorem `combined_zhitnitsky_qtheory_exceeds_observation` shows that *any* positive q-theory contribution `ρ_q > 0` added to the Zhitnitsky prediction at the Particle-Data-Group QCD scale exceeds the observed dark-energy density by more than a factor of three." The Lean theorem's actual statement and predicate is `H_BothActiveGivesInconsistency rho := rho > 1e-10`, and the proof only requires `6.71e-9 + ρ_q > 1e-10`, which is true regardless of `ρ_q` (Zhitnitsky alone already gives 6.71e-9, ~67× larger than 1e-10). The q-theory hypothesis `0 < rho_qtheory` is never used in a load-bearing way (the `linarith` discharge would succeed without it).
- **Evidence:** `Lean StrongCPTopologicalDE.lean:186-187`: `def H_BothActiveGivesInconsistency (rho_DE_combined : ℝ) : Prop := rho_DE_combined > 1.0e-10`. Proof body at lines 199-206 uses `h_zhit : 0.1^6 * 6.71e-3 = 6.71e-9` and then `linarith`. Without `rho_qtheory`, the same `linarith` closes from `6.71e-9 > 1e-10`. The "factor of three" claim is not encoded anywhere — the Prop says only "> 1e-10", not "> 3 × 2.8e-11 = 8.4e-11" (which would be a factor-of-three-over-observed).
- **Expected:** Either (a) the Lean predicate is `> 3 * 2.8e-11` (matching prose), with the proof requiring both Zhitnitsky and a positive q-theory contribution to clear that bar, or (b) prose is rewritten to match the actual content: "any positive q-theory addition pushes the combined value above 1e-10 (~3.6× the observed), and Zhitnitsky alone already does, so the q-theory contribution is decorative — the load-bearing falsifier is the Zhitnitsky-alone overshoot."
- **Fix:** Tighten the Prop to `rho > 3 * 2.8e-11` (or to a more substantive single-mechanism-vs-both-mechanism comparison), and use `rho_qtheory > 0` in the proof body so dropping the hypothesis breaks the proof. Alternatively, rewrite §5 ("One-mechanism inconsistency") so it does not claim a factor-of-three, and instead documents that the load-bearing structural fact is "Zhitnitsky alone already overshoots by ~240×."

### 5.1 — 🟡 REQUIRED — "Planck-natural value θ = 1" is non-standard terminology

- **Gate:** NarrativeGrounding (Gate 7)
- **Location:** `paper32_strong_cp_de/paper_draft.tex:118, 120, 123-128, 161, 254`
- **Observed:** Paper repeatedly refers to `θ = 1` as the "Planck-natural value." In the strong-CP literature, "naturally O(1)" (the standard contrast to the experimental bound `|θ| ≲ 1e-9`) covers values in `[-π, π]`, not specifically θ = 1. The structural falsifier `theta_planck_natural_violates_edm_bound : ¬ (∃ tv : ThetaVacuum, tv.theta = 1)` only rules out `θ = 1`, not the full O(1) range — though by the structural invariant `|θ| ≤ 1e-9` it would equally falsify any `|θ| > 1e-9`.
- **Evidence:** Lean theorem at `StrongCPTopologicalDE.lean:66-72`. Standard SC literature (e.g., Peccei-Quinn 1977, Vafa-Witten 1984): θ is naturally generic in `(-π, π]` not specifically 1. Calling θ = 1 "Planck-natural" conflates two distinct concepts (Planck-vacuum-energy naturalness ~ M_P^4, vs. dimensionless angle naturalness ~ O(1)).
- **Expected:** Refer to θ = 1 simply as "an O(1) value" or "a generic value of order unity"; reserve "Planck-natural" for the energy-density estimate `M_P^4 ≈ 1e112 eV^4` (which the paper does correctly use elsewhere, e.g. line 43, 161).
- **Fix:** Rename the Lean theorem `theta_planck_natural_violates_edm_bound → theta_order_unity_violates_edm_bound` (or strengthen to `∀ θ : ℝ, |θ| > 1e-9 → ¬ (∃ tv, tv.theta = θ)` — substantive generalization). In the prose, replace "Planck-natural value" with "naturally-O(1) value" wherever it refers to θ.

### 5.2 — 🔵 RECOMMENDED — abstract claim "approximately 120 orders of magnitude below the Planck-natural estimate" is loose

- **Gate:** NarrativeGrounding (Gate 7)
- **Location:** `paper32_strong_cp_de/paper_draft.tex:42-43`; `lean/SKEFTHawking/StrongCPTopologicalDE.lean:122-125`
- **Observed:** Abstract: "approximately 120 orders of magnitude below the Planck-natural estimate". Lean theorem `zhitnitsky_DE_far_below_planck` only proves `zhitnitskyDE_eV4 0.1 < 1e10`, which is 102 orders below 1e112 — so the theorem certifies "at least 102 orders" but not "120". The prose 120 number is implicit (6.71e-9 vs. 1e112 ≈ 121 orders), and the threshold 1e10 in the theorem is much weaker.
- **Evidence:** `StrongCPTopologicalDE.lean:122-125`: `theorem zhitnitsky_DE_far_below_planck : zhitnitskyDE_eV4 0.1 < 1.0e10`. Gap from `M_P^4 ≈ 1e112` to `< 1e10` = 102 orders.
- **Expected:** Tighten the Lean theorem's RHS to `< 1e-8` (one order above realized 6.71e-9), giving 120 orders below `1e112` — matching the prose claim.
- **Fix:** Replace `1e10` with `1e-8` in `zhitnitsky_DE_far_below_planck`; the existing `norm_num` proof should still succeed.

## Class 1 cache-skip summary

Bibitems inspected by author/title/venue plausibility:
- `VanWaerbeke2025` — arXiv:2506.14182 (2025), Van Waerbeke & Zhitnitsky, "Topological dark energy from QCD vacuum" — recent submission; `cache-skip` (no smell).
- `KlinkhamerVolovik2010` — arXiv:0907.4887, JETP Lett. 91, 259 (2010), "Cosmological constant from gravitating Skyrmions" — `cache-skip`.
- `Pendlebury2015` — arXiv:1509.04411, PRD 92, 092003 (2015) — `cache-skip` (well-known result).
- `Planck2018` — A&A 641, A6 (2020) — `cache-skip`.
- `DESI2024` — JCAP 02, 021 (2025) — `cache-skip`.

## Class 4 cross-paper consistency

No bibkeys shared with the other six papers in this batch; no cross-paper contradictions.

## Class 6 assumption disclosure

`IsAnomalyMatchingCompatible` is a 3-conjunct Prop. The paper §4 discloses each conjunct (a), (b), (c). The witness theorem at PDG Λ_QCD relies on the `sm_anomaly_with_nu_R` upstream theorem from `Z16AnomalyComputation`; this is implicitly disclosed via the prose "the Standard-Model anomaly-content calculation at the level of generators." Sufficient.

`H_BothActiveGivesInconsistency` is a tracked-hypothesis Prop. Paper §5 prose names it as the "structural inconsistency theorem" without explicitly disclosing it is a tracked Prop. RECOMMENDED: add one sentence at §5 noting that `H_BothActiveGivesInconsistency` is the project's tracked-hypothesis predicate, parallel to other Phase-6 correctness-push hypotheses.
