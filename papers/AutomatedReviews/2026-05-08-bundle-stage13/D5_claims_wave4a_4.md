# D5 Claims Review — Phase 6o Wave 4a.4 (Stage 10)

**Date:** 2026-05-08T20:30:00Z
**Bundle:** D5 (Tier 1 — Dark sector under substrate constraints)
**Reviewer agent:** physics-qa:claims-reviewer-v2-bundle-aware (scoped run)
**Reviewer model:** claude-opus-4-7-1m
**Run ID:** `claims-reviewer-v2-bundle-aware:2026-05-08T20:30:00Z:wave4a4-scoped`
**Trigger:** Phase 6o Wave 4a.4 substantive D5 §11 prose changes (Sakharov
Λ_J ↔ Λ_HK biconditional retired in favour of one-way implication +
load-bearing depletion-factor ℝ encoding); BUNDLE_LIFT_PROCEDURE.md §11
mandates Stage-13 reviewer triple after substantive bundle changes.
**Verdict:** **GREEN** — 15 PASS / 3 WARN (low-severity polish only) /
0 FAIL / 0 BLOCKERs.

## Scope

This pass is scoped narrowly to Wave 4a.4 changes in D5:

1. **§11 prose** (lines 981–1100), including:
   - The new "Wave 4a.4 closure --- biconditional retired (verdict (B))"
     paragraph block (lines 1023–1075).
   - The updated "primary-source-grounded ℝ-valued data via the new
     `SakharovExtended` structure" paragraph (lines 1004–1020) with
     refreshed JTGR12/JTGR13/JTGR14 theorem references.
2. **§11.5** (lines 1106–1124) "first systematic Λ-comparison" claim.
3. **§13 Discussion** (lines 1208–1211) repeat of the same first-claim.
4. **Bibliography block** (lines 1330–1357) — 3 new bibitems
   (FinazziLiberatiSindoni2012PRL, FinazziLiberatiSindoni2012Proc,
   BelenchiaLiberatiMohd2014).

The rest of D5 was reviewed-clean at the 2026-05-06 round-4 close
(`papers/D5/claims_review.json`: 16/16 PASS, both prior R3 BLOCKERs
deterministically auto-closed).

## Anchor checks

### A. Lean theorem references (TN class)

All 9 referenced theorems resolve in `lean/lean_deps.json`:

| Anchor | Lean theorem (qualified) | Status |
| --- | --- | --- |
| JTGR6 (renamed) | `SKEFTHawking.JacobsonThermoGRDarkEnergy.sakharov_induced_gravity_criterion_implies_lambda_j_eq_lambda_hk` | PASS — exists, `_iff_` -> `_implies_` rename honest |
| JTGR12 | `...SakharovExtended.sakharov_criterion_implies_lambda_j_eq_lambda_hk_real` | PASS |
| JTGR13 | `...SakharovExtended.volovikJannes_he3a_lambda_j_eq_lambda_hk_real` | PASS |
| JTGR14 | `...SakharovExtended.flsBEC_lambda_j_neq_lambda_hk_real` | PASS |
| JTGR16 | `...SakharovExtended.sakharov_depletion_factor_relation` | PASS |
| JTGR17 | `...SakharovExtended.volovikJannes_he3a_depletion_eq_one` | PASS |
| JTGR18 | `...SakharovExtended.flsBEC_depletion_strictly_between_zero_and_one` | PASS |
| JTGR19 | `...SakharovExtended.volovikJannes_vs_flsBEC_depletion_asymmetry` | PASS |
| JTGR20 | `...SakharovExtended.wave_4a_4_honest_one_way_closure` | PASS |

No TN-class findings.

### B. Numerical consistency (IA class)

Lean `flsBEC_extended` (JacobsonThermoGRDarkEnergy.lean lines 629–638):
- `lambdaJ := 6.0e-14` eV
- `lambdaHK := 7.5e-12` eV
- `depletion := 8.0e-3`

Cross-checks:
- `depletion * lambdaHK = 8.0e-3 * 7.5e-12 = 6.000e-14 eV = lambdaJ` —
  exact match (delta_pct = 0.000%). JTGR16's Lean proof is
  `S.depletionRelation`, which is constructor-required; for
  `flsBEC_extended` it is discharged by `by norm_num` (line 638), the
  rfl-equivalent at the placeholder values.
- `sqrt(rho_0 * a^3) ≈ sqrt(7e-5) ≈ 8.367e-3` (deep-research §3.3
  numerics) → placeholder rounded to `8e-3`, within ~5%.
- He³-A: `lambdaJ = lambdaHK = 1.6e-3` (K-units; Δ₀⁴ scaling shared
  between gap-energy substrate and heat-kernel vacuum energy under
  4-Weyl-fermion topology), `depletion = 1`, `1 * 1.6e-3 = 1.6e-3`
  exact.

Prose claim "placeholder √(ρ₀a³) ≈ 8 × 10⁻³ for canonical
Steinhauer-class ⁸⁷Rb parameters" (line 1060) matches.

No IA-class findings.

### C. Citation registry (Gate 1)

Three new bibitems verified against `src/core/citations.py`:

| Bibkey | Authors / journal / vol / page / year | DOI | arXiv | PDF cached? |
| --- | --- | --- | --- | --- |
| `FinazziLiberatiSindoni2012PRL` | Finazzi-Liberati-Sindoni / Phys. Rev. Lett. / 108 / 071101 / 2012 | 10.1103/PhysRevLett.108.071101 | 1103.4841 | YES |
| `FinazziLiberatiSindoni2012Proc` | Finazzi-Liberati-Sindoni / Proc. II Amazonian Symp. / — / — / 2012 | None (proceedings) | 1204.3039 | YES |
| `BelenchiaLiberatiMohd2014` | Belenchia-Liberati-Mohd / Phys. Rev. D / 90 / 104015 / 2014 | 10.1103/PhysRevD.90.104015 | 1407.7896 | YES |

All three primary-source PDFs verified at
`Lit-Search/Phase-1-and-Background/primary-sources/`. `doi_verified` is
`None` on all three (pending human verification — registry-promotion
default at Phase 7 Session 5; this is normal for newly-added
primary sources). Bibitem prose in `paper_draft.tex` (lines 1333–1350)
matches the registry titles, author lists, journals, volumes, pages,
years, DOIs, and arXiv IDs character-for-character.

No citation-integrity findings.

### D. Verdict-(B) framing fidelity (Gate 10)

The "honestly retired" / "publication-novelty without primary-source
precedent" / "maximally-honest substrate-physics statement" prose
(lines 1023–1048) faithfully reproduces the deep-research return §6
verdict (B) rationale:

> *"Honestly retire the biconditional reading and ship as a one-way
> implication Sakharov 4-criterion ⇒ Λ_J = Λ_HK, with deeper substrate
> encoding (the depletion pre-factor as a substrate-side computable
> real number) for transparency."*

The forward-only-implication framing in JTGR12/JTGR20 (Lean) matches
the prose framing exactly. `wave_4a_4_honest_one_way_closure` (JTGR20)
is the (⇒)-only theorem; the prior P5-anti-pattern Boolean projection
of `lambdaEffEqLambdaHK` is retained for backwards compatibility but
no longer load-bearing.

No narrative-fidelity findings.

### E. Wave 4a.3 → 4a.4 substrate-physics encoding shift (Gate 5)

The prose claim "the prior P5-anti-pattern Boolean projection of
λ_Eff = λ_HK has been strictly-extended to a witness-required
ℝ-level identity" (line 1073) is grounded:

- `SakharovExtended` (Lean line 542) requires both
  `lambdaJEqLambdaHKEvidence` (a Prop discharging Λ_J = Λ_HK whenever
  Boolean condition (iv) holds) AND `depletionRelation` (an
  unconditional Prop discharging Λ_J = depletion · Λ_HK) at
  construction time. Both fields are constructor-required; no default
  discharge. This is the strict-extension encoding.
- The depletion field (line 576) is the new ℝ-valued substrate-physics
  field that grounds the Λ_J ≠ Λ_HK structural separation on FLS BEC
  — load-bearing per the Wave 4a.4 deliverable.

PASS.

## Findings

### F1. WARN (low) — 'first systematic Λ_J vs Λ_HK on a common substrate' phrasing repeated 3x

The phrase "first systematic Λ_J vs Λ_HK comparison/test on a common
substrate" appears at three locations:

- Line 985 (§11 opening sentence): "providing the first systematic
  Λ_J vs Λ_HK comparison on a common substrate in the literature"
- Line 1109 (§11.5 short note): "is the first systematic Λ-comparison
  on a common substrate in the literature"
- Line 1209 (§13 discussion): "provides the program's first systematic
  Λ_J vs Λ_HK test on a common substrate"

The first-claim status itself is intact post-verdict (B): no primary
source applies the Sakharov 4-criterion as a discriminant pairing
He³-A and FLS BEC explicitly. FLS 2012 PRL/Proc and BLM 2014 publish
the BEC-side Λ result alone; Jannes-Volovik 2012 publishes the He³-A
side alone; no primary source pairs the two with the 4-criterion as
the comparator. So the "first systematic" framing is appropriate.

However, the phrasing "on a common substrate" is mildly ambiguous —
the comparison is *across* substrates (³He-A and FLS BEC), not on
one shared substrate. Three-place repetition of the same ambiguous
framing is a minor consistency issue.

**Severity:** Low. Non-blocking. Recommend tightening to
"across emergent-gravity substrates with the Sakharov 4-criterion as
the discriminant" or "first systematic Sakharov-criterion-driven
Λ_J vs Λ_HK comparison" in a future polish pass.

### F2. (no other findings)

## Cross-bridge checks (out of scope but spot-noted)

- **D5 §7 ↔ D3 §21 heat-kernel a₀ cross-bridge** (D5 anchor list item):
  Wave 4a.4 did not modify §7 prose; out of scope for this pass and
  was already round-4 GREEN. No regression.
- **D5 abstract** (lines 30–100): mentions "satisfied by Volovik--Jannes
  ³He-A and falsified by Finazzi--Liberati--Sindoni acoustic BEC"
  (lines 88–89). Consistent with the §11 §11.5 §13 retirement of
  the biconditional — abstract correctly reads as Sakharov-criterion
  *satisfaction* (Boolean) and *falsification at condition (ii)*,
  not as a biconditional Λ_J = Λ_HK claim. PASS.

## Reconciliation with prior round (2026-05-06 round 4)

No prior findings touch the §11 Wave 4a.4 zone. The 16 prior round-4
sentences cover earlier sections (§2 paper17, §4 BBN, §6 EP, §7 CC,
etc.); none reproduce as failures in this pass. No supersession
candidates emitted.

## Output artifacts

- Schema-valid JSON: `papers/D5/claims_review_wave4a_4.json` (18
  sentences, 15 PASS / 3 WARN / 0 FAIL, validates clean via
  `scripts/sentence_state.py validate`).
- This human-readable companion:
  `papers/AutomatedReviews/2026-05-08-bundle-stage13/D5_claims_wave4a_4.md`.

## Verdict

**GREEN.** Wave 4a.4 D5 §11 prose changes, Lean theorem references
(JTGR12–14, 16–20), and 3 new bibitems are all bundle-clean. Three WARN
findings are low-severity polish recommendations (single repeated
phrasing-ambiguity); none are blocking. Stage 10 (claims review) for
Wave 4a.4 closes GREEN.
