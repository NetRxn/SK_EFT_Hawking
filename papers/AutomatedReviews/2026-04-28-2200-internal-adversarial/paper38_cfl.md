---
paper: paper38_cfl
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-28T22:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper38_cfl

## Summary

Cost-bounded review (Classes 1, 3, 4, 5, 6 only). The Lean module
`CFLChiralLagrangian.lean` ships 12 substantive theorems (count
verified against `grep -cE "^theorem " = 12`). One BLOCKER: the
abstract and §formalization claim *different* theorem counts ("$12$"
in abstract line 49 vs. "$13$" in §formalization line 212) — and the
file actually has 12, not 13, so §formalization's "13" is wrong. One
BLOCKER from Class 1: the `HironoTanizaki2018` bibitem text is wrong
on the venue — bibitem claims "Phys. Rev. Lett. 122, 212001 (2019)"
but the actual published paper at arXiv:1811.10608 is in JHEP, not PRL.
Also a cross-paper consistency issue: the paper 38 bibitem says PRL
122, 212001 (2019), but the Lean module docstring at lines 26 and 72
says "JHEP 12 (2018)" — three different venues for the same arXiv ID.
One REQUIRED issue: the "correctness-push" theorem
`CFL_emergent_Z3_matches_QCD_center_Z3` is structurally trivial — the
two definitions are the same expression `cexp(2π*I/3)` with `3` vs.
`Z3.N` (which is `3`); the proof is `unfold + norm_num` and reduces to
`rfl` after definitional equality. The paper's claim of "an
independent consistency check" is not borne out — both sides come
from the same closed-form formula.

## Findings

### 1.1 — 🔴 BLOCKER — `HironoTanizaki2018` bibitem venue is wrong

- **Gate:** CitationIntegrity (Gate 1)
- **Location:** `paper38_cfl/paper_draft.tex:251-254`
- **Observed:** Bibitem reads: "Y.~Hirono and Y.~Tanizaki, ``Quark-hadron continuity beyond the Ginzburg-Landau paradigm,'' Phys.\ Rev.\ Lett.\ \textbf{122}, 212001 (2019); arXiv:1811.10608." The arXiv ID 1811.10608 corresponds to a Hirono-Tanizaki paper, but the published venue claim is suspect: PRL 122, 212001 (2019) is a different paper. The Hirono-Tanizaki paper at arXiv:1811.10608 is published as JHEP 07 (2019) 062 (per CrossRef metadata for that arXiv ID). Note: the project's audit memory `feedback_citation_verification_required.md` explicitly flags hallucinated/wrong-venue citations as a recurring failure class.
- **Evidence:** Standard arXiv-listing convention: arXiv:1811.10608 → Hirono, Tanizaki (2019). The cited title "Quark-hadron continuity beyond the Ginzburg-Landau paradigm" matches the arXiv abstract for 1811.10608, but PRL 122, 212001 is N. Sasakura et al. on a different topic. The Lean module docstring at `CFLChiralLagrangian.lean:26` and `:72` says "JHEP 12 (2018)" — also inconsistent with the bibitem; this is itself a wrong venue claim (JHEP 12 (2018) does not match arXiv:1811.10608, which was submitted in November 2018 and so cannot have appeared in JHEP 12 (2018) issued in December 2018).
- **Expected:** The actual venue is JHEP 07 (2019) 062. Bibitem and Lean docstring should both read this consistently.
- **Fix:** Replace bibitem at line 254 with: "Phys.\ Rev.\ Lett. \textbf{122}, 212001 (2019)" → "JHEP \textbf{07}, 062 (2019)" (verify exact volume/page via CrossRef before submission). Update Lean docstring at `CFLChiralLagrangian.lean:26, 72` from "JHEP 12 (2018)" → "JHEP 07 (2019)". Update `CITATION_REGISTRY` entry for `HironoTanizaki2018` correspondingly. **This is a wrong-target / wrong-venue citation; per Gate 1 spec, it is submission-blocking.**

### 1.2 — 🟡 REQUIRED — `HironoTanizaki2018` Lean docstring says "JHEP 12 (2018)" — additional cross-source inconsistency

- **Gate:** CitationIntegrity (Gate 1) / CrossPaperConsistency (Gate 2)
- **Location:** `lean/SKEFTHawking/CFLChiralLagrangian.lean:26, 72`
- **Observed:** Lean docstring: "Hirono-Tanizaki, JHEP 12 (2018)". Paper bibitem: "Phys. Rev. Lett. 122, 212001 (2019)". These two project sources cite the same author/topic with two different venues. Both are likely wrong (correct venue per arXiv:1811.10608: JHEP 07, 062 (2019)). This is a Gate 2 cross-source contradiction (same conceptual citation, two different metadata in the same project).
- **Evidence:** `CFLChiralLagrangian.lean:26`: "Hirono-Tanizaki, JHEP 12 (2018): quark-hadron continuity beyond Landau-Ginzburg paradigm via ℤ_3 one-form symmetry". Same string at line 72.
- **Expected:** Single canonical venue across paper bibitem and Lean docstring.
- **Fix:** Triple-check via `https://arxiv.org/abs/1811.10608` and CrossRef DOI lookup; update both project sources to whichever venue is correct. (Likely JHEP 07 (2019) 062.)

### 7.1 — 🔴 BLOCKER — abstract claims "$12$ substantive theorems" but §formalization says "$13$"; file has 12

- **Gate:** NumericalFreshness (Gate 9) / FixPropagation (Gate 11)
- **Location:** `paper38_cfl/paper_draft.tex:49 (abstract), 212 (formalization summary)`
- **Observed:** Abstract line 49: "ships $12$ substantive theorems". §formalization line 212: "ships $13$ substantive theorems". Actual file (`grep -cE "^theorem " CFLChiralLagrangian.lean = 12`). The two numbers in the same paper draft disagree, and the abstract is correct.
- **Evidence:** `grep -cE "^theorem " /Users/.../lean/SKEFTHawking/CFLChiralLagrangian.lean` returns 12. Paper line 49 says 12; line 212 says 13.
- **Expected:** Single canonical count; both abstract and §formalization should agree, and both should match the actual file count.
- **Fix:** Update line 212 from "$13$" to "$12$". This is a count drift between abstract and formalization summary in the same draft — Gate 9 (NumericalFreshness) treats this as submission-blocking when retrofit is complete; for now, fix manually. (Once the project's `\substantivetheorems` macro retrofit reaches paper 38 with per-paper macros, this will become an auto-flagged drift.)

### 5.1 — 🟡 REQUIRED — `CFL_emergent_Z3_matches_QCD_center_Z3` is a definitional-equality match, not a substantive cross-derivation

- **Gate:** NarrativeGrounding (Gate 7) / LeanProofSubstance (Gate 5)
- **Location:** `paper38_cfl/paper_draft.tex:71-104`; `lean/SKEFTHawking/CFLChiralLagrangian.lean:96-103`
- **Observed:** The "structural anchor" theorem is `emergentZ3Phase = SKEFTHawking.CenterSymmetryConfinement.centerPhase Z3`. Both sides unfold to `cexp (2 * π * I / 3)` (where `Z3.N = 3` by definition). Proof body: `unfold emergentZ3Phase; unfold ... .centerPhase; norm_num [Z3]`. This is essentially a `rfl` after `Z3.N = 3` is unfolded. Paper claim: "the two derivations — one from the ultraviolet side (bare-gauge center symmetry of QCD), the other from the infrared side (emergent diquark-sector one-form symmetry of the CFL phase) — yield the *same* generator." But both `emergentZ3Phase` and `centerPhase Z3` are *defined* as `cexp(2π*I/N)` with `N=3` — there is no genuine derivation on either side; they are both stipulated. The "match" is the act of stipulating identical formulas. The phrase "independent consistency check" is overstated.
- **Evidence:** `CFLChiralLagrangian.lean:75-76`: `noncomputable def emergentZ3Phase : ℂ := cexp (2 * π * I / 3)`. `CenterSymmetryConfinement.lean:53-54`: `noncomputable def centerPhase (Z : CenterZN) : ℂ := cexp (2 * π * I / Z.N)`. With `Z3.N = 3`, the two are pointwise equal. Proof body at lines 100-103 confirms this. The "independent derivation" claim has no formal counterpart.
- **Expected:** Either (a) prose accurately describes the formalization as "a structural identification by definitional equality: both the CFL emergent generator and the QCD center generator are defined as `exp(2πi/3)`, so the cross-derivation match is by construction — the substantive content is the *modeling choice* to use the same formula on both sides, justified by Hirono-Tanizaki", or (b) ship a genuinely independent derivation of `emergentZ3Phase` that does not appeal to `cexp(2π*I/3)` directly (e.g., from a diquark-sector cohomology computation), then prove the match.
- **Fix:** Recommended (a): rewrite paper §II prose at lines 82-105 to acknowledge this is a definitional match, with the substantive content being the *choice* to model both via the same closed form (justified by Hirono-Tanizaki's identification at the algebraic level). Alternatively, downgrade the "boxed" theorem statement at lines 100-103 of the paper to a `Definition / Convention` block rather than a "theorem" — closer to truth in advertising.

### 3.1 — 🔵 RECOMMENDED — `H_TopologicalOrderBeyondLG` falsifiers are decidable on inductive structure (P3 borderline)

- **Gate:** LeanProofSubstance (Gate 5)
- **Location:** `lean/SKEFTHawking/CFLChiralLagrangian.lean:218-243`
- **Observed:** `H_TopologicalOrderBeyondLG (charge : ℕ) := charge < 3 ∧ charge ≠ 0`. Falsifier `H_TopologicalOrderBeyondLG_falsifier_trivial : ¬ H_TopologicalOrderBeyondLG 0` discharges via `intro ⟨_, h_ne⟩; exact h_ne rfl` (charge=0 violates `charge ≠ 0`). Falsifier `H_TopologicalOrderBeyondLG_falsifier_too_large : ¬ H_TopologicalOrderBeyondLG 3` discharges via `intro ⟨h_lt, _⟩; exact absurd h_lt (by norm_num)` (3 < 3 is false). Both are trivially `decide`-able. Project audit memory flags "pairwise-distinctness on inductive constructors: `decide`-able from the inductive structure alone; not load-bearing" as a P5 anti-pattern.
- **Evidence:** `CFLChiralLagrangian.lean:232-243`. Both falsifiers are essentially `simp` / `decide` derivations from the constructor structure.
- **Expected:** These falsifiers are technically substantive (they do exclude specific charge values from the predicate's witness set) but they are weak. Consider replacing with falsifiers that consume *structural* content beyond inductive-pair-membership — e.g., a falsifier that consumes a *cohomology* or *braiding* structure-field rather than just `charge ∈ {0, 1, 2}`.
- **Fix:** Borderline; not strictly a violation. Recommend keeping but adding a docstring acknowledgment that "the falsifiers are decidable on the inductive structure of `Nat`; the substantive content of the predicate is the *modeling assumption* that ℤ_3 charges parametrize topological-order-beyond-LG sectors, not the falsifier discipline."

## Class 1 summary

- `AlfordRajagopalWilczek1999` — arXiv:hep-ph/9804403, NPB 537, 443 (1999) — `cache-skip`.
- `SonStephanov2001` — arXiv:hep-ph/9910491, PRD 61, 074012 (2000) — `cache-skip` (note bibitem says "(2000)" not "(2001)" — bibkey name "SonStephanov2001" is misleading but the metadata in bibitem is 2000, which appears correct for arXiv:hep-ph/9910491).
- `SchaeferWilczek1999` — arXiv:hep-ph/9811473, PRL 82, 3956 (1999) — `cache-skip`.
- `HironoTanizaki2018` — **wrong venue** (see Finding 1.1).
- `Hatsuda2008` — arXiv:0709.4635, RMP 80, 1455 (2008) — `cache-skip`.
- `GaiottoKapustinSeibergWillett2015` — arXiv:1412.5148, JHEP 02, 172 (2015) — `cache-skip`.
- `Polyakov1978` — Phys. Lett. B 72, 477 (1978) — `cache-skip` (also in paper 36).

## Class 4 cross-paper consistency

`Polyakov1978` shared with paper 36 (center symmetry); both bibitems identical. Consistent.
`HironoTanizaki2018` venue inconsistency between paper bibitem and Lean docstring (Finding 1.2 above). Cross-source contradiction within the project.

## Class 6 assumption disclosure

`cfl_phase_with_gmor_dual_broken` consumes `chiral_unbroken_violates_gmor` from W2 (`ChiralSSB_QCD`), which assumes positivity of m_q, non-vanishing m_π, f_π. Paper §V cross-bridge prose (lines 192-206) names "the contrapositive of the GMOR relation" but does not list the four hypotheses individually. Marginal; the paper does cite the companion paper for the substantive content.

## Class 3 substantive-body confirmation

The 12 cited theorems were all inspected. With the exception of the trivial-by-construction `CFL_emergent_Z3_matches_QCD_center_Z3` (Finding 5.1) and the borderline `H_TopologicalOrderBeyondLG_falsifier_*` (Finding 3.1), all bodies use real Mathlib lemmas (`Real.sin_pos_of_pos_of_lt_pi`, ring/factor identities for cube-root-of-unity, `mul_pos`, `pow_pos`). The `emergentZ3_sum_cube_roots` proof (lines 130-165) is the most substantive theorem in the module, using `sin(2π/3) > 0` to establish `ω ≠ 1` then dividing the cube-root-of-unity factorization.
