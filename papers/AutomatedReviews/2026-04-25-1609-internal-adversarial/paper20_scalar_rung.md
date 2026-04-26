---
paper: paper20_scalar_rung
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-25T16:09:00Z
readiness_gates_version: 1
round: 4
prior_round: papers/AutomatedReviews/2026-04-25-2106-internal-adversarial/paper20_scalar_rung.md
scope: Round 3 closure verification (66→68 paper-prose drift + Y_TOP llm_verified_notes drift) + audit of §6 rewrite for new findings
---

# Adversarial Review — paper20_scalar_rung (Round 4)

## Summary

Aggregate verdict: **GREEN** (paper-local; 1 carryforward REQUIRED inherited from Round 2/3, scope-deferred per task spec). Findings: **0 BLOCKER**, **0 new REQUIRED**, **0 RECOMMENDED**. The two Round 3 findings (7.1 BLOCKER 66→68 paper-prose drift; 2.1 REQUIRED Y_TOP `llm_verified_notes` stale) are both verified closed. The §6 rewrite did not introduce any new BLOCKER- or REQUIRED-class issues — block enumeration arithmetic is correct, all newly-quoted Lean theorem names resolve, top-mass / Yukawa values are cross-source consistent, and no count literals leaked. Counts are fresh (`\totaltheorems{4165}`, `\leanmodules{173}`, `\papercount{21}`). Paper 20 is submission-ready on Gates 1 / 2 / 3 / 5 / 7 / 9 modulo the carryforward.

## Round-3 finding closure verification

### 7.1 R3 — 🔴 → ✅ CLOSED — Paper §6 prose vs Lean dimension agreement

- **Status:** **CLOSED**.
- **Evidence:**
  - `grep -n "66\|68" papers/paper20_scalar_rung/paper_draft.tex` → only L372/375/376/378 remain, and all four explicitly carry the value 68: L372 "$68$-dimensional ($2 + 2 + 4 + 4 + 12 + 4 + 12 + 4 + 12 + 12$, summing the explicit ten representation-theoretic block sizes per O.2 §3.2)"; L375 references theorem `fierzBlockSum_eq_68`; L376 "the value $68$ corrects an arithmetic typo"; L378 "$68$, not the document's stated $66$".
  - Paper now *discloses* the deep-research arithmetic typo rather than silently propagating it — the right move for credibility.
  - Block-sum arithmetic verified by hand: 2+2+4+4+12+4+12+4+12+12 = 68 ✓ (matches `fierzBlockSum` definition at `BHLGaugeEmbedding.lean:123-124`).
  - L375/381/384 now reference `\texttt{fierzBlockSum\_eq\_68}` (the decide-proof), `\texttt{fierzBlockSum}` (in the H_FierzCompletenessExtended formula), `\texttt{bhlBilinearBasisDim}` (canonical witness), `\texttt{fierz\_completeness\_holds\_for\_bhl\_dim}` (witness), `\texttt{fierz\_completeness\_fails\_for\_zero\_dim}` (falsifier). All five names resolve to substantive theorems in `BHLGaugeEmbedding.lean` (Round 3 Lean-side audit verified non-vacuous).
  - Paper-prose dim formula in L381 now reads `dim_fn cfg = fierzBlockSum · (n_d · n_s · n_c · n_g)`, matching the Lean `H_FierzCompletenessExtended` body exactly.

### 2.1 R3 — 🟡 → ✅ CLOSED — `EW.Y_TOP` `llm_verified_notes` drift

- **Status:** **CLOSED**.
- **Evidence:** `provenance.py:1107-1112` — `llm_verified_date` flipped to `2026-04-26`; `llm_verified_notes` rewritten to "PDG 2024 top mass m_t = 172.57 ± 0.29 GeV (single canonical PDG 2024 entry, S. Navas et al., PRD 110, 030001). y_t = √2 · 172.57 / 246.21965 = 0.9912. Updated 2026-04-26 from prior 0.9946 (which used 172.76 as central) to align with EW.M_TOP_GEV = 172.57." Single canonical attribution; references the `EW.M_TOP_GEV` entry; no longer self-contradicts. Cross-source consistency: `constants.py:1815/1825` (172.57 / 0.9912), `provenance.py:1078,1098` (172.57 / 0.9912), `paper_draft.tex:440` (172.57). All agree.

## §6 rewrite audit (Round 4 fresh-context scan)

The Round 3 fix replaced L370–391 of `paper_draft.tex` with new prose discussing the 68-dim block enumeration plus tracked-hypothesis pattern. Audited per the 8 finding classes:

- **Class 1 (citations):** No new bibitems introduced. References block (L358) unchanged (BHL, MTY1989, Hill2025Redux, Cvetic1999). Carryforward 1.1 (Hill2025Redux / Cvetic1999 / MTY1989 cache appends) deferred per task spec.
- **Class 2 (parameter drift):** No new numerical values introduced beyond the dimension constant 68 (formal/Lean-grounded, not an experimental parameter — out of scope for `PARAMETER_PROVENANCE`). Block-sum 2+2+4+4+12+4+12+4+12+12 = 68 verified.
- **Class 3 (placeholder theorems):** All four newly-cited theorem names (`fierzBlockSum_eq_68`, `H_FierzCompletenessExtended`, `fierz_completeness_holds_for_bhl_dim`, `fierz_completeness_fails_for_zero_dim`) were audited substantive in Round 3 §"Substantive-refactor audit" and re-confirmed: decide-proof on 10-term arithmetic sum (non-rfl); parametric over `dim_fn` with non-trivial witness + falsifier pair. No Class 3 BLOCKER.
- **Class 4 (cross-paper):** `grep -rn "fierzBlockSum\|bhlBilinearBasisDim" papers/paper*/paper_draft.tex` (excluding paper20) → no hits. The 68 claim is paper-20-local; no cross-paper contradiction.
- **Class 5 (overclaim):** New §6 prose adds qualifier "corrects an arithmetic typo in the deep-research note" — appropriate disclosure, not an overclaim. The claim "the listed blocks sum to $68$, not the document's stated $66$" is verifiable arithmetic (2+2+4+4+12+4+12+4+12+12 = 68); no overclaim.
- **Class 6 (assumption disclosure):** `H_FierzCompletenessExtended`, `H_HSCovariantBosonisation` are explicitly named in paper prose (L378-381, L387-388) — tracked-hypothesis status is disclosed.
- **Class 7 (count literal drift):** `validate.py --check counts_fresh` PASS; `validate.py --check count_literals` shows paper20 not in warning list (uses macros). `counts.tex` confirms `\totaltheorems{4165}`, `\leanmodules{173}`, `\papercount{21}`, `\sorrycount{0}`, `\axiomcount{1}` — all match the project state in MEMORY.md.
- **Class 8 (production runs):** §6 makes no new MC/numerical-simulation claims; no ProductionRun dependency introduced.

## Carryforward (out of scope per task spec, not a new finding)

- **1.1 R2/R3 carryforward** — Wave 1b registry entries `Hill2025Redux`, `Cvetic1999`, `MiranskyTanabashiYamawaki1989` (and the already-removed `AAA-removed-already`) still `doi_verified: None` in `src/core/citations.py` (`:1521`, `:1622`, `:1502`); the citation-cache WebFetch round is a separate task. Status remains REQUIRED at the project / Gate-1 level, but not flagged as a Round 4 BLOCKER on this paper because the prose-side disclosures (preprint flag for Hill2025Redux at `BHLGaugeEmbedding.lean:44-45`) are already in place.

## QI Candidate

None new. The Round 3 QI ("paper-prose numeric-literal drift detector triggered by Lean `<def>_eq_<NUMBER>` theorem renames") remains the active QI suggestion; Round 3 catching this drift validates the diagnostic value, and Round 4 confirms that the *manual* fix lands cleanly. An automated `validate.py --check paper_lean_numeric_consistency` extension is still recommended for future refactors.
