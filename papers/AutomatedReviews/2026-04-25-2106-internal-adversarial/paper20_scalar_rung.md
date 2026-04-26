---
paper: paper20_scalar_rung
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-25T21:06:00Z
readiness_gates_version: 1
round: 3
prior_round: papers/AutomatedReviews/2026-04-26-1930-internal-adversarial/paper20_scalar_rung.md
scope: Round 2 closure verification + new BLOCKER from incomplete 66→68 refactor propagation
---

# Adversarial Review — paper20_scalar_rung (Round 3)

## Summary

Aggregate verdict: **RED**. Findings: **1 BLOCKER**, **2 REQUIRED**, **0 RECOMMENDED**.

Round 2 REQUIREDs verified closed:
- (2.1) `EW.M_H_GEV` value at 125.20, detail "125.20 ± 0.11", DOI `10.1103/PhysRevD.110.030001` ✓
- (2.2) `EW.M_TOP_GEV` provenance entry added at lines 1077-1096; `EW.Y_TOP` recomputed to 0.9912 (constants.py:1825 + provenance.py:1098 agree); source detail updated to use 172.57 ✓
- (3.1) BHL theorem-prefix count = 23, paper line 471 = 23, matches ✓
- (4.1) Andrianov line removed from `BHLGaugeEmbedding.lean:38-46` References block; Hill 2025 preprint flagged as "FERMILAB-PUB-25-0219-T preprint; …no journal venue at time of writing" ✓

But the Round 2 refactor that bumped `bhlBilinearBasisDim` from 66 → 68 in Lean **did not propagate to the paper prose**, introducing a new BLOCKER (7.1). Two REQUIREDs from Round 2 also remain open as carryforwards (Wave 1b registry `doi_verified` flips + stale Y_TOP `llm_verified_notes`). Gate 5 (LeanProofSubstance) and Gate 1 (CitationIntegrity) reopen as `blocked` until 7.1 is closed.

## Findings

### 7.1 — 🔴 BLOCKER — Paper prose claims `bhlBilinearBasisDim = 66`; Lean theorem certifies value as 68

- **Gate:** LeanProofSubstance (paper-Lean drift) + NumericalFreshness
- **Location:** `papers/paper20_scalar_rung/paper_draft.tex:372` ("the gauge-indexed Clifford basis is $66$-dimensional"); `paper_draft.tex:375` (`bhlBilinearBasisDim = 66 · (n_d · n_s · n_c · n_g)`).
- **Observed:** Paper prose still uses 66; the Round 2 refactor renamed the canonical theorem to `bhlBilinearBasisDim_minimal_eq_68` (`lean/SKEFTHawking/BHLGaugeEmbedding.lean:108-111`) and added an explicit decide-proof witness `fierzBlockSum_eq_68` (line 128, value `2+2+4+4+12+4+12+4+12+12 = 68`). Round 2 report explicitly stated the 66→68 correction was made "coherently across `bhlBilinearBasisDim`, `fierzBlockSum`, `bhlBilinearBasisDim_minimal_eq_68`, and module docstring" — but the paper prose was missed.
- **Evidence:**
  - `grep -n "66\|68" lean/SKEFTHawking/BHLGaugeEmbedding.lean` → 68 in `bhlBilinearBasisDim_minimal_eq_68` (line 108), `fierzBlockSum` def (line 124), `fierzBlockSum_eq_68` (line 128), `fierz_completeness_holds_for_bhl_dim` reduces to 68 via fierzBlockSum (line 150-153), and the module docstring at lines 28-29 ("dimension 68 for one-doublet + one-singlet, one-color, one-generation").
  - `grep -n "66" papers/paper20_scalar_rung/paper_draft.tex` → lines 372, 375.
- **Expected:** Paper prose must agree with the verified Lean theorem. The reader who follows the citation `\texttt{bhlBilinearBasisDim}` to the Lean module would find the proved value is 68, not the prose's 66 — a credibility blow exactly equivalent to the wrong-target citation class. The block-sum decomposition stated in the Lean docstring (scalar-LR(2) + scalar-RL(2) + pseudoscalar(4) + vector-LL singlet(4) + vector-LL triplet(12) + vector-RR singlet(4) + axial-LL triplet(12) + axial-RR singlet(4) + tensor-LR(12) + tensor-RL(12) = 68) is 68, not 66.
- **Fix:** Replace both literals in `paper_draft.tex`:
  - L372: "is $66$-dimensional" → "is $68$-dimensional"
  - L375: `bhlBilinearBasisDim = 66 \cdot ...` → `bhlBilinearBasisDim = 68 \cdot ...`
  Re-run `validate.py --check paper_lean_refs` (or equivalent figure-aware check) to confirm no other site references 66.
- **Cache:** N/A.

### 1.1 — 🟡 REQUIRED — Wave 1b registry entries `Hill2025Redux`, `Cvetic1999` still `doi_verified: None`; `MiranskyTanabashiYamawaki1989` not tracked in cache

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:1521` (Hill2025Redux), `:1622` (Cvetic1999), `:1502` (MiranskyTanabashiYamawaki1989); cache file `docs/citation_verifications.jsonl` (12 records, none for these three bibkeys).
- **Observed:** Round 2 noted this as REQUIRED (1.1) and explicitly recommended (a) appending fresh-fetch verdicts, (b) flipping `doi_verified` to True for Hill2025Redux + Cvetic1999, (c) appending `fetch_failed` for MTY1989. None of these three records have been added; all three registry entries still carry `doi_verified: None` with notes still saying "doi_verified pending — … fetch round."
- **Evidence:**
  - `wc -l docs/citation_verifications.jsonl` → 12 (one schema header + 11 records); last record is `CsikorFodorHeitger1999` for paper22 from 2026-04-25T20:02:21Z; no record for Hill2025Redux, Cvetic1999, or MTY1989.
  - `grep -n "doi_verified" src/core/citations.py | head` shows 30+ entries still at `None`, including Hill2025Redux:1521, Cvetic1999:1622, MTY1989:1502.
- **Expected:** The agent contract requires "Append a new record to `citation_verifications.jsonl` via `scripts/citation_cache.append_record`" for every fresh-fetch event. Round 2 verified the metadata (Hill 2025 = match preprint, Cvetic 1999 = match) but the cache append did not happen. Without `doi_verified: True`, Gate 1's pass criterion ("every registry entry has `doi_verified == True` for the bibkeys this paper uses") fails at submission.
- **Fix:** (a) Append `verdict: match` records for Hill2025Redux and Cvetic1999 with the metadata Round 2 already verified; flip both registry entries to `doi_verified: True`. (b) Append `verdict: fetch_failed` for MTY1989 (DOI 10.1142/S0217732389001210, World Scientific MPLA — host blocks WebFetch). The latter at minimum tracks the unverifiable state rather than letting it silently re-pend across rounds.
- **Cache:** fresh-fetch (Hill, Cvetic — Round 2 already verified); fetch_failed (MTY1989 — independent of paper).

### 2.1 — 🟡 REQUIRED — `EW.Y_TOP` `llm_verified_notes` field is stale; references 172.69/172.76 even though value was recomputed to use 172.57

- **Gate:** ParameterProvenance (internal consistency between `value`, `detail`, `notes`)
- **Location:** `src/core/provenance.py:1097-1114` (`EW.Y_TOP` entry).
- **Observed:** Round 2 fix updated `value: 0.9912`, `source` to "m_t = 172.57 GeV (PDG 2024)", and `detail` to "y_t = √2 m_t/v = √2 · 172.57 / 246.22 ≈ 0.9912" (lines 1098-1105). However, the `llm_verified_notes` field at line 1108 still says **"PDG 2024 top mass m_t = 172.69 ± 0.30 GeV (pole-mass combination). Using 172.76 as central for Yukawa — well within PDG uncertainty"** — describing the prior 172.76-based derivation. `llm_verified_date` is still 2026-04-24 (pre-fix), even though the value/detail/source were updated 2026-04-26. A future audit reading the `notes` will see a self-contradicting record (value 0.9912 attributed to a 172.76-based derivation).
- **Evidence:**
  - `grep -n "172\." src/core/provenance.py` → lines 1082 (M_TOP_GEV value, 172.57); 1086 (M_TOP_GEV notes, 172.57); 1095 (M_TOP_GEV notes, 172.57); 1101 (Y_TOP source, 172.57); 1102 (Y_TOP detail, 172.57); 1105 (Y_TOP detail, 172.57); 1108 (Y_TOP `llm_verified_notes`, 172.69); 1109 (Y_TOP `llm_verified_notes`, 172.76). Lines 1108-1109 are the only remnants of the old derivation.
- **Expected:** Single canonical value across `value`, `detail`, `source`, `llm_verified_notes`. Round 2's value/detail/source fixes left the verification-attestation field describing a different computation than the one now recorded — the provenance entry is internally inconsistent.
- **Fix:** Update `llm_verified_notes` at line 1108-1109 to read e.g. "PDG 2024 top mass m_t = 172.57 ± 0.29 GeV (single canonical world-average; per `EW.M_TOP_GEV`). Yukawa derivation matches the canonical M_TOP_GEV entry as of 2026-04-26."; bump `llm_verified_date` to 2026-04-26 to reflect the Round 2 cross-source consistency fix.
- **Cache:** N/A.

## Round-2 finding closure verification

- (1.1 R2) **Open** — same finding as 1.1 above. Carryforward.
- (2.1 R2) **CLOSED** — `EW.M_H_GEV` provenance now reads 125.20 with PDG 2024 PRD DOI; verified at provenance.py:968-987.
- (2.2 R2) **CLOSED** — `EW.M_TOP_GEV` entry added at provenance.py:1077-1096; `EW.Y_TOP` value/detail/source updated; constants.py:1815 + 1825 agree (M_TOP_GEV=172.57, Y_TOP=0.9912). However, `llm_verified_notes` is stale — reopened as 2.1 above (REQUIRED).
- (3.1 R2) **CLOSED** — strict `^theorem ` count in `BHLGaugeEmbedding.lean` is 23, matching paper line 471. The Round 2 docstring rewording removed the false-positive theorem-prefix at line 16.
- (4.1 R2) **CLOSED** — Andrianov line removed from BHLGaugeEmbedding.lean docstring; current References block is BHL 1990, MTY 1989, Hill 2025 (with preprint disclaimer), Cvetic 1999.
- (4.2 R2) **CLOSED** — Hill 2025 preprint status now flagged at BHLGaugeEmbedding.lean:44-45 ("FERMILAB-PUB-25-0219-T preprint; load-bearing for the bilocal-correction m_H = 125 GeV recovery — no journal venue at time of writing").

## Substantive-refactor audit (Lean side, Round 2 changes)

The Round 2 BHL-side refactor (`fierzBlockSum_eq_68`, `fierz_completeness_holds_for_bhl_dim` witness, `fierz_completeness_fails_for_zero_dim` falsifier, dim count 66 → 68) was inspected for new BLOCKER risks in the **Lean source**. Verdict on the Lean side: **clean**.

- `fierzBlockSum_eq_68` (line 128): proved by `decide`; non-trivial (sum of 10 distinct block dimensions, definitionally not the bare constant 68). Acceptable.
- `H_FierzCompletenessExtended` (line 141-144): now takes `dim_fn : BHLConfig → ℕ` parametrically. The hypothesis becomes `dim_fn cfg = fierzBlockSum * (n_d · n_s · n_c · n_g)` — genuinely non-trivial (universally quantified over the function space).
- `fierz_completeness_holds_for_bhl_dim` (line 150-153): instantiates `dim_fn := bhlBilinearBasisDim`; proved by `unfold + rfl`. The proof is non-vacuous because `bhlBilinearBasisDim` is defined to compute the dimension formula, and the hypothesis ties `dim_fn` to `fierzBlockSum * ...` — concrete witness, not a definitional tautology.
- `fierz_completeness_fails_for_zero_dim` (line 157-160): instantiates `dim_fn := fun _ => 0`; proved by `unfold + decide`. The falsifier is structurally non-trivial — a `dim_fn` that returns 0 fails the hypothesis. Both witness + falsifier together establish `H_FierzCompletenessExtended` as a load-bearing tracked hypothesis (per `feedback_tracked_hypothesis_nontrivial`).
- `bhl_embedding_master` (line 418-426): bundles the witness, HS-bosonisation, and hypercharge-half conjuncts; structurally sound term-mode tuple, no rfl-on-non-trivial.
- `wave1b_open_manifest_consistent` (line 476-488): existential bundle for the open-manifest predicate; constructs explicit `(cfg, φ, b)` witness. Non-trivial.

The Lean module is zero-sorry, zero-axiom, and the new theorems all pass the substantive-proof bar. No new Class 3 (placeholder-theorem) BLOCKERs.

The drift is purely in the **paper prose** — the 66→68 refactor was not propagated to `paper_draft.tex`. That is finding 7.1 above.

## QI Candidate

**Lean refactor → paper prose drift detector.** Round 2's 66→68 refactor in `bhlBilinearBasisDim` correctly cascaded across the Lean module + docstring (per the Round 2 report's explicit "coherently across `bhlBilinearBasisDim`, `fierzBlockSum`, …, and module docstring"), but did not propagate to `paper_draft.tex`. This is the inverse of the Wave 10 sentence-level prose-state pipeline, which detects changes to Lean theorems and prompts a paper-prose review — but it triggers on theorem-name changes, not on numeric-literal changes inside theorem bodies (a `decide`-proved arithmetic fact mutating from 66 to 68 doesn't change any name in the GROUNDED_IN graph). Proposed: extend `validate.py --check paper_lean_refs` to extract numeric literals from theorem names that follow the pattern `<def>_eq_<NUMBER>` and from `def`-body numeric constants whose names are referenced by paper prose, and assert those literals match across Lean + paper. Catches the present case and any future "we changed the constant in Lean" refactor.
