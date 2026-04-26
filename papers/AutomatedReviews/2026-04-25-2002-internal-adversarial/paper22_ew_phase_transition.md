---
paper: paper22_ew_phase_transition
reviewer: adversarial-reviewer
model: claude-opus-4-7[1m]
review_date: 2026-04-25T20:02:00Z
readiness_gates_version: 1
prior_round: 2026-04-26-1923-internal-adversarial
round: 2
---

# Adversarial Review — paper22_ew_phase_transition (Round 2)

## Summary

Round 2 closes 3 of 4 Round 1 BLOCKERs (`CitationIntegrity` 1.1 via
new `CsikorFodorHeitger1999` bibkey + cache verification; `LeanProofSubstance`
3.1 via the `transition_order_unfolds_to_cubic_sign` rename + the two new
substantive theorems `first_order_iff_positive_latent_heat` and
`latentHeat_zero_iff_crossover` whose bodies use `linarith` /
`by_contra` / `pow_eq_zero_iff`-style reasoning rather than `rfl`;
`NumericalFreshness` 9.1 via fresh `counts.tex` regen). However a NEW
BLOCKER surfaced: the paper draft at §2.2 (lines 140–143) still
references the OLD theorem name `transition_order_from_microscopic_parameters`
and still calls it "the master correctness-push theorem" — so the
Round 1 fix landed in Lean but the corresponding paper-side update was
not propagated. This is a Gate 5 + Gate 11 failure (FixPropagation).
The Round 1 NarrativeGrounding BLOCKER 7.1 is **partially closed** —
abstract is reframed (lines 41–55 acknowledge the LO-vs-physical
divergence) but the introduction at line 83 still says "the SM
transition is unambiguously a crossover" without the strict-LO caveat
applied; same overclaim survives in §3 line 188. Round 1 REQUIRED
findings (1.2, 3.2, 6.1, 7.2) were largely NOT addressed; 7.2 is
recurrent unchanged. Round 1 RECOMMENDED findings are unchanged.

**Aggregate verdict: RED.** 1 new BLOCKER (Gate 5 + 11 propagation),
1 partially-closed BLOCKER from Round 1 (Gate 7), plus the Round 1
REQUIREDs that were not addressed. Counts: 1 new BLOCKER, 1 partial-BLOCKER,
4 REQUIRED, 2 RECOMMENDED carried forward.

Working finding classes 1 through 8 in order. Citation cache stats:
prior cache had 0 records for CsikorFodorHeitger1999 / KLRS1996 /
ButtazzoEtAl2013 / ShaposhnikovWetterich2010; this round added 1 fresh
verification (CsikorFodorHeitger1999 → match).

## Findings

### 1.1 — 🟢 CLOSED — KLRS96 misattribution (Round 1 BLOCKER)

- **Gate:** CitationIntegrity
- **Round 1 status:** BLOCKER — paper attributed m_H ≈ 72 GeV to KLRS96
- **Round 2 status:** **closed**
- **Evidence of closure:** New `\bibitem{CsikorFodorHeitger1999}` at
  `paper_draft.tex:371–375`; abstract (lines 49–52) now correctly cites
  CFH1999 for 72.4 ± 1.7 GeV, KLRS96 for the broader 70–95 GeV range.
  Intro (lines 80–82) and §3 (lines 183–185) similarly split the
  attribution. CITATION_REGISTRY entry exists at `src/core/citations.py:1539–1556`.
- **Cache verification:** fresh-fetch via `arxiv.org/abs/hep-ph/9809291`
  returned title "Endpoint of the hot electroweak phase transition",
  authors "F. Csikor, Z. Fodor, J. Heitger", journal "Phys.Rev.Lett. 82
  (1999) 21–24", DOI `10.1103/PhysRevLett.82.21` — all match the
  registry. Verdict: **match**. Record appended to
  `docs/citation_verifications.jsonl`.

### 1.2 — 🟡 REQUIRED — Four bibkeys carry `doi_verified: None` (Round 1 carryforward + 1 new)

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:1539, 1557, 1576, 1594`
- **Observed:** `CsikorFodorHeitger1999`, `KLRS1996`, `ButtazzoEtAl2013`,
  and `ShaposhnikovWetterich2010` all flagged `doi_verified: None`. The
  new CFH1999 entry inherits the unverified-DOI status of the Round 1
  trio.
- **Evidence:** arXiv-side verification is now `match` for CFH1999
  (round-2 cache record) and was already `match` for the other three
  per Round 1 (per the Round 1 finding 1.2 evidence). DOI side remains
  un-fetched for all four.
- **Expected:** Run CrossRef live-resolution sweep on all four DOIs and
  flip `doi_verified: None → True` if titles match. Per Gate 1
  pass-criteria, submission requires `doi_verified == True`.
- **Fix:** `uv run python scripts/citation_cache.py --resolve
  CsikorFodorHeitger1999 KLRS1996 ButtazzoEtAl2013 ShaposhnikovWetterich2010`.
- **Cache:** arXiv side fresh-fetch (this round for CFH1999); DOI side
  un-fetched.

### 3.1 — 🟢 CLOSED — `transition_order_from_microscopic_parameters` Lean substance (Round 1 BLOCKER)

- **Gate:** LeanProofSubstance
- **Round 1 status:** BLOCKER — theorem body was `unfold; rfl ∧ rfl`
  framed as "master correctness-push"
- **Round 2 status:** **Lean side closed**, paper side **NOT closed**
  (see new finding 3.4 + 11.1)
- **Evidence (Lean side):** `lean/SKEFTHawking/EWPhaseTransition.lean:260–265`
  renames the theorem to `transition_order_unfolds_to_cubic_sign` and
  the docstring (lines 254–259) explicitly downgrades it to "definitional
  unfolding" with no mathematical content beyond unfolding. Two NEW
  substantive theorems land:
    - `first_order_iff_positive_latent_heat` (lines 337–348): proof body
      uses `refine ⟨first_order_has_positive_latent_heat p, ?_⟩`,
      `by_contra`, `push_neg`, `le_antisymm` against `cubic_coeff_nonneg`,
      `crossover_has_zero_latent_heat`, `linarith` — non-trivial
      reasoning, the converse direction is load-bearing on
      `cubic_coeff_nonneg`.
    - `latentHeat_zero_iff_crossover` (lines 355–365): mirror
      biconditional with similar `by_contra` + `lt_of_le_of_ne`
      + `first_order_has_positive_latent_heat` chain.
  Both compile clean (`lake build SKEFTHawking.EWPhaseTransition` →
  `Build completed successfully (8270 jobs)`; one deprecation warning on
  `push_neg` only).
- **Theorem count:** 21 in EWPhaseTransition.lean — matches paper
  prose at line 34 ("$21$ theorems") and §6 table at line 310.

### 3.2 — 🟢 CLOSED — `ew_latent_heat` docstring referenced nonexistent Lean theorem (Round 1 REQUIRED)

- **Gate:** LeanProofSubstance
- **Round 1 status:** REQUIRED — `formulas.py:7013` cited
  `latentHeat_zero_iff_crossover` which did not exist in Lean
- **Round 2 status:** **closed**
- **Evidence:** `latentHeat_zero_iff_crossover` now exists in
  `lean/SKEFTHawking/EWPhaseTransition.lean:355–365`; `formulas.py:7013`
  reference is now valid.

### 3.3 — 🔵 RECOMMENDED — `wave3_open_manifest_consistent` arm trivialised by `cubic_coeff_nonneg` (Round 1 carryforward)

- **Gate:** LeanProofSubstance
- **Status unchanged** — disjunction `IsFirstOrderEW p ∨ IsCrossoverEW p`
  remains structurally satisfied for any `EWFiniteTParams` inhabitant
  thanks to `cubic_coeff_nonneg`. Round 1 finding stands; advisory only.

### 3.4 — 🔴 BLOCKER — Paper §2.2 still references the OLD/renamed Lean theorem name + retains "master correctness-push" framing

- **Gate:** LeanProofSubstance + FixPropagation
- **Location:** `papers/paper22_ew_phase_transition/paper_draft.tex:140–143`
- **Observed:** Paper says verbatim:
  ```
  The master correctness-push theorem
  \texttt{transition\_order\_from\_microscopic\_parameters} reduces the
  predicate to the explicit cubic-coefficient inequality, providing the
  biconditional reduction from microscopic data to phase order.
  ```
  But (a) the theorem `transition_order_from_microscopic_parameters` no
  longer exists — `lean/SKEFTHawking/EWPhaseTransition.lean:260` declares
  it under the new name `transition_order_unfolds_to_cubic_sign`. (b) The
  Lean docstring at line 254–259 explicitly says this theorem "adds no
  mathematical content beyond unfolding the definitions" and that the
  substantive correctness-push lives in `first_order_iff_positive_latent_heat`.
  Paper continues to call it "the master correctness-push theorem".
- **Evidence:**
  ```
  $ grep -n "transition_order_from_microscopic_parameters\\|transition_order_unfolds_to_cubic_sign" lean/SKEFTHawking/EWPhaseTransition.lean
  260:theorem transition_order_unfolds_to_cubic_sign (p : EWFiniteTParams) :
  $ grep -n "transition_order_from_microscopic_parameters\\|transition_order_unfolds_to_cubic_sign" papers/paper22_ew_phase_transition/paper_draft.tex
  141:    \\texttt{transition\\_order\\_from\\_microscopic\\_parameters} reduces the
  ```
- **Expected:** Either (a) update paper §2.2 to cite
  `transition_order_unfolds_to_cubic_sign` and reframe as a "definitional
  unfolding lemma" (matching the Lean docstring); also add a sentence
  citing `first_order_iff_positive_latent_heat` as the actual substantive
  microscopic→macroscopic biconditional, or (b) revert the Lean rename.
  (a) is the correct fix per the Round 1 closure plan.
- **Fix:** Replace lines 140–143 with prose that names
  `transition_order_unfolds_to_cubic_sign` as a definitional reduction
  AND cites `first_order_iff_positive_latent_heat` and
  `latentHeat_zero_iff_crossover` as the substantive
  microscopic→macroscopic biconditionals via the latent-heat order
  parameter. This is also the Gate-11 propagation issue: the Lean fix
  did not propagate to the paper draft.

### 4.1 — 🔵 RECOMMENDED — Cross-paper bibkey check (Round 1 carryforward)

- **Gate:** CrossPaperConsistency
- **Status unchanged** — the four EWPT-only bibkeys remain unique to paper 22.
- **Evidence:** `grep -l "CsikorFodorHeitger1999\\|KLRS1996\\|ButtazzoEtAl2013\\|ShaposhnikovWetterich2010" papers/paper*_*/paper_draft.tex` returns paper22 only (post-rename of file structure unchanged).

### 6.1 — 🟡 REQUIRED — `cubic_coeff_nonneg` structure constraint not disclosed (Round 1 carryforward)

- **Gate:** AssumptionDisclosure
- **Location:** `lean/SKEFTHawking/EWPhaseTransition.lean:81` vs `paper_draft.tex` §2 / §3
- **Observed:** This finding gains importance in Round 2 because the new
  substantive theorems `first_order_iff_positive_latent_heat` and
  `latentHeat_zero_iff_crossover` *both* use `p.cubic_coeff_nonneg` as
  load-bearing in the converse directions (lines 345 and 361
  respectively — `le_antisymm h_E_npos p.cubic_coeff_nonneg` and
  `lt_of_le_of_ne p.cubic_coeff_nonneg (Ne.symm h_E_ne)`). The
  hypothesis is now load-bearing for the round-2 substantive theorems,
  not just for the disjointness/partition. Paper still does not mention
  it; absence is now a stronger Gate 6 issue.
- **Evidence:** `grep -n "cubic_coeff_nonneg\\|nonnegative.*cubic\\|E.*≥.*0\\|E\\\\geq" papers/paper22_ew_phase_transition/paper_draft.tex` returns zero matches.
- **Expected:** Add one sentence in §2 noting E ≥ 0 is assumed
  (physically motivated by HTL gauge-boson contributions); flag the
  hypothesis inline when introducing the new biconditionals
  (paper does not yet cite the new biconditionals at all — see 3.4).
- **Fix:** Two-sentence addition to §2 introducing E ≥ 0 + one phrase
  in §2.3 (latent-heat) explaining that the converse "L = 0 → crossover"
  needs E ≥ 0.

### 7.1 — 🟡 PARTIALLY CLOSED — Abstract / intro / §3 SM-verdict reframing (Round 1 BLOCKER)

- **Gate:** NarrativeGrounding
- **Round 1 status:** BLOCKER — abstract said "SM is a crossover at LO"
  contradicting `sm_benchmark_is_first_order` at LO.
- **Round 2 status:** **abstract closed**, **intro and §3 NOT fully closed**.
- **Evidence (closed):** `paper_draft.tex:41–55` reframes the abstract to
  acknowledge the strict-LO Lean prediction (first-order) vs the physical
  lattice verdict (crossover) divergence at the literature-documented
  m_H ≈ 72 GeV boundary.
- **Evidence (NOT closed):**
  - **Intro line 83:** "with the PDG observed $m_H = 125.20$ GeV, the
    SM transition is unambiguously a crossover, and EW baryogenesis in
    the SM is excluded." This sentence is unconditional — it makes the
    SM-as-crossover assertion without the strict-LO-vs-resummed caveat
    the abstract now carries. Reader who skipped the abstract sees only
    the unconditional crossover claim.
  - **§3 line 188:** "the physical SM is unambiguously a crossover; the
    LO prediction diverges from the resummed lattice verdict at the
    documented threshold." Better than the intro but still asserts
    "unambiguously a crossover" without flagging that this is *not*
    Lean-formalized in this module.
- **Expected:** Add the same caveat the abstract carries to both other
  locations: the "unambiguously a crossover" verdict is *external*
  (KLRS96 + CFH1999) and the Lean module's strict-LO theorem
  (`sm_benchmark_is_first_order`) predicts the opposite at LO; the
  divergence is the literature-documented loop-corrections gap.
- **Fix:** Two short rewrites in `paper_draft.tex` lines 82–84 and
  186–192 to mirror the abstract's hedging.
- **Severity rationale:** Downgraded from BLOCKER to REQUIRED-equivalent
  because the abstract is closed and a careful reader gets the correct
  framing; but the intro's unconditional claim remains a Gate-7
  contradiction with the shipped Lean theorem.

### 7.2 — 🟡 REQUIRED — "load-bearing input to … Phase 6c.2" forward-reference (Round 1 carryforward, NOT addressed)

- **Gate:** NarrativeGrounding
- **Status unchanged** — paper still uses "the load-bearing input to
  the future Phase 6c.2" at lines 59 and 238. No `Phase6c*.lean` artifact
  exists.
- **Fix unchanged from Round 1:** Replace "is the load-bearing input to"
  with "is intended to feed the future" at both sites.

### 9.1 — 🟢 CLOSED — counts.tex stale (Round 1 BLOCKER)

- **Gate:** NumericalFreshness
- **Round 2 status:** **closed**
- **Evidence:** `docs/counts.tex:1` header timestamp is
  `2026-04-25T15:00:10` (post-paper-22 ingestion); `\papercount{21}`,
  `\totaltheorems{4118}`, `\substantivetheorems{4007}`, `\leanmodules{172}`
  all match the post-Wave-3 state.
  `uv run python scripts/validate.py --check counts_fresh` exits 0:
  ```
  ✓ summary — theorems=4118 (substantive=4007, placeholder=111) | modules=172
            | sorry=0 | papers=21 | aristotle_proved=322
  Overall: 1/1 checks passed (1 warning)
  ```

### 9.2 — 🔵 RECOMMENDED — T_c rounding 139.13 vs 139.15 (Round 1 carryforward)

- **Gate:** NumericalFreshness
- **Status unchanged** — paper still says T_c ≈ 139.13 at lines 128 and
  172; canonical value is 139.1535 (rounds to 139.15). Fix unchanged.

## Round 2 net delta

- **Closed by Round 2 fixes:** 1.1, 3.1 (Lean-side), 3.2, 9.1
- **Partially closed:** 7.1 (abstract closed; intro/§3 still carry the
  unconditional claim)
- **Not addressed (Round 1 REQUIREDs / RECOMMENDEDs):** 1.2 (still
  unverified DOIs), 3.3, 6.1, 7.2, 9.2
- **Newly introduced by Round 2 fixes:** 3.4 — paper-side did not
  propagate the Lean theorem rename; references stale name
  `transition_order_from_microscopic_parameters` and retains "master
  correctness-push" framing that the Lean docstring explicitly removes.

## QI Candidate

- Pattern reproduced from Round 1: a Lean-side rename / docstring
  downgrade did not propagate to paper prose. Recommend adding a
  `validate.py --check paper_lean_refs` cross-check that fails when
  `\\texttt{theorem_name}` in any paper does not match a declared name
  in the Lean library (or matches a `PlaceholderMarker` without a
  paper-side hedge). The Round 1 strengthening pass landed but the
  retrofit to paper 22's §2.2 was missed; an automated check would
  prevent this class of drift.
