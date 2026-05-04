---
bundle: F
paper: F_flagship_review
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-05-04T22:30:00Z
readiness_gates_version: 1
round: 2
verdict: GREEN
blockers_open: 0
findings_total: 5
findings_blocker: 0
findings_required: 1
findings_recommended: 4
---

# Adversarial Review — F_flagship_review (round 2)

## Summary

Round 2 reconciliation pass for bundle F (Tier-0 flagship). Round 1 returned
AMBER with 1 BLOCKER + 2 REQUIRED + 5 RECOMMENDED. Round-2 fixes were
applied in commit `747bf65`. This pass verifies closure of the BLOCKER and
two REQUIRED items; remaining advisories carry forward as documented in the
parent review thread.

**Verdict: GREEN.** All round-1 BLOCKERs closed; one REQUIRED item closed;
the second REQUIRED carries forward as a known D3-bound advisory; the five
RECOMMENDED items either close or carry forward as non-load-bearing.

## Round-1 finding closure verification

### BLOCKER 1.1 — LaTeX undefined control sequences  →  CLOSED

**Round-1 issue.** F invoked `\totalsubstantivetheorems`, `\totalmodules`,
`\axioms`, `\sorries`, but `docs/counts.tex` exposes only
`\substantivetheorems`, `\leanmodules`, `\axiomcount`, `\sorrycount`. The
mismatched macros silently rendered as blanks in the compiled PDF
(8 sites total).

**Round-2 evidence.**

- `grep -ic "undefined control sequence" papers/F/paper_draft.log` → `0`
  (was non-zero in round 1; log is 2004 lines so the absence is meaningful).
- `grep -nE "totalsubstantivetheorems|totalmodules|\\\\axioms|\\\\sorries" papers/F/paper_draft.tex`
  → no matches across all 8 prior sites.
- `papers/F/paper_draft.pdf` exists at 476 KB, dated 2026-05-04 11:46 (post-commit).

**Status: CLOSED.** The fix is mechanical (sed replacement) and the absence
of any residual macro reference plus the clean log confirms closure. Counts
now render via the canonical `\substantivetheorems` / `\leanmodules` /
`\axiomcount` / `\sorrycount` bindings from `docs/counts.tex`.

### REQUIRED 1.3 — Figure-eight knot in-flight drift  →  CLOSED

**Round-1 issue.** F §7.2 and §10 register both flagged the figure-eight
knot invariant as "in flight" / "tracked hypothesis", but
`lean/SKEFTHawking/FigureEightKnot.lean` already shipped
`figure_eight_trace_neg_one` + `figure_eight_normalized` at zero sorry via
`native_decide`. Misrepresenting closed Lean content as open inflates the
open-register count and weakens the bundle's first-formalisation claims.

**Round-2 evidence.**

- §7.2 (paper_draft.tex lines 1220-1224) now reads "ships closed at zero
  `sorry` via `FigureEightKnot.figure_eight_trace_neg_one` and
  `figure_eight_normalized` (`native_decide`)." — affirmative-closure
  framing, no "in flight" / "tracked hypothesis" verbiage in scope.
- §10 register (lines 1782-1787) now presents the WRT-surgery entry as
  partial coverage on $S^3$ via Lickorish surgery, with both trefoil and
  figure-eight invariants shipped closed via
  `Ising_MTC.trefoil_eq_neg_sqrt2` and
  `FigureEightKnot.figure_eight_trace_neg_one`. The earlier separate
  figure-eight register entry has been merged.
- Cross-check `lean/lean_deps.json`: `SKEFTHawking.FigureEightKnot.Mat2`
  inductive + `F_matrix` def + `F_sq_identity` theorem (with
  `_native_decide.ax` axiom dependency) all present.
- `grep "figure-eight"` returns 4 hits across two scopes only (§7.2 and §10),
  none with "in flight" framing. The remaining "in flight" matches in the
  document (`wen_adw_factor_6000` D3 carry-forward; `DoublonGate.lean`
  adiabatic-drag; tracked-hypothesis register §10) are correct and unrelated.

**Status: CLOSED.** Closed-Lean content is now reported as closed; the
open-register count and the Phase 7c.4 "first machine-checked" claims
correctly distinguish figure-eight (closed) from Doublon-SWAP adiabatic-drag
(in-flight) and `wen_adw_factor_6000` (D3 carry-forward).

## Round-1 advisory disposition (carry-forward)

### REQUIRED 1.2 — `wen_adw_factor_6000` in-flight  →  CARRY-FORWARD

This is a D3-bound concern: F's representation of `wen_adw_factor_6000` as
in-flight at line 910 is consistent with D3 (paper3) which carries that
lemma as the open obligation. The flagship correctly inherits D3's
in-flight status; closure occurs via D3 reviewer triple, not F. No F-side
action required.

### RECOMMENDED 1.1 — 92%-reuse cross-bundle precision  →  CARRY-FORWARD

Cross-bundle reuse arithmetic depends on D1 first-pass content and is
documented as a known measurement-precision item; not load-bearing for the
flagship verdict. F can be tightened in a future minor pass after D1
Stage-13 close.

### RECOMMENDED 1.3 — KaulMajumdar2000 + Wen2003 registry hygiene  →  CARRY-FORWARD

Citation-registry hygiene; not blocking. Can fold into a global registry
sweep when scheduled.

### RECOMMENDED 1.4 — §10.5 tracked-hypothesis identifier-key disclosure  →  CARRY-FORWARD

Disclosure-completeness improvement; the existing register is sufficient
for the flagship's purpose of advertising the open-under-tracked-hypothesis
boundary as a substrate prediction.

### RECOMMENDED 1.5 — (per round-1 carry-forward note)  →  CARRY-FORWARD

Already noted in the round-1 dispatch as a non-load-bearing carry-forward.

## New observations (round 2 only)

### NEW RECOMMENDED 2.1 — Hedging consistency check (RECOMMENDED 1.2 follow-through)

Round 1 noted that the §10 Track-B closure entry was retitled with
"to our knowledge". I verified the hedging is now applied consistently:
nine "to our knowledge" / "To our knowledge" sites across the abstract
(line 363), §1.4-class intro (line 386), §1-§2 framing (lines 1091, 1143),
§8.4-class Phase 6e cross-bridge (line 1409), §8.4 first-machine-checked
package claim (line 1568), §10 register entry (line 1700), and §10 Sakharov
comparison (line 1962). The hedging is uniformly applied to first-of-its-kind
claims and is not over-hedging on results that the project has independently
verified.

The earlier round-1 RECOMMENDED 1.2 finding is therefore CLOSED via the
fix-set in `747bf65`.

## Verdict rationale

- 1 BLOCKER (LaTeX macros) → CLOSED with deterministic grep + log evidence.
- 1 REQUIRED (figure-eight in-flight drift) → CLOSED with confirmed
  affirmative-closure language in both §7.2 and §10 register and verified
  Lean deps.
- 1 REQUIRED (`wen_adw_factor_6000`) → CARRY-FORWARD as D3-bound; not
  blocking for F.
- 5 RECOMMENDED → mix of CLOSED (1.2 hedging) and CARRY-FORWARD; none
  load-bearing.

Bundle F flagship is now reviewer-triple-closed at GREEN. Heatmap can
advance F from RED → GREEN; bundle count rises to 11 of 13 reviewer-triple-
closed (D1 + D2 + D5 + I1 + I2 + L1 + L2 + L3 + E1 + E2 + F).

D3 + D4 remain pending Stage-13 close (D4 Stage-10 r2 GREEN; D3 Stage-10 r2
in flight at session-end per memory `project_phase7c_d3_d4_first_pass.md`).

## Findings summary

| Severity     | Open | Closed (round 2) | Carry-forward |
|--------------|-----:|-----------------:|--------------:|
| BLOCKER      |    0 |                1 |             0 |
| REQUIRED     |    0 |                1 |             1 |
| RECOMMENDED  |    0 |                1 |             4 |
| **Total**    |    0 |                3 |             5 |

## Suggested next actions

1. Update `docs/BUNDLE_READINESS_HEATMAP.md` to reflect F GREEN at Stage 13.
2. Run `scripts/bundle_readiness.py --heatmap` and refresh the
   provenance dashboard's bundle view.
3. Schedule the carry-forward RECOMMENDED items into a single global hygiene
   sweep (citation registry + tracked-hypothesis identifier disclosure)
   after D3 + D4 close.
4. After D3 close, revisit RECOMMENDED 1.1 (92%-reuse precision) and
   REQUIRED 1.2 (`wen_adw_factor_6000`) F-side updates as a minor revision.
