---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T13:40:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# A review document's DECLARED attribution is never read, so bundles report blockers they do not have and hide the ones they do

## Summary

**1 CRITICAL.** `UNATTRIBUTED_OPEN_BLOCKING_CEILING` fired at 55 against 52. The standing
remedy for that leg is the one its own failure message names — *"Re-attribute it or fix it;
never raise this limit."* Running that remedy to the end turned up why the population is 55
in the first place, and it is not that these findings have no bundle.

`extract_review_finding_nodes` resolves a finding's bundle from **two regexes over text**: a
literal `paper<digit>` in the heading/body/filename, and the filename stem matched against
the bundle-code roster. A review document that states its target in **frontmatter** — `paper:
note_rt_ch_bounds`, `paper: paper20_scalar_rung`, `scope: … bundle D12 authorized` — is
parsed by neither, so the declaration is inert. The convention exists (`bundle_target:` is
written by every recent review) and nothing reads it for attribution.

⚠️ **This is a FALSE GREEN of the class this subsystem has been repaired for five times.**
Measured 2026-08-15 against `_readiness_aggregate()` — the decider the check actually
reads, not `meta['inferred_bundle']`: **29 open blocking findings** whose own documents name
a target that resolves through `PAPER_DRAFT_MAPPING.md` reach no bundle. D12 reports 5 open
blockers and carries 24. F reports 0 and carries 10. Those bundles' readiness verdicts,
heatmap rows and `blockers_open` are computed over a corpus with the findings removed.

The two ratchet legs are complements over one id set, so the whole error is one displacement:

| | leg 1 (per-bundle occurrences) | leg 2 (unattributed findings) |
|---|---|---|
| at HEAD | 6 | 55 |
| with declared attribution honoured | 49 | 26 |

29 findings × their mapped bundles = 43 occurrences; 6 + 43 = 49 and 55 − 29 = 26. Every
number reconciles, which is the point: this is a displacement, not a discovery of new debt.

⚠️ **The fix cannot land without an operator call on leg 1, which is why it is filed rather
than shipped.** `docs/required_open_ceilings.json` was re-frozen to the live population of 6
in `7a63e17f` (2026-08-15 11:41, HEAD) with every bundle outside D12/L1 at zero. Honouring
the declarations moves 43 occurrences into that leg, so leg 1 goes red across nine bundles
the same day it was frozen. The file's own precedent covers this — *"a broader predicate gets
its own baseline, frozen at the live count on the day it was introduced"* — and reaching for
that precedent unprompted, hours after the freeze, is exactly the move its sibling docstring
warns is an abuse. **The displacement is measured and reconciled above; which leg absorbs it
is the operator's call, not this document's.**

⚠️ **This document adds one open blocking finding to leg 2 (55 → 56).** Filing it at a
severity that fits the ratchet would be tuning severity to a number, which this corpus has
already ruled out once (`2026-08-13-statement-substance/I1.md`). The number is worse and
correct.

---

### 1.1 — 🔴 CRITICAL — declared attribution is inert, so 29 open blocking findings are invisible to the bundles that own them

- **Severity:** critical
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -m pytest tests/test_declared_attribution.py -q`
  *What it asserts:* that a finding whose review document declares `paper: note_rt_ch_bounds`
  in frontmatter is reached by `aggregate_by_bundle` for D4 and F. Exits 1 at HEAD (no such
  test, and the finding is not reached).
- **Gate:** FixPropagation
- **Location:** `scripts/build_graph.py` (`_infer_paper_key_from_text`,
  `_infer_bundle_from_text`, `extract_review_finding_nodes` — the two regexes are the whole
  attribution channel), `scripts/bundle_readiness.py:151` (`load_findings_by_paper`, which
  partitions on the raw inferred key)
- **Observed:** Three independent sub-defects, one channel.
  1. **Frontmatter is never opened.** `extract_review_finding_nodes` reads the document body
     for severity, lane, gate, location and verify, and reads the frontmatter for none of
     them. `bundle_target:` appears in the frontmatter of every recent review document and
     has no reader anywhere in `scripts/`.
  2. **A short paper key is normalised in the graph layer and nowhere else.**
     `extract_flags_edges` already resolves `paper10` → `paper:paper10_modular_generation` by
     unique-prefix match (added 2026-05-14, with an explicit ambiguity guard).
     `load_findings_by_paper` partitions on the raw `paper10`, which is not a
     `PAPER_DRAFT_MAPPING` key, so the same finding that gets a correct FLAGS edge reaches no
     bundle. The two layers disagree about the same finding.
  3. **Substrate-phase reviews name their bundle in prose only.**
     `phase6EA_substrate.md` declares `scope: substrate phase, no paper target (bundle D12
     authorized, no on-disk draft)`; the mapping carries `_phase6EA_lean_only → D12` and
     `_phase6EE_lean_only → D12`. Nineteen of the 29 are these.
- **Evidence:** Measured 2026-08-15 at HEAD `7a63e17f`, by rebuilding
  `load_findings_by_paper` with declared attribution honoured and re-running
  `aggregate_by_bundle` unchanged. Each row is `count | review stem | severity | resolved
  mapping key → bundles | how it resolved`:

  | n | review | sev | resolved key → bundles | channel |
  |---|---|---|---|---|
  | 11 | `phase6EE_control` | major | `_phase6EE_lean_only` → D12 | frontmatter `scope:` + mapping |
  | 5 | `phase6EA_substrate` | major | `_phase6EA_lean_only` → D12 | frontmatter `scope:` + mapping |
  | 3 | `phase6EA_substrate_round2` | major | `_phase6EA_lean_only` → D12 | frontmatter `scope:` + mapping |
  | 3 | `note_rt_ch_bounds` | 1 critical, 2 major | `note_rt_ch_bounds` → D4, F | frontmatter `paper:` (exact mapping key) |
  | 1 | `Paper 10 Deep Review — …` | critical | `paper10_modular_generation` → L2, D2, F | unique-prefix on `paper10` |
  | 1 | `CitationReview-01` §9 | major | `paper10_modular_generation` → L2, D2, F | unique-prefix on `paper10` |
  | 1 | `CitationReview-01` §13 | major | `paper1_first_order` → D1, F | unique-prefix on `paper1` |
  | 1 | `CitationReview-01` §14 | major | `paper12_polariton` → D1, E1, F | unique-prefix on `paper12` |
  | 1 | `CitationReview-01` §15 | major | `paper15_methodology` → I1, F | unique-prefix on `paper15` |
  | 1 | `CitationReview-01` §8 | major | `paper9_sm_anomaly_drinfeld` → D2, D4, F | unique-prefix on `paper9` |
  | 1 | `paper20_scalar_rung_REINVOCATION` | major | `paper20_scalar_rung` → D3, F | frontmatter `paper:` (exact mapping key) |

  Resulting per-bundle blocking occurrences: D12 24, F 10, D4 4, D2 3, D1 2, L2 2, D3 1,
  E1 1, I1 1, L1 1 — against frozen ceilings of D12 5, L1 1, all others 0.
- **Expected:** A document that DECLARES its target attributes by that declaration, and a
  regex is the fallback — the same precedence this extractor already applies to severity,
  where a `- **Severity:**` line is authoritative and glyph inference is the fallback for the
  historical corpus. A declaration that no consumer reads is worse than no convention, because
  it reads as attribution to every human who opens the file.
- **Fix:** One channel, three layers, in dependency order.
  1. Parse the frontmatter in `extract_review_finding_nodes` and record
     `declared_paper` / `declared_bundle` in `meta`, **verbatim and unvalidated**.
  2. Resolve, in `load_findings_by_paper`, in this precedence: declared key that is an exact
     `PAPER_DRAFT_MAPPING` key → declared bundle code in the roster → filename stem that is an
     exact mapping key → unique-prefix normalisation of the short inferred key (reuse
     `extract_flags_edges`' resolver rather than writing a third one) → existing inference.
     **Exactly-one match or nothing:** an ambiguous or unrecognised declaration must leave the
     finding unattributed, so a typo cannot invent a bundle. `paper: infra`, `paper: process`
     and any key outside the mapping resolve to nothing, by construction.
  3. Re-derive BOTH ratchets in the commit that lands it, marked as a re-derivation with the
     reconciling arithmetic, and regenerate `papers/*/bundle_metadata.json` — the bundle
     readiness verdicts change, and `bundle_metadata_matches_graph` will fail until they do.
  ⚠️ **Do not "fix" this by narrowing leg 2's predicate to exclude infra-lane findings.** The
  four `bundle_target: infra` findings that pushed the leg over its ceiling are correctly
  unattributable, and excluding them would be reclassification standing in for remediation —
  and it would leave all 29 of these still hidden.
- **Related:** the same false-green class as D11 round-5 BLOCKER 4.1 (bundle-era findings
  dropped by `load_findings_by_paper`) and D12 round-4 BLOCKER 8.1 (two-digit bundle codes
  unmatchable). Both were repairs to this same two-regex channel; this is the third, and the
  reason it recurs is that the channel infers instead of reading what the document states.
- **Cache:** N/A.
