# 6EE prose-bridged-claim class sweep — log

## Why this exists
Three consecutive adversarial rounds hit the same defect class because remediation patched
the flagged instance and moved on. This sweep enumerates the class rather than the flags.

## Mechanical enumeration (author, regex-based)
Across all four `Control/` modules: **64 flagged instances at 53 sites** —
37 cited-not-called, 23 superlative, 4 numeral. Reviews had named a handful.

## ⚠️ The predicate is a PROXY, and its precision is now measured
Slot 2 adjudicated every flag in `CompositeReadoutCeilings.lean` by hand:

- **superlative predicate: 4 of 4 flags in that file were FALSE POSITIVES.** "only by eye"
  (adverbial), "uses only rational enclosures" (verified true), "differ only in which noise
  budget" (verified true), and a "first" that was positional ("first conjunct"), not a
  ranking claim.
- **cited-not-called: 5 of 6 flags were NOT defects** — forward references from a `def` to a
  theorem below it (a `def` cannot call one), sibling context, explicit analogies
  ("the 6EB analogue of X"), and style comparisons ("the same factoring as X").
- **The predicate also MISSED a real defect**: `relaxation_thermal_ceiling_does_not_bite`
  restated its ceiling's expression by hand instead of calling it. Slot 2 found it by
  extending §4.1's class-level claim to the whole roster — i.e. by sweeping the class, which
  is the thing the regex was standing in for.

So the enumeration is a starting point for adjudication, **not a defect list**. Reporting
"64 found" as though it were 64 defects would be the same overstatement this session
produced repeatedly. The real yield in that module was 13 changes from 51 blocks examined,
two of them theorem restatements rather than prose edits.

## Follow-ups deliberately NOT actioned (out of module scope)
- `docs/roadmaps/Phase6EE_Roadmap.md:79` — describes every does-not-bite half as "stated on
  that ceiling's own bound expression"; now UNDERSTATED for all four after slot 2's work.
- `Phase6EE_Roadmap.md:93` — still records "first cross-layer composite", the superlative
  slot 2 neutralised in the Lean.
- `papers/D12/paper_draft.tex:558` — "the deepest chain in the paper", which the Lean now
  grounds in dependency containment rather than asserting.
- `lean/lean_deps.json` is stale for slot 2's two restatements until ExtractDeps re-runs; a
  cited-means-called re-run will show false MISSes for them until then.
