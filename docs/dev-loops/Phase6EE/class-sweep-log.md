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


---

# Item G verdict: DISCOVERY pass, not confirmation

Stated plainly, per the process correction: **B and C were not done properly.** G returned
20 findings (2 BLOCKER, 10 REQUIRED, 8 RECOMMENDED). Every instance the sweep enumerated and
patched checks out; the CLASS did not get swept.

## Why the enumeration could not have worked

1. **It is line-oriented.** BLOCKER 1.1's primary site (`BanachAveraging.lean:94-95`) was
   missed purely because the docstring hard-wraps mid-phrase: "…`‖L s‖ ≤ 1` would" /
   "exclude every rotation…". Any line-oriented sweep over this corpus under-reports.
   **Corrected: unwrap each doc block to one line before matching.**
2. **Its patterns were the wrong family.** All three surviving class defects carry no
   numeral, no superlative, and no unresolvable identifier. The class-level patterns that
   DO reach them are universals, counterfactuals, ordinals and comparatives — measured
   below.
3. **`lean_docstring_refs_resolve` is structurally blind here.** It passes with ZERO
   `Control` findings, because every mis-pointed identifier G found *exists*. A
   name-resolution gate cannot see "cited but not called" or "points at the wrong sibling".

## Corrected sweep (unwrapped blocks, class-level patterns)

| pattern | blocks |
|---|---|
| universal (`every X would…`) | 16 |
| counterfactual (`would survive/exclude/fail…`) | 8 |
| ordinal (`first conjunct`) | 3 |
| comparative (`stronger than`) | 2 |
| identity-claim (`IS`, `is exactly`, `equals`) | 146 |

146 blocks carry at least one, against 53 sites from the line-oriented version. This is
**still a candidate generator, not a defect list** — the identity-claim row in particular
will be mostly legitimate. The lesson from the first sweep stands: adjudicate, don't
blanket-edit.

## Fixed from G

- **BLOCKER 3.1** — `rwaRate`'s docstring said "half the magnitude of `rwaGenerator`" and
  justified it with `H_RWA² = rate²·1`, which says the magnitude IS the rate. The
  justification refuted its own claim in the same sentence, and `DriveCalibration.lean:102`
  is titled "The rate in the calibration formula IS the generator magnitude".
- **BLOCKER 1.1** — the "excludes every rotation" universal is proved for the TRANSVERSE
  family only; `norm_zRotation` gives `‖zRotation θ‖ = 1` at every θ, and the module's own
  headline `diagonal_drive_propagator_bound` instantiates the capstone at `KL = KU = KUr = 1`
  and succeeds. Scoped at all four sites to what is proved.

## Still open from G (not yet actioned)

`kramers_degeneracy_instantiated` is NOT non-degenerate and cannot be at ℂ² (for Θ = J∘K the
commuting algebra is the quaternions; discriminant −4(Im α² + |β|²) ≤ 0 forces a real
eigenvalue to mean H = real scalar). Nondegeneracy needs dim ≥ 4 — real infrastructure, and
the claim that it rules `kramers_degeneracy` out of vacuity should be withdrawn or the
witness rebuilt. Roadmap line 79 overshot (generalises to five witnesses; one calls no
ceiling). Plus 4.1/4.2, 5.1–5.4, 6.1, 7.1/7.2, 8.1/8.2.
