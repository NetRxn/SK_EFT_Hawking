# Closure probe — settling §7 and §8 of the intake design

**Date:** 2026-08-06 · **Branch:** `infra/adr-009-validation-modularization`
**Input:** `docs/architecture/.working-docs/PUBLICATION_INTAKE_DESIGN.md` §7 (four open
questions) and §8 (the cheapest next step)
**Probe scripts:** scratchpad only — these are measurements, not instruments. Anything that
survives into a gate gets rebuilt as a registered check with its own tests.

Every number below seeds closures from what the **existing drafts already cite** — the
verbatim spans `_prose_verbatim_tokens` extracts, resolved by the same machinery
`prose_theorem_reference_coverage` uses. No apexes have been declared, so this is a
**lower bound** on what a bundle would claim once they are.

---

## Cross-check first — the probe reproduces an independent measurement exactly

M4(a) measured **D6 ∩ D9 = 78 theorems** by a different route, and R6 reproduced it. This
probe's directly-referenced-theorem intersection for the same pair is **78**. The
resolution path is therefore sound before any conclusion rests on it.

⚠️ **Units, because this pair has already caused one withdrawal (§C7).** Three different
numbers describe D6 ∩ D9 and they are not interchangeable:

| unit | value |
|---|---|
| directly-referenced theorems (M4a's unit) | **78** |
| closure declarations | 662 |
| closure modules | 70 |

Always state which.

---

## §8 — does closure shape separate letters from deep papers?

**Partly, and the exceptions are the finding.** Seeded from prose references:

| bundle | thm seeds | closure decls | modules | max depth |
|---|---|---|---|---|
| **L1** | 10 | 18 | 1 | 1 |
| **L3** | 13 | 54 | 5 | 3 |
| **L2** | 15 | **408** | **39** | **14** |
| D7 | 11 | 81 | 6 | 3 |
| D1 | 54 | 260 | 18 | 3 |
| D10 | 34 | 312 | 17 | 13 |
| D6 | 147 | 736 | 74 | 8 |
| D9 | 150 | 1 300 | 142 | 18 |
| **D8** | 35 | **2 292** | **289** | **24** |

L1 and L3 are shallow exactly as §3 predicted — one narrow stack each. But:

- **L2 is a letter sitting on a deep-paper substrate** — 39 modules, depth 14, more
  substrate than nine of the twelve D bundles.
- **D7 (6 modules, depth 3) and D1 (18 modules, depth 3) are shaped like letters.**

This is the re-tiering signal the operator authorized, arriving as a measurement rather
than an editorial impression. It does **not** by itself justify moving anything: closure
shape is a claim about substrate, and tier is also a claim about audience and framing.
It says where to look.

**D8 remains the outlier it was in M2.** 35 cited theorems reaching 289 modules — the
substrate is enormous and the manuscript's attachment to it is four filenames and a glob
(M2). Closure quantifies the gap the earlier measurement described.

---

## §7 Q1 — distinctive vs raw closure: **the worry was unfounded; drop the complication**

The design feared that shared singular-homology foundations would make every closure
intersect every other, leaving raw overlap meaningless. Measured across 21 bundles:

| a declaration appears in… | count |
|---|---|
| 1 bundle closure | **4 555** (70 %) |
| 2 | 1 282 |
| 3 | 548 |
| 4 | 73 |
| 5 | 10 |
| 6 | 1 |
| 7 | 1 |

**Maximum ubiquity across 21 bundles is 7, reached by one declaration.** There is no
shared-foundations blob. Raw closure is already distinctive, and **§7 Q1 needs no
"distinctive closure" definition** — a complication the design can drop entirely.

**Why**, so this is not mistaken for luck: `name_deps_project` is **project-closed** —
verified, 0 of 279 602 dependency edges resolve to a non-`SKEFTHawking` module. Mathlib,
the genuinely universal substrate, is already excluded upstream. The project's own
foundations are shared much more narrowly than the design assumed.

## §7 Q4 — closures do cross bundles, sparsely

| pair | closure ∩ | Jaccard |
|---|---|---|
| D6 ∩ D9 | 662 | **0.482** |
| D4 ∩ D8 | 398 | 0.146 |
| D8 ∩ D9 | 426 | 0.135 |
| L2 ∩ D9 | 0 | 0.000 |

The map is many-to-many but sparse. **D6/D9 — the pair the portfolio decision turns on —
is the one genuinely entangled pair**, now with a substrate-level number attached to what
M4(a) established at the level of named theorems.

## §7 Q2 — un-homed is loud, and two independent predicates agree on how loud

| predicate | homed modules | un-homed |
|---|---|---|
| M2 loose (leaf name appears anywhere in a draft; over-counts homed) | 636 | **1 403** |
| M2 strict (dotted name / `\lean{}` span / `source_manifest`) | 406 | 1 633 |
| **closure** (a draft cites something that transitively depends on it) | **631** | **1 405** |

Denominator 2 036–2 039 modules depending on the exact predicate.

Two mechanisms with nothing in common — substring presence versus dependency reachability
— land within 2 modules of each other. **~1 400 un-homed modules is a robust number, not
an artifact of either predicate.** (The *cardinalities* agree; the two homed sets have not
been checked for identity, and there is no reason to expect it.)

**Closure homes 631 modules against 275 by direct reference — a 2.3× gain**, and it beats
the name-based strict rule (406) as well. That gain is the design paying for itself: it is
substrate a bundle genuinely rests on that no name-matching rule can see.

Per-bundle, the gain concentrates exactly where the drafts are thinnest against their
substrate — D8 26 → 289, D9 70 → 142, D2 28 → 71, D4 26 → 69, L2 7 → 39.

---

## Limitation, measured rather than assumed: the closure has holes

12.4 % of dependency edges (34 569 of 279 602, 13 687 distinct targets) name a declaration
absent from `lean_deps.json`, so the walk stops there. Classified:

| category | distinct | edges | lossy? |
|---|---|---|---|
| proof-internal artifacts (`_proof_1_1`, `_simp_1_1`, `_abel_1_1`, …) | ~10 000 | ~27 000 | no — leaves |
| structure constructors / compiler companions | ~1 500 | ~5 900 | no — leaves |
| **`_private.*` declarations** | **553** | **1 278** | **yes** |

`ExtractDeps` deliberately omits `private` declarations, so a closure routing through one
truncates and silently loses whatever sits beneath it. That is **0.46 % of edges** —
bounded and documentable, not a design defect, but it must be **stated wherever closure
size is reported**, or it becomes another absence rendered as success.

---

## What this changes in the design

1. **§7 Q1 is closed** — no distinctive-closure definition. Raw closure is distinctive.
2. **§7 Q4 is closed** — sparse many-to-many; D6/D9 is the one entangled pair.
3. **§7 Q2 is closed** — un-homed ≈ 1 400 modules, robust across two predicates.
4. **§8 is answered** — closure shape separates most bundles and flags three (L2, D7, D1)
   whose tier does not match their substrate. Re-tiering is a **content decision** that
   this measurement informs and does not make.
5. **New, must carry into the design** — report the private-truncation caveat alongside any
   closure count.

§7 Q3 (apex declarations are hand-maintained) is unchanged, and is now **gated**:
`bundle_apex_resolves` fails on an apex naming no live declaration or naming a non-theorem.

---

## Reproducing these numbers

The probe scripts were scratchpad-only, deliberately — a measurement is not an instrument. What
shipped instead is `scripts/bundle_closure.py`, which computes the same closures from **declared
apexes** rather than prose references:

```bash
uv run python scripts/bundle_closure.py          # table + un-homed summary
uv run python scripts/bundle_closure.py --json   # machine-readable
```

Today it prints an empty table and names all 21 bundles as UNMEASURABLE, because none has declared
apexes yet. **That is the honest reading of the current state**, and the difference between it and
the tables above is exactly the difference between *what the drafts cite* and *what the bundles
claim* — which is the gap the retrofit closes, one bundle at a time.
