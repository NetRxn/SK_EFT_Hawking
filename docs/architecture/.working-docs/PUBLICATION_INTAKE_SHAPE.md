# Publication intake — the graph shape and the apex-creation flow

**Status: DESIGN. Authored 2026-08-06.** Companion to
[`PUBLICATION_INTAKE_DESIGN.md`](PUBLICATION_INTAKE_DESIGN.md), which holds the *what* (apex +
derived closure) and the measurements that settled §7/§8. This holds the *how*: where apexes are
declared, what reaches the graph, and how a new roadmap gets a publication home.

**Prerequisite discharged.** The design doc's §6 required reading the extractor contract in
`scripts/build_graph.py` **before** shaping anything. Done — the contract is summarised in §2 and
the shape below is chosen to fit it rather than to be retrofitted into it.

---

## 1. The one hand-maintained thing, and where it lives

A bundle **declares its apex theorems**: the results it claims, which its abstract already asserts
in prose. Everything else is derived.

**Home: `papers/<bundle>/bundle_metadata.json`, new key `apex_theorems`.**

```jsonc
{
  "bundle_target": "D6",
  // …existing machine-written state…
  "apex_theorems": [
    {"name": "SKEFTHawking.WilliamsonYoder.gauging_qec_overhead_bound",
     "claims": "§3 — gauging-QEC overhead is linear-polylog",
     "declared": "2026-08-06"}
  ]
}
```

**Why here and not a central registry in `constants.py`,** despite Invariant #2:

- §4's ergonomics require that **merging two bundles concatenates apex lists and splitting
  partitions them**. Co-located lists do that by moving a file; a central registry needs an edit
  whose correctness nothing checks.
- The file is already the canonical per-bundle state, already discovered by
  `iter_v2_paper_dirs`, already graph-visible through the `Paper` node.
- Creating a bundle already means creating this file. Apex declaration adds a key, not a step.

Invariant #2 governs *physics* registries — parameters, constants, the Aristotle registry — whose
value must have exactly one source. An apex list is bundle-local editorial data, and centralising
it would trade a checkable local edit for an unchecked remote one.

## 2. What reaches the graph — apexes as EDGES, closure as an OVERLAY

The extractor contract (`build_graph.py`): nodes are `{id, type, label, name, verification,
detail, meta}`; edges are `{source, target, type}`. Lean declarations are `lean:<fqn>`, modules
`module:<dotted>`, papers `paper:<dirname>`. The default graph is **47 287 nodes / 14 040 edges**,
and the full proof DAG (`USES`, ~40 k edges) is **off by default** behind `SK_EFT_INCLUDE_USES`
precisely because it swamps that.

So closure must **not** materialise as edges. Measured: D8's closure alone is 2 292 declarations;
across 21 bundles the homed union is 6 470 and the un-homed complement 29 250. Emitting
`CLAIMS_SUBSTRATE` per closure member would roughly double the graph's edge count to render one
view.

**The precedent to follow is `_overlay_atlas`**, which annotates `meta` on existing nodes and is
documented as *"a VIEW, not a store — it adds NO new nodes or edges here"*. The implication DAG it
renders is the `USES`/`ASSUMES` edges that already exist. Closure is the same situation: the DAG
is already there.

### 2a. New edge — small, hand-declared, checkable

| edge | from → to | count |
|---|---|---|
| `CLAIMS_APEX` | `paper:<bundle>` → `lean:<fqn>` | a handful per bundle (~100 total) |

This is the only new edge type. It is exactly the hand-maintained data of §1, so it is exactly
what a check must verify resolves to a live declaration.

### 2b. New overlay — derived, unbounded, free

On each `lean:` node:

| key | meaning |
|---|---|
| `meta.homed_by` | `["D6", "D9"]` — bundles whose apex closure contains it; `[]` = **un-homed** |
| `meta.home_count` | `len(homed_by)` — the ubiquity measured in FINDINGS §Q1 |
| `meta.closure_depth_min` | shortest distance to any claiming apex |

On each `module:` node: `meta.homed_by`, `meta.homed_declaration_count`.

On each `paper:` node:

| key | meaning |
|---|---|
| `meta.closure_size` / `closure_modules` / `closure_max_depth` | the shape numbers of FINDINGS §8 |
| `meta.closure_exclusive` | declarations no other bundle claims |
| `meta.closure_truncated_private` | ⚠️ **required** — how many closure walks stopped at a `private` declaration |

The last one is not optional. `ExtractDeps` omits `private` declarations, so **553 of them (1 278
edges, 0.46 %) truncate a walk silently**. A closure size reported without it is an absence
rendered as success — the defect class this branch exists to remove.

### 2c. What the dashboard gets for free

Colour the substrate by `homed_by`; filter `home_count == 0` for the un-homed map; size a bundle by
`closure_size`. No second conversation, no separate report — which is the operator's stated bar.

## 3. Apex creation — the flow that was missing

> *"the atlas/apex was introduced after papers/bundles — I don't know if we actually have a
> streamlined way of creating new apex nodes when we're building out new roadmaps/phases."*

Correct, and retrofitting existing bundles does not solve it. Two paths, one ongoing and one
one-time.

### 3a. Ongoing — the wave-close hook (the real fix)

A wave close is where a result becomes real, it already passes a gate, and it is the moment of
maximum author context. At Stage 14, for each theorem the wave shipped, exactly one question:

> *Does this establish something a publication claims — and which one?*

Three answers, and **two of them need no action**:

1. **Already in a bundle's closure** (an existing apex depends on it) → nothing to do. This is the
   common case and the whole point of deriving rather than declaring.
2. **It is a new headline result** → add one line to that bundle's `apex_theorems`.
3. **It belongs to no existing bundle** → it surfaces as un-homed, and stays there until someone
   decides. Un-homed is a legitimate state, not an error.

### 3b. One-time — retrofit, one bundle at a time

Operator's condition, and it binds: apexes may be authored **only** with full context review per
bundle — contributing roadmaps, the Lean cited, the claims record. One bundle at a time, never a
sweep. An apex asserted without reading the substrate is the same authorization-before-measurement
pattern that produced the D-tier problem in the first place.

The prose-reference seeding used for the FINDINGS measurements is **not** a shortcut to this: it
resolves every verbatim token, including mid-level lemmas cited in passing, so it is a lower bound
on substrate and an over-count of apexes. It says where to look. It does not name the claim.

## 4. Checks this implies

| check | fails when |
|---|---|
| `bundle_apex_resolves` | a declared apex names no live declaration (the §7 Q3 hand-maintenance risk) |
| `bundle_apex_is_a_theorem` | an apex is a `def`/`structure` — a bundle claims results, not definitions |
| `bundle_closure_freshness` | a bundle's closure content-hash moved since its last lift → absorption due (**content hash, not mtime** — the trigger the D6 branch turns on) |
| `substrate_homing_ratchet` | un-homed count rises without an entry saying why |

⚠️ **`bundle_apex_resolves` must not pass vacuously on an empty apex list.** Every content-facing
predicate on this branch was `∀x ∈ S(draft). P(x)` with the draft supplying `S`, making the whole
system **monotone in emptiness** (H1). This is the single most important line in this document.

**How it is enforced, and why not by `measured=False`.** The first draft set `measured=False` when
nothing was declared. That is wrong: `measured` means *the check could not run* — an absent
artifact or toolchain — and it feeds the `--ci` coverage floor, whose job is to catch an
under-provisioned runner. All 21 metadata files are present and readable; the check runs fine and
returns a definite result. Reporting `measured=False` would have told the floor the runner was one
check short and masked a real provisioning failure by one.

So the teeth come from **the house ratchet instead**: `UNDECLARED_APEX_CEILING = 21` hard-fails
when the undeclared count RISES, the per-bundle detail says substrate UNKNOWN rather than summing
it to zero, and the substantive `apexes_resolve` detail reads `UNMEASURABLE` instead of claiming a
resolution it never performed. Every bundle retrofitted lowers the ceiling in the same commit; 0 is
the target. `measured=False` is reserved for the one branch that genuinely cannot measure — no
bundle metadata on disk at all.

## 5. Sequencing

1. ✅ **BUILT** — `scripts/bundle_closure.py` (derivation), `_overlay_closure` +
   `extract_claims_apex_edges` in `build_graph.py`. With no apexes declared, all 32 744 project
   declarations are un-homed and all 21 bundles report `closure_measurable: false` — **that is the
   honest reading**, not a failure to paper over by seeding apexes automatically.
2. ✅ **BUILT** — `bundle_apex_resolves` (registered, in `_CANONICAL_ORDER` after the roster gate)
   plus 28 tests in `tests/test_bundle_closure.py`. It hard-fails on an apex naming no live
   declaration, on an apex that is not a theorem, and on the undeclared count rising above
   `UNDECLARED_APEX_CEILING = 21`. `--ci`'s coverage floor moved 57 → 58 in the same commit, per
   the zero-headroom ratchet.
3. ⏭️ **NEXT** — retrofit **one** bundle end-to-end under §3b as a proof of the flow. D6 or L2 — D6 because its
   entanglement with D9 (Jaccard 0.482) is the portfolio question, L2 because its substrate depth
   (39 modules, depth 14) contradicts its tier.
4. Only then the remaining bundles, one at a time.
5. The wave-close hook (§3a) — last, because it should encode a flow already proven by hand.

Re-tiering decisions wait on step 4. Closure shape says where to look; tier is also a claim about
audience and framing, and that is the operator's call, not the graph's.
