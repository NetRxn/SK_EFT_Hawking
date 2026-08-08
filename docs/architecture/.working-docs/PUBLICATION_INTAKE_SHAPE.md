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
   `UNDECLARED_APEX_CEILING` — which shipped at the maximum (every bundle on disk) by design, so
   the gate had teeth on day one. `--ci`'s coverage floor moved 57 → 58 in the same commit, per
   the zero-headroom ratchet. **The ceiling's live value and its full descent are in the ratchet
   comment above the constant; never copy it here.**
3. ✅ **DONE** — four bundles retrofitted under §3b, ceiling **21 → 17**:
   **D6** (11 apexes → 51 decls / 4 modules, depth 3) · **D9** (25 → 623 / 68, depth 12) ·
   **L2** (8 → 430 / 40, depth 14) · **D12** (11 → 147 / 14, depth 6).
   The flow is proven, and it has already paid: D12 was chosen to test ADR-010's untested
   **D6+D9+D12** merge, and the closure says D12 is not part of it (D6∩D12 = 0, D9∩D12 = 3).
   More importantly the retrofit **relocated** the D6/D9 finding — the audit's 78 shared theorems
   reproduce exactly, but the two bundles' *declared* closures are **disjoint**: D6 cites 133
   declarations from D9's namespace and claims none of them, covering only **19 %** of its own
   citations with its own apexes. Borrowing, not duplication.
   Full working: [`../../audits/2026-08-06-d12-retrofit/FINDINGS.md`](../../audits/2026-08-06-d12-retrofit/FINDINGS.md).
3b. ✅ **DONE 2026-08-07** — **D11**, ceiling **17 → 16** (73 apexes → 413 decls / 22 modules,
   depth 6). Chosen as the other half of ADR-010's second untested merge (D10+D11). Three results:
   its closure's module set **equals** `update_counts.py`'s hand-listed `_D11_MODULES` in both
   directions, so that roster is now derivable (TODO-D10); its closure intersects **every** other
   declared bundle in **zero** declarations, so no merge or homing question arises from its
   dependency shape; and ≈69 author-written declarations in its own modules — in three coherent
   families — are named in **no draft in the portfolio**, which locates D11's charter-length
   shortfall in the writing rather than in the physics.
   Full working: [`../../audits/2026-08-07-d11-retrofit/FINDINGS.md`](../../audits/2026-08-07-d11-retrofit/FINDINGS.md).
   ⚠️ **A high apex-to-closure ratio is a prose signal.** D9 declares 25 apexes over a
   623-declaration closure; D11 declares 73 over 413, because its draft introduces nearly every
   theorem by name in running prose. That ratio is computable before anyone reads a draft.
3c. ✅ **DONE 2026-08-07** — **D10**, ceiling **16 → 15** (33 apexes → 311 decls / 17 modules,
   depth 13). It **closes ADR-010's second untested merge**: `D10 ∩ D11 = 0` — no shared
   substrate at all, so the pairing was authorization adjacency, not content. Where D10 actually
   couples is **D9** (50 declarations, all in `QuantumNetwork.*`, every one of them claimed by
   D9's own apexes — borrowing *with* attribution available, unlike the D6→D9 case).
   It also found a CRITICAL claim gap the closure alone would not have shown: §4.2–§4.3 claim the
   first-ever Hohenberg–Kohn/Levy–Lieb formalization over three structures with **no inhabitant
   in the tree**, while §4.1's unconditional molecular self-adjointness verifies genuine.
   Full working: [`../../audits/2026-08-07-d10-retrofit/FINDINGS.md`](../../audits/2026-08-07-d10-retrofit/FINDINGS.md).
   ⚠️ **Method:** read the *statement*, not the prose describing it — and read the **full Lean
   source** of a module before judging its strength. §4.1's "unconditional" and §5.3's
   "discharged" both survive that test; §4.2's "constructive reductio" does not.
3d. ✅ **DONE 2026-08-07** — **D1**, ceiling **15 → 14** (41 apexes → 249 decls / 18 modules,
   depth 3). Taken for its exposure rather than for a merge: it carries TODO-D9's
   `\substantivetheorems{}` overclaim, and the closure supplies the honest denominator —
   **249**, not the 114 that item's arithmetic had been using (114 is §7.2's *reuse* population,
   a different set). Two new findings: §3.1 says four counting theorems are *"closed by
   `native_decide`"* when they are `by decide` (read directly at `SecondOrderSK.lean:260, 272,
   285, 937`, and their `axiom_deps_project` is empty); and four `Lift-section` events in the
   append log inserted **zero** manuscript content.
   ❌ **A corpus-wide generalisation of the first was filed and WITHDRAWN the same day** — see
   TODO-D13. The library has **546** declarations in the `native_decide` closure, measured by the
   existing `native_decide_regression` check.
   Full working: [`../../audits/2026-08-07-d1-retrofit/FINDINGS.md`](../../audits/2026-08-07-d1-retrofit/FINDINGS.md).
   ⚠️ **Near-miss worth carrying:** the extraction and the draft disagreed on §7.2's population
   (194 vs 114) and the draft was right — the two are the project's two counting conventions.
   **Run the tool a claim names before filing against it**, especially when the contradicting
   number is already in hand.
3e. ✅ **DONE 2026-08-07** — **F**, ceiling **14 → 13**. The first Tier-0 (29 apexes → 221 decls
   / 27 modules, depth 5). The flagship states a **17-bundle / 16-sibling** roster in seven
   places and **does not know D9–D12 exist**; its §7 D6-absorption checklist shows six unchecked
   boxes for work that has shipped. Measured: **F ∩ D1 = 27** and **F ∩ each of D6/D9/D10/D11/
   D12/L2 = 0** — the flagship's declared substrate touches none of the quantum-computation,
   detection or band-theory bundles. ❌ **One F finding was filed and WITHDRAWN:** F §7.2's `(native_decide)` annotation on
   `figure_eight_normalized` is **correct**, and the corpus-wide claim built on it was an artifact
   of probing the wrong axiom field. ADR-010's `native_decide` posture item is **untouched** and
   remains operator-owned. See TODO-D13 and ledger V26.
   Full working: [`../../audits/2026-08-07-f-retrofit/FINDINGS.md`](../../audits/2026-08-07-f-retrofit/FINDINGS.md).
   ⚠️ **Sequencing consequence:** F cannot be redrafted until the bundles it surveys are
   measured. **The retrofit is now a prerequisite for the flagship, not a parallel workstream.**
3f. ✅ **DONE 2026-08-07** — **D3**, ceiling **13 → 12** (89 apexes → 332 decls / 37 modules,
   depth 3). The heaviest bundle, and it produced the retrofit's most consequential measurement:
   **D3 ∩ F = 126** (F's substrate is largely D3's) but **D3 ∩ D1 = 0**, and three independent
   probes find **no Lean witness** for the program's central synthesis claim that the Sakharov
   `N_f` and the anomaly-classification `N_f = 16` are the same `N_f` (TODO-D16). The claim is
   **unformalized, not refuted** — disjoint proof DAGs are compatible with physical identity —
   but it is the one architectural claim the corpus asserts in prose alone.
   Also: two dangling `\ref`s inside D3's own tracked-hypothesis registry (TODO-D17), and seven
   more empty `Lift-section` events, bringing TODO-D14 to eleven across two bundles.
   Full working: [`../../audits/2026-08-07-d3-retrofit/FINDINGS.md`](../../audits/2026-08-07-d3-retrofit/FINDINGS.md).
   ⚠️ **D3 §28.3's tracked-hypothesis registry is the disclosure standard to copy** — every open
   `Prop` by module-qualified identifier with a one-line closure path, including one since
   discharged. And F is wrong about D3 in **both** directions in one document, so a drift audit
   that only hunts overclaims finds half the drift.
3g. ✅ **DONE 2026-08-07** — **D2** (47 apexes, ceiling 12→11), **D4** (66, 11→10), **D5**
   (70, 10→9). D2 narrowed TODO-D16 against my own filing (a Witt-invariant bridge D3↔D2 DOES
   exist). D4 made the D4→D8 boundary concrete (D4 and D8 name the same `GenericSU2` theorem) and
   found that **D4 ∩ D6 = 0** though F says D6 absorbed D4's SK headline. D5 supplied the corpus's
   best disclosure instrument — a three-way **Derived / MCC / Heuristic** taxonomy applied against
   itself — which with D4's point-of-use sentence is the fix TODO-D12 needs.
   ⚠️ **Apex-to-closure ratio is a GENRE signal, not a quality metric.** D11's high ratio was a
   prose signal; D5's flat closure (216 decls, depth 3) is what a register of verdicts looks like,
   and its own MCC labelling says so. Compare only within a genre.
3h. ✅ **DONE 2026-08-07** — **D8**, ceiling 9→8 (35 apexes → **2,290** decls / **289** modules /
   depth **24** — the largest closure in the portfolio). It **resolved the D4→D8 declaration
   conflict on both drafts' own instructions**: D8 cedes Fibonacci to D4 twice, D4 named the
   Clifford+T layer only in a module list, so four `GenericSU2` apexes moved D4 → D8. **The closure
   corroborated it independently — D4 fell 753 → 620 declarations, 61 → 43 modules.**
   Full working: [`../../audits/2026-08-07-d8-retrofit/FINDINGS.md`](../../audits/2026-08-07-d8-retrofit/FINDINGS.md).
   ⚠️ **A conflict recorded and deferred cost one line; guessing it would have cost a wrong
   ownership assignment in two bundles.** Flag conflicts at the first retrofit; resolve them at
   the second, when both drafts are readable.
3i. ✅ **DONE 2026-08-07** — **D7**, ceiling 8→7 (14 apexes → 93 decls / 8 modules). **Second
   declaration conflict resolved**: D1 §8.2 had declared D7's entire headline as a cross-check;
   six apexes moved D1 → D7, and D1's closure fell 249 → 171. D7's draft is **five-sevenths
   square-bracket placeholders** — not overclaiming, unwritten. Also found a dangling theorem name
   in the sentence naming D7's own headline, which `prose_theorem_reference_coverage` misses
   because its extractor keys on `\texttt{}` and D7 uses backtick quoting (TODO-D18).
   Full working: [`../../audits/2026-08-07-d7-retrofit/FINDINGS.md`](../../audits/2026-08-07-d7-retrofit/FINDINGS.md).
   ⚠️ **"A check exists" and "the check covers this input" are different claims.** Only the second
   licenses trusting a green result.
4. ⏭️ **NEXT** — the remaining 7: the I tier (**I1**, I2, I3), then L1/L3, then **E1/E2** — the
   last open ADR-010 §D4 merge question, measurable as soon as either is declared.
   ⚠️ **Method, learned on D12 and re-confirmed on D11:** `grep` for a theorem name in a draft
   returns 0 — drafts escape underscores inside `\thm{}`. Resolve references with the
   underscore-aware scan, **seeded with a known-present name first**, never a bare grep.
   This is the same artifact class behind ADR-010's two withdrawn figures.
5. The wave-close hook (§3a) — last, because it should encode a flow already proven by hand.

Re-tiering decisions wait on step 4. Closure shape says where to look; tier is also a claim about
audience and framing, and that is the operator's call, not the graph's.
