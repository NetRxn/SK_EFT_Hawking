# Remediation Loop Core — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make a review finding routable and closable — it carries a lane, a target, a verification command and its blockers; REQUIRED severity blocks bundle-green; and closing it is a script call that cannot mint a broken key.

**Architecture:** Everything extends a mechanism that already exists. The extractor gains fields it currently discards. The closure bar loses its severity scoping. `bundle_stage13_claim_consistent` gains a severity tier. `ledger_ids_resolve` is promoted out of `graph_integrity` and its leg deleted. One new script (`close_finding.py`), modelled on `record_review.py`. No new subsystem.

**Tech Stack:** Python 3.14, `uv run`, pytest. No new dependencies.

**Implements:** ADR-012 P1, P4, P5, P6, P7, P8b and D17. **Out of scope, deliberately:** the dashboard (P9/D15/D20), orchestration (P10), the architecture-change skill (P11), re-filing D45–D49 (P8), queueing ADR-010's items (P8c), the DASHBOARD canonicalization (P8d). Each is a different subsystem with different gates; each gets its own plan.

**Spec:** [`../specs/2026-08-12-finding-closure-lifecycle-design.md`](../specs/2026-08-12-finding-closure-lifecycle-design.md) · **ADR:** [`../../adrs/ADR-012-finding-lifecycle-routing-and-closure.md`](../../adrs/ADR-012-finding-lifecycle-routing-and-closure.md)

## Global Constraints

- **Branch:** all implementation lands on `feat/adr012-remediation-loop`. Planning was on `main`.
- **Never build a second mechanism beside a working one** (`CLAUDE.md` rule 1). Task 11 exists because the first draft of this work proposed a check that already existed.
- **The id minter is shared, never copied.** `close_finding.py` imports it from `build_graph`.
- **Every check leg ships with a PRODUCTION-seeded mutation** that observes red (ADR-012 D8, `CHECK_AUTHORING_GUIDE.md` §2.4). A fixture-only mutation raises `FIXTURE_ONLY_CEILING`, which may only shrink — so it is not merely weaker, it is blocked.
- **Ratchets carry zero headroom** and may only be lowered, in the commit that lowers the population.
- **A new registered check owes five things in the same commit:** `validate._CANONICAL_ORDER` (its absence *raises*), the `validate.py` re-export, a `MUTATION_VERIFIED` entry naming a real test (`AWAITING_MUTATION_TEST` is empty, `AWAITING_CEILING` is 0), `_config.CI_MIN_CHECKS_RUN`, and a regenerated `SURFACE_INVENTORY.md`.
- **Architecture docs land in the commit that makes them wrong** (architecture rule 2), never batched.
- **Never write a census count into a `docs/architecture/` narrative** (rule 3).
- **Paths in checks are reached as `_H.<NAME>` at each use** (ADR-009 H1); flags by attribute on `_cfg` (H5).
- Run everything from `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking`.
- CLI convention from `record_review.py`: a `close(...)`-style function returns `(ok: bool, msg: str)`; `main()` prints `"✓ "` or `"✗ REFUSED — "` and returns `0`/`1`.

## File Structure

| file | responsibility | tasks |
|---|---|---|
| `docs/READINESS_GATES.md` | the closure contract, canonically | 1 |
| `scripts/build_graph.py` | mint ids · parse the six fields · emit `BLOCKED_BY` · apply the bar | 2, 3, 4, 5, 10 |
| `scripts/validation/checks/reviews.py` | field enforcement · the promoted ledger check | 4, 11 |
| `scripts/validation/checks/bundles_readiness.py` | the REQUIRED tier + its two ratchets | 6 |
| `scripts/validation/checks/graph_atlas.py` | **loses** the `ledger_ids_resolve` leg | 11 |
| `scripts/close_finding.py` | **new** — the only supported ledger writer | 7, 8 |
| `scripts/review_runner.py` | per-finding orientation brief | 13 |
| `docs/review_finding_supersessions.json` | schema + nine re-keys + the 98 closures | 9, 14 |
| `.claude/plugins/skeft-qa/agents/*.md` | the emission template | 4 |

---

### Task 0: Branch

- [ ] **Step 1: Cut the implementation branch**

```bash
cd /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking
git checkout -b feat/adr012-remediation-loop
git status --short
```

Expected: clean tree on the new branch.

---

### Task 1: The closure contract enters the canonical gate document

Docs first (ADR-012 P1, D3). `READINESS_GATES.md` is the canonical gate document and has **zero** mentions of the ledger, so a reader cannot learn how a gate un-blocks. Every later task depends on a rule that currently lives only in a `build_graph.py` comment.

**Files:**
- Modify: `docs/READINESS_GATES.md`
- Modify: `docs/WAVE_EXECUTION_PIPELINE.md` (Stage 13)

**Interfaces:**
- Consumes: nothing
- Produces: the prose contract Tasks 6, 10 and 11 implement.

- [ ] **Step 1: Add the lifecycle section to `docs/READINESS_GATES.md`**

Append a section titled `## Finding lifecycle — how a gate un-blocks` stating, in this order:

1. A `ReviewFinding` is born `open`, unconditionally. Heading text cannot close it.
2. `docs/review_finding_supersessions.json` is the **only** channel that can change that.
3. A closure record must carry an explicit closing status (`fixed` or `accepted`), **≥40 characters** of rationale in any of `evidence`/`rationale`/`note`, and an anchor in any of `commit`/`date`/`closed_date`/`applied_at`.
4. **The bar applies at every severity** (from Task 10). It was scoped to `critical`/`major`/`blocker`, and because `- **Severity:**` is body-declarable and beats the heading glyph, declaring `recommended` under a 🔴 heading closed a finding on a two-key record.
5. A finding carrying a `verify` command additionally needs a passing `verified_by`.
6. Records are written with `scripts/close_finding.py`. Hand-editing the JSON is how 66 records came to name no finding.
7. **Severity tiers:** a BLOCKER blocks submission; a REQUIRED (`major`) blocks `stage13_status: green` (Task 6).

Cross-reference `ADR-012` for the rationale; do not restate it.

- [ ] **Step 2: Cross-reference from `docs/WAVE_EXECUTION_PIPELINE.md` Stage 13**

After the existing re-invocation rule ("the re-run is evidence"), add three sentences: closures are recorded with `scripts/close_finding.py`; the bar applies at every severity; the contract itself lives in `docs/READINESS_GATES.md`. **One owner per fact** — do not restate the bar here.

- [ ] **Step 3: Verify no path claim broke**

```bash
uv run python scripts/validate.py --check architecture_inventory_fresh
```

Expected: PASS.

- [ ] **Step 4: Commit**

```bash
git add docs/READINESS_GATES.md docs/WAVE_EXECUTION_PIPELINE.md
git commit -m "docs: the closure contract enters the canonical gate document

READINESS_GATES.md had zero mentions of the ledger — the mechanism that
decides whether a gate can un-block. ADR-012 D3/P1: the rule lands before
the code that depends on it."
```

---

### Task 2: Extract the id minter to module scope

**Files:**
- Modify: `scripts/build_graph.py` (the minting site, `finding_id = f'review:{date_dir}:{review_name}:{section_num}'`)
- Test: `tests/test_build_graph.py`

**Interfaces:**
- Produces: `build_graph.mint_finding_id(date_dir: str, review_name: str, section_num: str) -> str` — imported by Tasks 7 and 11.

- [ ] **Step 1: Write the failing test**

```python
class TestTheFindingIdMinterIsShared:
    """One minter, importable, and the one production uses.

    `close_finding.py` mints ids to WRITE the ledger; `extract_review_finding_nodes`
    mints them to READ it back. Two implementations diverging is exactly how 66
    review:-scheme ledger records came to reference ids that match no node.
    """

    def test_mint_finding_id_is_importable_and_stable(self):
        import build_graph as bg
        assert bg.mint_finding_id('2026-08-12-0006-internal-adversarial', 'I1', '5.5') \
            == 'review:2026-08-12-0006-internal-adversarial:I1:5.5'

    def test_every_minted_node_id_round_trips_through_the_function(self):
        import build_graph as bg
        for n in bg.extract_review_finding_nodes():
            m = n['meta']
            assert n['id'] == bg.mint_finding_id(
                m['review_date'], m['review_name'], m['section']), (
                f"{n['id']} was not produced by mint_finding_id — the extractor "
                "and the minter have diverged")
```

- [ ] **Step 2: Run it and watch it fail**

```bash
uv run python -m pytest tests/test_build_graph.py::TestTheFindingIdMinterIsShared -v
```

Expected: FAIL — `module 'build_graph' has no attribute 'mint_finding_id'`.

- [ ] **Step 3: Add the function immediately above `extract_review_finding_nodes`**

```python
def mint_finding_id(date_dir: str, review_name: str, section_num: str) -> str:
    """The canonical ReviewFinding node id.

    ⚠️ MODULE SCOPE ON PURPOSE. `scripts/close_finding.py` imports this to WRITE the
    supersession ledger, and `extract_review_finding_nodes` calls it to READ the ledger
    back. A second implementation is not a duplication smell, it is the defect: 66 of the
    870 ledger records reference `review:` ids no node carries, because every one was
    hand-typed against a format nobody could check. Same reasoning as `_recurrence_norm`,
    which moved to module scope after the production matcher could have been deleted or
    inverted with its test still green.
    """
    return f'review:{date_dir}:{review_name}:{section_num}'
```

- [ ] **Step 4: Replace the inline f-string with `finding_id = mint_finding_id(date_dir, review_name, section_num)`**

- [ ] **Step 5: Run the graph tests**

```bash
uv run python -m pytest tests/test_build_graph.py -q
```

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add scripts/build_graph.py tests/test_build_graph.py
git commit -m "build_graph: extract mint_finding_id to module scope

The writer in Task 7 must mint ids with the function the reader uses."
```

---

### Task 3: Parse `Gate:` and `Location:` into `blocks` and `target`

The reviewer template has carried these since before ADR-012 and the extractor discards them. **Measured 2026-08-12: of 1,178 severity-glyph sections, 1,105 carry `Gate:` (93%) and 1,094 carry `Location:` (92%).** No backfill, no re-review — a parser change.

**Files:**
- Modify: `scripts/build_graph.py` (`extract_review_finding_nodes`)
- Test: `tests/test_build_graph.py`

**Interfaces:**
- Produces: `meta['blocks']` and `meta['target']` on every `ReviewFinding` node; `None` when the line is absent.

- [ ] **Step 1: Write the failing test**

```python
class TestRoutingFieldsAreParsedNotInvented:
    """ADR-012 C7: `Gate:` and `Location:` are ALREADY written on 92-93% of findings.

    The first draft of this ADR proposed adding two new fields for data the system
    already collects and threw away at extraction.
    """

    def test_the_field_parser_reads_a_body_line(self):
        import build_graph as bg
        body = ("- **Gate:** CitationIntegrity\n"
                "- **Location:** `src/core/citations.py:412`\n"
                "- **Observed:** something\n")
        assert bg._parse_finding_field(body, 'Gate') == 'CitationIntegrity'
        assert bg._parse_finding_field(body, 'Location') == '`src/core/citations.py:412`'
        assert bg._parse_finding_field(body, 'Nope') is None

    def test_the_live_corpus_populates_both_above_their_measured_floor(self):
        import build_graph as bg
        ns = bg.extract_review_finding_nodes()
        assert ns, "no findings extracted — the seam is empty, not clean"
        blocks = sum(1 for n in ns if n['meta'].get('blocks'))
        target = sum(1 for n in ns if n['meta'].get('target'))
        # Floors, not equalities: the corpus grows. Measured 2026-08-12 at 93% / 92%.
        assert blocks / len(ns) > 0.80, f"blocks coverage collapsed to {blocks}/{len(ns)}"
        assert target / len(ns) > 0.80, f"target coverage collapsed to {target}/{len(ns)}"
```

- [ ] **Step 2: Run it and watch it fail**

```bash
uv run python -m pytest tests/test_build_graph.py::TestRoutingFieldsAreParsedNotInvented -v
```

Expected: FAIL — `_parse_finding_field` does not exist.

- [ ] **Step 3: Add the parser at module scope, above `mint_finding_id`**

```python
_FINDING_FIELD_RE_CACHE: dict[str, "re.Pattern[str]"] = {}


def _parse_finding_field(body: str, label: str) -> str | None:
    """Read one `- **Label:** value` line out of a finding body.

    ⚠️ The reviewer template has carried `Gate:`, `Location:`, `Observed:`, `Evidence:`,
    `Expected:` and `Fix:` since before ADR-012, and this extractor parsed NONE of them.
    Measured 2026-08-12: 93% of severity-glyph sections carry `Gate:` and 92% carry
    `Location:`. They are `blocks` and `target` — written by the reviewer, sitting in the
    markdown, discarded here. This function is the whole retrofit.
    """
    pat = _FINDING_FIELD_RE_CACHE.get(label)
    if pat is None:
        pat = re.compile(rf"^\s*[-*]\s*\*\*{re.escape(label)}:?\*\*:?\s*(.+?)\s*$", re.M)
        _FINDING_FIELD_RE_CACHE[label] = pat
    m = pat.search(body or "")
    return m.group(1).strip() or None if m else None
```

- [ ] **Step 4: Populate the two keys in the `meta` dict**

In `extract_review_finding_nodes`, inside the `meta = {...}` literal, add:

```python
                'blocks': _parse_finding_field(body, 'Gate'),
                'target': _parse_finding_field(body, 'Location'),
```

- [ ] **Step 5: Run and measure**

```bash
uv run python -m pytest tests/test_build_graph.py -q
uv run python -c "
import sys; sys.path.insert(0,'scripts'); import build_graph as bg
ns=bg.extract_review_finding_nodes()
print('blocks', sum(1 for n in ns if n['meta'].get('blocks')), '/', len(ns))
print('target', sum(1 for n in ns if n['meta'].get('target')), '/', len(ns))"
```

Expected: tests PASS; roughly 93% / 92% populated.

- [ ] **Step 6: Commit**

```bash
git add scripts/build_graph.py tests/test_build_graph.py
git commit -m "build_graph: parse Gate: and Location: into blocks and target

ADR-012 C7. The reviewer already writes both on 92-93% of findings; the
extractor threw them away. The 'unaffordable backfill' is a parser change."
```

---

### Task 4: The four new emission fields, and their enforcement

**Files:**
- Modify: `scripts/build_graph.py` (`_LANE_DECL_MAP`, `meta` keys)
- Modify: `.claude/plugins/skeft-qa/agents/adversarial-reviewer.md`, `claims-reviewer.md`, `figure-reviewer.md`
- Modify: `scripts/validation/checks/reviews.py` (`review_severity_declared`)
- Test: `tests/test_build_graph.py`, `tests/test_d5_reviews.py`

**Interfaces:**
- Consumes: `_parse_finding_field` (Task 3)
- Produces: `build_graph._LANE_DECL_MAP: dict[str, str]`; `meta['lane'|'verify'|'blocked_by'|'needs_operator']`

- [ ] **Step 1: Write the failing tests**

```python
class TestLaneAndVerifyAreParsedForwardOnly:
    def test_the_lane_map_is_the_single_declaration(self):
        import build_graph as bg
        assert set(bg._LANE_DECL_MAP) == {
            'lean', 'pyrust', 'substrate', 'prose', 'research', 'infra'}

    def test_an_absent_lane_reads_unclassified_not_a_failure(self):
        import build_graph as bg
        assert bg._parse_lane("- **Observed:** x\n") == 'unclassified'

    def test_a_declared_lane_is_normalised(self):
        import build_graph as bg
        assert bg._parse_lane("- **Lane:** Substrate\n") == 'substrate'

    def test_an_unknown_lane_is_preserved_verbatim_for_the_check_to_catch(self):
        import build_graph as bg
        assert bg._parse_lane("- **Lane:** wizardry\n") == 'wizardry'
```

```python
class TestLaneEnforcementExtendsSeverityDeclared:
    def test_the_check_is_green_on_the_live_corpus(self):
        from validation.checks.reviews import check_review_severity_declared
        assert check_review_severity_declared().passed is True

    def test_a_seeded_unknown_lane_turns_the_check_red(self, tmp_path, monkeypatch):
        """Non-vacuity (ADR-012 D8): seed the PRODUCTION artifact, observe red."""
        import validate_helpers as _H
        from validation.checks.reviews import check_review_severity_declared
        import datetime
        d = _H.PROJECT_ROOT / "papers" / "AutomatedReviews" / "9999-99-99-seeded-lane"
        d.mkdir(parents=True, exist_ok=True)
        f = d / "SEED.md"
        f.write_text("### 1.1 — 🔴 CRITICAL — seeded\n\n"
                     "- **Severity:** critical\n- **Lane:** wizardry\n")
        try:
            assert check_review_severity_declared().passed is False
        finally:
            f.unlink(); d.rmdir()
```

- [ ] **Step 2: Run and watch them fail**

```bash
uv run python -m pytest tests/test_build_graph.py::TestLaneAndVerifyAreParsedForwardOnly \
  tests/test_d5_reviews.py::TestLaneEnforcementExtendsSeverityDeclared -v
```

Expected: FAIL — `_LANE_DECL_MAP` / `_parse_lane` do not exist.

- [ ] **Step 3: Add the lane declaration and parsers to `scripts/build_graph.py`**

```python
#: The six routing lanes (ADR-012 D2). ⚠️ Lean/substrate and infra are separate because
#: they need different AGENT PROFILES, not merely different gates: substrate work runs the
#: atlas + the lean4 MCP loop + a lean-worker in a worktree slot, while infra is work on
#: the machine itself (architecture, workflows, harness, plugin, dashboard).
#: Declared ONCE, validated against — same shape as `_SEVERITY_DECL_MAP`.
_LANE_DECL_MAP: dict[str, str] = {
    'lean': 'lean', 'pyrust': 'pyrust', 'substrate': 'substrate',
    'prose': 'prose', 'research': 'research', 'infra': 'infra',
}

#: External release-condition schemes for `blocked_by` (ADR-012 D19). Anything NOT
#: carrying one of these prefixes must resolve to a minted node id — including an
#: unrecognised scheme, so `runs:42` fails rather than becoming a blocker nothing can
#: ever satisfy. ⚠️ There is deliberately no `operator:` scheme: an operator decision
#: that gates work is itself a queue item with a node id, so parking behind it is the
#: plain node-id case.
_RELEASE_SCHEMES: tuple[str, ...] = ('run:', 'phase:', 'pub:', 'research:')


def _parse_lane(body: str) -> str:
    """Forward-only. Absent reads `unclassified`; an unknown token is preserved verbatim
    so `review_severity_declared` can name it rather than silently coercing it."""
    raw = _parse_finding_field(body, 'Lane')
    if not raw:
        return 'unclassified'
    return _LANE_DECL_MAP.get(raw.strip().strip('`').lower(), raw.strip().strip('`').lower())


def _parse_blocked_by(body: str) -> list[str]:
    raw = _parse_finding_field(body, 'Blocked-by') or _parse_finding_field(body, 'Blocked by')
    if not raw:
        return []
    return [p.strip().strip('`') for p in raw.split(',') if p.strip().strip('`')]
```

- [ ] **Step 4: Populate the four keys in `meta`**

```python
                'lane': _parse_lane(body),
                'verify': _parse_finding_field(body, 'Verify'),
                'blocked_by': _parse_blocked_by(body),
                'needs_operator': (_parse_finding_field(body, 'Needs-operator') or '').lower() or None,
```

- [ ] **Step 5: Extend `check_review_severity_declared` in `scripts/validation/checks/reviews.py`**

Inside the existing loop that validates the declared severity token, add a parallel leg. Import the map the same way the severity leg imports its own:

```python
    try:
        from build_graph import _LANE_DECL_MAP
    except ImportError as exc:
        details.append(Detail("lane_map", False, measured=False,
                              message=f"build_graph._LANE_DECL_MAP unavailable ({exc}) — "
                                      "the lane leg did not run; its silence is not evidence"))
    else:
        unknown_lanes = sorted({
            lane for lane in declared_lanes
            if lane not in _LANE_DECL_MAP and lane != 'unclassified'})
        details.append(Detail(
            "lane_declared", not unknown_lanes,
            f"{len(declared_lanes)} finding(s) declare a lane; "
            + (f"unmappable: {', '.join(unknown_lanes)}. A lane build_graph cannot map "
               "routes nowhere — it is an unroutable finding, not a typo."
               if unknown_lanes else "all map")))
```

Collect `declared_lanes` from the same document walk the severity leg already performs, using `build_graph._parse_lane` on each finding body. **Do not add a second walk.**

- [ ] **Step 6: Add the four lines to each of the three reviewer templates**

In `adversarial-reviewer.md`, `claims-reviewer.md` and `figure-reviewer.md`, in the per-finding field template, after `- **Severity:**`:

```markdown
- **Lane:** lean | pyrust | substrate | prose | research | infra
- **Verify:** a runnable command that FAILS against the unrepaired artifact
- **Blocked-by:** finding ids and/or release conditions (`run:` `phase:` `pub:` `research:`), comma-separated — omit if none
- **Needs-operator:** now | queue — omit unless a human decision is genuinely required
```

Add one sentence beneath: *`Verify` must name the invariant it asserts, not merely run. A DOI that resolves is not a DOI that resolves to the cited work.*

- [ ] **Step 7: Run everything**

```bash
uv run python -m pytest tests/test_build_graph.py tests/test_d5_reviews.py -q
uv run python scripts/validate.py --check review_severity_declared
uv run python -m pytest .claude/plugins/skeft-qa/tests -q
```

Expected: all PASS.

- [ ] **Step 8: Commit**

```bash
git add scripts/build_graph.py scripts/validation/checks/reviews.py tests/ \
        .claude/plugins/skeft-qa/agents/adversarial-reviewer.md \
        .claude/plugins/skeft-qa/agents/claims-reviewer.md \
        .claude/plugins/skeft-qa/agents/figure-reviewer.md
git commit -m "findings carry a lane, a verify command, blockers and an operator flag

ADR-012 D1/D2/D12. Enforcement EXTENDS review_severity_declared rather than
adding a sibling — it already validates a declared token against a map, which
is the same shape as validating a lane."
```

---

### Task 5: `BLOCKED_BY` edges, with scheme discrimination and a real consumer

**Files:**
- Modify: `scripts/build_graph.py` (edge extractor)
- Modify: `docs/KNOWLEDGE_GRAPH.md`
- Test: `tests/test_build_graph.py`

**Interfaces:**
- Consumes: `_parse_blocked_by`, `_RELEASE_SCHEMES` (Task 4)
- Produces: `build_graph.extract_blocked_by_edges(nodes: list[dict]) -> list[dict]`; `build_graph.finding_is_dispatchable(node: dict, node_ids: set[str], closed: set[str]) -> bool`

- [ ] **Step 1: Write the failing tests**

```python
class TestBlockedByIsADagWithAConsumer:
    """⚠️ KNOWLEDGE_GRAPH.md already carries three edge types gates query and nothing
    emits, and PRODUCES sat expired for a whole wave because a fallback masked it. A new
    edge type ships with a consumer and a test proving the consumer sees it."""

    def test_a_release_scheme_is_not_treated_as_a_node_reference(self):
        import build_graph as bg
        n = {'id': 'review:d:X:1', 'meta': {'blocked_by': ['run:mlx-rhmc-2026'], 'status': 'open'}}
        edges = bg.extract_blocked_by_edges([n])
        assert edges == [], "a release condition must not become a node edge"
        assert bg.finding_is_dispatchable(n, {'review:d:X:1'}, set()) is False

    def test_an_unrecognised_scheme_fails_rather_than_blocking_forever(self):
        import build_graph as bg
        n = {'id': 'review:d:X:1', 'meta': {'blocked_by': ['runs:42'], 'status': 'open'}}
        with pytest.raises(ValueError, match='runs:42'):
            bg.extract_blocked_by_edges([n])

    def test_a_blocked_by_naming_no_node_fails_loudly(self):
        import build_graph as bg
        n = {'id': 'review:d:X:1', 'meta': {'blocked_by': ['review:d:X:99'], 'status': 'open'}}
        with pytest.raises(ValueError, match='review:d:X:99'):
            bg.extract_blocked_by_edges([n])

    def test_a_resolvable_blocker_emits_an_edge_and_gates_dispatch(self):
        import build_graph as bg
        a = {'id': 'review:d:X:1', 'meta': {'blocked_by': ['review:d:X:2'], 'status': 'open'}}
        b = {'id': 'review:d:X:2', 'meta': {'blocked_by': [], 'status': 'open'}}
        edges = bg.extract_blocked_by_edges([a, b])
        assert edges == [{'source': 'review:d:X:1', 'target': 'review:d:X:2',
                          'type': 'BLOCKED_BY'}]
        ids = {'review:d:X:1', 'review:d:X:2'}
        assert bg.finding_is_dispatchable(a, ids, set()) is False
        assert bg.finding_is_dispatchable(a, ids, {'review:d:X:2'}) is True
```

- [ ] **Step 2: Run and watch them fail**

```bash
uv run python -m pytest tests/test_build_graph.py::TestBlockedByIsADagWithAConsumer -v
```

- [ ] **Step 3: Implement both functions at module scope**

```python
def extract_blocked_by_edges(finding_nodes: list[dict]) -> list[dict]:
    """`ReviewFinding → ReviewFinding` edges from `meta['blocked_by']` (ADR-012 D10).

    ⚠️ This field carries TWO kinds of entry. A declared release scheme
    (`_RELEASE_SCHEMES`) is an external condition and never resolves to a node. Anything
    else must resolve to a minted id, INCLUDING an unrecognised scheme — `runs:42` raises
    rather than becoming a blocker nothing can ever satisfy.
    """
    ids = {n['id'] for n in finding_nodes}
    edges: list[dict] = []
    for n in finding_nodes:
        for dep in (n.get('meta') or {}).get('blocked_by') or []:
            if dep.startswith(_RELEASE_SCHEMES):
                continue
            if ':' in dep and not dep.startswith('review:'):
                raise ValueError(
                    f"{n['id']}: blocked_by {dep!r} carries an unrecognised scheme. "
                    f"Known release schemes: {', '.join(_RELEASE_SCHEMES)}. A token nothing "
                    "can satisfy reads as WAITING when it is STUCK.")
            if dep not in ids:
                raise ValueError(
                    f"{n['id']}: blocked_by {dep!r} names no minted finding. Silently "
                    "dropping it is the 66-record orphan class one layer up.")
            edges.append({'source': n['id'], 'target': dep, 'type': 'BLOCKED_BY'})
    return edges


def finding_is_dispatchable(node: dict, node_ids: set[str], closed_ids: set[str]) -> bool:
    """THE CONSUMER. A finding waits on every unclosed blocker and on every unmet release
    condition. Release conditions are opaque here — evaluated in Task 12 — so any present
    one holds the finding, which is the safe direction."""
    meta = node.get('meta') or {}
    for dep in meta.get('blocked_by') or []:
        if dep.startswith(_RELEASE_SCHEMES):
            return False
        if dep not in closed_ids:
            return False
    return True
```

- [ ] **Step 4: Wire the edges into the graph build**

In the function that assembles `links`, after the `FLAGS` extraction, add:

```python
    links.extend(extract_blocked_by_edges(
        [n for n in nodes if n.get('type') == 'ReviewFinding']))
```

- [ ] **Step 5: Document the edge type**

In `docs/KNOWLEDGE_GRAPH.md`, add a row to the readiness-system edge table:

```
| `BLOCKED_BY` | ReviewFinding | ReviewFinding | This finding waits on another, or on an external release condition | ADR-012 D10 | ✅ — consumer is `build_graph.finding_is_dispatchable` |
```

Extend the existing `SUPERSEDES` note to name `scripts/close_finding.py` as the ledger's writer.

- [ ] **Step 6: Run**

```bash
uv run python -m pytest tests/test_build_graph.py -q
uv run python scripts/validate.py --check graph_integrity --check gate_edge_types_are_emitted
```

Expected: PASS. If any live finding carries a malformed `blocked_by`, the build **raises** — that is the design; fix the finding.

- [ ] **Step 7: Commit**

```bash
git add scripts/build_graph.py docs/KNOWLEDGE_GRAPH.md tests/test_build_graph.py
git commit -m "BLOCKED_BY: the queue becomes a DAG, with a consumer

Four typed fields are a sortable list; a cascade needs edges. Ships with
finding_is_dispatchable as the consumer, because this graph already carries
three edge types that gates query and nothing emits."
```

---

### Task 6: REQUIRED blocks bundle-green, on two ratchets

**Files:**
- Modify: `scripts/validation/checks/bundles_readiness.py` (`check_bundle_stage13_claim_consistent`)
- Test: `tests/test_d5_bundles_readiness.py`

**Interfaces:**
- Produces: `bundles_readiness.REQUIRED_OPEN_BY_BUNDLE: dict[str, int]`, `bundles_readiness.UNATTRIBUTED_OPEN_BLOCKING_CEILING: int`

- [ ] **Step 1: Measure both populations first**

```bash
uv run python - <<'PY'
import sys, collections; sys.path.insert(0,'scripts')
import build_graph as bg
ns = bg.extract_review_finding_nodes()
maj = [n for n in ns if n['meta']['severity'] == 'major' and n['meta']['status'] == 'open']
by = collections.Counter(n['meta'].get('inferred_bundle') for n in maj)
print('REQUIRED_OPEN_BY_BUNDLE =', {k: v for k, v in sorted(by.items()) if k})
unattr = sum(1 for n in ns if n['meta']['status'] == 'open'
             and n['meta']['severity'] in ('critical', 'major')
             and not n['meta'].get('inferred_bundle'))
print('UNATTRIBUTED_OPEN_BLOCKING_CEILING =', unattr)
PY
```

Record both. Measured 2026-08-12: 52 unattributed majors + 19 unattributed criticals = **71**; 15 bundles carry open majors.

- [ ] **Step 2: Write the failing tests**

```python
class TestTheRequiredTier:
    def test_the_check_is_green_at_the_frozen_ceilings(self):
        from validation.checks.bundles_readiness import check_bundle_stage13_claim_consistent
        assert check_bundle_stage13_claim_consistent().passed is True

    def test_both_ratchets_have_zero_headroom(self):
        import sys, collections; sys.path.insert(0, 'scripts')
        import build_graph as bg
        from validation.checks.bundles_readiness import (
            REQUIRED_OPEN_BY_BUNDLE, UNATTRIBUTED_OPEN_BLOCKING_CEILING)
        ns = bg.extract_review_finding_nodes()
        live = collections.Counter(
            n['meta']['inferred_bundle'] for n in ns
            if n['meta']['severity'] == 'major' and n['meta']['status'] == 'open'
            and n['meta'].get('inferred_bundle'))
        for b, c in live.items():
            assert c <= REQUIRED_OPEN_BY_BUNDLE.get(b, 0), (
                f"{b} has {c} open majors against ceiling "
                f"{REQUIRED_OPEN_BY_BUNDLE.get(b, 0)}")
        assert dict(live) == {k: v for k, v in REQUIRED_OPEN_BY_BUNDLE.items() if v}, \
            "ceilings carry headroom — lower them to the live count"
        unattr = sum(1 for n in ns if n['meta']['status'] == 'open'
                     and n['meta']['severity'] in ('critical', 'major')
                     and not n['meta'].get('inferred_bundle'))
        assert unattr == UNATTRIBUTED_OPEN_BLOCKING_CEILING

    def test_the_unattributed_ratchet_is_what_makes_the_per_bundle_one_honest(self, monkeypatch):
        """Seeded: with only a per-bundle ratchet, LOSING attribution leaves the ratchet.
        Raising the unattributed population must go red."""
        import validation.checks.bundles_readiness as br
        monkeypatch.setattr(br, 'UNATTRIBUTED_OPEN_BLOCKING_CEILING', 0)
        assert br.check_bundle_stage13_claim_consistent().passed is False
```

- [ ] **Step 3: Run and watch them fail**

```bash
uv run python -m pytest tests/test_d5_bundles_readiness.py::TestTheRequiredTier -v
```

- [ ] **Step 4: Add the constants and the two legs**

Add at module scope, with the values measured in Step 1:

```python
#: Open `major` (REQUIRED) findings per bundle. **A RATCHET: may only shrink.**
#:
#: ADR-012 D9 mechanizes PD-5, which has said since 2026-07-29 that BLOCKER/MAJOR/
#: IMPORTANT findings are never deferred and which binds no gate. This is NOT a
#: deferral: PD-5 governs the finding you just found (fix it in-session); this governs
#: the POPULATION, which cannot grow. A new major takes its bundle above ceiling and
#: blocks green — PD-5 firing mechanically.
#:
#: Frozen at the live count because a gate that fires on the existing corpus gets
#: switched off (`bundle_source_freshness` under --strict; the pre-ADR-011 figure prefix).
REQUIRED_OPEN_BY_BUNDLE: dict[str, int] = {}   # ← fill from Step 1

#: Open critical+major findings that resolve to NO bundle. **A RATCHET: may only shrink.**
#:
#: ⚠️ THIS IS WHAT MAKES THE PER-BUNDLE RATCHET HONEST. Measured 2026-08-12: 52 of 219
#: open majors (23%) and 19 of 152 open criticals carry no `inferred_bundle` — silent-drop
#: point 1 — so they attach to no ceiling. With only a per-bundle ratchet, a finding that
#: LOSES its attribution silently leaves the ratchet, and "no bundle carries an open major"
#: becomes reachable by degrading attribution rather than by fixing anything. That is
#: absence rendered as success, one level up from where this suite usually catches it.
UNATTRIBUTED_OPEN_BLOCKING_CEILING: int = 71   # ← confirm against Step 1
```

Inside `check_bundle_stage13_claim_consistent`, after the existing blocker leg, add two legs: per-bundle open-major counts against `REQUIRED_OPEN_BY_BUNDLE` (a bundle over ceiling fails, naming the bundle and the delta), and the unattributed count against `UNATTRIBUTED_OPEN_BLOCKING_CEILING`. Reuse the graph the existing leg already built — **do not rebuild it**.

- [ ] **Step 5: Run, then production-seed the mutation**

```bash
uv run python -m pytest tests/test_d5_bundles_readiness.py -q
uv run python scripts/validate.py --check bundle_stage13_claim_consistent
```

Then seed a real extra major into a live review document, confirm the check goes red naming the bundle, and restore.

- [ ] **Step 6: Register the mutation obligation**

In `tests/test_d5_mutation_obligation.py`, update the `MUTATION_VERIFIED` entry for `bundle_stage13_claim_consistent` to name the new test. Do not raise `FIXTURE_ONLY_CEILING`.

- [ ] **Step 7: Commit**

```bash
git add scripts/validation/checks/bundles_readiness.py tests/
git commit -m "REQUIRED blocks bundle-green, on two ratchets

D9 mechanizes PD-5. It EXTENDS bundle_stage13_claim_consistent, which already
forbids a green Stage-13 against live blockers, by adding a severity tier.

Two ratchets, not one: a per-bundle ceiling covers 167 of 219 open majors, and
52 carry no bundle at all. With only the first, a finding that LOSES its
attribution silently leaves the ratchet."
```

---

### Task 7: `close_finding.py` — minting, and the unresolvable-id refusal

**Files:**
- Create: `scripts/close_finding.py`
- Test: `tests/test_close_finding.py`

**Interfaces:**
- Consumes: `build_graph.mint_finding_id` (Task 2)
- Produces: `close_finding.close(doc, sections, status, evidence, commit=None, date=None, verify=None, superseded_by=None, dry_run=False) -> tuple[bool, str]`; `close_finding.ids_for_doc(doc) -> list[str]`; `close_finding.main(argv=None) -> int`

- [ ] **Step 1: Write the failing tests**

```python
"""The ledger writer. Spec: docs/superpowers/specs/2026-08-12-finding-closure-lifecycle-design.md"""
import json
import pytest

DOC = 'papers/AutomatedReviews/2026-08-12-0006-internal-adversarial/I1.md'


class TestTheHappyPath:
    def test_a_resolvable_finding_is_written(self):
        import close_finding as cf
        ok, msg = cf.close(
            doc=DOC, sections=['5.5'], status='fixed',
            evidence='Figure rebuilt from the module dependency edges; every label '
                     'resolves by exact name in lean_deps.json.',
            commit='b0f44815', dry_run=True)
        assert ok is True
        assert 'review:2026-08-12-0006-internal-adversarial:I1:5.5' in msg


class TestTheRefusals:
    def test_an_unresolvable_id_is_refused_and_lists_what_exists(self):
        import close_finding as cf
        ok, msg = cf.close(doc=DOC, sections=['99.99'], status='fixed',
                           evidence='x' * 60, commit='deadbeef', dry_run=True)
        assert ok is False
        assert 'no such finding' in msg.lower()
        assert '5.5' in msg, "the caller must see the real section numbers"

    def test_an_unknown_status_is_refused(self):
        import close_finding as cf
        ok, msg = cf.close(doc=DOC, sections=['5.5'], status='closed',
                           evidence='x' * 60, commit='abc', dry_run=True)
        assert ok is False and 'status' in msg.lower()
```

⚠️ If `…I1.md` section `5.5` no longer exists, pick a live `(doc, section)` from
`bg.extract_review_finding_nodes()` and update `DOC` and the section — do **not** weaken the assertion.

- [ ] **Step 2: Run and watch it fail** — `uv run python -m pytest tests/test_close_finding.py -v`

- [ ] **Step 3: Write `scripts/close_finding.py`**

```python
#!/usr/bin/env python3
"""Write a closure into the supersession ledger — the writer the ledger never had.

`docs/review_finding_supersessions.json` is the ONLY channel that can close a blocking
`ReviewFinding`, and it had no writer. All 870 records were hand-typed, and 66 of the
`review:`-scheme ones carry a `finding_id` matching no minted node — inert, while the
findings they meant to close still read `open`.

Same shape of gap `record_review.py` closed for bundle status, where "every green in the
corpus was therefore a hand edit". Nobody skips a script; people skip a hand-edit.

⚠️ `mint_finding_id` is IMPORTED, never reimplemented. A second minter reproduces the
orphan class by construction.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from datetime import date as _date
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))

import build_graph as _bg  # noqa: E402 — after sys.path setup

LEDGER = PROJECT_ROOT / "docs" / "review_finding_supersessions.json"
VALID_STATUSES = ("fixed", "accepted", "reopened")
CLOSING_STATUSES = ("fixed", "accepted")
MIN_EVIDENCE = 40


def _live_ids() -> set[str]:
    return {n["id"] for n in _bg.extract_review_finding_nodes()}


def ids_for_doc(doc: str) -> list[str]:
    """Every minted id belonging to one review document — for the refusal message."""
    prefix = _bg.mint_finding_id(Path(doc).parent.name, Path(doc).stem, "")
    return sorted(i for i in _live_ids() if i.startswith(prefix))


def close(doc: str, sections: list[str], status: str, evidence: str,
          commit: str | None = None, date: str | None = None,
          verify: str | None = None, superseded_by: str | None = None,
          dry_run: bool = False) -> tuple[bool, str]:
    if status not in VALID_STATUSES:
        return False, f"status={status!r} is not one of {VALID_STATUSES}"

    date_dir, review_name = Path(doc).parent.name, Path(doc).stem
    live = _live_ids()
    minted = [_bg.mint_finding_id(date_dir, review_name, s) for s in sections]
    missing = [m for m in minted if m not in live]
    if missing:
        have = ids_for_doc(doc)
        return False, (f"no such finding: {', '.join(missing)}. This document mints: "
                       f"{', '.join(have) if have else '(none)'}")
    if not dry_run:
        _append(minted, status, evidence, commit, date, None, superseded_by)
    verb = "would write" if dry_run else "wrote"
    return True, f"{verb} {len(minted)} record(s): {', '.join(minted)}"


def _append(minted, status, evidence, commit, date, verified_by, superseded_by) -> None:
    data = json.loads(LEDGER.read_text(encoding="utf-8"))   # re-read immediately before writing
    existing = {e["finding_id"]: e for e in data["supersessions"]}   # last-wins, matching the reader
    for fid in minted:
        prior = existing.get(fid)
        if prior is not None and prior.get("status") == status:
            continue                                        # idempotent
        if prior is not None:
            raise ValueError(
                f"{fid} already carries status={prior.get('status')!r}; refusing to append a "
                f"conflicting {status!r}. The reader is last-wins and does not say so, which is "
                "how a closure silently does nothing. Amend the existing record deliberately.")
        rec = {"finding_id": fid, "status": status, "evidence": evidence,
               "superseded_by": superseded_by,
               "date": date or _date.today().isoformat()}
        if commit:
            rec["commit"] = commit
        if verified_by:
            rec["verified_by"] = verified_by
        data["supersessions"].append(rec)
    _atomic_write(data)


def _atomic_write(data: dict) -> None:
    """⚠️ Temp-and-replace. A crash midway through rewriting the ONLY closure channel
    leaves the malformed-ledger state every reader is told to fail closed on."""
    fd, tmp = tempfile.mkstemp(dir=str(LEDGER.parent), suffix=".tmp")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(data, fh, indent=2, ensure_ascii=False)
            fh.write("\n")
        os.replace(tmp, str(LEDGER))
    except BaseException:
        Path(tmp).unlink(missing_ok=True)
        raise


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--doc", required=True)
    ap.add_argument("--section", required=True, nargs="+")
    ap.add_argument("--status", required=True, choices=VALID_STATUSES)
    ap.add_argument("--evidence", required=True)
    ap.add_argument("--commit")
    ap.add_argument("--date")
    ap.add_argument("--verify")
    ap.add_argument("--superseded-by", dest="superseded_by")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)
    ok, msg = close(a.doc, a.section, a.status, a.evidence, a.commit, a.date,
                    a.verify, a.superseded_by, a.dry_run)
    print(("✓ " if ok else "✗ REFUSED — ") + msg)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
```

- [ ] **Step 4: Run** — `uv run python -m pytest tests/test_close_finding.py -v`. Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add scripts/close_finding.py tests/test_close_finding.py
git commit -m "close_finding: the ledger writer, with the unresolvable-id refusal

Mints from --doc and --section using build_graph's own minter, so a broken key
cannot be produced. On refusal it prints the ids the document DOES mint.
Writes atomically; refuses a conflicting existing record rather than appending
a second one the last-wins reader would silently prefer."
```

---

### Task 8: Evidence, anchor and verify refusals

**Files:**
- Modify: `scripts/close_finding.py`
- Test: `tests/test_close_finding.py`

**Interfaces:**
- Consumes: `close_finding.close` (Task 7)
- Produces: no new names; `close()` gains three refusals and writes `verified_by`.

- [ ] **Step 1: Append the failing tests to `TestTheRefusals`**

```python
    def test_thin_evidence_is_refused(self):
        import close_finding as cf
        ok, msg = cf.close(doc=DOC, sections=['5.5'], status='fixed',
                           evidence='fixed it', commit='b0f44815', dry_run=True)
        assert ok is False and 'evidence' in msg.lower()

    def test_a_closure_with_no_anchor_is_refused(self):
        import close_finding as cf
        ok, msg = cf.close(doc=DOC, sections=['5.5'], status='fixed',
                           evidence='x' * 60, dry_run=True)
        assert ok is False and 'anchor' in msg.lower()

    def test_a_failing_verify_command_is_refused(self):
        import close_finding as cf
        ok, msg = cf.close(doc=DOC, sections=['5.5'], status='fixed', evidence='x' * 60,
                           commit='b0f44815', verify='python3 -c "raise SystemExit(1)"',
                           dry_run=True)
        assert ok is False and 'verify' in msg.lower()

    def test_a_passing_verify_command_is_recorded(self):
        import close_finding as cf
        ok, msg = cf.close(doc=DOC, sections=['5.5'], status='fixed', evidence='x' * 60,
                           commit='b0f44815', verify='python3 -c "pass"', dry_run=True)
        assert ok is True
```

- [ ] **Step 2: Run and watch the four fail**

- [ ] **Step 3: Insert the refusals in `close()`, immediately after the `missing` check**

```python
    if status in CLOSING_STATUSES and len(evidence.strip()) < MIN_EVIDENCE:
        return False, (f"evidence is {len(evidence.strip())} chars; the bar is "
                       f"{MIN_EVIDENCE}. A closure has to say what changed and where.")

    if not (commit or date):
        return False, "no anchor: pass --commit or --date"

    verified_by = None
    if verify:
        proc = subprocess.run(verify, shell=True, cwd=str(PROJECT_ROOT),
                              capture_output=True, text=True)
        if proc.returncode != 0:
            return False, (f"verify command failed (exit {proc.returncode}): {verify}\n"
                           f"{proc.stdout}{proc.stderr}")
        verified_by = {"command": verify, "exit_code": 0,
                       "run_at": _date.today().isoformat()}
```

Then change the write call to `_append(minted, status, evidence, commit, date, verified_by, superseded_by)`. **The positional slot is `verified_by`, not `verify`** — `_append` never receives the raw command.

Add to the module docstring: *`--verify` runs `shell=True` against the repo root. It executes whatever the caller supplies, so it is for operator-authored commands, not untrusted input.*

- [ ] **Step 4: Run** — `uv run python -m pytest tests/test_close_finding.py -v`. Expected: all six PASS.

- [ ] **Step 5: Commit**

```bash
git add scripts/close_finding.py tests/test_close_finding.py
git commit -m "close_finding: evidence, anchor and verify refusals

A --verify command is RUN before the record is written and its result recorded
in verified_by. A ledger record once asserted it had cleaned up duplicate keys
in 57 registry entries that still carry them; one second of machine time would
have caught it."
```

---

### Task 9: Ledger schema, and re-key the nine dead records

**Files:**
- Modify: `docs/review_finding_supersessions.json`
- Modify: `docs/WAVE_EXECUTION_PIPELINE.md` (the append-only rule)

- [ ] **Step 1: Re-key the mechanically re-keyable records**

```bash
uv run python - <<'PY'
import sys, json, re, pathlib; sys.path.insert(0,'scripts')
import build_graph as bg
ids = {n['id'] for n in bg.extract_review_finding_nodes()}
p = pathlib.Path('docs/review_finding_supersessions.json')
data = json.loads(p.read_text())
n = 0
for rec in data['supersessions']:
    fid = rec['finding_id']
    if fid in ids or not fid.startswith('review:'):
        continue
    m = re.match(r'(review:[^:]+:[^:]+:[0-9]+(?:\.[0-9]+)*)', fid)
    if m and m.group(1) in ids:
        rec['finding_id'] = m.group(1)
        rec['notes'] = (str(rec.get('notes') or '') +
                        f' [2026-08-12 re-keyed from {fid}: the suffix was never part of '
                        'any minted id, so this record closed nothing.]').strip()
        n += 1
p.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')
print('re-keyed', n)
PY
```

Record the number. If it is not 9, **re-measure before proceeding** — do not assume.

- [ ] **Step 2: Amend `_entry_format` to match its only reader**

```json
  "_entry_format": {
    "finding_id": "string — the canonical ReviewFinding node ID. Produced by build_graph.mint_finding_id(date_dir, review_name, section_num); write records with scripts/close_finding.py, which mints it for you. NEVER hand-type this: every one of the first 870 records was, and 66 of the review:-scheme ones match no node.",
    "status": "string — one of 'fixed', 'accepted', 'reopened'. An unrecognised token reads as 'open'.",
    "superseded_by": "string|null — review_id of the re-review that confirmed the fix, or a Wave close-doc path. Optional since 2026-08-12: a passing `verified_by` is the supported alternative.",
    "evidence": "string — what changed, where. >= 40 chars at every severity since 2026-08-12.",
    "verified_by": "object|null — {command, exit_code, run_at}. Written by close_finding.py --verify.",
    "date": "ISO-8601 date the supersession was applied",
    "commit": "string|null — commit anchoring the fix. ANY of commit/date/closed_date/applied_at satisfies the bar; before 2026-08-12 this format named only `date` while build_graph accepted all four."
  },
```

- [ ] **Step 3: Record the append-only exception**

In `docs/WAVE_EXECUTION_PIPELINE.md`, beside *"The supersession ledger is append-only"*, add: re-keying a record whose `finding_id` matches no minted node is the one permitted in-place edit, because such a record closes nothing; the former key is preserved in `notes`. Performed once on 2026-08-12.

- [ ] **Step 4: Verify**

```bash
uv run python - <<'PY'
import sys, json; sys.path.insert(0,'scripts')
import build_graph as bg
ids = {n['id'] for n in bg.extract_review_finding_nodes()}
led = json.load(open('docs/review_finding_supersessions.json'))['supersessions']
rev = [r for r in led if r['finding_id'].startswith('review:') and r['finding_id'] not in ids]
print('records', len(led), 'review:-scheme orphans', len(rev))
PY
```

Expected: orphans fell from 66 by the number re-keyed.

- [ ] **Step 5: Commit**

```bash
git add docs/review_finding_supersessions.json docs/WAVE_EXECUTION_PIPELINE.md
git commit -m "ledger: re-key the dead records, document the anchors the reader accepts

Their suffixes (:3.1-residual, :5.1-5.3) match no minted id, so they closed
nothing. _entry_format declared `date` as the only temporal field while
build_graph has always accepted commit/date/closed_date/applied_at."
```

---

### Task 10: The closure bar applies at every severity, and honours `verified_by`

**Files:**
- Modify: `scripts/build_graph.py` (the inline bar)
- Test: `tests/test_closure_guard_bypasses.py`

**Interfaces:**
- Produces: `build_graph._closure_record_meets_bar(rec: dict, finding_has_verify: bool = False) -> bool`

- [ ] **Step 1: Write the failing tests**

```python
class TestTheBarAppliesAtEverySeverity:
    """D12 13.2 — open across four rounds, reproducing at HEAD.

    Gated on severity in ('critical','major','blocker'). Below that line a two-key
    record closed a finding. `- **Severity:**` is body-declarable and beats the heading
    glyph, and _SEVERITY_DECL_MAP maps `recommended` -> `minor`, so a 🔴 heading
    declaring `recommended` closed on {"finding_id": X, "status": "fixed"}.
    """

    def test_a_content_free_record_cannot_close(self):
        import build_graph as bg
        assert bg._closure_record_meets_bar({"finding_id": "x", "status": "fixed"}) is False

    def test_a_complete_record_still_closes(self):
        import build_graph as bg
        assert bg._closure_record_meets_bar(
            {"status": "fixed", "evidence": "y" * 60, "commit": "abc1234"}) is True


class TestVerifiedByIsRequiredWhenAVerifyCommandExists:
    def test_missing_verified_by_fails(self):
        import build_graph as bg
        assert bg._closure_record_meets_bar(
            {"status": "fixed", "evidence": "y" * 60, "commit": "abc"},
            finding_has_verify=True) is False

    def test_a_passing_verified_by_succeeds(self):
        import build_graph as bg
        assert bg._closure_record_meets_bar(
            {"status": "fixed", "evidence": "y" * 60, "commit": "abc",
             "verified_by": {"command": "pytest -q", "exit_code": 0, "run_at": "2026-08-12"}},
            finding_has_verify=True) is True

    def test_a_recorded_nonzero_exit_does_not_close(self):
        import build_graph as bg
        assert bg._closure_record_meets_bar(
            {"status": "fixed", "evidence": "y" * 60, "commit": "abc",
             "verified_by": {"command": "pytest -q", "exit_code": 1, "run_at": "2026-08-12"}},
            finding_has_verify=True) is False
```

- [ ] **Step 2: Run and watch them fail**

- [ ] **Step 3: Extract the predicate to module scope and unscope it**

```python
_CLOSING_STATUSES = ('fixed', 'accepted')


def _closure_record_meets_bar(rec: dict, finding_has_verify: bool = False) -> bool:
    """Does this ledger record justify closing a finding?

    ⚠️ APPLIES AT EVERY SEVERITY since 2026-08-12. It was gated on
    `severity in ('critical','major','blocker')`, which made a below-bar severity a
    closure bypass: declare `- **Severity:** recommended` under a 🔴 heading and a two-key
    record closed the finding. Filed as D12 13.2, open across FOUR rounds, mutating each
    time the previous route was shut — round 11 it was heading-parse closure, round 12
    removed that and left this. **Do not re-scope it.**

    Measured blast radius at the time of the change: ZERO. All 231 non-blocking findings
    then closed carried a record, and every record already met the bar.

    Schema-tolerant deliberately: 264 historical blocking closures use
    (date, evidence, finding_id, status, superseded_by) and 23 use commit/closed_by/
    closed_date. Requiring `commit` would reopen 264 well-formed closures.
    """
    rec = rec or {}
    why = str(rec.get('evidence') or rec.get('note') or rec.get('rationale') or '').strip()
    anchor = any(str(rec.get(k) or '').strip()
                 for k in ('commit', 'date', 'closed_date', 'applied_at'))
    base = bool(rec.get('status') in _CLOSING_STATUSES and len(why) >= 40 and anchor)
    if not base or not finding_has_verify:
        return base
    vb = rec.get('verified_by') or {}
    return vb.get('exit_code') == 0 and bool(str(vb.get('command') or '').strip())
```

Replace the inline bar with:

```python
            if meta.get('status') in _CLOSING_STATUSES:
                if not _closure_record_meets_bar(ledger, bool(meta.get('verify'))):
                    meta['status'] = 'open'
                    meta['blocking_closure_rejected'] = (
                        'ledger record does not meet the closure bar (explicit closing '
                        'status, >=40 chars of rationale, a commit or date, and — when the '
                        'finding carries a verify command — a passing verified_by)')
```

⚠️ `meta['verify']` is populated by Task 4. **This is the coupling that made shipping closure without routing produce a leg that could never fire.**

- [ ] **Step 4: Run and re-measure**

```bash
uv run python -m pytest tests/test_closure_guard_bypasses.py -q
uv run python -c "
import sys,collections; sys.path.insert(0,'scripts'); import build_graph as bg
print(collections.Counter(n['meta']['status'] for n in bg.extract_review_finding_nodes()))"
```

Expected: tests PASS; the `open` count rises by 0 (measured 2026-08-12). **If it rises, stop and report** — the population moved since measurement.

- [ ] **Step 5: Commit**

```bash
git add scripts/build_graph.py tests/test_closure_guard_bypasses.py
git commit -m "build_graph: the closure bar applies at every severity

D12 13.2, open across four rounds and reproducing at HEAD. Also honours
verified_by when the finding carries a verify command — live only because
Task 4 populates meta['verify']."
```

---

### Task 11: Promote `ledger_ids_resolve` out of `graph_integrity`

⚠️ **This check ALREADY EXISTS.** It is a `Detail` leg inside `check_graph_integrity` (`scripts/validation/checks/graph_atlas.py`), pinned at `_LEDGER_DANGLING_BASELINE = 66` with zero headroom, mutation-verified. **ADR-012 D13 permits promotion or widening — never a second check.** This task promotes and **deletes the leg**.

**Files:**
- Modify: `scripts/validation/checks/graph_atlas.py` (delete the leg)
- Modify: `scripts/validation/checks/reviews.py` (the promoted check)
- Modify: `scripts/validate.py` (`_CANONICAL_ORDER`, re-export)
- Modify: `scripts/validation/_config.py` (`CI_MIN_CHECKS_RUN`)
- Modify: `tests/test_d5_mutation_obligation.py`
- Modify: `docs/architecture/SURFACE_INVENTORY.md` (regenerated)
- Test: `tests/test_d5_reviews.py`

**Interfaces:**
- Produces: registered check `ledger_ids_resolve`; `reviews.LEDGER_DANGLING_BASELINE: int`

- [ ] **Step 1: Write the failing tests**

```python
class TestLedgerIdsResolveIsOneCheckNotTwo:
    def test_the_promoted_check_is_green_at_its_baseline(self):
        from validation.checks.reviews import check_ledger_ids_resolve
        assert check_ledger_ids_resolve().passed is True

    def test_the_baseline_has_zero_headroom(self):
        import sys, json; sys.path.insert(0, 'scripts')
        import build_graph as bg
        from validation.checks.reviews import LEDGER_DANGLING_BASELINE
        ids = {n['id'] for n in bg.extract_review_finding_nodes()}
        led = json.load(open('docs/review_finding_supersessions.json'))['supersessions']
        live = len({r['finding_id'] for r in led
                    if r['finding_id'].startswith('review:') and r['finding_id'] not in ids})
        assert live == LEDGER_DANGLING_BASELINE, (
            f"live {live} != baseline {LEDGER_DANGLING_BASELINE}; if the backlog shrank, "
            "LOWER the baseline — headroom makes it unfireable")

    def test_the_leg_is_gone_from_graph_integrity(self):
        """One mechanism, not two (CLAUDE.md rule 1)."""
        import inspect
        from validation.checks import graph_atlas
        assert 'ledger_ids_resolve' not in inspect.getsource(graph_atlas), \
            "the promoted check and its old leg both exist — that is the duplication D13 forbids"
```

- [ ] **Step 2: Run and watch them fail**

- [ ] **Step 3: Move the leg into `scripts/validation/checks/reviews.py` as a registered check**

Move the body verbatim — **including every comment**, which records the 67-vs-66 headroom correction and the retracted false finding. Convert the `Detail`s into a `CheckResult`, keep the `review:`-scheme scoping and its stated reason, and rename `_LEDGER_DANGLING_BASELINE` → module-scope `LEDGER_DANGLING_BASELINE`. Preserve the fail-closed exception handler (`passed=False` on a scan that could not run).

- [ ] **Step 4: Delete the leg from `graph_atlas.py`**, leaving a one-line comment naming where it went and why.

- [ ] **Step 5: Register it — all five obligations, this commit**

1. `validate._CANONICAL_ORDER`: insert `'ledger_ids_resolve'` immediately after `'accepted_findings_carry_rationale'`. **Its absence raises**, taking the suite down.
2. `validate.py`: add `check_ledger_ids_resolve = _checks_reviews.check_ledger_ids_resolve` beside the other reviews re-exports.
3. `tests/test_d5_mutation_obligation.py`: add a `MUTATION_VERIFIED` entry naming the production-seeded test from Step 6. Do **not** touch `AWAITING_MUTATION_TEST` (empty) or raise `FIXTURE_ONLY_CEILING`.
4. `scripts/validation/_config.py`: `CI_MIN_CHECKS_RUN` 76 → 77, with a dated comment.
5. `uv run python scripts/architecture_inventory.py --write`.

- [ ] **Step 6: Production-seeded mutation**

```bash
uv run python - <<'PY'
import json, pathlib
p = pathlib.Path('docs/review_finding_supersessions.json')
d = json.loads(p.read_text())
d['supersessions'].append({"finding_id": "review:9999-99-99-seed:SEED:1.1",
                           "status": "fixed", "evidence": "x"*60, "date": "2026-08-12"})
p.write_text(json.dumps(d, indent=2, ensure_ascii=False) + "\n")
PY
uv run python scripts/validate.py --check ledger_ids_resolve   # expect FAIL, baseline+1
git checkout docs/review_finding_supersessions.json
uv run python scripts/validate.py --check ledger_ids_resolve   # expect PASS
```

- [ ] **Step 7: Full suite**

```bash
uv run python -m pytest -q
uv run python scripts/validate.py --check architecture_inventory_fresh --check graph_integrity
```

- [ ] **Step 8: Commit**

```bash
git add scripts/validation/checks/reviews.py scripts/validation/checks/graph_atlas.py \
        scripts/validate.py scripts/validation/_config.py tests/ \
        docs/architecture/SURFACE_INVENTORY.md
git commit -m "promote ledger_ids_resolve to a registered check, and delete the leg

⚠️ It already existed inside graph_integrity at baseline 66 with zero headroom.
An earlier draft of this work proposed BUILDING it at a ceiling of 247 — the
aggregate over three schemes — which would have been a second mechanism beside
a working one AND weaker: one ratchet over 190 permanently-inert legacy records
plus 57 live ones lets deleting a legacy record buy headroom for a real dangler.

Promoted, not duplicated. Carries all five registration obligations."
```

---

### Task 12: Parked work — release conditions (D19)

**Files:**
- Create: `scripts/parked_items.py`
- Modify: `scripts/build_graph.py` (mint parked nodes)
- Modify: `docs/WAVE_EXECUTION_PIPELINE.md` (the declaration block)
- Test: `tests/test_parked_items.py`

**Interfaces:**
- Produces: `parked_items.parse_parked_blocks(text: str, source: str) -> list[dict]`; `parked_items.release_condition_met(token: str) -> bool | None`

- [ ] **Step 1: Write the failing tests**

```python
BLOCK = """
<!-- PARKED
id: mlx-rhmc-campaign
lane: pyrust
target: docs/RHMC_CAMPAIGN_SEQUENCE.md
blocked_by: run:mlx-rhmc-2026-08
reason: campaign staged; the operator launches it, results gate the analysis wave
-->
"""


class TestParkedBlocks:
    def test_a_block_parses_into_a_queue_item(self):
        from parked_items import parse_parked_blocks
        items = parse_parked_blocks(BLOCK, 'docs/roadmaps/PhaseX_Roadmap.md')
        assert len(items) == 1
        it = items[0]
        assert it['id'] == 'parked:mlx-rhmc-campaign'
        assert it['meta']['lane'] == 'pyrust'
        assert it['meta']['blocked_by'] == ['run:mlx-rhmc-2026-08']
        assert it['meta']['source'] == 'docs/roadmaps/PhaseX_Roadmap.md'

    def test_a_block_missing_a_release_condition_is_rejected(self):
        from parked_items import parse_parked_blocks
        import pytest
        with pytest.raises(ValueError, match='blocked_by'):
            parse_parked_blocks("<!-- PARKED\nid: x\nlane: prose\n-->", 'r.md')

    def test_an_unknown_condition_reads_UNKNOWN_never_met(self):
        from parked_items import release_condition_met
        assert release_condition_met('phase:no-such-phase') is None

    def test_the_live_roadmaps_parse_without_raising(self):
        import pathlib
        from parked_items import parse_parked_blocks
        for p in pathlib.Path('docs/roadmaps').glob('*.md'):
            parse_parked_blocks(p.read_text(errors='ignore'), str(p))
```

- [ ] **Step 2: Run and watch them fail**

- [ ] **Step 3: Write `scripts/parked_items.py`**

Implement `parse_parked_blocks` over `<!-- PARKED … -->` comment blocks with `key: value` lines, requiring `id`, `lane` and `blocked_by`; mint `parked:<id>`; return node dicts shaped like `ReviewFinding` (`{'id', 'type': 'ParkedItem', 'meta': {...}}`) so the same consumers work.

`release_condition_met(token)` returns `True` / `False` / `None` (**cannot determine**):

| scheme | met when |
|---|---|
| `run:<id>` | a completed run with that id is recorded |
| `phase:<id>` | the named roadmap carries a close marker |
| `pub:<citekey>` | the key resolves in `CITATION_REGISTRY` with a non-`inprep` entry |
| `research:<task>` | a file with that name exists under `Lit-Search/Tasks/complete/` |

⚠️ **`None` is not `False`.** An unresolvable condition is reported as *cannot determine*, never as *not met* — the distinction the whole suite exists to preserve.

- [ ] **Step 4: Document the block in `docs/WAVE_EXECUTION_PIPELINE.md`**

One subsection under Stage 14 giving the block's shape, the four schemes, and the rule that a parked item **must** name a release condition. State that roadmaps are otherwise untouched and that the roadmap layer remains ungated (`END_TO_END_MAP.md` §2).

- [ ] **Step 5: Run** — `uv run python -m pytest tests/test_parked_items.py -q`

- [ ] **Step 6: Commit**

```bash
git add scripts/parked_items.py tests/test_parked_items.py docs/WAVE_EXECUTION_PIPELINE.md
git commit -m "parked work: a release condition is a first-class blocker

The pattern is already in the roadmaps in several prose dialects, readable by
nothing, and every instance names a release condition. Opt-in block; the 119
roadmap files are untouched until something is parked deliberately.

There is no operator: scheme — an operator decision that gates work is itself a
queue item with a node id, so parking behind it is the plain node-id case."
```

---

### Task 13: Per-finding orientation brief (D17)

**Files:**
- Modify: `scripts/review_runner.py`
- Test: `tests/test_review_runner.py`

**Interfaces:**
- Consumes: `meta['target']` (Task 3)
- Produces: `review_runner.emit_finding_brief(finding_id: str) -> str`; CLI `--finding <id>`

- [ ] **Step 1: Write the failing test**

```python
class TestPerFindingBrief:
    def test_the_brief_names_the_target_and_its_provenance(self):
        import sys; sys.path.insert(0, 'scripts')
        import build_graph as bg
        from review_runner import emit_finding_brief
        cand = [n for n in bg.extract_review_finding_nodes()
                if n['meta'].get('target') and n['meta']['status'] == 'open']
        assert cand, "no open finding carries a target — the seam is empty"
        out = emit_finding_brief(cand[0]['id'])
        assert cand[0]['meta']['target'] in out
        for heading in ('TARGET', 'LANE', 'GIT HISTORY', 'ROADMAP'):
            assert heading in out

    def test_an_unknown_finding_id_raises_rather_than_emitting_an_empty_brief(self):
        import pytest
        from review_runner import emit_finding_brief
        with pytest.raises(KeyError):
            emit_finding_brief('review:no-such:X:1.1')
```

- [ ] **Step 2: Run and watch it fail**

- [ ] **Step 3: Implement `emit_finding_brief`**

Resolve the finding, then emit sections: `TARGET` (the `Location:` value, with the file read if it resolves), `LANE`, `BLOCKS`, `VERIFY`, `BLOCKED-BY`, `GIT HISTORY` (`git log -5 --oneline -- <path>` when the target names a path), `ROADMAP` (the roadmap that mentions the target, if one does), and `LEAN` (declarations from `lean_deps.json` when the target names a module). **Raise `KeyError` on an unknown id** — an empty brief is worse than an error.

- [ ] **Step 4: Add `--finding <id>` to the CLI**, beside `--prep-brief`.

- [ ] **Step 5: Run** — `uv run python -m pytest tests/test_review_runner.py -q`

- [ ] **Step 6: Commit**

```bash
git add scripts/review_runner.py tests/test_review_runner.py
git commit -m "review_runner: per-finding orientation brief

D17 — orientation is generated, not gathered. The finding carries its pointers;
the worker does not go looking. This is also what makes the decision package
affordable: four of its five elements are generated rather than researched."
```

---

### Task 14: Write the pilot's closure records through the writer

**Files:**
- Modify: `docs/review_finding_supersessions.json` (via `close_finding.py` only)
- Create: `docs/audits/2026-08-12-critical-triage/refusals.md`

- [ ] **Step 1: Re-derive the population — do not inherit 117/98**

```bash
uv run python - <<'PY'
import sys, json, pathlib, collections; sys.path.insert(0,'scripts')
import build_graph as bg
rows = json.loads(pathlib.Path('docs/audits/2026-08-12-critical-triage/manifest.json').read_text())
ids = {n['id'] for n in bg.extract_review_finding_nodes()}
print(collections.Counter(r['disposition'] for r in rows))
print('rows whose id no longer resolves:', sum(1 for r in rows if r['id'] not in ids))
print('rows with <40 char evidence:', sum(1 for r in rows if len(str(r['evidence']).strip()) < 40))
PY
```

Any non-zero in the last two lines is a **stop-and-report**, not a workaround.

- [ ] **Step 2: Drive the manifest through the writer, in-process**

```bash
uv run python - <<'PY'
import sys, json, pathlib; sys.path.insert(0,'scripts')
import close_finding as cf
rows = json.loads(pathlib.Path('docs/audits/2026-08-12-critical-triage/manifest.json').read_text())
todo = [r for r in rows if r['disposition'] in ('fixed', 'superseded', 'not-a-defect')]
ok, refused = 0, []
for r in todo:
    status = 'fixed' if r['disposition'] == 'fixed' else 'accepted'
    good, msg = cf.close(doc=r['file'], sections=[r['section']], status=status,
                         evidence=r['evidence'], date='2026-08-12')
    if good: ok += 1
    else: refused.append((r['id'], msg))
print('written', ok, 'refused', len(refused))
for fid, m in refused: print('  REFUSED', fid, '—', m)
PY
```

⚠️ **In-process, not 98 subprocesses.** Each `uv run` pays interpreter startup plus a full corpus extraction.

- [ ] **Step 3: Triage every refusal — do NOT force any**

Record each in `docs/audits/2026-08-12-critical-triage/refusals.md` with its reason. **Evidence under 40 characters means the disposition was too thin to justify a closure and needs rewriting, not bypassing.** This whole thread began with a ledger containing a false closure.

- [ ] **Step 4: Re-derive every downstream artifact the closures moved**

```bash
uv run python scripts/bundle_readiness.py          # rewrites metadata counts + the heatmap
uv run python scripts/validate.py --check bundle_metadata_matches_graph \
    --check bundle_stage13_claim_consistent --check readiness_verdicts_agree \
    --check recurrence_reopens_closures --check ledger_ids_resolve
```

⚠️ `blockers_open` / `open_findings` / `readiness` are written **only** by `bundle_readiness.write_metadata_counts`. Skipping this leaves `bundle_metadata_matches_graph` red.

- [ ] **Step 5: Lower any ratchet whose population fell**

`LEDGER_DANGLING_BASELINE`, `REQUIRED_OPEN_BY_BUNDLE`, `UNATTRIBUTED_OPEN_BLOCKING_CEILING`. Lower in **this** commit; never raise.

- [ ] **Step 6: Commit**

```bash
git add docs/review_finding_supersessions.json docs/audits/2026-08-12-critical-triage/refusals.md \
        docs/BUNDLE_READINESS_HEATMAP.md papers/*/bundle_metadata.json \
        scripts/validation/checks/reviews.py scripts/validation/checks/bundles_readiness.py
git commit -m "ledger: record the ADR-012 pilot's dispositions through the writer

The findings were repaired and never recorded; that recording gap IS the
backlog. Written last, after the bar's severity bypass was closed, so no
closure rests on a bar that could be walked around."
```

---

### Task 15: Architecture documents, and the full gate

**Files:**
- Modify: `docs/architecture/END_TO_END_MAP.md`, `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md`, `docs/adrs/ADR-012-…md`
- Regenerate: `docs/architecture/SURFACE_INVENTORY.md`

- [ ] **Step 1: `END_TO_END_MAP.md` — re-route the writer edge**

Line 43 reads `HUMAN -.->|"supersession ledger"| GATE`, accurate until Task 7. Replace with an explicit ledger node written by `close_finding.py`. In §8's promotion path, add the REQUIRED tier: a `major` open finding blocks `stage13_status: green`, ratcheted per bundle, with the unattributed population separately ratcheted.

- [ ] **Step 2: `QA_QI_INFRASTRUCTURE_MAP.md` — name the writer and the new drop points**

In the §3 diagram, the ledger node becomes `written by close_finding.py`. Add to the silent-drop list: a `blocked_by` naming no node now **raises** rather than dropping, and a finding with no `inferred_bundle` attaches to no bundle ratchet (**counted**, by `UNATTRIBUTED_OPEN_BLOCKING_CEILING`). **State mechanisms, not counts** — rule 3.

- [ ] **Step 3: ADR-012 — mark the phases that landed**

P1, P4, P5, P6, P7, P8b and D17 → ✅, each naming its commit. Leave P8, P8c, P8d, P9, P10, P11 as-is.

- [ ] **Step 4: Regenerate and gate**

```bash
uv run python scripts/architecture_inventory.py --write
uv run python -m pytest -m '' -q
uv run python scripts/validate.py
uv run python scripts/verify_scope.py --merge-gate
```

Expected: `architecture_inventory_fresh` PASSES; the suite is no worse than the pre-branch baseline. **Record any check that was already red on `main` before the branch** — do not claim a pre-existing red as new, or a new red as pre-existing.

- [ ] **Step 5: Commit**

```bash
git add docs/architecture/ docs/adrs/ADR-012-finding-lifecycle-routing-and-closure.md
git commit -m "docs: the ledger has a writer, findings route, and REQUIRED blocks green

END_TO_END_MAP modelled the writer as HUMAN — accurate until this branch."
```

---

## Self-Review

**Spec coverage.** §1 emission/extraction → Tasks 3, 4, 5, 13. §2 gating → Task 6. §3 operator path → Task 4 (`needs_operator` field); the panes are the dashboard plan. §4 closure → Tasks 7, 8, 9, 10, 11. §5.1 parked → Task 12. §5.2/§5.3 → dashboard plan, declared out of scope above. §6 loop terminus → Task 15 plus the branch merge. Doc-update table → Tasks 1, 5, 9, 12, 15.

**Placeholders.** None. Two tasks (11, 12) direct a *move* and a *parser* rather than pasting a body: Task 11 must move existing code verbatim including its comments (pasting a paraphrase would lose the 67-vs-66 correction), and Task 12's four resolvers each read a different artifact. Both carry their full test bodies and their exact interfaces.

**Type consistency.** `mint_finding_id(date_dir, review_name, section_num) -> str` — Task 2, used in 7 and 11. `_parse_finding_field(body, label) -> str | None` — Task 3, used in 4. `_LANE_DECL_MAP`, `_RELEASE_SCHEMES` — Task 4, used in 5. `extract_blocked_by_edges(nodes) -> list[dict]` and `finding_is_dispatchable(node, ids, closed) -> bool` — Task 5. `close(...) -> tuple[bool, str]` — Task 7, extended in 8 **without** signature change; `_append`'s sixth positional is `verified_by`, and Task 8 Step 3 states the call-site change explicitly. `_closure_record_meets_bar(rec, finding_has_verify=False) -> bool` — Task 10, both tests and the call site pass the second argument.

**Ordering.** Task 10's `verified_by` leg reads `meta['verify']`, populated by Task 4 — routing before closure, which is the coupling that made the superseded plan ship a leg that could never fire. Task 14 runs after Task 10 so no closure rests on a bypassable bar, and after Task 6 so its ratchets exist to be lowered.

**Gaps found and fixed during review:** Task 14 originally omitted `bundle_readiness.py`, leaving `bundle_metadata_matches_graph` red; Step 4 now runs it. Task 11 originally omitted the `graph_atlas.py` deletion, which would have left two mechanisms — the exact defect the task exists to prevent; Step 4 and a test now enforce it.
