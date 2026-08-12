# P9a — Operator Control Surface, Wave A

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the dashboard tell the operator the truth about what is blocking a gate, make its sign-off button actually persist, and un-saturate the QI derivation so the recurrent-failure detector can emit again.

**Architecture:** Three independent repairs plus the test gate they all need. S1 turns a gate's blockers from prose into references, which is an *evaluator* change, not a render change — the finding id is destroyed in `readiness_gates.py` before the graph ever sees it. The sign-off repair extracts the one thing that does not exist today: a per-entry writer for `human_verified_date`. The QI repair changes an id scheme that structurally caps the register at eleven items forever. Nothing here invents a subsystem; each replaces a lossy step with a lossless one.

**Tech Stack:** Python 3.14, Flask + Datastar SSE, Jinja2 templates on disk, pytest, Playwright (`-m e2e`).

**Implements:** ADR-012 P9a — D15 S1, D15 S4, the QI de-saturation and the sign-off persistence repair. **Out of scope:** S2 the Flow board and S3 Attention (P9b), the Loops pane (P9c), orchestration (P10).

**ADR:** [`../../adrs/ADR-012-finding-lifecycle-routing-and-closure.md`](../../adrs/ADR-012-finding-lifecycle-routing-and-closure.md) §D15, §D20.

## Global Constraints

- **Branch:** all implementation lands on `feat/adr012-p9a-control-surface`, cut from `main` after the ADR-012 branch merges.
- **Dashboard changes carry two extra gates** (ADR-012 D2): a **template-contract test** and a **real browser test**. ⚠️ The browser gate is infrastructure that already exists — `tests/e2e/`, 13 files, `conftest.py` boots the real dashboard on an ephemeral port and collects console errors. It is excluded from the default run; invoke with `-m e2e`. The template-contract gate does **not** exist and Task 7 builds it.
- **A Flask `test_client` never executes page JavaScript.** It is necessary and not sufficient. No task may treat a `test_client` assertion as evidence that a panel renders.
- **No silent caps** (`CLAUDE.md`). Two exist in this path today and both must be disclosed rather than removed blindly: `readiness_gates.py:911` truncates blockers to `[:10]`, `to_node_payload` (`:104`) to `[:50]`. A truncated list must say it is truncated.
- **Never write a census count into a `docs/architecture/` narrative** (rule 3).
- **Architecture docs land in the commit that makes them wrong** (rule 2), never batched.
- Run everything from `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking`.
- The dashboard builds its graph in-process via `build_graph_json(sync_pg=False)` (`provenance_dashboard.py:308`) behind an mtime fingerprint cache (`:204`). Any new input file a task reads **must be added to `_graph_fingerprint`'s stat list** (`:210-235`) or the panel will serve stale data with no way to tell.

## File Structure

| file | responsibility | tasks |
|---|---|---|
| `scripts/readiness_gates.py` | `GateResult` carries blocker IDs; `_eval_fix_propagation` stops discarding them | 1, 2 |
| `scripts/provenance_dashboard.py` | render the drill-through; call the new provenance writer; sentence markers | 3, 6, 8 |
| `scripts/templates/partials/readiness_tab.html` | the focus pane's blocker list | 3 |
| `src/core/provenance_writer.py` | **new** — the only per-entry writer for `human_verified_date` | 5 |
| `scripts/wave2_flip_provenance.py` | becomes a caller of that writer, not a second implementation | 5 |
| `scripts/qi_register.py` | the id scheme, and the `unclassified` bucket | 4 |
| `tests/test_template_contract.py` | **new** — the missing dashboard gate | 7 |
| `tests/e2e/test_readiness_drilldown.py` | **new** — browser proof for S1 | 3 |
| `tests/e2e/test_paper_provenance_markers.py` | **new** — browser proof for S4 | 8 |

---

### Task 1: `GateResult` can carry a blocker's identity

**Files:**
- Modify: `scripts/readiness_gates.py:60-108` (`GateResult`, `to_node_payload`)
- Test: `tests/test_readiness_gates.py`

**Interfaces:**
- Produces: `GateResult.blocker_refs: list[dict]` — each `{'id': str, 'label': str, 'severity': str, 'lane': str, 'status': str}`. **`blockers: list[str]` is unchanged and stays the human-readable list**; `blocker_refs` is additive, so all eleven evaluators keep working untouched and only the ones with a node in hand populate it.

- [ ] **Step 1: Write the failing test**

```python
def test_a_gate_result_can_carry_the_identity_of_what_blocks_it():
    """⚠️ `blockers` is prose and always has been. A drill-through needs the id, and the
    evaluator is the ONLY place that still has it — `_eval_fix_propagation` holds the whole
    ReviewFinding dict and keeps `f['label'][:60]`."""
    from scripts.readiness_gates import GateResult
    r = GateResult(gate='FixPropagation', paper='D1')
    r.blocker_refs = [{'id': 'review:d:X:1', 'label': 'x', 'severity': 'major',
                       'lane': 'prose', 'status': 'open'}]
    payload = r.to_node_payload()
    assert payload['blocker_refs'][0]['id'] == 'review:d:X:1'

def test_a_truncated_blocker_list_SAYS_it_is_truncated():
    """No silent caps. `blockers[:10]` and `[:50]` both exist in this path today."""
    from scripts.readiness_gates import GateResult
    r = GateResult(gate='FixPropagation', paper='D1')
    r.blocker_refs = [{'id': f'review:d:X:{i}', 'label': str(i), 'severity': 'major',
                       'lane': 'prose', 'status': 'open'} for i in range(60)]
    payload = r.to_node_payload()
    assert payload['blocker_refs_truncated'] is True
    assert payload['blocker_refs_total'] == 60
```

- [ ] **Step 2: Run it and watch it fail**

Run: `uv run python -m pytest tests/test_readiness_gates.py -k "blocker" -v`
Expected: FAIL — `GateResult` has no attribute `blocker_refs`.

- [ ] **Step 3: Add the field and serialize it**

In the `GateResult` dataclass beside `blockers: list[str]`:

```python
    #: Identity of each blocker, when the evaluator had a node in hand.
    #: ⚠️ ADDITIVE. `blockers` stays the prose list every evaluator already builds, so the
    #: other ten need no change. Only evaluators that resolve real nodes populate this.
    blocker_refs: list[dict] = field(default_factory=list)
```

In `to_node_payload()`, beside `'blockers': self.blockers[:50]`:

```python
        # ⚠️ DISCLOSE THE CAP. `blockers[:50]` has silently truncated since this method was
        # written; a reader cannot tell a paper with 50 blockers from one with 500.
        'blockers': self.blockers[:50],
        'blockers_total': len(self.blockers),
        'blockers_truncated': len(self.blockers) > 50,
        'blocker_refs': self.blocker_refs[:50],
        'blocker_refs_total': len(self.blocker_refs),
        'blocker_refs_truncated': len(self.blocker_refs) > 50,
```

- [ ] **Step 4: Run to green**

Run: `uv run python -m pytest tests/test_readiness_gates.py -k "blocker" -v`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add scripts/readiness_gates.py tests/test_readiness_gates.py
git commit -m "readiness_gates: a gate can name what blocks it, and says when it truncated"
```

---

### Task 2: `_eval_fix_propagation` stops throwing the id away

**Files:**
- Modify: `scripts/readiness_gates.py:859-925` (`_eval_fix_propagation`)
- Test: `tests/test_readiness_gates.py`

**Interfaces:**
- Consumes: `GateResult.blocker_refs` from Task 1.

- [ ] **Step 1: Write the failing test**

```python
def test_fix_propagation_keeps_the_finding_id_it_already_has():
    """⚠️ `readiness_gates.py:911` reads
        r.blockers = [f'{f.get("label","?")[:60]}' for f in blocking[:10]]
    It holds the entire ReviewFinding — id, severity, lane, target — and keeps 60 characters
    of label. That single line is why a blocker cell has nothing to drill through to, and why
    the 4,879 FLAGS edges are invisible to the operator."""
    import scripts.readiness_gates as rg
    res = [g for g in rg.evaluate_all_gates()
           if g.gate == 'FixPropagation' and g.state == 'blocked']
    assert res, "no blocked FixPropagation gate in the live corpus — pick another fixture"
    g = res[0]
    assert g.blocker_refs, "blocked on findings but named none of them"
    assert all(r['id'].startswith('review:') for r in g.blocker_refs)
    # the prose list is preserved for humans, and the two agree in length
    assert len(g.blocker_refs) == len(g.blockers)
```

- [ ] **Step 2: Run it and watch it fail**

Run: `uv run python -m pytest tests/test_readiness_gates.py -k "keeps_the_finding_id" -v`
Expected: FAIL — `blocker_refs` empty.

- [ ] **Step 3: Populate it at both sites**

Replace the two list comprehensions (the `if blocking:` branch at `:911` and the `elif open_findings:` branch at `:918`) so each keeps the node beside the prose:

```python
    def _refs(findings):
        return [{'id': f.get('id', ''),
                 'label': str(f.get('label', '?'))[:60],
                 'severity': str((f.get('meta') or {}).get('severity', '')),
                 'lane': str((f.get('meta') or {}).get('lane', 'unclassified')),
                 'status': str((f.get('meta') or {}).get('status', 'open'))}
                for f in findings]

    if blocking:
        # ⚠️ The [:10] cap stays but is now disclosed by `blocker_refs_total`. Removing it
        # here would put 34 rows into a gate cell; hiding it is what made 24 of them vanish.
        r.blockers = [x['label'] for x in _refs(blocking[:10])]
        r.blocker_refs = _refs(blocking[:10])
```

Apply the same shape to the `elif open_findings:` branch.

- [ ] **Step 4: Run to green, and confirm the graph carries it**

```bash
uv run python -m pytest tests/test_readiness_gates.py -k "keeps_the_finding_id" -v
uv run python -c "
import sys; sys.path.insert(0,'scripts')
import build_graph as bg
gs=[g for g in bg.extract_readiness_gate_nodes() if (g['meta'] or {}).get('blocker_refs')]
print('gates naming their blockers:', len(gs))
"
```
Expected: PASS, and a non-zero count.

- [ ] **Step 5: Commit**

```bash
git add scripts/readiness_gates.py tests/test_readiness_gates.py
git commit -m "FixPropagation: keep the finding id the evaluator already holds"
```

---

### Task 3: The blocker drills through (S1)

**Files:**
- Modify: `scripts/provenance_dashboard.py:5199` (carry the field), `:5413-5418` (render it)
- Test: `tests/e2e/test_readiness_drilldown.py` (create)

- [ ] **Step 1: Write the browser test first**

```python
import pytest
pytestmark = pytest.mark.e2e


def test_a_blocker_names_the_finding_it_came_from(page, dashboard_url):
    """⚠️ A `test_client` cannot see this: the focus pane arrives over Datastar SSE and is
    morphed in by JS. The old assertion `'Blockers' in html` passed while every entry was an
    unlinkable 60-char prose fragment."""
    page.goto(f"{dashboard_url}/?tab=readiness")
    page.wait_for_selector(".blockers li", timeout=15000)
    first = page.locator(".blockers li").first
    assert first.get_attribute("data-finding-id", "").startswith("review:")


def test_a_truncated_blocker_list_says_so(page, dashboard_url):
    page.goto(f"{dashboard_url}/?tab=readiness")
    page.wait_for_selector(".blockers", timeout=15000)
    note = page.locator(".blockers-truncated")
    if note.count():
        assert "of" in note.first.inner_text()
```

- [ ] **Step 2: Run it and watch it fail**

Run: `uv run python -m pytest tests/e2e/test_readiness_drilldown.py -m e2e -v`
Expected: FAIL — no `data-finding-id` attribute.

- [ ] **Step 3: Carry the field through the dashboard's data build**

At `provenance_dashboard.py:5199`, beside `'blockers': m.get('blockers', [])`:

```python
            'blockers': m.get('blockers', []),
            'blocker_refs': m.get('blocker_refs', []),
            'blockers_total': m.get('blockers_total'),
            'blockers_truncated': m.get('blockers_truncated', False),
```

⚠️ `_paper_gate_list()` at `:5225` pads absent gates with `'blockers': []`; give the filler `'blocker_refs': []` too, or the pad and the real row have different shapes and the template must branch.

- [ ] **Step 4: Render the reference**

Replace the `<li>` loop at `:5413-5418`:

```python
    refs = g.get('blocker_refs') or []
    if refs:
        parts.append('<div><strong>Blockers</strong><ul class="blockers">')
        for b in refs:
            parts.append(
                f'<li data-finding-id="{esc(b["id"])}" '
                f'data-lane="{esc(b.get("lane", "unclassified"))}">'
                f'<span class="sev sev--{esc(b.get("severity", ""))}">'
                f'{esc(b.get("severity", ""))}</span> {esc(b["label"])}</li>')
        parts.append('</ul>')
        if g.get('blockers_truncated'):
            parts.append(f'<p class="blockers-truncated">showing {len(refs)} '
                         f'of {esc(str(g.get("blockers_total")))}</p>')
        parts.append('</div>')
    elif g.get('blockers'):
        # A gate whose evaluator has no node to name — prose only, and SAY that, so an
        # un-drillable blocker is visibly a different thing from a drillable one.
        parts.append('<div><strong>Blockers</strong> <em>(no finding reference — this '
                     'gate reports prose)</em><ul class="blockers">')
        for b in g['blockers']:
            parts.append(f'<li>{esc(b)}</li>')
        parts.append('</ul></div>')
```

- [ ] **Step 5: Run both gates**

```bash
uv run python -m pytest tests/e2e/test_readiness_drilldown.py -m e2e -v
uv run python -m pytest tests/test_graph_dashboard.py -q
```
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add scripts/provenance_dashboard.py tests/e2e/test_readiness_drilldown.py
git commit -m "dashboard: a gate blocker drills through to its finding"
```

---

### Task 4: Un-saturate the QI derivation

**Files:**
- Modify: `scripts/qi_register.py:117-200`
- Test: `tests/test_qi_register.py`

**The measured diagnosis — do not re-derive it, but do re-measure before acting.** `qi_id = f'qi-{gate.lower()}'` derives the id **solely** from the gate name, so the register can hold at most one item per gate for all time. There are 11 gate keys, 9 are already in `## Closed Items` and can never re-emit, and the 2 survivors are `FirstClaimVerification` (0 open findings) and `FixPropagation` (1 finding → 1 paper, below the `len(papers) < 2` threshold). Separately, **233 open findings classify as `unclassified` and are dropped at `:165`** — the largest single bucket, larger than any gate. That is why 1,631 findings produce 0 items.

⚠️ **Invariant #13 preserves `## Closed Items` verbatim.** This task must not regenerate them, and must not reopen a closed item merely because its gate recurs — a closure is per-occurrence, not per-gate-forever.

- [ ] **Step 1: Write the failing tests**

```python
def test_the_id_is_not_the_gate_name_alone():
    """⚠️ THE SATURATION. `qi-{gate}` caps the register at one item per gate FOREVER; once
    closed, that failure class can never be detected again. Nine of eleven are already
    closed, which is why the detector emits nothing."""
    import scripts.qi_register as q
    ids = {q.qi_id_for(gate='CitationIntegrity', papers=['D1', 'D2'], window='2026-08'),
           q.qi_id_for(gate='CitationIntegrity', papers=['D5', 'D7'], window='2026-08')}
    assert len(ids) == 2, "two distinct recurrences collapsed onto one id"


def test_unclassified_findings_are_REPORTED_not_dropped():
    """The largest bucket is the one the detector discards. A recurrence the keyword map
    cannot name is still a recurrence, and silence about it reads as 'nothing there'."""
    import scripts.qi_register as q
    stats = q.derive_stats()
    assert stats['unclassified_open'] > 0
    assert stats['unclassified_reported'] is True


def test_a_closed_item_is_not_reopened_by_the_same_gate_recurring():
    """Invariant #13. Closure is per-occurrence; a new occurrence gets a NEW id."""
    import scripts.qi_register as q
    closed, _ = q.load_closed_qi_ids()
    items = q.cluster_findings(q.load_review_findings())
    assert not ({i['id'] for i in items} & closed)


def test_the_derivation_is_not_saturated():
    """The end-to-end assertion: a corpus with 1,631 findings and 233 unclassified must not
    produce zero items."""
    import scripts.qi_register as q
    assert q.cluster_findings(q.load_review_findings()), "derivation still saturated"
```

- [ ] **Step 2: Run and watch them fail**

Run: `uv run python -m pytest tests/test_qi_register.py -v`
Expected: FAIL — `qi_id_for` and `derive_stats` do not exist; the last test fails on an empty list.

- [ ] **Step 3: Give an occurrence its own identity**

```python
def qi_id_for(gate: str, papers: list[str], window: str) -> str:
    """A QI item identifies a RECURRENCE, not a gate.

    ⚠️ The id was `qi-{gate}`, which meant the register could hold one item per gate for all
    time — and closing it retired that failure class permanently. Nine of eleven gates were
    closed, so the detector the operator asked for was switched off by its own success.
    The occurrence's papers and window are what make two recurrences distinguishable.
    """
    key = f'{gate}|{"+".join(sorted(papers))}|{window}'
    return f'qi-{gate.lower()}-{hashlib.sha1(key.encode()).hexdigest()[:8]}'
```

Replace the `qi_id = f'qi-{gate.lower()}'` line at `:168` with a call to it, passing the cluster's papers and a window derived from the findings' `review_date`.

- [ ] **Step 4: Report the unclassified bucket instead of dropping it**

At `:165`, replace `if gate == 'unclassified': continue` with an accumulation into a reported total, and add:

```python
def derive_stats() -> dict:
    """What the derivation SAW, including what it could not classify.

    ⚠️ `unclassified` is the largest bucket in the corpus. Skipping it silently is the
    difference between 'no recurrent failure modes' and 'the detector cannot name them'.
    """
```

- [ ] **Step 5: Run to green and re-measure**

```bash
uv run python -m pytest tests/test_qi_register.py -v
uv run python scripts/qi_register.py --stats
```
Expected: PASS, and `qi_items_detected` > 0 with `unclassified_open` reported.

- [ ] **Step 6: Commit**

```bash
git add scripts/qi_register.py tests/test_qi_register.py
git commit -m "qi_register: an item identifies a recurrence, not a gate"
```

---

### Task 5: A per-entry provenance writer, shared by both callers

**Files:**
- Create: `src/core/provenance_writer.py`
- Modify: `scripts/wave2_flip_provenance.py:105-178` (become a caller)
- Test: `tests/test_provenance_writer.py`

**The measured diagnosis.** There is **no** per-entry writer for `human_verified_date`. The dashboard's `/verify` (`provenance_dashboard.py:1241`) mutates the imported module dict in memory and writes only `docs/verification_log.jsonl`; a page refresh silently reverts the green badge, which is visually identical to a genuinely persisted one. The only file-writing route is `wave2_flip_provenance.py:178`, a bulk regex sweep with a **frozen `VERIFY_DATE = "2026-04-28"`** — so it would stamp a parameter verified today with a date months in the past, and it records no audit event. The two halves are disjoint: the dashboard writes the event, the script writes the field.

- [ ] **Step 1: Write the failing test**

```python
def test_one_entry_is_written_to_the_source_file(tmp_path, monkeypatch):
    from src.core.provenance_writer import set_human_verified
    ok, msg = set_human_verified(key='TEST_KEY', date='2026-08-12',
                                 notes='confirmed against CODATA', dry_run=True)
    assert ok is True, msg


def test_the_date_is_a_PARAMETER_not_a_module_constant():
    """⚠️ `wave2_flip_provenance.VERIFY_DATE` is frozen at 2026-04-28. A writer that stamps
    today's confirmation with a date from four months ago is worse than one that refuses."""
    import inspect
    from src.core import provenance_writer
    assert 'date' in inspect.signature(provenance_writer.set_human_verified).parameters


def test_the_bulk_script_CALLS_the_writer_rather_than_reimplementing_it():
    """Two implementations of one write is how they drift — the defect this repo hits most.
    Precedent: `mint_finding_id`, shared by the extractor and `close_finding`.

    ⚠️ VIA `ast`, ASSERTING THE CALL. `CHECK_AUTHORING_GUIDE.md` §2.5 — a substring scan for
    the helper's name finds it in a comment and passes over a seeded regression. The first
    draft of this very test was a substring scan.
    """
    import ast
    tree = ast.parse((PROJECT_ROOT / 'scripts' / 'wave2_flip_provenance.py')
                     .read_text(encoding='utf-8'))
    called = {c.func.id if isinstance(c.func, ast.Name) else
              c.func.attr if isinstance(c.func, ast.Attribute) else None
              for c in ast.walk(tree) if isinstance(c, ast.Call)}
    assert 'set_human_verified' in called, "the bulk script does not call the shared writer"
    # …and it no longer writes the file itself: no `.write_text(` call survives.
    assert 'write_text' not in called, "the bulk script still writes provenance.py itself"
```

- [ ] **Step 2: Run and watch fail**

Run: `uv run python -m pytest tests/test_provenance_writer.py -v`
Expected: FAIL — module does not exist.

- [ ] **Step 3: Write the writer**

`src/core/provenance_writer.py` exposes `set_human_verified(key, date, notes, actor=None, dry_run=False) -> tuple[bool, str]`, rewriting exactly one entry's `human_verified_date`/`human_verified_notes` in `src/core/provenance.py`, atomically (temp-and-replace, as `close_finding._atomic_write` does), refusing an unknown key and refusing to overwrite an existing non-null date without an explicit `force`.

⚠️ **`wave2_flip_provenance`'s regex only matches an entry currently holding `None`.** `HUMAN_NULL_RE` requires the literal pair `'human_verified_date': None,` / `'human_verified_notes': None,`, so the existing route cannot *revise* a verified entry at all — only flip a null one. The new writer must handle both, which is why `force` exists rather than being defensive scaffolding. Measured at HEAD, not inherited from the ADR.

- [ ] **Step 3b: Update `VALIDATION_GATE_TOPOLOGY.md` §6 IN THIS COMMIT**

§6 is the field-ownership table and it now carries a `human_verified_date` row stating that **nothing writes it per entry**, with the two disjoint halves named. That row was added ahead of this plan (rule 2: the design lands in the doc first) and deliberately does **not** name `src/core/provenance_writer.py`, because `architecture_inventory_fresh` requires every path-like reference to resolve and the file does not exist yet — a fact table promising a writer the tree lacks is the drift §6 exists to stop.

The commit that creates the writer replaces that row's "written by" cell with `src/core/provenance_writer.set_human_verified` and moves the absence narrative into past tense. **Not a follow-up:** rule 2 makes it part of this change.

- [ ] **Step 4: Make both callers use it**

`wave2_flip_provenance.py` keeps its classifier and loses its regex writer. `provenance_dashboard.verify_param` (`:1272-1276`) calls `set_human_verified(...)` and **only** renders the green badge when it returns `ok`, then records the audit event as it already does.

- [ ] **Step 5: Browser proof that the badge survives a reload**

```python
def test_a_confirmed_parameter_is_still_confirmed_after_reload(page, dashboard_url):
    """⚠️ THE DEFECT, stated as a test. The badge and the persisted badge are the same
    markup, so the only way to tell them apart is to reload."""
```

- [ ] **Step 6: Run every gate and commit**

```bash
uv run python -m pytest tests/test_provenance_writer.py -q
uv run python -m pytest tests/e2e/ -m e2e -q
git add src/core/provenance_writer.py scripts/wave2_flip_provenance.py scripts/provenance_dashboard.py tests/
git commit -m "provenance: one writer, called by the dashboard and the bulk sweep"
```

---

### Task 6: `--write` and the confirm button tell the same story

**Files:** `scripts/provenance_dashboard.py:5468-5491`

`--write` currently raises with *"`--write` was never implemented: it printed a success message and returned without writing provenance.py."* Once Task 5 lands, that is no longer true. Re-point it at `set_human_verified` or keep it refusing with a message that names the new route — **never leave a message that describes a defect that has been fixed**, which is how a corrected mistake gets re-litigated.

- [ ] **Step 1: Update the message and its test; commit.**

---

### Task 7: The template-contract gate

**Files:** Create `tests/test_template_contract.py`

**Interfaces:** Consumes nothing; guards every task above.

This gate does not exist. `render_template` is called once (`provenance_dashboard.py:1157`), the app leaves Jinja's default `Undefined` rather than `StrictUndefined`, and **no test anywhere uses `app.test_client()`** — so a template that dereferences a key the server never passes renders an empty panel and every existing test still passes.

- [ ] **Step 1: Write it**

Use `jinja2.meta.find_undeclared_variables` over `dashboard.html` and every partial, and assert the set is covered by the kwargs `index()` passes plus the context processor's injections. Then drive `app.test_client()` over each `?tab=` value and assert a 200 with the tab's sentinel element present.

⚠️ State in the module docstring that this is **necessary and not sufficient** — it cannot execute the Datastar JS that populates the panels, which is why `tests/e2e/` exists and why both gates are required.

- [ ] **Step 2: Run, fix any drift it finds, commit.**

---

### Task 8: Reading-while-blocked (S4)

**Files:** `scripts/provenance_dashboard.py:2662` (chain link states), `:4427-4445` (the sentence span), `tests/e2e/test_paper_provenance_markers.py`

⚠️ **The ADR's data column was wrong and is corrected.** Paper Provenance v2 reads **no** `BACKED_BY` edge and **no** `FLAGS` edge — it reconstructs chains from `claims_review.json`. So this task builds a sentence→finding resolution: for each chain link, resolve its target node id, ask the graph whether any open `ReviewFinding` FLAGS it, and attach the result to the sentence dict at `:2864-2891`.

The attachment point is clean: the per-sentence `<span>` at `:4439` already carries a state-driven class list built at `:4427`, so the marker is one more class plus a `data-blocking-findings` count.

- [ ] **Step 1: Browser test first — a sentence whose backing artifact has an open finding carries the marker; one whose artifact is clean does not.**
- [ ] **Step 2–4: resolve, render, run both gates, commit.**

---

### Task 9: Documents, and the full gate

- [ ] **Step 1:** `docs/architecture/DASHBOARD.md` — the corrections below are **measured, not inherited**. ⚠️ An earlier draft of this step said "`docs/verification_log.jsonl` exists; `docs/submission_state.json` does not", taken from the ADR rather than from the disk. **Neither file exists.** That is the same claim-vs-measurement defect this plan exists to fix, so the list is now stated with how each was checked:

  | claim in `DASHBOARD.md` | measured |
  |---|---|
  | `docs/submission_state.json` is a Bundles-tab input (×3: §Bundles, §Architecture, §Bundle readiness command) | **does not exist** |
  | the change-bus writes `docs/verification_log.jsonl` (§Sentence-level provenance) | **does not exist** — the bus has never written a file, which is stronger than "never carried an event". ⚠️ `_graph_fingerprint` stats this path (`provenance_dashboard.py:210-232`); confirm it tolerates absence rather than silently pinning the cache |
  | "18-bundle architecture" (×2, §Bundles and §Bundle readiness command) | `bundle_registry.BUNDLE_CODES` = **21** |
  | "25 node types, 25 edge types" (§Architecture diagram) | stale; `SURFACE_INVENTORY.md` is the only place a count may live — replace with a pointer, per rule 3 |
  | `POST /api/verify` | the route is **`/verify`** (`:1241`); no `/api/verify` exists |
  | `POST /api/save` — "Save accumulated verification actions" | **no such route.** Removed, and documented as a dead no-op at `:1423-1429` |
  | Paper Provenance v2 renders "each with its `BACKED_BY` chain" | the dashboard contains **zero** occurrences of `BACKED_BY`; chains come from `claims_review.json` |
  | Readiness tab offers "click-through to gate-specific evidence … review findings" | blockers render as unlinkable prose (`:5413`) until Task 3 lands — after Task 3 this becomes true, so correct it in **that** commit, not this one |

  ⚠️ Do **not** write census counts into it if it moves under `docs/architecture/` (that is P8d, not this plan).
- [ ] **Step 2:** `QA_QI_INFRASTRUCTURE_MAP.md` §4 — the operator decision points that now persist. ⚠️ Its "Verify a parameter for submission → provenance dashboard → Invariant #8" row currently describes a decision the system does not record; that row changes with Task 5, not here.
- [ ] **Step 3:** ADR-012 — mark P9a ✅ with commits.
- [ ] **Step 4:** Pin whatever load-bearing claim this wave adds, in `tests/test_architecture_claims.py`. **Not optional and not a nicety:** `END_TO_END_MAP` and `QA_QI_INFRASTRUCTURE_MAP` had zero pinned claims until 2026-08-12, and the first thing pinning them surfaced was a false coverage sentence in a green suite. S1's blocker drill-through is exactly the shape that rots — it is true the moment Task 3 lands and silently false the first time an evaluator stops populating `blocker_refs`.
- [ ] **Step 5:** `uv run python -m pytest -m '' -q` · `uv run python -m pytest -m e2e -q` · `uv run python scripts/validate.py` · `uv run python scripts/verify_scope.py --merge-gate`.

⚠️ **Record any check already red on `main` before the branch. RE-MEASURE THIS LIST — it is stale as written.** It named `bundle_manuscript_length` (did-not-measure) and the CI-floor test as inherited conditions. **Both were fixed on `main` in `1e633702`**: the cause was a regenerated `counts.tex` sitting inside every bundle's `\input` closure, and the remedy was `compile_bundle_pdf.py --all --force` — step 3 of the four-step order in `VALIDATION_ARCHITECTURE.md` §5.1. Two of the four "inherited failures" were neither inherited nor failures. Run the suite and write down what is *actually* red before cutting the branch; a stale red-list is how a branch gets credited with a failure it did not cause, and blamed for one it did.

---

## Self-Review

**Spec coverage.** D15 S1 → Tasks 1, 2, 3. D15 S4 → Task 8. QI de-saturation → Task 4. Sign-off persistence → Tasks 5, 6. The two dashboard gates → Task 7 (template contract) and the `tests/e2e/` cases inside Tasks 3, 5, 8. S2/S3 are P9b and are declared out of scope above; the Loops pane is P9c.

**Placeholders.** None. Tasks 8 and 9 carry compressed step lists because their first step is a browser test whose exact selector depends on Task 3's markup landing first; every file and line they touch is named.

**Type consistency.** `GateResult.blocker_refs: list[dict]` — Task 1, populated in Task 2, read in Task 3. `qi_id_for(gate, papers, window) -> str` and `derive_stats() -> dict` — Task 4. `set_human_verified(key, date, notes, actor=None, dry_run=False) -> tuple[bool, str]` — Task 5, called in Tasks 5 and 6.

**Ordering.** Task 1 before 2 (the field must exist before an evaluator fills it); 2 before 3 (the dashboard cannot render an id nothing emits); 5 before 6 (the message can only be corrected once the route it describes exists). Task 7 guards 3, 5 and 8 and could run first, but is placed after them so it is written against real template drift rather than against an imagined contract.

**Risk this plan does not remove.** Task 4 changes an id scheme that `## Closed Items` keys on. A closed item's id is stable only if its `papers` and `window` are — re-derive both against the live corpus before writing, and if an existing closed id cannot be reproduced by `qi_id_for`, stop and reconcile rather than regenerating the section (Invariant #13 preserves it verbatim).
