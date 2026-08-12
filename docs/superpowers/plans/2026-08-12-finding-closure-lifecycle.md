# Finding-Closure Lifecycle Implementation Plan

> ⛔ **SUPERSEDED 2026-08-12 — DO NOT EXECUTE. Awaiting rewrite against the expanded spec.**
>
> An adversarial review and an intent-drift assessment found four defects that make this plan
> unsafe to run as written:
>
> 1. **Task 6 builds a check that already exists.** `ledger_ids_resolve` is live in
>    `scripts/validation/checks/graph_atlas.py`, pinned at 66 with zero headroom and
>    mutation-verified. The proposed ceiling of 247 is the aggregate over three schemes and is
>    *weaker*. See spec §4.
> 2. **Task 8's `finding_has_verify` can never be True in production** — nothing here makes a
>    finding carry a `verify` command, so it ships a leg that cannot fire.
> 3. **Task 6 omits every registration obligation** — `_CANONICAL_ORDER` (whose absence *raises*),
>    the re-export, `MUTATION_VERIFIED`, `CI_MIN_CHECKS_RUN`, `SURFACE_INVENTORY.md`.
> 4. **Task 3→4 breaks its own interface**: `close()` still passes `verify` into `_append`'s
>    `verified_by` slot.
>
> Measured while reviewing it, and worth carrying into the rewrite: **Task 1's `N_FLIPPED` is 0** —
> all 231 currently-closed non-blocking findings already meet the bar.
>
> The plan also covered only the closure half of ADR-012. Operator ruling 2026-08-12: routing and
> closure are one build. Current design:
> [`../specs/2026-08-12-finding-closure-lifecycle-design.md`](../specs/2026-08-12-finding-closure-lifecycle-design.md).

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give the supersession ledger a writer, so closing a finding is a script call that cannot mint a broken key, instead of a hand-edit that silently fails 29% of the time.

**Architecture:** One new CLI script (`scripts/close_finding.py`) modelled directly on `scripts/record_review.py`, which solved this exact class of gap for bundle status and whose docstring calls itself "the writer transition 2 never had". One new ratchet check. Two edits inside the closure bar that already exists in `build_graph.py`. No new subsystem.

**Tech Stack:** Python 3.14, `uv run`, pytest. No new dependencies.

## Global Constraints

- **The id minter is shared, never copied.** `close_finding.py` imports the minting function from `build_graph`. A second implementation reproduces the 29% orphan class by construction. Precedent: `_recurrence_norm` was moved to module scope for exactly this reason.
- **Every refusal path ships with a seeded-defect test** that observes red (ADR-012 D8). A check whose population can be empty while it reports PASS does not count as built.
- **Ratchets may only be lowered, in the same commit that lowers the population.**
- **Architecture docs land with the code, not after** (architecture rule 2).
- **Never write a census count into an architecture narrative** (architecture rule 3) — counts live in the derived `SURFACE_INVENTORY.md`.
- Run everything from the repo root: `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking`
- CLI convention to follow, from `record_review.py`: a `record(...)`-style function returns `(ok: bool, msg: str)`; `main()` prints `"✓ "` on success or `"✗ REFUSED — "` on failure and returns `0`/`1`.

---

### Task 1: Measure the blast radius of unscoping the closure bar

Task 7 removes `severity in ('critical','major','blocker')` from the bar. Findings currently reading `fixed` at non-blocking severities will be re-tested against the bar, and some will flip back to `open`. Nobody has measured how many. This task produces that number so Task 7 is a decision, not a surprise.

**Files:**
- Create: `docs/audits/2026-08-12-critical-triage/bar_unscoping_blast_radius.md`

**Interfaces:**
- Consumes: nothing
- Produces: the integer `N_FLIPPED` (findings that would move `fixed`/`accepted` → `open`), quoted in Task 7's commit message and in the ADR-012 amendment.

- [ ] **Step 1: Measure, without editing any source**

```bash
cd /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking
uv run python - <<'PY'
import sys, json, collections; sys.path.insert(0, 'scripts')
import build_graph as bg

_CLOSING = ('fixed', 'accepted')
ledger = {}
for e in json.load(open('docs/review_finding_supersessions.json')).get('supersessions', []):
    ledger[e['finding_id']] = e

flipped = []
for n in bg.extract_review_finding_nodes():
    m = n['meta']
    if m.get('status') not in _CLOSING:
        continue
    if m.get('severity') in ('critical', 'major', 'blocker'):
        continue          # already subject to the bar today
    rec = ledger.get(n['id'], {})
    why = str(rec.get('evidence') or rec.get('note') or rec.get('rationale') or '').strip()
    anchor = any(str(rec.get(k) or '').strip()
                 for k in ('commit', 'date', 'closed_date', 'applied_at'))
    if not (rec.get('status') in _CLOSING and len(why) >= 40 and anchor):
        flipped.append((n['id'], m.get('severity'), m.get('status')))

print('N_FLIPPED =', len(flipped))
print(collections.Counter(s for _, s, _ in flipped))
for fid, sev, st in flipped[:15]:
    print(f'  {sev:9} {st:8} {fid}')
PY
```

- [ ] **Step 2: Write the measurement up**

Create `docs/audits/2026-08-12-critical-triage/bar_unscoping_blast_radius.md` containing: the exact command above, its output, the value of `N_FLIPPED`, the per-severity breakdown, and one paragraph answering — *are these findings that were genuinely closed and merely under-documented, or closures that never met the bar?* Sample five and say which, naming each.

- [ ] **Step 3: Commit**

```bash
git add docs/audits/2026-08-12-critical-triage/bar_unscoping_blast_radius.md
git commit -m "measure: blast radius of unscoping the closure bar

Task 7 removes the severity scoping that lets a below-bar finding close on a
two-key ledger record. This measures what flips back to open when it does."
```

---

### Task 2: Extract the id minter into a shared function

**Files:**
- Modify: `scripts/build_graph.py` (the minting site currently at line ~1887, `finding_id = f'review:{date_dir}:{review_name}:{section_num}'`)
- Test: `tests/test_build_graph.py`

**Interfaces:**
- Consumes: nothing
- Produces: `build_graph.mint_finding_id(date_dir: str, review_name: str, section_num: str) -> str` — imported by `close_finding.py` in Task 3 and by the check in Task 6.

- [ ] **Step 1: Write the failing test**

Add to `tests/test_build_graph.py`:

```python
class TestTheFindingIdMinterIsShared:
    """The minter must be one function, importable, and the one production uses.

    `close_finding.py` mints ids to write the ledger; `extract_review_finding_nodes`
    mints them to read it. Two implementations diverging is exactly how 256 of 870
    ledger records came to reference ids that match no node.
    """

    def test_mint_finding_id_is_importable_and_stable(self):
        import build_graph as bg
        assert bg.mint_finding_id(
            '2026-08-12-0006-internal-adversarial', 'I1', '5.5'
        ) == 'review:2026-08-12-0006-internal-adversarial:I1:5.5'

    def test_every_minted_node_id_round_trips_through_the_function(self):
        import build_graph as bg
        for n in bg.extract_review_finding_nodes():
            m = n['meta']
            assert n['id'] == bg.mint_finding_id(
                m['review_date'], m['review_name'], m['section']), (
                f"{n['id']} was not produced by mint_finding_id — the extractor "
                "and the minter have diverged")
```

- [ ] **Step 2: Run it to verify it fails**

```bash
uv run python -m pytest tests/test_build_graph.py::TestTheFindingIdMinterIsShared -v
```

Expected: FAIL with `AttributeError: module 'build_graph' has no attribute 'mint_finding_id'`

- [ ] **Step 3: Add the function at module scope in `scripts/build_graph.py`**

Place it immediately above `extract_review_finding_nodes`:

```python
def mint_finding_id(date_dir: str, review_name: str, section_num: str) -> str:
    """The canonical ReviewFinding node id.

    ⚠️ MODULE SCOPE ON PURPOSE. `scripts/close_finding.py` imports this to write the
    supersession ledger, and `extract_review_finding_nodes` calls it to read the ledger
    back. A second implementation is not a duplication smell, it is the defect: 256 of
    870 ledger records reference ids that no node carries, because every one of them was
    hand-typed against a format nobody could check. Same reasoning as `_recurrence_norm`,
    which moved here after the production matcher could have been deleted with its test
    still green.
    """
    return f'review:{date_dir}:{review_name}:{section_num}'
```

- [ ] **Step 4: Replace the inline f-string with a call**

At the minting site, change

```python
            finding_id = f'review:{date_dir}:{review_name}:{section_num}'
```

to

```python
            finding_id = mint_finding_id(date_dir, review_name, section_num)
```

- [ ] **Step 5: Run the test and the graph tests**

```bash
uv run python -m pytest tests/test_build_graph.py -q
```

Expected: PASS, including both new tests.

- [ ] **Step 6: Commit**

```bash
git add scripts/build_graph.py tests/test_build_graph.py
git commit -m "build_graph: extract mint_finding_id to module scope

The writer in the next task must mint ids with the same function the reader uses.
Two implementations is how 256 of 870 ledger records came to reference ids that
match no node."
```

---

### Task 3: `close_finding.py` — minting and the unresolvable-id refusal

**Files:**
- Create: `scripts/close_finding.py`
- Test: `tests/test_close_finding.py`

**Interfaces:**
- Consumes: `build_graph.mint_finding_id` (Task 2)
- Produces:
  - `close_finding.close(doc: str, sections: list[str], status: str, evidence: str, commit: str | None = None, date: str | None = None, verify: str | None = None, superseded_by: str | None = None) -> tuple[bool, str]`
  - `close_finding.main(argv=None) -> int`
  - `close_finding.ids_for_doc(doc: str) -> list[str]` — used in the refusal message and by Task 4

- [ ] **Step 1: Write the failing tests**

Create `tests/test_close_finding.py`:

```python
"""The ledger writer. See docs/superpowers/specs/2026-08-12-finding-closure-lifecycle-design.md"""
import json
import pytest


class TestTheHappyPath:
    def test_a_resolvable_finding_is_written(self, tmp_path, monkeypatch):
        import close_finding as cf
        ok, msg = cf.close(
            doc='papers/AutomatedReviews/2026-08-12-0006-internal-adversarial/I1.md',
            sections=['5.5'], status='fixed',
            evidence='Figure rebuilt from the module dependency edges; every label '
                     'resolves by exact name in lean_deps.json.',
            commit='b0f44815', dry_run=True)
        assert ok is True
        assert 'review:2026-08-12-0006-internal-adversarial:I1:5.5' in msg


class TestTheRefusals:
    def test_an_unresolvable_id_is_refused_and_lists_what_exists(self):
        import close_finding as cf
        ok, msg = cf.close(
            doc='papers/AutomatedReviews/2026-08-12-0006-internal-adversarial/I1.md',
            sections=['99.99'], status='fixed',
            evidence='x' * 60, commit='deadbeef', dry_run=True)
        assert ok is False
        assert 'no such finding' in msg.lower()
        # the caller must be shown the real section numbers, not left guessing
        assert '5.5' in msg
```

- [ ] **Step 2: Run to verify it fails**

```bash
uv run python -m pytest tests/test_close_finding.py -v
```

Expected: FAIL with `ModuleNotFoundError: No module named 'close_finding'`

- [ ] **Step 3: Write `scripts/close_finding.py`**

```python
#!/usr/bin/env python3
"""Write a closure into the supersession ledger — the writer the ledger never had.

Why this exists
---------------
`docs/review_finding_supersessions.json` is the ONLY channel that can close a blocking
`ReviewFinding` (`build_graph.py`, the blocking-closure bar). It had no writer. All 870
records were hand-typed into a 645 KB JSON file, and **256 of them — 29% — carry a
`finding_id` that matches no minted node**, so they are inert: the findings they meant to
close still read `open`.

This is the same shape of gap `record_review.py` was written to close for bundle status,
where "every green in the corpus was therefore a hand edit". Nobody skips a script.
People skip a hand-edit, and when they do not skip it, a third of the time it silently
does nothing.

The load-bearing decision is that `mint_finding_id` is imported, not reimplemented.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import date as _date
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))

import build_graph as _bg  # noqa: E402  — after sys.path setup

LEDGER = PROJECT_ROOT / "docs" / "review_finding_supersessions.json"
CLOSING_STATUSES = ("fixed", "accepted", "reopened")
MIN_EVIDENCE = 40


def _live_ids() -> set[str]:
    return {n["id"] for n in _bg.extract_review_finding_nodes()}


def ids_for_doc(doc: str) -> list[str]:
    """Every minted id belonging to one review document, for the refusal message."""
    stem = Path(doc).stem
    date_dir = Path(doc).parent.name
    prefix = _bg.mint_finding_id(date_dir, stem, "")
    return sorted(i for i in _live_ids() if i.startswith(prefix))


def close(doc: str, sections: list[str], status: str, evidence: str,
          commit: str | None = None, date: str | None = None,
          verify: str | None = None, superseded_by: str | None = None,
          dry_run: bool = False) -> tuple[bool, str]:
    if status not in CLOSING_STATUSES:
        return False, f"status={status!r} is not one of {CLOSING_STATUSES}"

    date_dir = Path(doc).parent.name
    review_name = Path(doc).stem
    live = _live_ids()

    minted = [_bg.mint_finding_id(date_dir, review_name, s) for s in sections]
    missing = [m for m in minted if m not in live]
    if missing:
        have = ids_for_doc(doc)
        return False, (
            f"no such finding: {', '.join(missing)}. "
            f"This document mints: {', '.join(have) if have else '(none)'}")

    if not dry_run:
        _append(minted, status, evidence, commit, date, verify, superseded_by)
    return True, f"{'would write' if dry_run else 'wrote'} {len(minted)} record(s): {', '.join(minted)}"


def _append(minted, status, evidence, commit, date, verify, superseded_by) -> None:
    data = json.loads(LEDGER.read_text())          # re-read immediately before writing
    existing = {e["finding_id"]: e for e in data["supersessions"]}
    for fid in minted:
        if existing.get(fid, {}).get("status") == status:
            continue                                # idempotent
        rec = {"finding_id": fid, "status": status, "evidence": evidence,
               "superseded_by": superseded_by,
               "date": date or _date.today().isoformat()}
        if commit:
            rec["commit"] = commit
        data["supersessions"].append(rec)
    LEDGER.write_text(json.dumps(data, indent=2) + "\n")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--doc", required=True)
    ap.add_argument("--section", required=True, nargs="+")
    ap.add_argument("--status", required=True, choices=CLOSING_STATUSES)
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

- [ ] **Step 4: Run the tests**

```bash
uv run python -m pytest tests/test_close_finding.py -v
```

Expected: PASS — both tests.

- [ ] **Step 5: Commit**

```bash
git add scripts/close_finding.py tests/test_close_finding.py
git commit -m "close_finding: the ledger writer, with the unresolvable-id refusal

Mints the id from --doc and --section using build_graph's own minter, so a broken
key cannot be produced. On refusal it prints the ids the document DOES mint, so
the caller sees real section numbers instead of guessing."
```

---

### Task 4: `close_finding.py` — evidence, anchor and verify refusals

**Files:**
- Modify: `scripts/close_finding.py`
- Test: `tests/test_close_finding.py`

**Interfaces:**
- Consumes: `close_finding.close(...)` (Task 3)
- Produces: no new names; `close()` gains three refusal paths and a `verified_by` record field consumed by Task 8.

- [ ] **Step 1: Write the failing tests**

Append to `tests/test_close_finding.py::TestTheRefusals`:

```python
    def test_thin_evidence_is_refused(self):
        import close_finding as cf
        ok, msg = cf.close(
            doc='papers/AutomatedReviews/2026-08-12-0006-internal-adversarial/I1.md',
            sections=['5.5'], status='fixed', evidence='fixed it',
            commit='b0f44815', dry_run=True)
        assert ok is False and 'evidence' in msg.lower()

    def test_a_closure_with_no_anchor_is_refused(self):
        import close_finding as cf
        ok, msg = cf.close(
            doc='papers/AutomatedReviews/2026-08-12-0006-internal-adversarial/I1.md',
            sections=['5.5'], status='fixed', evidence='x' * 60, dry_run=True)
        assert ok is False and 'anchor' in msg.lower()

    def test_a_failing_verify_command_is_refused(self):
        import close_finding as cf
        ok, msg = cf.close(
            doc='papers/AutomatedReviews/2026-08-12-0006-internal-adversarial/I1.md',
            sections=['5.5'], status='fixed', evidence='x' * 60,
            commit='b0f44815', verify='python3 -c "raise SystemExit(1)"', dry_run=True)
        assert ok is False and 'verify' in msg.lower()

    def test_a_passing_verify_command_is_recorded(self):
        import close_finding as cf
        ok, msg = cf.close(
            doc='papers/AutomatedReviews/2026-08-12-0006-internal-adversarial/I1.md',
            sections=['5.5'], status='fixed', evidence='x' * 60,
            commit='b0f44815', verify='python3 -c "pass"', dry_run=True)
        assert ok is True
```

- [ ] **Step 2: Run to verify they fail**

```bash
uv run python -m pytest tests/test_close_finding.py::TestTheRefusals -v
```

Expected: the four new tests FAIL (no refusal implemented yet).

- [ ] **Step 3: Add the refusals to `close()`**

Insert immediately after the `missing` check in `close()`:

```python
    if status in ("fixed", "accepted") and len(evidence.strip()) < MIN_EVIDENCE:
        return False, (f"evidence is {len(evidence.strip())} chars; the bar is "
                       f"{MIN_EVIDENCE}. A closure has to say what changed and where.")

    if not (commit or date):
        return False, "no anchor: pass --commit or --date"

    verified_by = None
    if verify:
        proc = subprocess.run(verify, shell=True, cwd=PROJECT_ROOT,
                              capture_output=True, text=True)
        if proc.returncode != 0:
            return False, (f"verify command failed (exit {proc.returncode}): {verify}\n"
                           f"{proc.stdout}{proc.stderr}")
        verified_by = {"command": verify, "exit_code": 0,
                       "run_at": _date.today().isoformat()}
```

Thread `verified_by` into `_append` by changing its signature to accept it and adding, inside the record construction:

```python
        if verified_by:
            rec["verified_by"] = verified_by
```

- [ ] **Step 4: Run the tests**

```bash
uv run python -m pytest tests/test_close_finding.py -v
```

Expected: PASS — all six.

- [ ] **Step 5: Commit**

```bash
git add scripts/close_finding.py tests/test_close_finding.py
git commit -m "close_finding: evidence, anchor and verify refusals

A --verify command is RUN before the record is written and its result recorded in
verified_by. A ledger record once asserted it had cleaned up duplicate keys in 57
registry entries that still carry them; one second of machine time would have
caught it."
```

---

### Task 5: Amend the ledger schema and re-key the nine

**Files:**
- Modify: `docs/review_finding_supersessions.json` (the `_entry_format` block, and nine `finding_id` values)

**Interfaces:**
- Consumes: nothing
- Produces: a ledger whose declared format matches its reader; orphan count drops from 256 to 247, the baseline Task 6 ratchets.

- [ ] **Step 1: Re-key the nine mechanically re-keyable records**

```bash
cd /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking
uv run python - <<'PY'
import sys, json, re, pathlib; sys.path.insert(0, 'scripts')
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
        rec.setdefault('notes', '')
        rec['notes'] = (str(rec.get('notes') or '') +
                        f' [2026-08-12 re-keyed from {fid}: the suffix was never part of '
                        'any minted id, so this record closed nothing.]').strip()
        n += 1
p.write_text(json.dumps(data, indent=2) + '\n')
print('re-keyed', n)
PY
```

Expected output: `re-keyed 9`

- [ ] **Step 2: Amend `_entry_format` to match the reader**

Replace the `_entry_format` block with:

```json
  "_entry_format": {
    "finding_id": "string — the canonical ReviewFinding node ID. Produced by build_graph.mint_finding_id(date_dir, review_name, section_num); write records with scripts/close_finding.py, which mints it for you. NEVER hand-type this: 256 of the first 870 records did, and 29% of them matched no node.",
    "status": "string — one of 'fixed', 'accepted', 'reopened'",
    "superseded_by": "string|null — review_id of the re-review that confirmed the fix, OR a Wave close-doc path. Optional since 2026-08-12: a passing `verified_by` command is the supported alternative.",
    "evidence": "string — what changed, where. Blocking-severity closures need >= 40 chars.",
    "verified_by": "object|null — {command, exit_code, run_at}. The command that proves the finding fixed, and its result. Written by close_finding.py --verify.",
    "date": "ISO-8601 date the supersession was applied",
    "commit": "string|null — commit anchoring the fix. ANY of commit/date/closed_date/applied_at satisfies the closure bar; before 2026-08-12 this format named only `date` while build_graph accepted all four."
  },
```

- [ ] **Step 3: Verify the count moved and nothing else changed**

```bash
uv run python - <<'PY'
import sys, json; sys.path.insert(0, 'scripts')
import build_graph as bg
ids = {n['id'] for n in bg.extract_review_finding_nodes()}
led = json.load(open('docs/review_finding_supersessions.json'))['supersessions']
print('records', len(led), 'orphans', sum(1 for r in led if r['finding_id'] not in ids))
PY
```

Expected: `records 870 orphans 247`

- [ ] **Step 4: Commit**

```bash
git add docs/review_finding_supersessions.json
git commit -m "ledger: re-key nine dead records, and document the anchors the reader accepts

The nine carried suffixes (:3.1-residual, :5.1-5.3) that no minted id has, so they
closed nothing. _entry_format declared `date` as the only temporal field while
build_graph has always accepted commit/date/closed_date/applied_at."
```

---

### Task 6: `ledger_finding_ids_resolve` check

**Files:**
- Modify: `scripts/validation/checks/reviews.py`
- Test: `tests/test_d5_reviews.py`

**Interfaces:**
- Consumes: `build_graph.mint_finding_id` (Task 2), the re-keyed ledger (Task 5)
- Produces: registered check `ledger_finding_ids_resolve`; module constant `LEDGER_ORPHAN_CEILING = 247`

- [ ] **Step 1: Write the failing test**

Add to `tests/test_d5_reviews.py`:

```python
class TestLedgerOrphanRatchet:
    def test_the_check_is_green_at_the_frozen_ceiling(self):
        from validation.checks.reviews import check_ledger_finding_ids_resolve
        assert check_ledger_finding_ids_resolve().passed is True

    def test_the_ratchet_has_zero_headroom(self):
        import sys, json
        sys.path.insert(0, 'scripts')
        import build_graph as bg
        from validation.checks.reviews import LEDGER_ORPHAN_CEILING
        ids = {n['id'] for n in bg.extract_review_finding_nodes()}
        led = json.load(open('docs/review_finding_supersessions.json'))['supersessions']
        live = sum(1 for r in led if r['finding_id'] not in ids)
        assert live == LEDGER_ORPHAN_CEILING, (
            f"live orphan count {live} != ceiling {LEDGER_ORPHAN_CEILING}; if the "
            "backlog shrank, LOWER the ceiling — headroom makes it unfireable")

    def test_a_seeded_broken_id_turns_the_check_red(self, monkeypatch):
        """Non-vacuity (ADR-012 D8): plant the defect, observe red."""
        import validation.checks.reviews as rv
        monkeypatch.setattr(rv, 'LEDGER_ORPHAN_CEILING', 0)
        assert rv.check_ledger_finding_ids_resolve().passed is False
```

- [ ] **Step 2: Run to verify it fails**

```bash
uv run python -m pytest tests/test_d5_reviews.py::TestLedgerOrphanRatchet -v
```

Expected: FAIL with `ImportError: cannot import name 'check_ledger_finding_ids_resolve'`

- [ ] **Step 3: Add the check to `scripts/validation/checks/reviews.py`**

```python
#: Ledger records whose `finding_id` matches no minted node. **A RATCHET: may only shrink.**
#:
#: MEASURED 2026-08-12: 247 of 870 records (28%) are inert — the findings they meant to
#: close still read `open`. Cause: the ledger had no writer until `close_finding.py`, so
#: every id was hand-typed against a format nobody could check. 187 use conventions the
#: minter never produced (`bundle-stage13:`, `bundle-stage10:`, `bundle-stage9:`), 57 are
#: `review:` ids matching nothing, and 9 were re-keyed in the same change that froze this.
#: Lower it by re-keying a record or by removing one that closes nothing. Never raise it.
LEDGER_ORPHAN_CEILING = 247


@register_check("ledger_finding_ids_resolve",
                "Supersession records name findings that exist (ratcheted)")
def check_ledger_finding_ids_resolve() -> CheckResult:
    """CHECK: a closure that names no finding closes nothing, silently.

    The ledger is the only channel that can retire a blocking finding, so a record whose
    `finding_id` resolves to nothing is indistinguishable from no record at all — the
    same "unrecordable finding" class `build_graph` records at its BLOCKER→gate site.
    Nothing measured this until 2026-08-12.
    """
    import sys as _sys
    _sys.path.insert(0, str(_H.PROJECT_ROOT / "scripts"))
    import build_graph as _bg

    ledger_path = _H.DOCS_DIR / "review_finding_supersessions.json"
    if not ledger_path.is_file():
        return CheckResult(passed=True, measured=False, details=[
            Detail("ledger", True, "no supersession ledger; skipping",
                   warning=True, measured=False)])
    try:
        records = json.loads(ledger_path.read_text()).get("supersessions", [])
    except (OSError, json.JSONDecodeError) as exc:
        return CheckResult(passed=False, details=[
            Detail("ledger", False, f"unreadable supersession ledger: {exc}")])

    live = {n["id"] for n in _bg.extract_review_finding_nodes()}
    orphans = [r["finding_id"] for r in records if r.get("finding_id") not in live]
    ok = len(orphans) <= LEDGER_ORPHAN_CEILING
    return CheckResult(passed=ok, details=[Detail(
        "ratchet", ok,
        f"{len(orphans)} of {len(records)} supersession record(s) name no live finding; "
        f"ceiling {LEDGER_ORPHAN_CEILING}"
        + ("" if ok else " — a record that closes nothing is indistinguishable from no "
                         "record. Re-key it or remove it; do not raise the ceiling."))])
```

- [ ] **Step 4: Run the tests and the check**

```bash
uv run python -m pytest tests/test_d5_reviews.py::TestLedgerOrphanRatchet -v
uv run python scripts/validate.py --check ledger_finding_ids_resolve
```

Expected: 3 tests PASS; check reports `247 of 870 … ceiling 247` and PASSES.

- [ ] **Step 5: Commit**

```bash
git add scripts/validation/checks/reviews.py tests/test_d5_reviews.py
git commit -m "check: ledger_finding_ids_resolve — 29% of closures named nothing

A record whose finding_id resolves to no node closes nothing, silently. Nothing
measured this until now. Ships with a seeded-defect test per ADR-012 D8."
```

---

### Task 7: Remove the severity scoping from the closure bar

**Files:**
- Modify: `scripts/build_graph.py` (the bar, currently at lines 1954-1967)
- Test: `tests/test_closure_guard_bypasses.py`

**Interfaces:**
- Consumes: Task 1's `N_FLIPPED`
- Produces: a bar that applies at every severity.

- [ ] **Step 1: Write the failing test**

Add to `tests/test_closure_guard_bypasses.py`:

```python
class TestTheBarAppliesAtEverySeverity:
    """D12 13.2, open across four rounds and reproducing at HEAD.

    The bar was gated on severity in ('critical','major','blocker'). Below that line a
    two-key record — no evidence, no anchor — closed a finding. Because `- **Severity:**`
    is declarable in the body and the declared value beats the heading glyph, a 🔴 BLOCKER
    heading declaring `recommended` closed on {"finding_id": X, "status": "fixed"}.
    """

    def test_a_content_free_record_cannot_close_a_minor_finding(self):
        import build_graph as bg
        rec = {"finding_id": "x", "status": "fixed"}   # no evidence, no anchor
        assert bg._closure_record_meets_bar(rec) is False

    def test_a_complete_record_still_closes(self):
        import build_graph as bg
        rec = {"finding_id": "x", "status": "fixed",
               "evidence": "y" * 60, "commit": "abc1234"}
        assert bg._closure_record_meets_bar(rec) is True
```

- [ ] **Step 2: Run to verify it fails**

```bash
uv run python -m pytest tests/test_closure_guard_bypasses.py::TestTheBarAppliesAtEverySeverity -v
```

Expected: FAIL — `_closure_record_meets_bar` does not exist.

- [ ] **Step 3: Extract the bar into a testable predicate and unscope it**

Add at module scope in `scripts/build_graph.py`:

```python
_CLOSING_STATUSES = ('fixed', 'accepted')


def _closure_record_meets_bar(rec: dict) -> bool:
    """Does this ledger record justify closing a finding?

    ⚠️ APPLIES AT EVERY SEVERITY since 2026-08-12. It was gated on
    `severity in ('critical','major','blocker')`, which made a below-bar severity a
    closure bypass: declare `- **Severity:** recommended` under a 🔴 heading and a
    two-key record closed the finding. Filed as D12 13.2 and open across FOUR rounds,
    mutating each time the previous route was shut — round 11 it was heading-parse
    closure, round 12 removed that and left this. Do not re-scope it.
    """
    rec = rec or {}
    why = str(rec.get('evidence') or rec.get('note') or rec.get('rationale') or '').strip()
    anchor = any(str(rec.get(k) or '').strip()
                 for k in ('commit', 'date', 'closed_date', 'applied_at'))
    return bool(rec.get('status') in _CLOSING_STATUSES and len(why) >= 40 and anchor)
```

Then replace the inline bar with:

```python
            if meta.get('status') in _CLOSING_STATUSES:
                if not _closure_record_meets_bar(ledger):
                    meta['status'] = 'open'
                    meta['blocking_closure_rejected'] = (
                        'ledger record does not meet the closure bar '
                        '(explicit status=fixed, >=40 chars of rationale, and a commit '
                        'or date)')
```

- [ ] **Step 4: Run the tests and re-measure**

```bash
uv run python -m pytest tests/test_closure_guard_bypasses.py -q
uv run python -c "
import sys,collections; sys.path.insert(0,'scripts')
import build_graph as bg
print(collections.Counter(n['meta']['status'] for n in bg.extract_review_finding_nodes()))"
```

Expected: tests PASS; the `open` count rises by exactly Task 1's `N_FLIPPED`.

- [ ] **Step 5: Update the orphan ratchet if the finding population changed**

Re-run Task 6's measurement. If the live orphan count changed, lower `LEDGER_ORPHAN_CEILING` in the same commit. Never raise it.

- [ ] **Step 6: Commit**

```bash
git add scripts/build_graph.py scripts/validation/checks/reviews.py tests/test_closure_guard_bypasses.py
git commit -m "build_graph: the closure bar applies at every severity

D12 13.2, open across four rounds and reproducing at HEAD. The bar was scoped to
critical/major/blocker, so declaring a lower severity in the body closed a finding
on a two-key record. N_FLIPPED findings move back to open; see
docs/audits/2026-08-12-critical-triage/bar_unscoping_blast_radius.md."
```

---

### Task 8: Require `verified_by` when the finding carries a verify command

**Files:**
- Modify: `scripts/build_graph.py` (`_closure_record_meets_bar`)
- Test: `tests/test_closure_guard_bypasses.py`

**Interfaces:**
- Consumes: `_closure_record_meets_bar` (Task 7), the `verified_by` field (Task 4)
- Produces: no new names.

- [ ] **Step 1: Write the failing test**

```python
class TestVerifiedByIsRequiredWhenAVerifyCommandExists:
    def test_a_record_without_verified_by_fails_when_the_finding_has_a_verify(self):
        import build_graph as bg
        rec = {"status": "fixed", "evidence": "y" * 60, "commit": "abc1234"}
        assert bg._closure_record_meets_bar(rec, finding_has_verify=True) is False

    def test_a_record_with_a_passing_verified_by_succeeds(self):
        import build_graph as bg
        rec = {"status": "fixed", "evidence": "y" * 60, "commit": "abc1234",
               "verified_by": {"command": "pytest -q", "exit_code": 0,
                               "run_at": "2026-08-12"}}
        assert bg._closure_record_meets_bar(rec, finding_has_verify=True) is True

    def test_a_recorded_nonzero_exit_does_not_close(self):
        import build_graph as bg
        rec = {"status": "fixed", "evidence": "y" * 60, "commit": "abc1234",
               "verified_by": {"command": "pytest -q", "exit_code": 1,
                               "run_at": "2026-08-12"}}
        assert bg._closure_record_meets_bar(rec, finding_has_verify=True) is False
```

- [ ] **Step 2: Run to verify it fails**

```bash
uv run python -m pytest tests/test_closure_guard_bypasses.py::TestVerifiedByIsRequiredWhenAVerifyCommandExists -v
```

Expected: FAIL — `_closure_record_meets_bar() got an unexpected keyword argument`.

- [ ] **Step 3: Extend the predicate**

```python
def _closure_record_meets_bar(rec: dict, finding_has_verify: bool = False) -> bool:
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

- [ ] **Step 4: Run the tests**

```bash
uv run python -m pytest tests/test_closure_guard_bypasses.py -q
```

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add scripts/build_graph.py tests/test_closure_guard_bypasses.py
git commit -m "build_graph: a finding with a verify command needs a passing verified_by

A ledger record once asserted it removed duplicate keys from 57 registry entries
that still carry them. The record met every other requirement."
```

---

### Task 9: Update the seven architecture documents

**Files:**
- Modify: `docs/READINESS_GATES.md`, `docs/architecture/END_TO_END_MAP.md`, `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md`, `docs/WAVE_EXECUTION_PIPELINE.md`, `docs/KNOWLEDGE_GRAPH.md`, `docs/adrs/ADR-012-finding-lifecycle-routing-and-closure.md`
- Regenerate: `docs/architecture/SURFACE_INVENTORY.md`

**Interfaces:**
- Consumes: everything above
- Produces: documentation matching the implementation.

- [ ] **Step 1: `docs/READINESS_GATES.md` — add the closure contract**

It has **zero** mentions of the ledger today, so a reader of the canonical gate document cannot learn how a gate un-blocks. Add a section stating: status is `open` until a ledger record says otherwise; the ledger is the only transition channel; a closure needs an explicit status, ≥40 characters of evidence, and a commit or date anchor; a finding carrying a `verify` command additionally needs a passing `verified_by`; records are written with `scripts/close_finding.py`.

- [ ] **Step 2: `docs/architecture/END_TO_END_MAP.md:43` — re-route the writer edge**

It currently reads `HUMAN -.->|"supersession ledger"| GATE`, which is accurate today and wrong after Task 3. Change to route through the script:

```
    HUMAN -.->|"close_finding.py"| LEDGER
    LEDGER -.-> GATE
```

- [ ] **Step 3: `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md:195` — name the writer**

The node currently reads `review_finding_supersessions.json<br/>append-only`. Change to `review_finding_supersessions.json<br/>append-only · written by close_finding.py`, and add one sentence in the surrounding prose noting that records naming no live finding are ratcheted by `ledger_finding_ids_resolve`.

- [ ] **Step 4: `docs/WAVE_EXECUTION_PIPELINE.md` §Stage 13 — add the closure step**

After the existing re-invocation rule, add: how a closure is recorded (`close_finding.py`), and that the bar applies at every severity. Cross-reference `docs/READINESS_GATES.md` for the contract rather than restating it — one owner per fact.

- [ ] **Step 5: `docs/KNOWLEDGE_GRAPH.md:167` — note the writer**

The `SUPERSEDES` row correctly says the edge is unimplemented because supersession is ledger-based. Extend that note to name `close_finding.py` as the writer.

- [ ] **Step 6: `docs/adrs/ADR-012-…md` — point at the spec**

Add to the status block: the write-side gap was found *after* this ADR's own pilot, and is specified in `docs/superpowers/specs/2026-08-12-finding-closure-lifecycle-design.md`. Mark D6 as implemented by Tasks 7 and 8.

- [ ] **Step 7: Regenerate the derived inventory and verify**

```bash
uv run python scripts/architecture_inventory.py --write
uv run python scripts/validate.py --check architecture_inventory_fresh
uv run python -m pytest tests/test_architecture_claims.py -q
```

Expected: check PASSES; architecture-claims tests pass.

- [ ] **Step 8: Commit**

```bash
git add docs/READINESS_GATES.md docs/architecture/END_TO_END_MAP.md \
        docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md docs/WAVE_EXECUTION_PIPELINE.md \
        docs/KNOWLEDGE_GRAPH.md docs/adrs/ADR-012-finding-lifecycle-routing-and-closure.md \
        docs/architecture/SURFACE_INVENTORY.md
git commit -m "docs: the ledger has a writer, and the architecture says so

END_TO_END_MAP modelled the writer as HUMAN — accurate until this change.
READINESS_GATES, the canonical gate document, had zero mentions of the mechanism
that decides whether a gate can un-block."
```

---

### Task 10: Write the 98 pending closures from the ADR-012 pilot

**Files:**
- Modify: `docs/review_finding_supersessions.json` (via `close_finding.py` only)
- Modify: `scripts/validation/checks/reviews.py` (lower `LEDGER_ORPHAN_CEILING` if it moved)

**Interfaces:**
- Consumes: `close_finding.py` (Tasks 3-4), the fixed bar (Tasks 7-8), `docs/audits/2026-08-12-critical-triage/manifest.json`
- Produces: the 98 `fixed` dispositions recorded; `readiness_submission_gate` reflecting them.

- [ ] **Step 1: Drive the manifest through the writer**

```bash
cd /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking
uv run python - <<'PY'
import json, subprocess, sys, pathlib
rows = json.loads(pathlib.Path('docs/audits/2026-08-12-critical-triage/manifest.json').read_text())
todo = [r for r in rows if r.get('disposition') in ('fixed', 'superseded', 'not-a-defect')]
ok = fail = 0
for r in todo:
    status = 'fixed' if r['disposition'] == 'fixed' else 'accepted'
    cmd = ['uv', 'run', 'python', 'scripts/close_finding.py',
           '--doc', r['file'], '--section', r['section'], '--status', status,
           '--evidence', r['evidence'], '--date', '2026-08-12']
    if r.get('verify'):
        cmd += ['--verify', r['verify']]
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode == 0:
        ok += 1
    else:
        fail += 1
        print('REFUSED', r['file'], r['section'], p.stdout.strip(), file=sys.stderr)
print(f'written {ok}, refused {fail}')
PY
```

- [ ] **Step 2: Triage every refusal — do not force any of them**

A refusal is information. Record each in `docs/audits/2026-08-12-critical-triage/refusals.md` with the reason. Evidence under 40 characters means the disposition was too thin to justify a closure and needs rewriting, not bypassing.

- [ ] **Step 3: Re-measure and lower the orphan ratchet**

```bash
uv run python scripts/validate.py --check ledger_finding_ids_resolve
```

If the live count fell, lower `LEDGER_ORPHAN_CEILING` to it in this commit.

- [ ] **Step 4: Confirm the gate moved**

```bash
uv run python scripts/validate.py --check readiness_submission_gate
uv run python -c "
import sys,collections; sys.path.insert(0,'scripts')
import build_graph as bg
print(collections.Counter(n['meta']['status'] for n in bg.extract_review_finding_nodes()))"
```

Expected: the `open` count falls by the number written in Step 1.

- [ ] **Step 5: Full suite**

```bash
uv run python -m pytest -q
```

Expected: green.

- [ ] **Step 6: Commit**

```bash
git add docs/review_finding_supersessions.json scripts/validation/checks/reviews.py \
        docs/audits/2026-08-12-critical-triage/refusals.md
git commit -m "ledger: record the ADR-012 pilot's dispositions through the writer

98 findings were repaired and never recorded; that recording gap IS the backlog.
Written last, after the bar's severity bypass was closed, so none of these
closures rests on a bar that could be walked around."
```

---

## Self-Review

**Spec coverage.** `close_finding.py` → Tasks 3-4. Schema amendment → Task 5. `ledger_finding_ids_resolve` → Task 6. ADR-012 D6.1 → Task 7. D6.2 → Task 8. Shared minter constraint → Task 2. Re-key the nine → Task 5. Orphan ratchet → Task 6. Seven architecture docs → Task 9. Sequencing (98 closures last) → Task 10. Blast-radius measurement → Task 1. `CHECK_AUTHORING_GUIDE.md` verified as not needing a change — no task, correctly.

**Placeholders.** None. Every code step carries the code.

**Type consistency.** `mint_finding_id(date_dir, review_name, section_num) -> str` is defined in Task 2 and used with that signature in Tasks 3 and 6. `_closure_record_meets_bar(rec, finding_has_verify=False) -> bool` is introduced in Task 7 with one parameter and extended in Task 8 with the keyword — Task 7's tests call it without the keyword, which the default preserves. `close(...) -> tuple[bool, str]` is defined in Task 3 and extended in Task 4 without changing its signature; `dry_run` is present from Task 3 because Task 3's tests use it.

**Gap found and fixed during review:** Task 3's `_append` signature did not accept `verified_by`; Task 4 Step 3 now states the signature change explicitly rather than leaving it implied.
