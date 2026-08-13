"""Gate on the Stage-14 QI derivation — ADR-012 P9a Task 4.

WHAT THIS FILE IS DEFENDING
---------------------------
`qi_register.cluster_findings` derived **zero** QI items from 1,655 ReviewFinding
nodes (946 open). The cause was not a threshold and not a missing input: the item id
was `qi-{gate.lower()}`, derived **solely** from the gate name, so the register could
hold at most one item per gate for all time. Nine of the eleven gate ids sit in
`## Closed Items`, and a closed id is skipped forever — the detector was switched off
by its own success. Separately, the largest single bucket in the corpus
(`unclassified`, 246 open findings across 25 papers under the OLD `inferred_paper`-only partition; `--stats` now reports 42 under the shipped paper-or-bundle partition) was dropped by a bare `continue`
with no trace, which reads as "no recurrent failure modes" rather than "the detector
cannot name them".

⚠️ WHERE A TEST HERE CHECKS THAT A FUNCTION IS CALLED, IT PARSES WITH `ast` AND
ASSERTS THE `Call` NODE. `CHECK_AUTHORING_GUIDE.md` §2.5: a source-substring scan for
a helper's name finds it in a comment or a docstring and passes over a seeded
regression — and this module's docstrings name every helper it defines, so a substring
scan here would be vacuous by construction.

Every test in this file was mutation-checked by seeding the defect into
`scripts/qi_register.py` itself — the production artifact the tests read — running the
file, watching it go red, and restoring.
"""
from __future__ import annotations

import ast
import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import qi_register as q  # noqa: E402

SOURCE = ROOT / "scripts" / "qi_register.py"


# ── helpers ────────────────────────────────────────────────────────────────

def _func_def(name: str) -> ast.FunctionDef:
    """The `ast` node for one top-level function of the production module."""
    tree = ast.parse(SOURCE.read_text(encoding="utf-8"))
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name == name:
            return node
    raise AssertionError(f"scripts/qi_register.py defines no function {name!r}")


def _called_names(node: ast.AST) -> set[str]:
    """Every name invoked as a CALL inside `node` — not every name mentioned."""
    out = set()
    for c in ast.walk(node):
        if isinstance(c, ast.Call):
            if isinstance(c.func, ast.Name):
                out.add(c.func.id)
            elif isinstance(c.func, ast.Attribute):
                out.add(c.func.attr)
    return out


@pytest.fixture(scope="module")
def findings():
    return q.load_review_findings()


@pytest.fixture(scope="module")
def stats(findings):
    return q.derive_stats(findings)


# ── the id identifies a recurrence, not a gate ─────────────────────────────

def test_the_id_is_not_the_gate_name_alone():
    """⚠️ THE SATURATION. `qi-{gate}` caps the register at one item per gate FOREVER;
    once closed, that failure class can never be detected again. Nine of eleven are
    already closed, which is why the detector emits nothing."""
    ids = {q.qi_id_for(gate='CitationIntegrity', papers=['D1', 'D2'], window='2026-08'),
           q.qi_id_for(gate='CitationIntegrity', papers=['D5', 'D7'], window='2026-08')}
    assert len(ids) == 2, "two distinct recurrences collapsed onto one id"


def test_the_id_distinguishes_two_windows_of_the_same_gate_and_papers():
    """The papers leg alone is not enough. The same gate failing on the same papers in
    July and again in August is two recurrences, and it is the WINDOW that carries that
    — it is the leg that un-saturates a gate whose paper set is stable."""
    same_papers = ['D1', 'D2']
    assert (q.qi_id_for(gate='CitationIntegrity', papers=same_papers, window='2026-07')
            != q.qi_id_for(gate='CitationIntegrity', papers=same_papers, window='2026-08'))


def test_the_id_is_order_independent_in_its_paper_set():
    """`{D2, D1}` and `{D1, D2}` are one recurrence. If the id depended on iteration
    order it would be unstable across runs and every regen would look like a new
    occurrence."""
    assert (q.qi_id_for(gate='FixPropagation', papers=['D2', 'D1'], window='2026-08')
            == q.qi_id_for(gate='FixPropagation', papers=['D1', 'D2'], window='2026-08'))


def test_the_derivation_CALLS_qi_id_for():
    """⚠️ VIA `ast`, ASSERTING THE CALL (`CHECK_AUTHORING_GUIDE.md` §2.5). `qi_id_for`
    existing and being correct proves nothing if the derivation still formats its own
    `f'qi-{gate.lower()}'`; the defect is in the emit loop, not in the helper."""
    called = _called_names(_func_def('derive_stats'))
    assert 'qi_id_for' in called, "derive_stats does not call qi_id_for"


def test_cluster_findings_does_not_reimplement_the_derivation():
    """Two implementations of one derivation is how they drift. `cluster_findings` is
    the public entry point every caller uses (`provenance_dashboard./api/qi`), so it
    must DELEGATE — otherwise `derive_stats`'s accounting describes a derivation the
    callers do not run."""
    node = _func_def('cluster_findings')
    assert 'derive_stats' in _called_names(node)
    assert 'qi_id_for' not in _called_names(node), \
        "cluster_findings builds ids itself instead of delegating"


# ── the unclassified bucket is reported, not dropped ───────────────────────

def test_unclassified_findings_are_REPORTED_not_dropped(stats):
    """The largest bucket is the one the detector discards. A recurrence the keyword
    map cannot name is still a recurrence, and silence about it reads as 'nothing
    there'."""
    assert stats['unclassified_open'] > 0
    assert stats['unclassified_reported'] is True
    assert stats['unclassified_papers'] > 0
    assert stats['unclassified_by_window'], "no per-window breakdown of the bucket"


def test_derive_stats_loads_the_corpus_when_given_nothing():
    """The plan calls `derive_stats()` with no argument, and the dashboard may too. A
    default that silently derives over an empty list would report
    `unclassified_open == 0` and look like a clean corpus."""
    assert q.derive_stats()['unclassified_open'] > 0


def test_every_cluster_is_accounted_for(stats, findings):
    """⚠️ GUARD THE SEAM (§2.5). Emitted + suppressed + sub-threshold + unclassified
    must exhaust the cluster population, or a future `continue` can drop a bucket the
    way `unclassified` was dropped and leave no arithmetic trace."""
    accounted = (stats['qi_items_detected']
                 + len(stats['clusters_suppressed_by_closure'])
                 + len(stats['clusters_below_paper_threshold'])
                 + len(stats['unclassified_by_window']))
    assert accounted == stats['clusters_total'], (
        f"{stats['clusters_total'] - accounted} cluster(s) vanished without being "
        f"counted in any reported bucket")
    assert stats['clusters_total'] > 10, "cluster population implausibly small"
    assert stats['open_total'] == sum(stats['gate_open_counts'].values())
    assert stats['findings_total'] == len(findings) > 100


# ── Invariant #13: a closure is per-occurrence, not per-gate-forever ───────

def test_a_closed_item_is_not_reopened_by_the_same_gate_recurring(findings):
    """Invariant #13. Closure is per-occurrence; a new occurrence gets a NEW id."""
    closed, _ = q.load_closed_qi_ids()
    items = q.cluster_findings(findings)
    assert not ({i['id'] for i in items} & closed)


def test_a_legacy_gate_closure_still_suppresses_its_OWN_window(stats):
    """⚠️ THE OTHER HALF, and the one the id change puts at risk. `## Closed Items`
    holds date-free `qi-{gate}` ids that `qi_id_for` cannot reproduce, so nothing in
    the new scheme stops the very occurrence those blocks closed from re-emitting as a
    fresh item. `closed_qi_windows` reconstructs the bound; without it the April 2026
    Phase-6i closures would all reopen."""
    suppressed = stats['clusters_suppressed_by_closure']
    assert suppressed, "no cluster was suppressed by a closure — closures are inert"
    assert any(s['closed_by'] == 'qi-citationintegrity' for s in suppressed)


def test_no_emitted_item_predates_its_gates_closure(stats):
    """The suppression must be a WINDOW bound, not a filter that happens to fire. Every
    emitted item whose gate carries a legacy closure must sit strictly after it."""
    windows = stats['closed_qi_windows']
    for item in stats['items']:
        legacy = f"qi-{item['gate_affected'].lower()}"
        closed_through = windows.get(legacy)
        if closed_through:
            assert item['window'] > closed_through, (
                f"{item['id']} re-opens {legacy}, closed through {closed_through}")


def test_a_closure_window_comes_from_the_whole_block_not_its_heading():
    """⚠️ PRODUCTION-SEEDED, against `docs/QI_REGISTER.md` as it stands. A closure block
    records RE-closures in its body: `qi-assumptiondisclosure` reads
    'closed 2026-04-29' in its heading and 'RE-CLOSED VIA STRUCTURAL PREVENTION
    (2026-06-13)' in its body. Reading only the heading would reopen the May and June
    occurrences of a class whose closure policy explicitly says it closes only via
    structural prevention."""
    windows = q.closed_qi_windows()
    assert windows['qi-assumptiondisclosure'] == '2026-06', (
        "closure window read from the heading date, not the latest date in the block")
    assert windows['qi-citationintegrity'] == '2026-04'


def test_the_derivation_consults_the_closure_windows():
    """⚠️ VIA `ast`. `closed_qi_windows` can be correct and unused — that is exactly the
    shape of the bug it exists to prevent."""
    assert 'closed_qi_windows' in _called_names(_func_def('derive_stats'))


# ── the end-to-end assertion ───────────────────────────────────────────────

def test_the_derivation_is_not_saturated(findings):
    """A corpus of this size (2026-08-12: 1,663 findings, 954 open), must not produce zero items."""
    items = q.cluster_findings(findings)
    assert items, "derivation still saturated"


def test_bundle_era_findings_reach_the_cross_paper_threshold(findings, stats):
    """⚠️ THE SECOND CAUSE OF THE SATURATION, and one the plan does not name.
    Partitioning on `inferred_paper` alone collapses every bundle-era finding onto the
    single `(unknown)` sentinel — measured live, 687 open findings carry
    `inferred_bundle` and NO `inferred_paper`. The ≥2-paper threshold was therefore
    being evaluated against a seventh of the corpus's spread.
    `bundle_readiness.load_findings_by_paper` took this fallback on 2026-07-31 after
    the same omission produced a FALSE GREEN there; this module never did."""
    open_meta = [(f.get('meta') or {}) for f in findings
                 if ((f.get('meta') or {}).get('status', 'open')) == 'open']
    bundle_only = {m['inferred_bundle'] for m in open_meta
                   if not m.get('inferred_paper') and m.get('inferred_bundle')}
    assert len(bundle_only) > 1, "corpus shape changed — re-derive this gate"

    reached = {p for it in stats['items'] for p in it['affected_papers']} & bundle_only
    assert reached, (
        "no emitted item names a bundle-only attribution: bundle-era findings are "
        "still collapsed onto the '(unknown)' sentinel")


def test_emitted_items_carry_the_fields_their_consumers_read(stats):
    """`render_register` and the dashboard's `/api/qi` both index these directly; a
    KeyError there surfaces as an empty Process Health panel, not as a failure."""
    for item in stats['items']:
        for key in ('id', 'pattern_summary', 'gate_affected', 'window', 'occurrences',
                    'affected_papers', 'severity_mix', 'first_observed',
                    'last_observed', 'status', 'owner', 'target_date',
                    'evidence_on_close', 'representative_findings'):
            assert key in item, f"{item['id']} is missing {key!r}"
        assert item['status'] == 'open'


def test_the_stats_cli_reports_both_numbers():
    """The operator-facing contract from the plan's DONE list: `--stats` reports a
    non-zero detected count AND the unclassified total. Run as a SUBPROCESS, because
    that is how the operator runs it and it is the only way `main()`'s wiring is
    exercised."""
    proc = subprocess.run([sys.executable, str(SOURCE), '--stats'],
                          cwd=ROOT, capture_output=True, text=True)
    assert proc.returncode == 0, proc.stderr
    out = json.loads(proc.stdout)
    assert out['qi_items_detected'] > 0
    assert out['unclassified_open'] > 0
    assert out['unclassified_reported'] is True


# ── Invariant #13, the other direction: regeneration must not wipe ─────────

def test_regeneration_refuses_to_delete_hand_curated_open_items(tmp_path, monkeypatch):
    """⚠️ `## Open Items` holds hand-curated entries (`qi-bibfilename`,
    `qi-vizdiscipline`, …) in a pre-derivation id style that no derivation reproduces,
    and `render_register` rebuilds that section purely from the derived list — so a
    regen DELETES them. Invariant #13 says the register is never wiped. This was true
    before the id scheme changed; it matters more now, because the derivation emits
    again and a regen is newly tempting."""
    assert q.load_open_qi_ids(), "no hand-curated Open Items to protect — re-derive"

    target = tmp_path / "QI_REGISTER.md"
    shutil.copy(q.REGISTER_PATH, target)
    before = target.read_text(encoding="utf-8")
    monkeypatch.setattr(q, 'REGISTER_PATH', target)
    monkeypatch.setattr(sys, 'argv', ['qi_register.py'])

    rc = q.main()
    assert rc == 1, "regeneration wrote over hand-curated Open Items"
    assert target.read_text(encoding="utf-8") == before, "register was modified anyway"


def test_the_writer_consults_the_open_items_guard():
    """⚠️ VIA `ast`. The guard is only a guard if `main` calls it before writing."""
    called = _called_names(_func_def('main'))
    assert 'load_open_qi_ids' in called
    assert 'write_text' in called, "main no longer writes at all — re-derive this gate"


# ── Manual fields survive a regeneration (pr-review IMPORTANT I5) ──────────────────────

def test_hand_curated_fields_survive_a_regeneration(tmp_path, monkeypatch):
    """⚠️ THE GUARD SAW VANISHED IDS, NOT VANISHED FIELDS. `main()` refuses to write when a
    curated id is ABSENT from the derivation — but an id the derivation still reproduces
    sailed through while the renderer rebuilt its Owner/Target date from the derived dict,
    where both are hardcoded `None`. Assign an owner, regenerate, and it silently became
    `_(unassigned)_` — while the register's own text asserted the generator "does NOT
    overwrite manual fields"."""
    import qi_register as q
    reg = tmp_path / "QI_REGISTER.md"
    reg.write_text(
        "# QI\n\n## Open Items\n\n### qi-x-1234abcd — a thing\n\n"
        "- **Owner:** J. Roehm\n- **Target date:** 2026-09-15\n- **Status:** in-progress\n"
        "\n## Closed Items\n\n")
    monkeypatch.setattr(q, "REGISTER_PATH", reg)
    got = q.load_manual_fields()
    assert got["qi-x-1234abcd"] == {"owner": "J. Roehm", "target_date": "2026-09-15",
                                    "status": "in-progress"}


def test_the_renderers_own_placeholders_do_not_read_back_as_values(tmp_path, monkeypatch):
    """`_(unassigned)_` is the renderer saying "no value". Reading it back as one would turn
    a blank into a curated blank and pin it forever."""
    import qi_register as q
    reg = tmp_path / "QI_REGISTER.md"
    reg.write_text("# QI\n\n## Open Items\n\n### qi-y-9999 — a thing\n\n"
                   "- **Owner:** _(unassigned)_\n- **Target date:** _(unset)_\n"
                   "\n## Closed Items\n\n")
    monkeypatch.setattr(q, "REGISTER_PATH", reg)
    assert q.load_manual_fields() == {}


def test_the_register_no_longer_claims_a_persistence_it_lacks():
    """The document used to assert manual-field persistence and then admit, in the same
    sentence, that it was "a follow-up". Now it is true, so the admission must go."""
    import qi_register as q
    text = q.render_register([], 0, {})
    assert "manual-field persistence is a follow-up" not in text
    assert "read back and preserved across regenerations" in text
