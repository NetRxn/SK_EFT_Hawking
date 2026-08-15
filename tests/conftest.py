"""Suite-wide fixtures.

THE ONE THING IN HERE, AND WHY IT IS NOT OPTIONAL
-------------------------------------------------
`scripts/validation/_memo.py` caches a PASS verdict for the two most expensive
checks, keyed on a fingerprint of their real inputs. Dozens of tests call those
checks with their internals monkeypatched — a stubbed `subprocess.run`, a fake
`lean_deps.json`, an empty allow-list. Without this, such a test writes a cache
entry keyed on the **real** tree while holding a verdict reached under the
**patch**, and the developer's next `validate.py` reads it back as a genuine PASS.

That is the fixture-vs-production confusion QI-30 named, aimed at the cache: a
result obtained against a patched fixture standing in for a production
measurement. Bypassing the memo for the whole suite removes the possibility
rather than relying on each test to remember.

It is set as an environment variable, not by patching `_config`, so it also
covers checks invoked in a SUBPROCESS (`tests/test_ci_mode.py` and the mutation
harness both shell out to `validate.py`), where a patched module attribute in
this process would not travel.
"""
from __future__ import annotations

import os

os.environ["SKEFT_VALIDATION_NO_MEMO"] = "1"

# ⚠️ Deliberately NOT also setting `SKEFT_VALIDATION_NO_LATEX_CACHE`. The two are
# different: the VERDICT memo is keyed on a check name, so a patched test run can
# poison a key a real run later reads — that one must be off. The LaTeX cache is
# keyed on each draft's own content closure, so a seeded defect changes the hash
# and correctly misses; disabling it only bought a 41.84 s pdflatex recompile of
# all 64 drafts on every slow run. Set `SKEFT_VALIDATION_NO_LATEX_CACHE=1` if you
# genuinely want the recompile.


# ── shared results for expensive, IDEMPOTENT live-corpus checks ──────────────
#
# ⚠️ These exist because a test-quality audit measured the same pure function being
# re-run once per assertion. `check_prose_theorem_reference_coverage()` costs
# **24.6 s** and was called FOUR times unpatched across two files — 97 s, a sixth of
# the fast suite, for one answer. Measured back-to-back: `call1=24.60s call2=23.99s
# identical=True`.
#
# ⚠️ **Session scope is only safe because these take no arguments, read only tracked
# files, and mutate nothing.** A test that monkeypatches the corpus, a ceiling, or a
# resolver MUST keep its own direct call — the fixture would hand it a result
# computed before the patch. Every such site in `test_d5_prose_lean_refs.py` does.

import pytest  # noqa: E402


@pytest.fixture(scope="session")
def prose_ref_coverage_result():
    """`check_prose_theorem_reference_coverage()` over the REAL corpus, once."""
    from validation.checks.prose_lean_refs import (
        check_prose_theorem_reference_coverage,
    )
    return check_prose_theorem_reference_coverage()


@pytest.fixture(scope="session")
def architecture_inventory_result():
    """`check_architecture_inventory_fresh()` over the REAL tree, once.

    Three tests read a different `Detail` out of this same result at ~10.7 s each.
    The one test that monkeypatches the census keeps its own call.
    """
    from validation.checks.freshness import check_architecture_inventory_fresh
    return check_architecture_inventory_fresh()


@pytest.fixture(scope="session")
def chain_backing_result():
    """`check_chain_backing_targets_resolve()` over the REAL corpus, once.

    Three tests each built their own `GraphIndex` (~9-18 s apiece). Only the
    UNPATCHED calls share this; the seeded and empty-corpus tests monkeypatch
    `chain_canonicalize._iter_links` and correctly keep their own.
    """
    from validation.checks import reviews as rv
    return rv.check_chain_backing_targets_resolve()


@pytest.fixture(scope="session")
def bundles_summary():
    """`datastar_bundles.load_bundles_summary()`, once. Measured 11.27 s / 11.40 s
    back-to-back — no memoization, and two tests each paid it.

    ⚠️ Shared HERE, in the tests, and deliberately NOT with an `lru_cache` on
    `datastar_bundles.load_bundles_summary` itself: that module backs a
    long-running dashboard, and caching there would serve a stale roster to a live
    process. Test-local sharing is safe; production-local caching is not.
    """
    from datastar_bundles import load_bundles_summary
    return load_bundles_summary()


@pytest.fixture(scope="session")
def all_graph_nodes():
    """`build_graph.extract_all_nodes()`, once per session.

    ⚠️ Measured 7.11 s for 49,003 nodes, and **24 slow tests each called it at
    FUNCTION scope** — ~284 s, 20% of the slow suite, re-deriving an artifact none
    of them mutates. Safe to share for exactly that reason: the extractors read
    tracked files and return fresh lists.

    A test that monkeypatches an extractor MUST keep its own call.
    """
    from build_graph import extract_all_nodes
    return extract_all_nodes()


@pytest.fixture(scope="session")
def all_graph_node_ids(all_graph_nodes):
    """`{n['id']}` — derived, so callers don't rebuild the set per test."""
    return {n["id"] for n in all_graph_nodes}


@pytest.fixture(scope="session")
def all_graph_edges(all_graph_node_ids):
    """`build_graph.extract_all_edges(node_ids)`, once per session (2.72 s)."""
    from build_graph import extract_all_edges
    return extract_all_edges(all_graph_node_ids)


@pytest.fixture(scope="session")
def graph_integrity_report():
    """`graph_integrity.run_integrity_checks()`, once per session.

    Four tests re-ran this independently. It is a pure read over the same graph.
    """
    from graph_integrity import run_integrity_checks
    return run_integrity_checks()


# ── Orphaned seeded mutations — repaired BEFORE anything reads the corpus ────────────
#
# ⚠️ SESSION-SCOPED, AUTOUSE, AND FIRST. A production-seeded mutation restores in a
# `finally`, which does not run under SIGKILL or a harness timeout. When that happened on
# 2026-08-12 the seed stayed in `papers/AutomatedReviews/.../D10.md` and was consumed as a
# live open CRITICAL for three days. Every subsequent test run read the polluted corpus and
# reported cleanly on it, because nothing looked.
#
# This runs the repair at session start rather than at session end deliberately: the run
# that CRASHES cannot repair itself, so the repair has to belong to the NEXT run. It also
# runs before the first test touches the corpus, so a suite whose ratchets count findings
# counts the real ones.
#
# ⚠️ IT ANNOUNCES ITSELF. A silent repair would make the crash invisible, and the killed
# run is a fact worth knowing — `-s` shows it, and `seed_residue_absent` reports the same
# state to anyone who does not run pytest at all.
@pytest.fixture(scope="session", autouse=True)
def _repair_orphaned_seeds():
    """Restore any production artifact a killed run left seeded. See `scripts/seed_journal.py`."""
    import sys as _sys
    from pathlib import Path as _Path
    _sys.path.insert(0, str(_Path(__file__).resolve().parent.parent / "scripts"))
    try:
        import seed_journal
    except ImportError:                       # pragma: no cover - the module is tracked
        yield
        return
    actions = seed_journal.repair()
    if actions:
        banner = "\n".join(f"  • {a}" for a in actions)
        print(f"\n⚠️  SEED JOURNAL: repaired {len(actions)} orphaned seeded mutation(s) "
              f"left by a killed run:\n{banner}\n", file=_sys.stderr)
    yield
