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
