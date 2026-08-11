"""The skeft-qa plugin's prompts reference code. Nothing checked that the code exists.

The repo already enforces that a Python docstring naming a Lean theorem must resolve
(`lean_docstring_refs_resolve`) and that bundle prose naming a declaration must resolve
(`prose_theorem_reference_coverage`). Agent prompts name check names, registry symbols
and file paths with the same authority and had no equivalent guard — so a renamed check
or a moved file degraded a reviewer's instructions silently, and the reviewer's output
still looked like a review.

Deliberately a TEST rather than a `validate.py` check: this is a repo-consistency
invariant, not a claim about the physics/paper corpus, and it needs no place in the
validation gate topology.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import pytest  # noqa: E402

PLUGIN = SK_ROOT / ".claude" / "plugins" / "skeft-qa"

_CHECK_REF = re.compile(r"validate\.py\s+--check\s+([a-z0-9_]+)")
_SCRIPT_REF = re.compile(r"`(scripts/[A-Za-z0-9_./-]+\.py)`")


def _plugin_files():
    if not PLUGIN.is_dir():
        return []
    return sorted(p for ext in ("*.md", "*.py") for p in PLUGIN.rglob(ext))


pytestmark = pytest.mark.skipif(not PLUGIN.is_dir(),
                                reason="skeft-qa plugin not installed in this checkout")


def test_every_referenced_check_name_is_registered():
    """A prompt naming `validate.py --check X` must name a real check.

    A dead name does not error — the agent runs it, `validate.py` returns rc 2, and the
    reviewer proceeds with one fewer piece of evidence than its instructions claim.
    """
    import validate
    live = {spec.name for spec in validate._CHECKS}
    dead = {}
    for f in _plugin_files():
        for name in _CHECK_REF.findall(f.read_text(errors="replace")):
            if name not in live:
                dead.setdefault(str(f.relative_to(PLUGIN)), set()).add(name)
    assert not dead, (
        f"plugin prompts reference check names that are not registered: "
        f"{ {k: sorted(v) for k, v in dead.items()} }. Repoint them at the live check, "
        f"or delete the reference — an agent told to run a check that does not exist "
        f"silently reviews with less evidence than its prompt promises.")


def test_every_referenced_script_path_exists():
    """Same rule for `scripts/*.py` paths quoted in a prompt.

    A prompt's `scripts/foo.py` may mean the REPO's `scripts/` or the PLUGIN's own
    `scripts/` — both are real and both are referenced this way. Resolve against either;
    requiring the repo root would fail on correct references to plugin-local tooling.
    """
    missing = {}
    for f in _plugin_files():
        for rel in _SCRIPT_REF.findall(f.read_text(errors="replace")):
            if not ((SK_ROOT / rel).is_file() or (PLUGIN / rel).is_file()):
                missing.setdefault(str(f.relative_to(PLUGIN)), set()).add(rel)
    assert not missing, (
        f"plugin prompts reference script paths that do not exist: "
        f"{ {k: sorted(v) for k, v in missing.items()} }")


def test_no_prompt_hardcodes_a_bundle_roster():
    """The roster lives in `bundle_registry.BUNDLE_CODES`. A prompt that enumerates it
    goes stale on the next authorization, and the failure is invisible: the reviewer
    simply never considers the bundles its list omits.

    Both bundle-aware reviewers carried `F, D1–D5, L1–L3, I1, I2, E1, E2` — 13 codes
    against a canonical 21, so D6–D12 and I3 were outside their scope entirely.
    """
    import bundle_registry as br
    live = set(br.BUNDLE_CODES)
    # A prompt that names >= 6 distinct bundle codes is enumerating, not illustrating —
    # the same threshold `bundle_registry_consistency` Leg C uses for scripts.
    code_re = re.compile(r"`(" + "|".join(sorted(live, key=len, reverse=True)) + r")`")
    offenders = {}
    for f in _plugin_files():
        found = set(code_re.findall(f.read_text(errors="replace")))
        if len(found) >= 6 and found != live:
            offenders[str(f.relative_to(PLUGIN))] = sorted(found)
    assert not offenders, (
        f"plugin prompt(s) enumerate a PARTIAL bundle roster: {offenders}. Point at "
        f"`scripts/bundle_registry.py::BUNDLE_CODES` instead — the live roster is "
        f"{len(live)} codes and grows by authorization.")
