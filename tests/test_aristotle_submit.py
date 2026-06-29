"""Tests for the safe Aristotle submission engine (ADR-006), focused on the
D7 staged-environment pre-clean (closure-aware require/manifest prune).

These are pure-function tests over synthetic lakefile/manifest strings — no
network, no `lake`, no staging of the real tree — so they run in the fast suite.
The slow `verify_staged_build` gate (which shells out to `lake`) is not tested
here; it is exercised manually per-submission.
"""
import json

from src.core import aristotle_submit as A

# A synthetic lakefile mirroring the real structure: preamble, three [[require]]
# blocks (mathlib / repl / Physlib, the last with a preceding comment), a
# [[lean_lib]], and a [[lean_exe]] metaprogram stanza.
_LAKEFILE = """\
name = "sk-eft-hawking"
defaultTargets = ["SKEFTHawking"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[require]]
name = "repl"
git = "https://github.com/leanprover-community/repl.git"
rev = "abc"

# Physlib provides the QuantumNetwork floor lemmas.
[[require]]
name = "Physlib"
git = "https://github.com/leanprover-community/physlib.git"
rev = "def"

[[lean_lib]]
name = "SKEFTHawking"

[[lean_exe]]
name = "extractDeps"
root = "SKEFTHawking.ExtractDeps"
"""

_MANIFEST = json.dumps({
    "version": "1.1.0",
    "packages": [
        {"name": "Physlib", "rev": "def"},
        {"name": "repl", "rev": "abc"},
        {"name": "mathlib", "rev": "5e932f97"},
        {"name": "Cli", "rev": "x"},
        {"name": "batteries", "rev": "y"},
    ],
})


def test_parse_lakefile_blocks_preamble_and_stanzas():
    blocks = A._parse_lakefile_blocks(_LAKEFILE)
    # blocks[0] is the preamble (no leading [[...]]); the rest each start with [[
    assert 'name = "sk-eft-hawking"' in blocks[0]
    assert not blocks[0].lstrip().startswith("[[")
    assert sum(b.lstrip().startswith("[[require]]") for b in blocks) == 3
    assert sum(b.lstrip().startswith("[[lean_exe]]") for b in blocks) == 1


def test_prune_l2_like_closure_drops_physlib_and_repl():
    # An L2-like closure imports only Mathlib + SKEFTHawking.
    prune = A._prunable_require_names(_LAKEFILE, {"Mathlib", "SKEFTHawking"})
    assert prune == {"Physlib", "repl"}


def test_prune_keeps_physlib_when_closure_imports_it():
    # A QuantumNetwork-like closure imports Physlib -> it must survive.
    prune = A._prunable_require_names(_LAKEFILE, {"Mathlib", "SKEFTHawking", "Physlib"})
    assert prune == {"repl"}


def test_mathlib_is_never_pruned():
    # Even an (unrealistic) closure importing nothing keeps mathlib.
    prune = A._prunable_require_names(_LAKEFILE, set())
    assert "mathlib" not in {p.lower() for p in prune}


def test_staged_lakefile_drops_pruned_requires_and_lean_exe_keeps_lib():
    out = A._staged_lakefile(_LAKEFILE, frozenset({"Physlib", "repl"}))
    assert 'name = "mathlib"' in out
    assert "[[lean_lib]]" in out
    assert 'name = "SKEFTHawking"' in out
    assert "[[lean_exe]]" not in out          # metaprogram stanza dropped
    assert 'name = "repl"' not in out
    assert 'name = "Physlib"' not in out


def test_staged_manifest_drops_pruned_package_entries():
    out = A._staged_manifest(_MANIFEST, frozenset({"Physlib", "repl"}))
    names = {p["name"] for p in json.loads(out)["packages"]}
    assert "mathlib" in names and "Cli" in names and "batteries" in names
    assert "Physlib" not in names and "repl" not in names


def test_staged_manifest_invalid_json_is_returned_verbatim():
    assert A._staged_manifest("not json", frozenset({"repl"})) == "not json"
