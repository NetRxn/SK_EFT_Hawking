"""Per-finding orientation — ADR-012 D17.

Orientation is GENERATED, not gathered. Re-deriving it per finding from cold context is the
expensive way, and it is what the operator's step 1 was reacting to.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

import review_runner as rr  # noqa: E402


def _a_finding_with_a_target():
    from build_graph import extract_review_finding_nodes
    for n in extract_review_finding_nodes():
        if n["meta"].get("target") and n["meta"].get("status") == "open":
            return n
    return None


class TestPerFindingBrief:
    def test_the_brief_names_the_target_and_its_provenance(self):
        node = _a_finding_with_a_target()
        assert node is not None, (
            "no open finding carries a target — the seam is empty, not clean")
        out = rr.emit_finding_brief(node["id"])
        assert node["meta"]["target"].strip("`") in out
        for heading in ("## TARGET", "## GIT HISTORY", "## ROADMAP",
                        "## SUBSTRATE DELTA"):
            assert heading in out, f"{heading} missing from the brief"

    def test_it_carries_the_routing_fields_a_worker_needs(self):
        node = _a_finding_with_a_target()
        out = rr.emit_finding_brief(node["id"])
        for label in ("LANE:", "BLOCKS:", "VERIFY:", "BLOCKED-BY:", "NEEDS-OPERATOR:"):
            assert label in out

    def test_an_unknown_finding_id_RAISES_rather_than_emitting_an_empty_brief(self):
        """⚠️ An empty brief reads as 'nothing to orient on' when the truth is 'not
        found' — absence rendered as success, in the one artifact a worker trusts."""
        with pytest.raises(KeyError, match="names no minted finding"):
            rr.emit_finding_brief("review:no-such-date:NOPE:1.1")

    def test_the_substrate_delta_prompt_is_always_present(self):
        """The operator's step 1 asks explicitly whether anything moved. A brief that
        omits the question lets a worker skip it silently."""
        node = _a_finding_with_a_target()
        out = rr.emit_finding_brief(node["id"])
        assert "including 'no'" in out


class TestTheCLI:
    def test_finding_is_handled_before_the_bundle_gate(self, capsys):
        """⚠️ `main()` returns 1 on anything without `--bundle`, so a `--finding` handled
        after that gate would exit 1 while printing nothing."""
        node = _a_finding_with_a_target()
        rc = rr.main(["--finding", node["id"]])
        assert rc == 0
        assert "# Orientation —" in capsys.readouterr().out

    def test_an_unknown_id_exits_1_with_a_message_on_stderr(self, capsys):
        rc = rr.main(["--finding", "review:no-such-date:NOPE:1.1"])
        assert rc == 1
        assert "names no minted finding" in capsys.readouterr().err

    def test_main_accepts_argv_so_it_is_testable_in_process(self):
        import inspect
        assert "argv" in inspect.signature(rr.main).parameters
