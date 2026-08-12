"""Parked work — ADR-012 D19.

Spec: `docs/superpowers/specs/2026-08-12-finding-closure-lifecycle-design.md` §5.1.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

import parked_items as pi  # noqa: E402

BLOCK = """
Some roadmap prose above.

<!-- PARKED
id: mlx-rhmc-campaign
lane: pyrust
target: docs/RHMC_CAMPAIGN_SEQUENCE.md
blocked_by: run:mlx-rhmc-2026-08
reason: campaign staged; the operator launches it, results gate the analysis wave
-->

More prose below.
"""


class TestParkedBlocks:
    def test_a_block_parses_into_a_queue_item(self):
        items = pi.parse_parked_blocks(BLOCK, "docs/roadmaps/PhaseX_Roadmap.md")
        assert len(items) == 1
        it = items[0]
        assert it["id"] == "parked:mlx-rhmc-campaign"
        assert it["type"] == "ParkedItem"
        assert it["meta"]["lane"] == "pyrust"
        assert it["meta"]["blocked_by"] == ["run:mlx-rhmc-2026-08"]
        assert it["meta"]["source"] == "docs/roadmaps/PhaseX_Roadmap.md"
        assert "operator launches it" in it["meta"]["reason"]

    def test_it_is_shaped_like_a_finding_node(self):
        """Same shape on purpose, so one consumer works on both without a second path."""
        it = pi.parse_parked_blocks(BLOCK, "r.md")[0]
        assert set(it) >= {"id", "type", "meta"}
        assert set(it["meta"]) >= {"lane", "blocked_by", "status"}

    def test_a_block_with_no_release_condition_is_REJECTED(self):
        """A parked item with no `blocked_by` is not parked, it is abandoned — and the
        queue must be able to tell those apart."""
        with pytest.raises(ValueError, match="blocked_by"):
            pi.parse_parked_blocks("<!-- PARKED\nid: x\nlane: prose\n-->", "r.md")

    def test_a_document_with_no_block_yields_nothing(self):
        assert pi.parse_parked_blocks("# Just a roadmap\n\nNo blocks here.\n", "r.md") == []

    def test_several_blocks_in_one_document(self):
        two = BLOCK + BLOCK.replace("mlx-rhmc-campaign", "second-item")
        assert len(pi.parse_parked_blocks(two, "r.md")) == 2


class TestReleaseConditions:
    def test_an_unrecognised_scheme_is_UNKNOWN_never_met(self):
        """⚠️ None is not False. Reporting an unresolvable condition as UNMET makes a
        released item look parked forever; reporting it as MET releases work on no
        evidence."""
        assert pi.release_condition_met("wizardry:42") is None
        assert pi.release_condition_met("run:") is None

    def test_a_run_condition_is_UNKNOWN_until_a_run_registry_exists(self):
        """Deliberate. Returning False would render every staged campaign permanently
        parked, which is worse than admitting we cannot tell."""
        assert pi.release_condition_met("run:mlx-rhmc-2026-08") is None

    def test_an_unknown_phase_is_UNKNOWN_not_unmet(self):
        assert pi.release_condition_met("phase:no-such-phase-anywhere") is None

    def test_a_closed_phase_reads_released(self):
        """Phase 5 closed long ago; its roadmap carries a COMPLETE status marker."""
        assert pi.release_condition_met("phase:Phase5_Roadmap") is True

    def test_an_unknown_citekey_is_UNKNOWN(self):
        assert pi.release_condition_met("pub:NoSuchKey2099") is None

    def test_the_release_schemes_are_the_shared_declaration(self):
        """Imported from build_graph, never restated — two declarations of one vocabulary
        is how they drift. And there is deliberately no `operator:` scheme."""
        import build_graph as bg
        assert pi.RELEASE_SCHEMES == bg._RELEASE_SCHEMES
        assert not any(s.startswith("operator") for s in pi.RELEASE_SCHEMES)


class TestTheLiveCorpus:
    def test_every_roadmap_parses_without_raising(self):
        """The corpus is untouched by this change — the block is opt-in — so this asserts
        the parser is inert over it rather than that anything is parked yet."""
        items = pi.collect()
        assert isinstance(items, list)

    def test_a_seeded_block_is_collected_from_the_real_directory(self, tmp_path):
        d = tmp_path / "roadmaps"
        d.mkdir()
        (d / "PhaseZ_Roadmap.md").write_text(BLOCK, encoding="utf-8")
        items = pi.collect(d)
        assert [i["id"] for i in items] == ["parked:mlx-rhmc-campaign"]
