"""TODO-D26 / ADR-011 F-02: a source registration must not create a section.

MEASURED before the change, across all 21 bundles' `append_log.json`: **74 of 74
content lifts inserted a top-level `\\section`.** The `§§` subsection form the old
`is_subsection` hint recognised was used zero times — nothing ever required it,
so registering a source silently bought a heading. 28 of those 74 landed in D3,
which is how it reached 31 top-level sections.

⚠️ The fix is NOT "stop inserting a skeleton". `bundle_section_inserted` is the
anchor the absorption protocol reads; an append that inserts nothing makes that
field meaningless. These tests pin both halves: the default path now attaches a
`\\subsection` inside a section that already exists, AND every lift still writes
a resolvable anchor.

The section-plan source of truth is the draft's own top-level sections rather
than a separate `CHARTER.md`: a plan stored beside the document it describes
drifts from it, a plan read from the document cannot.
"""
from __future__ import annotations

import json
import pathlib
import subprocess
import sys

import pytest

REPO = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))

from bundle_append import (  # noqa: E402
    _append_section_to_draft,
    _resolve_target_section,
    _top_level_sections,
)

DRAFT = r"""\documentclass{revtex4-2}
\begin{document}
\title{T}
\maketitle

\section{Introduction}
Intro body.

%% \section{This one is a comment banner, not structure}

\section{Anyons in $\mathbb{Z}_{16}$ and other braces}
Body with a \subsection{existing sub} inside.

\section{Conclusion}
Closing body.

%% BUNDLE_APPEND_INSERT_HERE — marker

\bibliography{bibliography}
\end{document}
"""


@pytest.fixture
def draft(tmp_path):
    p = tmp_path / "paper_draft.tex"
    p.write_text(DRAFT)
    return p


class TestSectionPlanIsReadFromTheDraft:
    def test_titles_survive_nested_braces(self, draft):
        """A `[^}]*` title scan stops inside `\\mathbb{Z}` and truncates. This is
        the same brace-matching trap that mis-parsed the D3 restructuring."""
        titles = [t for t, _s, _e in _top_level_sections(draft.read_text())]
        assert titles == [
            "Introduction",
            r"Anyons in $\mathbb{Z}_{16}$ and other braces",
            "Conclusion",
        ]

    def test_a_commented_section_is_not_structure(self, draft):
        """This script writes `%% ─── Lifted from ...` banners around every
        skeleton; a scan that counted commented `\\section` would append into
        its own bookkeeping."""
        assert not any("comment banner" in t
                       for t, _s, _e in _top_level_sections(draft.read_text()))

    @pytest.mark.parametrize("wanted", ["Conclusion", "conclusion", "onclusio"])
    def test_matching_widens_exact_then_fold_then_substring(self, draft, wanted):
        title, _off = _resolve_target_section(draft.read_text(), wanted)
        assert title == "Conclusion"

    def test_an_absent_section_lists_what_the_draft_has(self, draft):
        """Guessing would file content under the wrong argument, which is the
        failure the target is meant to prevent."""
        with pytest.raises(LookupError) as exc:
            _resolve_target_section(draft.read_text(), "Methods")
        msg = str(exc.value)
        assert "Introduction" in msg and "Conclusion" in msg
        assert "--new-section" in msg

    def test_an_ambiguous_name_is_an_error_not_a_first_match(self, tmp_path):
        p = tmp_path / "d.tex"
        p.write_text("\\section{Results A}\nx\n\\section{Results B}\ny\n"
                     "\\end{document}\n")
        with pytest.raises(LookupError, match="matches 2 sections"):
            _resolve_target_section(p.read_text(), "Results")


class TestTheDefaultPathDoesNotCreateASection:
    def test_a_targeted_lift_adds_a_subsection_and_no_section(self, draft):
        before = len(_top_level_sections(draft.read_text()))
        ok, msg, anchor = _append_section_to_draft(
            draft, bundle="D3", source="paper99_x", source_title="New Result",
            insertion_point="§2", notes="", target_section="Conclusion",
        )
        assert ok, msg
        text = draft.read_text()
        assert len(_top_level_sections(text)) == before
        assert r"\subsection{New Result}" in text
        assert r"\section{New Result}" not in text
        assert anchor == "§ Conclusion / §§ New Result"

    def test_the_subsection_lands_inside_the_named_section(self, draft):
        _append_section_to_draft(
            draft, bundle="D3", source="paper99_x", source_title="New Result",
            insertion_point="§2", notes="", target_section="Introduction",
        )
        text = draft.read_text()
        # It must sit after \section{Introduction} and before the next section.
        intro = text.index(r"\section{Introduction}")
        nxt = text.index(r"\section{Anyons")
        assert intro < text.index(r"\subsection{New Result}") < nxt

    def test_the_lift_lands_before_the_next_sections_banner(self, tmp_path):
        """Every draft in this corpus precedes a `\\section` with a
        `%% ===== §N — ... =====` banner. Inserting exactly at the terminator
        put the new subsection *between the banner and the section it
        announces*, so the banner read as belonging to the wrong body."""
        p = tmp_path / "d.tex"
        p.write_text(
            "\\section{One}\nBody.\n\n"
            "%% =====================\n%% \u00a72 \u2014 Two\n%% =====================\n"
            "\\section{Two}\nBody two.\n\\end{document}\n")
        _append_section_to_draft(
            p, bundle="D3", source="s", source_title="Lifted",
            insertion_point="\u00a71", notes="", target_section="One")
        lines = p.read_text().splitlines()
        lifted = next(i for i, l in enumerate(lines) if r"\subsection{Lifted}" in l)
        banner = next(i for i, l in enumerate(lines) if l.startswith("%% \u00a72"))
        assert lifted < banner

    def test_an_unresolvable_target_leaves_the_draft_byte_identical(self, draft):
        before = draft.read_text()
        ok, msg, anchor = _append_section_to_draft(
            draft, bundle="D3", source="p", source_title="T",
            insertion_point="§2", notes="", target_section="Nonexistent",
        )
        assert not ok and anchor == ""
        assert draft.read_text() == before


class TestCreatingASectionIsExplicitAndJustified:
    def test_new_section_records_its_rationale_in_the_draft(self, draft):
        ok, _msg, anchor = _append_section_to_draft(
            draft, bundle="D3", source="paper99_x", source_title="Whole New Thread",
            insertion_point="§9", notes="", new_section=True,
            section_rationale="no existing section argues this channel",
        )
        assert ok
        text = draft.read_text()
        assert r"\section{Whole New Thread}" in text
        assert "no existing section argues this channel" in text
        assert anchor == "§ (new) Whole New Thread"

    def test_cli_refuses_a_lift_that_names_neither(self):
        """The measured defect was that the section came for free. It no longer
        does, and the refusal names the remedy."""
        r = subprocess.run(
            [sys.executable, "scripts/bundle_append.py", "--bundle", "D3",
             "--source-paper", "paper99_x", "--insertion-point", "§2"],
            cwd=REPO, capture_output=True, text=True,
        )
        assert r.returncode == 2
        assert "--target-section" in r.stderr and "F-02" in r.stderr

    def test_cli_refuses_a_new_section_with_no_rationale(self):
        r = subprocess.run(
            [sys.executable, "scripts/bundle_append.py", "--bundle", "D3",
             "--source-paper", "paper99_x", "--insertion-point", "§2",
             "--new-section"],
            cwd=REPO, capture_output=True, text=True,
        )
        assert r.returncode == 2
        assert "--section-rationale" in r.stderr

    def test_cli_refuses_both_at_once(self):
        r = subprocess.run(
            [sys.executable, "scripts/bundle_append.py", "--bundle", "D3",
             "--source-paper", "paper99_x", "--insertion-point", "§2",
             "--new-section", "--section-rationale", "x",
             "--target-section", "Conclusion"],
            cwd=REPO, capture_output=True, text=True,
        )
        assert r.returncode == 2
        assert "exclusive" in r.stderr


class TestTheAnchorStaysMeaningful:
    """⚠️ Removing the skeleton insertion alone would leave appends with no
    structural anchor, and `append_log.json`'s `bundle_section_inserted` — read
    by the absorption protocol — would become meaningless. Both shapes must
    still produce an anchor that names a place a reader can find."""

    def test_every_shape_returns_a_locatable_anchor(self, draft):
        _ok, _m, sub_anchor = _append_section_to_draft(
            draft, bundle="D3", source="a", source_title="Sub Lift",
            insertion_point="§2", notes="", target_section="Conclusion")
        _ok, _m, new_anchor = _append_section_to_draft(
            draft, bundle="D3", source="b", source_title="Sec Lift",
            insertion_point="§9", notes="", new_section=True,
            section_rationale="r")
        text = draft.read_text()
        assert "Conclusion" in sub_anchor and "Sub Lift" in sub_anchor
        assert r"\subsection{Sub Lift}" in text
        assert "Sec Lift" in new_anchor and r"\section{Sec Lift}" in text

    def test_every_script_written_event_carries_an_anchor(self):
        """Measured over the live corpus: 129 events, 127 written by this script
        (they carry `agent_run_id`), and **every one of those 127 has an
        anchor.** The 128th, F's hand-authored `Revision` row, has no
        `bundle_section_inserted` at all — which is why the population is scoped
        to script-written events rather than asserted over the whole log."""
        checked = 0
        for log in sorted(REPO.glob("papers/*/append_log.json")):
            data = json.loads(log.read_text(encoding="utf-8"))
            for e in data.get("events", []):
                if "agent_run_id" not in e:
                    continue        # hand-authored row; not this script's contract
                checked += 1
                assert str(e.get("bundle_section_inserted", "")).strip(), \
                    f"{log.parent.name}: script-written event with no anchor"
        assert checked >= 127, f"population shrank to {checked}; re-measure"
