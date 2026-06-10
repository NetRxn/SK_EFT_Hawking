"""
test_convert_inprep_citations.py — converter rewrite-core tests (synthetic
fixtures) + dry-run-against-real-tree smoke tests.

The conversion itself (--apply) is NEVER run against the real tree here;
apply-path coverage uses tmp_path fixtures with the module's path globals
monkeypatched. The real-tree smoke test runs the script in dry-run mode
only (read-only), via subprocess.run with a list argv (no shell).
"""
from __future__ import annotations

import ast
import json
import subprocess
import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

import convert_inprep_citations as cic  # noqa: E402


# ────────────────────────────────────────────────────────────────────────────
# Synthetic fixtures
# ────────────────────────────────────────────────────────────────────────────

SYNTH_REGISTRY_SRC = '''\
"""synthetic registry fixture"""

CITATION_REGISTRY = {

    'External2020': {
        'authors': 'Doe, J.',
        'title': 'An external paper',
        'journal': 'Phys. Rev. X',
        'volume': '10',
        'page': '010101',
        'year': 2020,
        'doi': '10.1000/xyz',
        'arxiv': '2001.00001',
        'doi_verified': True,
        'inprep': False,
        'primary_source_path': 'Lit-Search/Phase-1/primary-sources/External2020.pdf',
        'used_in': ['papers/paperX_alpha/paper_draft.tex'],
        'provides': [],
        'notes': 'External reference; untouched by conversion.',
    },

    'Roehm2026TestWave': {
        'authors': 'Roehm, J. G.',
        'title': 'Synthetic self-cite with & special chars',
        'journal': 'in preparation',
        'volume': None,
        'page': None,
        'year': 2026,
        'doi': None,
        'arxiv': None,
        'doi_verified': True,
        'inprep': True,
        'primary_source_path': None,
        'used_in': ['papers/paperX_alpha/paper_draft.tex',
                    'papers/paperY_beta/paper_draft.tex'],
        'provides': [],
        'notes': 'In-preparation self-cite to a synthetic companion. '
                 'Multi-line notes with implicit concatenation.',
    },

    'Roehm2026NoAnchor': {
        'authors': 'Roehm, J. G.',
        'title': 'Self-cite whose arxiv anchor is missing',
        'journal': 'in preparation',
        'volume': None,
        'page': None,
        'year': 2026,
        'doi': None,
        'arxiv': '2599.99999',
        'doi_verified': True,
        'inprep': True,
        'primary_source_path': None,
        'used_in': [],
        'provides': [],
        'notes': 'Already has an arXiv id (like WaveDeepResearchSMG2024).',
    },
}
'''

SYNTH_TEX = r"""\documentclass{article}
\begin{document}
Body text citing~\cite{Roehm2026TestWave} and~\cite{External2020}.
This companion is in preparation (2026).

\begin{thebibliography}{99}
\bibitem{External2020}
J.~Doe, \emph{An external paper},
Phys.~Rev.~X \textbf{10}, 010101 (2020).

\bibitem{Roehm2026TestWave}
J.~Roehm, in preparation (2026), Phase 9z wave (synthetic
companion).
%% --- separator comment to preserve ---

\bibitem{Last2021}
A.~Last, \emph{The final entry}, J.~Synth.~\textbf{1}, 1 (2021).
\end{thebibliography}
\end{document}
"""


@pytest.fixture
def synth_tree(tmp_path, monkeypatch):
    """Fixture repo: synthetic citations.py + two drafts; module globals
    monkeypatched so nothing touches the real tree."""
    reg = tmp_path / "citations.py"
    reg.write_text(SYNTH_REGISTRY_SRC)
    papers = tmp_path / "papers"
    for key in ("paperX_alpha", "paperY_beta"):
        d = papers / key
        d.mkdir(parents=True)
        (d / "paper_draft.tex").write_text(SYNTH_TEX)
    lit = tmp_path / "Lit-Search"
    monkeypatch.setattr(cic, "CITATIONS_PATH", reg)
    monkeypatch.setattr(cic, "PAPERS_DIR", papers)
    monkeypatch.setattr(cic, "LIT_SEARCH", lit)
    ns: dict = {}
    exec(SYNTH_REGISTRY_SRC, ns)
    return tmp_path, ns["CITATION_REGISTRY"]


# ────────────────────────────────────────────────────────────────────────────
# Registry surgery core
# ────────────────────────────────────────────────────────────────────────────

class TestFindEntryBlock:
    def test_finds_unique_block(self):
        span = cic.find_entry_block(SYNTH_REGISTRY_SRC, "Roehm2026TestWave")
        assert span is not None
        s, e = span
        assert SYNTH_REGISTRY_SRC[s:e].startswith("    'Roehm2026TestWave': {")
        assert SYNTH_REGISTRY_SRC[s:e].rstrip().endswith("},")

    def test_missing_key_returns_none(self):
        assert cic.find_entry_block(SYNTH_REGISTRY_SRC, "Nope2026") is None

    def test_duplicate_key_returns_none(self):
        doubled = SYNTH_REGISTRY_SRC + SYNTH_REGISTRY_SRC
        assert cic.find_entry_block(doubled, "Roehm2026TestWave") is None


class TestRegistrySurgery:
    def test_three_edits_applied_and_parse_clean(self):
        new, res = cic.registry_edits_for_key(
            SYNTH_REGISTRY_SRC, "Roehm2026TestWave", "2606.12345",
            "2026-06-10")
        assert res.ok and new is not None
        ast.parse(new)                                   # still valid Python
        ns: dict = {}
        exec(new, ns)
        entry = ns["CITATION_REGISTRY"]["Roehm2026TestWave"]
        assert entry["inprep"] is False
        assert entry["arxiv"] == "2606.12345"
        assert "[2026-06-10] Converted to arXiv:2606.12345" in entry["notes"]
        assert entry["notes"].startswith("In-preparation self-cite")
        # sibling entries untouched
        assert ns["CITATION_REGISTRY"]["External2020"]["inprep"] is False
        assert (ns["CITATION_REGISTRY"]["Roehm2026NoAnchor"]["arxiv"]
                == "2599.99999")

    def test_edit_records_are_exact(self):
        _, res = cic.registry_edits_for_key(
            SYNTH_REGISTRY_SRC, "Roehm2026TestWave", "2606.12345",
            "2026-06-10")
        olds = [e.old for e in res.registry_edits]
        assert any("'arxiv': None," in o for o in olds)
        assert any("'inprep': True," in o for o in olds)
        news = [e.new for e in res.registry_edits]
        assert any("'arxiv': '2606.12345'," in n for n in news)
        assert any("'inprep': False," in n for n in news)
        # line numbers point at the right pre-edit lines
        lines = SYNTH_REGISTRY_SRC.splitlines()
        for er in res.registry_edits:
            if "(inserted" in er.old:
                continue
            assert lines[er.line - 1] == er.old

    def test_missing_anchor_degrades_to_problem_report(self):
        new, res = cic.registry_edits_for_key(
            SYNTH_REGISTRY_SRC, "Roehm2026NoAnchor", "2606.00001",
            "2026-06-10")
        assert new is None and not res.ok
        assert any("'arxiv': None," in p for p in res.problems)

    def test_unknown_key_reports_problem(self):
        new, res = cic.registry_edits_for_key(
            SYNTH_REGISTRY_SRC, "Ghost2026", "2606.00001", "2026-06-10")
        assert new is None and not res.ok
        assert "not found" in res.problems[0]


# ────────────────────────────────────────────────────────────────────────────
# Bibitem rewrite core
# ────────────────────────────────────────────────────────────────────────────

class TestBibitemRewrite:
    def test_rewrites_body_preserving_title_form(self):
        body = cic.canonical_bibitem_body(
            "Synthetic self-cite with & special chars", "2606.12345", 2026)
        new, found = cic.rewrite_bibitem(SYNTH_TEX, "Roehm2026TestWave", body)
        assert found
        assert ("J.~Roehm, \\emph{Synthetic self-cite with \\& special "
                "chars}, arXiv:2606.12345 (2026)." in new)
        assert "Phase 9z wave" not in new                # old body gone
        assert "%% --- separator comment to preserve ---" in new
        # neighbours untouched
        assert "J.~Doe, \\emph{An external paper}," in new
        assert "A.~Last, \\emph{The final entry}" in new

    def test_last_bibitem_before_end_is_rewritable(self):
        body = cic.canonical_bibitem_body("The final entry", "2606.54321",
                                          2021)
        new, found = cic.rewrite_bibitem(SYNTH_TEX, "Last2021", body)
        assert found
        assert "arXiv:2606.54321 (2021)." in new
        assert "\\end{thebibliography}" in new

    def test_absent_key_found_false(self):
        new, found = cic.rewrite_bibitem(SYNTH_TEX, "Ghost2026", "X")
        assert not found and new == SYNTH_TEX

    def test_latex_escape_title(self):
        assert cic.latex_escape_title("A & B 100% #1") == r"A \& B 100\% \#1"
        assert cic.latex_escape_title(r"pre-escaped \& stays") \
            == r"pre-escaped \& stays"


# ────────────────────────────────────────────────────────────────────────────
# Driver on fixtures (incl. the only --apply exercised anywhere: tmp tree)
# ────────────────────────────────────────────────────────────────────────────

class TestRunOnFixtures:
    def test_dry_run_reports_and_writes_nothing(self, synth_tree, capsys):
        tmp, registry = synth_tree
        rc = cic.run({"Roehm2026TestWave": {"arxiv": "2606.12345"}},
                     apply=False, registry=registry)
        assert rc == 0
        out = capsys.readouterr().out
        assert "[CONVERT] Roehm2026TestWave" in out
        assert "Dry-run complete" in out
        assert "Roehm2026NoAnchor" in out                # unmapped report
        # nothing written
        assert "in preparation (2026), Phase 9z wave" in (
            tmp / "papers" / "paperX_alpha" / "paper_draft.tex").read_text()
        assert "'inprep': True" in (tmp / "citations.py").read_text()
        assert not (tmp / "Lit-Search").exists()

    def test_apply_writes_registry_drafts_and_stub(self, synth_tree, capsys):
        tmp, registry = synth_tree
        rc = cic.run({"Roehm2026TestWave": {"arxiv": "2606.12345"}},
                     apply=True, registry=registry)
        assert rc == 0
        reg_text = (tmp / "citations.py").read_text()
        ast.parse(reg_text)
        ns: dict = {}
        exec(reg_text, ns)
        entry = ns["CITATION_REGISTRY"]["Roehm2026TestWave"]
        assert entry["inprep"] is False
        assert entry["arxiv"] == "2606.12345"
        assert "Converted to arXiv:2606.12345" in entry["notes"]
        for paper in ("paperX_alpha", "paperY_beta"):
            tex = (tmp / "papers" / paper / "paper_draft.tex").read_text()
            assert "arXiv:2606.12345 (2026)." in tex
            assert "Phase 9z wave" not in tex
        # cache stub routed via used_in fallback (synthetic keys are not in
        # PAPER_TO_PHASE, so the validate.py fallback phase is used)
        stub = (tmp / "Lit-Search" / cic.PHASE_FALLBACK / "primary-sources"
                / "Roehm2026TestWave.json")
        assert stub.is_file()
        payload = json.loads(stub.read_text())
        assert payload["arxiv"] == "2606.12345"
        assert payload["kind"] == "project-self-deposit"

    def test_title_override_wins(self, synth_tree, capsys):
        tmp, registry = synth_tree
        rc = cic.run({"Roehm2026TestWave": {
            "arxiv": "2606.12345",
            "title_override": "Overridden deposit title"}},
            apply=True, registry=registry)
        assert rc == 0
        tex = (tmp / "papers" / "paperX_alpha" / "paper_draft.tex").read_text()
        assert "\\emph{Overridden deposit title}, arXiv:2606.12345" in tex

    def test_bad_arxiv_id_is_rejected(self, synth_tree, capsys):
        _, registry = synth_tree
        rc = cic.run({"Roehm2026TestWave": {"arxiv": "not-an-id"}},
                     apply=False, registry=registry)
        assert rc == 0                                    # dry-run still 0
        out = capsys.readouterr().out
        assert "bad arXiv id" in out
        assert "[EDIT-LIST/SKIP] Roehm2026TestWave" in out

    def test_check_mode_on_fixture(self, synth_tree, capsys):
        tmp, registry = synth_tree
        # pre-conversion: prose "in preparation" present -> fail
        assert cic.check_paper("paperX_alpha") == 1
        out = capsys.readouterr().out
        assert "CHECK FAIL" in out
        # clean draft -> pass
        clean = tmp / "papers" / "clean_paper"
        clean.mkdir()
        (clean / "paper_draft.tex").write_text(
            "\\documentclass{article}\\begin{document}"
            "ok % in preparation only in a comment\n\\end{document}\n")
        assert cic.check_paper("clean_paper") == 0
        assert "CHECK PASS" in capsys.readouterr().out


# ────────────────────────────────────────────────────────────────────────────
# Real-tree smoke (read-only: dry-run only, never --apply)
# ────────────────────────────────────────────────────────────────────────────

class TestRealTreeDryRun:
    def test_inventory_dry_run_clean_on_live_repo(self):
        proc = subprocess.run(
            [sys.executable,
             str(PROJECT_ROOT / "scripts" / "convert_inprep_citations.py")],
            cwd=PROJECT_ROOT, capture_output=True, text=True, timeout=120)
        assert proc.returncode == 0, proc.stderr
        assert "inprep self-cites" in proc.stdout
        assert "Unmapped inprep keys remaining" in proc.stdout
        assert "Dry-run complete" in proc.stdout

    def test_live_inprep_anchors_still_safe(self):
        """The anchored-surgery preconditions hold on the live registry:
        every inprep entry block is unique, ends with a string-terminated
        notes field, and carries exactly one inprep anchor."""
        from src.core.citations import CITATION_REGISTRY
        text = cic.CITATIONS_PATH.read_text(encoding="utf-8")
        for key, entry in CITATION_REGISTRY.items():
            if not entry.get("inprep"):
                continue
            span = cic.find_entry_block(text, key)
            assert span is not None, f"{key}: block not found/unique"
            block = text[span[0]:span[1]]
            assert block.count("'inprep': True") == 1, key
            body = block.removesuffix("\n    },")
            assert body.rstrip().endswith("',"), (
                f"{key}: notes is not the final string-terminated field")
