#!/usr/bin/env python3
"""Extract \\bibitem stubs for cited bibkeys absent from CITATION_REGISTRY.

Walks every `papers/*/paper_draft.tex`, finds every `\\cite{<key>}`, and for
each key not already in CITATION_REGISTRY, parses the local `\\bibitem{<key>}`
block (if present in any paper) into a registry-shaped stub. Writes the
result to `docs/missing_bibkey_stubs.json` for downstream consumption by:

    - back_fill_primary_sources.py (fetches the cached primary source)
    - the Stage-5 promotion script (appends stubs to CITATION_REGISTRY)

Stubs carry: bibkey, authors, title, journal, volume, page, year, doi, arxiv,
plus the citing-paper list (from the \\cite occurrences) and the source paper
where the \\bibitem block was found.

Bibkeys that are cited but have no \\bibitem block anywhere are reported as
orphans — those need manual entry, not auto-fetch.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from dataclasses import dataclass, field, asdict
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
SK_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = SK_ROOT / "papers"
OUTPUT_PATH = SK_ROOT / "docs" / "missing_bibkey_stubs.json"

sys.path.insert(0, str(SK_ROOT))
from src.core.citations import CITATION_REGISTRY  # noqa: E402


CITE_RE = re.compile(r"\\cite[a-zA-Z]*\*?\s*(?:\[[^\]]*\])*\s*\{([^}]+)\}")
BIBITEM_RE = re.compile(r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}")

TITLE_RE = re.compile(r"\\textit\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}", re.DOTALL)
TITLE_ALT_RE = re.compile(r"\\emph\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}", re.DOTALL)
ARXIV_RE = re.compile(
    r"arXiv\s*[:.]?\s*([a-z\-]+/\d{7}|\d{4}\.\d{4,5})", re.IGNORECASE
)
DOI_RE = re.compile(
    r"(?:DOI[:\s]*|doi\.org/|doi[:\s]+)(10\.[^\s,);\]]+)", re.IGNORECASE
)
YEAR_RE = re.compile(r"\((\d{4})\)")
VOLUME_RE = re.compile(r"\\textbf\{(\d+)\}")
JOURNAL_BEFORE_VOLUME_RE = re.compile(
    r"([A-Z][A-Za-z. \-]+?)\s+\\textbf\{\d+\}", re.DOTALL
)


@dataclass
class BibitemStub:
    bibkey: str
    authors: str = ""
    title: str = ""
    journal: str | None = None
    volume: int | None = None
    page: str | None = None
    year: int | None = None
    doi: str | None = None
    arxiv: str | None = None
    raw_block: str = ""
    cited_in: list[str] = field(default_factory=list)
    bibitem_source: str = ""  # paper_key where \bibitem was found

    def fill_from_block(self, block: str) -> None:
        self.raw_block = block.strip()

        # Title — try \textit then \emph
        m = TITLE_RE.search(block)
        if not m:
            m = TITLE_ALT_RE.search(block)
        if m:
            t = m.group(1)
            t = re.sub(r"\s+", " ", t).strip()
            t = re.sub(r"^[\"“”`]+|[\"“”`]+$", "", t)
            self.title = t

        # Year (last 4-digit-paren match, since DOIs / arXiv may include 4-digit segments)
        years = YEAR_RE.findall(block)
        if years:
            try:
                self.year = int(years[-1])
            except ValueError:
                pass

        # arXiv ID
        m = ARXIV_RE.search(block)
        if m:
            self.arxiv = m.group(1)

        # DOI
        m = DOI_RE.search(block)
        if m:
            doi = m.group(1).rstrip(".,;")
            self.doi = doi

        # Volume
        m = VOLUME_RE.search(block)
        if m:
            try:
                self.volume = int(m.group(1))
            except ValueError:
                pass

        # Journal — heuristic: text immediately before \textbf{volume}
        m = JOURNAL_BEFORE_VOLUME_RE.search(block)
        if m:
            j = m.group(1).strip().rstrip(",.")
            j = re.sub(r"\s+", " ", j)
            # Strip the trailing "DOI", "arXiv", or other noise that crept in
            j = re.sub(r"^(DOI|arXiv|in)\b.*$", "", j, flags=re.IGNORECASE).strip()
            if j and len(j) < 80:
                self.journal = j

        # Authors — text between \bibitem{...} line and \textit{...}
        # We strip the bibitem prefix (already removed by caller) and any
        # leading whitespace; the authors line is the first non-empty line
        # before the title delimiter.
        before_title = block
        if self.title:
            # Find the title's location in the raw block to clip
            ti = block.find(self.title)
            if ti > 0:
                before_title = block[:ti]
        # before_title may still contain the bibitem header line; remove it
        before_title = re.sub(r"^\\bibitem(?:\[[^\]]*\])?\{[^}]+\}\s*", "", before_title)
        # Strip \textit / \textbf / surrounding LaTeX commands but keep author names
        ab = re.sub(r"\\textit\{[^}]*\}?", "", before_title)
        ab = re.sub(r"\\textbf\{[^}]*\}?", "", ab)
        ab = re.sub(r"\\[a-zA-Z]+\*?\s*\{?", "", ab)
        ab = re.sub(r"[{}]", "", ab)
        ab = ab.strip().rstrip(",;.")
        ab = re.sub(r"\s+", " ", ab)
        self.authors = ab[:200]

    @property
    def is_orphan(self) -> bool:
        """True if cited but no bibitem block found anywhere."""
        return self.raw_block == ""


def collect_cite_keys(paper_dir: Path) -> set[str]:
    """Return the set of \\cite{} keys used in `paper_dir/paper_draft.tex`."""
    tex = paper_dir / "paper_draft.tex"
    if not tex.is_file():
        return set()
    text = tex.read_text(encoding="utf-8", errors="replace")
    text = "\n".join(line.split("%", 1)[0] for line in text.splitlines())
    keys = set()
    for m in CITE_RE.finditer(text):
        for raw in m.group(1).split(","):
            k = raw.strip()
            if k:
                keys.add(k)
    return keys


def collect_bibitem_blocks(paper_dir: Path) -> dict[str, str]:
    """Return {bibkey: raw_block_text} for every \\bibitem in this paper."""
    tex = paper_dir / "paper_draft.tex"
    if not tex.is_file():
        return {}
    text = tex.read_text(encoding="utf-8", errors="replace")
    # Drop comment lines
    text = "\n".join(line.split("%", 1)[0] for line in text.splitlines())
    # Find all bibitem starts; each block runs until the next \bibitem or
    # \end{thebibliography}.
    matches = list(BIBITEM_RE.finditer(text))
    if not matches:
        return {}
    end_marker = re.search(r"\\end\{thebibliography\}", text)
    end_pos = end_marker.start() if end_marker else len(text)
    blocks: dict[str, str] = {}
    for i, m in enumerate(matches):
        start = m.start()
        stop = matches[i + 1].start() if i + 1 < len(matches) else end_pos
        key = m.group(1).strip()
        blocks[key] = text[start:stop]
    return blocks


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out", type=Path, default=OUTPUT_PATH, help="Output JSON path")
    p.add_argument("--report", action="store_true", help="Print summary to stdout")
    args = p.parse_args(argv)

    # Pass 1: gather all cite-keys and all bibitem blocks across papers
    cite_usage: dict[str, list[str]] = defaultdict(list)        # bibkey -> [paper_keys]
    bibitem_blocks: dict[str, tuple[str, str]] = {}             # bibkey -> (paper_key, block)

    for paper_dir in sorted(PAPERS_DIR.iterdir()):
        if not paper_dir.is_dir():
            continue
        if (paper_dir / "paper_draft.tex").is_file() is False:
            continue
        paper_key = paper_dir.name
        for key in collect_cite_keys(paper_dir):
            cite_usage[key].append(paper_key)
        for key, block in collect_bibitem_blocks(paper_dir).items():
            # First-found wins; subsequent duplicates ignored (paper-local
            # variants under the same key would conflict at the registry).
            if key not in bibitem_blocks:
                bibitem_blocks[key] = (paper_key, block)

    # Pass 2: extract stubs for cited bibkeys missing from CITATION_REGISTRY
    stubs: list[BibitemStub] = []
    orphans: list[str] = []
    for bibkey in sorted(cite_usage):
        if bibkey in CITATION_REGISTRY:
            continue
        stub = BibitemStub(bibkey=bibkey, cited_in=sorted(set(cite_usage[bibkey])))
        if bibkey in bibitem_blocks:
            paper_key, block = bibitem_blocks[bibkey]
            stub.bibitem_source = paper_key
            stub.fill_from_block(block)
            stubs.append(stub)
        else:
            orphans.append(bibkey)

    # Persist
    payload = {
        "generated_by": "scripts/extract_missing_bibkeys.py",
        "n_total_cited": len(cite_usage),
        "n_in_registry": sum(1 for k in cite_usage if k in CITATION_REGISTRY),
        "n_stubs": len(stubs),
        "n_orphans": len(orphans),
        "stubs": [asdict(s) for s in stubs],
        "orphans": [
            {"bibkey": k, "cited_in": sorted(set(cite_usage[k]))}
            for k in orphans
        ],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"wrote {args.out}", file=sys.stderr)

    if args.report or True:
        print()
        print(f"Cited bibkeys (total):              {payload['n_total_cited']}")
        print(f"  In CITATION_REGISTRY:             {payload['n_in_registry']}")
        print(f"  Stubs created (bibitem found):    {payload['n_stubs']}")
        print(f"  Orphans (no bibitem block found): {payload['n_orphans']}")
        # Coverage of stub fields
        if stubs:
            with_arxiv = sum(1 for s in stubs if s.arxiv)
            with_doi = sum(1 for s in stubs if s.doi)
            with_year = sum(1 for s in stubs if s.year)
            with_title = sum(1 for s in stubs if s.title)
            print()
            print("Stub field coverage:")
            print(f"  title:  {with_title}/{len(stubs)}")
            print(f"  year:   {with_year}/{len(stubs)}")
            print(f"  arxiv:  {with_arxiv}/{len(stubs)}")
            print(f"  doi:    {with_doi}/{len(stubs)}")
        if orphans:
            print()
            print(f"Orphan bibkeys (cited but no \\bibitem block):")
            for k in orphans:
                citers = ", ".join(sorted(set(cite_usage[k]))[:3])
                print(f"  {k}  ({citers})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
