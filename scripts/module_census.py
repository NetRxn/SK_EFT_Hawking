"""Derive the census — the one answer to "what is this module, script or notebook".

    uv run python scripts/module_census.py            # print the census
    uv run python scripts/module_census.py --write    # write the tracked doc

ADR-013 D1. Replaces the hand-maintained Inventory pair (both retired), whose narrative
had drifted while the generated blocks beside it stayed fresh — a half-generated document inherits the credibility of its
generated half. This file is generated in whole; there is no hand-edited region for that
failure to recur in.

**Scope is Python, shell and notebooks, and it is stated on the artifact's face (D1b).**
Lean is answered by `docs/counts.json` (`lean.module_names`), `lean/lean_deps.json` and
`lean/atlas_view.json`, all derived from the extraction chokepoint and unable to drift;
papers and tests by counts in `docs/counts.json`. An unstated boundary is how the next hand
catalogue gets started.

⚠️ **`docs/counts.json` answers HOW MANY notebooks; nothing answered WHAT EACH ONE IS.**
That is the same gap this census exists to close, which is why notebooks joined it at D3
rather than staying a bare count.

⚠️ **Shell was added at D5 (2026-08-13) and the four scripts were ALREADY described**, so
`_NO_DOCSTRING_CEILING` holds at 4 — verified before the walk widened, not after. That
check matters more than it looks: **a ratchet is scoped by the population predicate, so
widening the walk redefines what the ceiling counts.** Had any of the four lacked a header
the honest move would have been to write one, never to raise the ceiling to admit it.

⚠️ **THE DECIDER DIFFERS BY LANGUAGE, and neither is a regex over the whole file (D2).**
Python uses `ast.get_docstring`; a source scan finds a docstring-shaped string inside a
function and calls the module documented (`CHECK_AUTHORING_GUIDE` §2.5). Shell has no AST,
so the analogue is the **leading comment block only** — contiguous `#` lines after an
optional shebang, stopping at the first line that is not one. Bounding it to the leading
block is what keeps it from matching an explanatory comment anywhere in the body, which is
the same failure the Python leg avoids by not scanning source.

⚠️ **The artifact is sited at `docs/`, not `docs/architecture/`.** That directory's README
declares it does not own "what does this module do", and `architecture_inventory_fresh`
forbids a census count in any narrative under it — which two module docstrings would trip
via their Phase-6i wave numbers, with nothing editable to fix since this file is wholly
generated.
"""
from __future__ import annotations

import argparse
import ast
import json
import re
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
OUT_PATH = PROJECT_ROOT / "docs" / "MODULE_CENSUS.md"

#: The trees nothing else derives a per-file description for.
TREES: tuple[str, ...] = ("src", "scripts", "notebooks")

#: Never walked: caches, virtualenvs, the gitignored scratch tree, and Jupyter's
#: checkpoint copies (which would double-count every notebook under a stale name).
SKIP_PARTS: frozenset[str] = frozenset({
    "__pycache__", ".venv", "node_modules", ".temp", ".ipynb_checkpoints"})


def _first_paragraph(doc: str) -> str:
    """The docstring's first paragraph, flattened to one line.

    Paragraph rather than line: a line loses the second sentence where there is one, and
    the measured cost of the wider form is small. Where a docstring has no second
    sentence the census has none either — it can only be as good as the source (ADR-013
    C5), which is the point: the gap is then fixable in the module rather than in a
    parallel prose file that drifts.
    """
    first = doc.strip().split("\n\n")[0]
    # ⚠️ Strip banner rules. A docstring styled as
    #     Cross-Layer Validation Suite
    #     ============================
    # has no blank line, so the underline is part of paragraph one and lands in the
    # published row as a wall of `=`. Measured 2026-08-13: 19 of 315 rows (6%).
    # Drop rule-only lines, and trailing rule characters left on a text line.
    kept = [ln for ln in first.splitlines() if not re.fullmatch(r"[=\-~_*#\s]{3,}", ln)]
    return re.sub(r"[\s=~_-]{4,}$", "", " ".join(" ".join(kept).split())).strip()


def _shell_header(src: str) -> str | None:
    """The LEADING comment block of a shell script, or None.

    Shell has no AST, so this is the closest honest analogue of a module docstring:
    contiguous `#` lines after an optional shebang, stopping at the first line that is
    not one. **Bounded to the leading block on purpose** — scanning the whole file for
    comments would match an explanatory note anywhere in the body and call the script
    described, the same false-positive the Python leg avoids by not scanning source.
    """
    lines, out = src.splitlines(), []
    i = 1 if lines and lines[0].startswith("#!") else 0
    for line in lines[i:]:
        s = line.strip()
        if not s.startswith("#"):
            break
        out.append(s.lstrip("#").strip())
    body = "\n".join(out).strip()
    return body or None


def _notebook_header(src: str) -> str | None:
    """A notebook's leading markdown cell, as `heading — first prose paragraph`.

    The decider for notebooks (D3). Measured 2026-08-13: **91 of 91 notebooks already
    open with a markdown heading**, so this encodes a convention the corpus already
    follows universally rather than imposing a new one — which is why it costs nothing
    to adopt and why the ceiling does not move.

    Sub-headings and rule lines are skipped when gathering the prose, so a title block
    styled with an underline does not publish as a wall of `=`.
    """
    lines = [ln.rstrip() for ln in src.strip().splitlines()]
    if not lines:
        return None
    head = lines[0].lstrip("#").strip()
    rest: list[str] = []
    for ln in lines[1:]:
        s = ln.strip()
        if not s:
            if rest:
                break
            continue
        if s.startswith("#") or re.fullmatch(r"[=\-~_*\s]{3,}", s):
            continue
        rest.append(s)
    out = (head + (" — " + " ".join(rest) if rest else "")).strip()
    return out or None


def _notebook_first_markdown(path: Path) -> str | None:
    """First cell of a notebook IF it is markdown, else None.

    ⚠️ Deliberately not "the first markdown cell anywhere". A notebook that opens with
    code and explains itself later is NOT self-describing at the point a reader opens
    it, and calling it described would be the same false positive the shell leg bounds
    against.
    """
    doc = json.loads(path.read_text(encoding="utf-8"))
    cells = doc.get("cells") or []
    if not cells or cells[0].get("cell_type") != "markdown":
        return None
    return _notebook_header("".join(cells[0].get("source") or []))


def collect() -> dict:
    """Walk the trees; read each file's description by the decider for its language."""
    documented: list[tuple[str, str]] = []
    undocumented: list[tuple[str, str]] = []
    for tree in TREES:
        base = PROJECT_ROOT / tree
        if not base.is_dir():
            continue
        paths = sorted((p for pat in ("*.py", "*.sh", "*.ipynb") for p in base.rglob(pat)),
                       key=lambda p: p.as_posix())
        for path in paths:
            if SKIP_PARTS & set(path.parts):
                continue
            rel = path.relative_to(PROJECT_ROOT).as_posix()
            try:
                if path.suffix == ".ipynb":
                    doc = _notebook_first_markdown(path)
                else:
                    src = path.read_text(encoding="utf-8")
                    doc = (_shell_header(src) if path.suffix == ".sh"
                           else ast.get_docstring(ast.parse(src)))
            except (SyntaxError, UnicodeDecodeError, json.JSONDecodeError, KeyError) as exc:
                undocumented.append((rel, f"unparseable — {type(exc).__name__}"))
                continue
            if doc and doc.strip():
                documented.append((rel, _first_paragraph(doc)))
            else:
                undocumented.append((rel, {
                    ".sh": "no leading comment block",
                    ".ipynb": "first cell is not a markdown heading",
                }.get(path.suffix, "no module docstring")))
    return {"documented": documented, "undocumented": undocumented}


def render(data: dict) -> str:
    """Render the census. Pure — the check calls `render(collect())` and compares."""
    documented = data["documented"]
    undocumented = data["undocumented"]
    out: list[str] = [
        "# Module census — what each module and script is",
        "",
        "**Generated by `scripts/module_census.py`. Do not edit — every line is derived**",
        "from the source: a Python module docstring read via the AST, or a shell script's",
        "leading comment block. To change a description, change it at the source; the next",
        "`sync` regenerates this file.",
        "",
        "**Scope: Python, shell and notebooks** — `src/`, `scripts/`, `notebooks/`. Lean is",
        "answered by `docs/counts.json` (`lean.module_names`), `lean/lean_deps.json` and",
        "`lean/atlas_view.json`; papers and tests by counts in `docs/counts.json`.",
        "Nothing else belongs here.",
        "",
        "---",
        "",
        "| module | what it is |",
        "|---|---|",
    ]
    out += [f"| `{rel}` | {summary} |" for rel, summary in documented]
    out += [
        "",
        "## Modules this census cannot describe",
        "",
    ]
    if undocumented:
        out += [
            "These carry no module docstring (Python), leading comment block (shell) or",
            "opening markdown heading (notebook), so",
            "there is nothing to derive. **An entry here is a description that does not",
            "exist, not one this file failed to find** — the fix is at the source.",
            "",
        ]
        out += [f"- `{rel}` — {why}" for rel, why in undocumented]
    else:
        out.append("None: every module in scope carries a docstring.")
    out.append("")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--write", action="store_true", help="write the tracked doc")
    args = ap.parse_args(argv)

    data = collect()
    text = render(data)
    if args.write:
        OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
        if not OUT_PATH.is_file() or OUT_PATH.read_text(encoding="utf-8") != text:
            OUT_PATH.write_text(text, encoding="utf-8")
            print(f"wrote {OUT_PATH.relative_to(PROJECT_ROOT)}")
        else:
            print(f"{OUT_PATH.relative_to(PROJECT_ROOT)} already current")
    else:
        print(text, end="")
    n_doc, n_un = len(data["documented"]), len(data["undocumented"])
    print(f"\n{n_doc + n_un} module(s): {n_doc} documented, {n_un} without a docstring")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
