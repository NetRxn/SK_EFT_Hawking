"""Canonical final-target boundary for paper-derived artifact reads.

Resolve before opening, under cooperative local writers. The returned read path
must never replace a lexical writer destination or a paper's lexical identity.
This is not a no-follow defense against hostile concurrent link replacement.
"""
from pathlib import Path


def safe_paper_dir(papers_root: Path, paper_id: str) -> Path | None:
    """Resolve one selected paper directory beneath the resolved papers root."""
    if (not isinstance(paper_id, str) or not paper_id or paper_id in ('.', '..')
            or any(c in paper_id for c in ('/', '\\', '\x00'))):
        return None
    try:
        root = Path(papers_root).resolve(strict=True)
        target = (root / paper_id).resolve(strict=True)
        if target == root or root not in target.parents or not target.is_dir():
            return None
        return target
    except (OSError, ValueError, RuntimeError):
        return None


def paper_artifact_path(papers_root: Path, paper_id: str, *parts: str,
                        must_exist: bool = True) -> Path | None:
    """Return a confined final read target, including intermediate symlinks.

    Missing targets are allowed only for writer prerequisite inspection; selected
    directories must still exist. The containment root stays papers, so links
    between papers inside that root remain supported.
    """
    directory = safe_paper_dir(papers_root, paper_id)
    if directory is None:
        return None
    try:
        child = Path(*parts)
        if child.is_absolute() or '..' in child.parts:
            return None
        root = Path(papers_root).resolve(strict=True)
        target = (directory / child).resolve(strict=must_exist)
        if target == root or root not in target.parents:
            return None
        return target
    except (OSError, ValueError, RuntimeError):
        return None


def confined_paper_path(papers_root: Path, path: Path) -> Path | None:
    """Guard an existing lexical paper path without inferring identity from realpath."""
    try:
        relative = Path(path).absolute().relative_to(Path(papers_root).absolute())
        if len(relative.parts) < 2:
            return None
        return paper_artifact_path(papers_root, relative.parts[0], *relative.parts[1:])
    except (OSError, ValueError, RuntimeError):
        return None
