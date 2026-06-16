"""Canonical workspace-root resolver.

Single source of truth for locating the **workspace** directory: the
(non-git) parent folder that holds this repository alongside shared,
*untracked* sibling resources — notably ``Lit-Search/``, the deep-research
corpus that must stay untracked for copyright reasons.

Why this module exists
----------------------
Three scripts historically recomputed the workspace location with *different*
parent-walking expressions::

    LIT_SEARCH = PROJECT_ROOT / "Lit-Search"          # back_fill_primary_sources
    LIT_SEARCH = PROJECT_ROOT.parent / "Lit-Search"   # convert_inprep_citations
    LIT_SEARCH = PROJECT_ROOT_LOCAL / "Lit-Search"     # validate.py

They happen to agree today, but the divergent derivations are a latent bug:
any future refactor of one ``PROJECT_ROOT`` silently breaks one consumer.
Every site now imports :func:`find_workspace` from here instead.

Public-safe by construction
---------------------------
Detection keys off **this repo's own directory name**, the workspace-level
``.mcp.json``, and the *absence* of a ``.git`` directory at the workspace
level (the workspace is not itself a git repo). It never references any
sibling repository by name, so it is safe to ship in the public tree.
"""
from __future__ import annotations

from pathlib import Path

# This file lives at <workspace>/SK_EFT_Hawking/src/core/workspace.py
_THIS_REPO_DIRNAME = "SK_EFT_Hawking"
_SENTINEL = ".workspace-root"


def _looks_like_workspace(d: Path) -> bool:
    """True if ``d`` has the structural markers of the workspace root.

    Public-safe: no sibling-repo name appears here. The workspace is the
    directory that (a) carries the shared ``.mcp.json``, (b) contains this
    repo as a child, and (c) is itself **not** a git repo.
    """
    return (
        (d / ".mcp.json").is_file()
        and (d / _THIS_REPO_DIRNAME).is_dir()
        and not (d / ".git").exists()
    )


def find_workspace(start: Path | None = None) -> Path:
    """Return the workspace root.

    Resolution order (first hit wins):

    1. An explicit ``.workspace-root`` sentinel file encountered while walking
       up from ``start`` — lets the harness pin the root unambiguously.
    2. Structural detection via :func:`_looks_like_workspace`.
    3. Fallback to the parent of this repo's root (legacy behaviour), so the
       resolver is never *worse* than the hard-coded paths it replaces — even
       in an unusual checkout where ``.mcp.json`` is absent.

    ``start`` defaults to this module's own location, making resolution
    deterministic and independent of the caller's current working directory.
    """
    base = (Path(start) if start is not None else Path(__file__)).resolve()
    chain = [base, *base.parents]

    for d in chain:
        if (d / _SENTINEL).is_file():
            return d
    for d in chain:
        if _looks_like_workspace(d):
            return d

    # Fallback: derive from this module's fixed position in the repo.
    here = Path(__file__).resolve()
    for d in here.parents:
        if d.name == _THIS_REPO_DIRNAME:
            return d.parent
    # core -> src -> SK_EFT_Hawking -> <workspace>
    return here.parents[3]


def lit_search_dir(start: Path | None = None) -> Path:
    """The shared (untracked) ``Lit-Search`` corpus at the workspace root."""
    return find_workspace(start) / "Lit-Search"
