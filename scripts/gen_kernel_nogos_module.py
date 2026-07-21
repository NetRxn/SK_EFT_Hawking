#!/usr/bin/env python3
"""Regenerate ``lean/SKEFTHawking/KernelNoGos.lean`` — the Lean-side consolidated fence for the
kernel-verified no-gos.

**DERIVED artifact — never hand-edit the ``.lean`` output.** The single source of truth is the
``KERNEL_NOGO_REGISTRY`` in ``src/core/constants.py`` (already consumed by ``atlas_view.py`` for the
negative frontier and by ``validate.py`` for the ``nogo_substrate_integrity`` gate). This script adds
a *Lean-visible* view of that same registry: it resolves each backing refutation theorem's source
module, then emits a module that

  (a) ``import``s every source module (so the module is in the build closure), and
  (b) re-exports each backing theorem under an ``alias`` whose docstring is the registry's
      ``false_statement`` — i.e. a single browsable place a Lean developer sees the fenced forks.

Because it is generated from the registry, it **cannot drift**: adding a no-go to the registry and
re-running this (or ``sync.py``) regenerates the module; the ``sync_manifest`` staleness edge flags
it if it is ever out of date (pre-commit + ``/sync`` both check it). The compiler itself becomes the
fence — if a backing theorem is renamed/removed, this module fails to build.

Usage:  ``python scripts/gen_kernel_nogos_module.py [--check]``
  (no args) writes the module; ``--check`` exits 1 (without writing) if the on-disk module differs
  from a fresh render — the staleness detector used by ``sync_manifest``.

Stdlib only (plus the in-repo ``src.core.constants``).
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent
LEAN = ROOT / "lean"
LEAN_SRC = LEAN / "SKEFTHawking"
OUT = LEAN_SRC / "KernelNoGos.lean"

sys.path.insert(0, str(ROOT))
from src.core.constants import KERNEL_NOGO_REGISTRY  # noqa: E402

_DECL_RE_CACHE: dict[str, re.Pattern] = {}


def _resolve_module(thm_fq: str) -> str | None:
    """Grep the Lean tree for the theorem's short name → its source module dotted-path.

    Robust to namespace≠file: we search for the *defining* line, not the namespace. Returns e.g.
    ``SKEFTHawking.NonHausdorffBordismCollapse`` for
    ``SKEFTHawking.NonHausdorffBordismCollapse.bordismGrp_subsingleton``.
    """
    short = thm_fq.split(".")[-1]
    pat = _DECL_RE_CACHE.get(short)
    if pat is None:
        pat = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:theorem|lemma|def)\s+{re.escape(short)}\b")
        _DECL_RE_CACHE[short] = pat
    for f in sorted(LEAN_SRC.rglob("*.lean")):
        try:
            text = f.read_text(encoding="utf-8")
        except Exception:
            continue
        for line in text.splitlines():
            if pat.match(line):
                rel = f.relative_to(LEAN).with_suffix("")
                return ".".join(rel.parts)
    return None


def _alias_name(short: str, used: set[str]) -> str:
    """A collision-free `nogo_`-prefixed alias handle for the KernelNoGos namespace."""
    base = f"nogo_{short}"
    name = base
    i = 2
    while name in used:
        name = f"{base}_{i}"
        i += 1
    used.add(name)
    return name


def _wrap(text: str, width: int = 108, indent: str = "  ") -> list[str]:
    """Soft-wrap a docstring/comment body to keep lines readable (mathlib 100-col convention leeway)."""
    words = text.split()
    lines: list[str] = []
    cur = indent.rstrip("\n")
    for w in words:
        if cur and len(cur) + 1 + len(w) > width:
            lines.append(cur)
            cur = indent + w
        else:
            cur = (cur + " " + w) if cur.strip() else (indent + w)
    if cur.strip():
        lines.append(cur)
    return lines


def render() -> str:
    # Collect, in registry order, each fork's resolved backing theorems.
    forks: list[dict] = []
    imports: set[str] = set()
    for key, e in KERNEL_NOGO_REGISTRY.items():
        fid = e.get("fork_id", key)
        false_statement = (e.get("false_statement") or "").strip()
        # Optional citation bound: exactly what the backing theorems do and do NOT support. Present
        # when an entry has previously been over-cited; rendered verbatim so a reader of the Lean
        # fence sees the limit at the same place they read the claim.
        scope_limit = (e.get("scope_limit") or "").strip()
        kind = e.get("nogo_kind", "?")
        backing = list(e.get("backing_theorems") or [])
        resolved: list[tuple[str, str, str]] = []  # (short, fq, module)
        unresolved: list[str] = []
        for t in backing:
            mod = _resolve_module(t)
            if mod:
                imports.add(mod)
                resolved.append((t.split(".")[-1], t, mod))
            else:
                unresolved.append(t)
        forks.append({
            "key": key, "fid": fid, "false_statement": false_statement, "kind": kind,
            "scope_limit": scope_limit,
            "backing": backing, "resolved": resolved, "unresolved": unresolved,
        })

    lines: list[str] = []
    ap = lines.append

    # --- module docstring: the human-readable "clearly avoid" index ---
    ap("/-")
    ap("# Kernel-verified NO-GO fence — the consolidated register (GENERATED)")
    ap("")
    ap("**DO NOT HAND-EDIT.** This module is regenerated by `scripts/gen_kernel_nogos_module.py`")
    ap("from the single source of truth `KERNEL_NOGO_REGISTRY` (`src/core/constants.py`) and is kept")
    ap("fresh by the `sync_manifest` staleness edge (pre-commit + `/sync`). It gathers EVERY")
    ap("kernel-checked no-go of the project into one place so future work — and fresh-context")
    ap("workers — see the provably-false forks that must NEVER be re-derived, and so the compiler")
    ap("itself enforces their presence: if a backing refutation theorem is renamed or removed, this")
    ap("module fails to build (the fence is down → investigate before proceeding).")
    ap("")
    ap("Companion registers: the machine `KERNEL_NOGO_REGISTRY` (Python; feeds the atlas negative")
    ap("frontier + `validate.py --check nogo_substrate_integrity`) and the prose")
    ap("`docs/dev-loops/SETTLED_FORKS.md` (policy/route bans, not kernel-encodable).")
    ap("")
    ap("## The register (fork-id → FALSE statement → backing theorem[s])")
    ap("")
    for i, fk in enumerate(forks, 1):
        ap(f"{i}. `{fk['fid']}` [{fk['kind']}]")
        for wl in _wrap(fk["false_statement"] or "(no false-statement recorded)", indent="   "):
            ap(wl)
        if fk["scope_limit"]:
            for wl in _wrap("SCOPE LIMIT — " + fk["scope_limit"], indent="   "):
                ap(wl)
        if fk["resolved"]:
            ap("   backing: " + ", ".join(f"`{s}`" for s, _, _ in fk["resolved"]))
        if fk["unresolved"]:
            ap("   ⚠ UNRESOLVED backing (not found in-tree — check the registry): "
               + ", ".join(f"`{t}`" for t in fk["unresolved"]))
        if not fk["backing"]:
            ap("   (structural/prose fork — no single backing theorem; see SETTLED_FORKS.md)")
        ap("")
    ap("-/")

    # --- imports (deduped, sorted) ---
    for mod in sorted(imports):
        ap(f"import {mod}")
    ap("")
    ap("namespace SKEFTHawking.KernelNoGos")
    ap("")

    # --- per-theorem re-export aliases (the compile-time fence + reusable handles) ---
    used: set[str] = set()
    any_alias = False
    for fk in forks:
        for short, fq, _mod in fk["resolved"]:
            any_alias = True
            handle = _alias_name(short, used)
            summary = (fk["false_statement"] or "").strip()
            # keep the per-alias docstring to a single tight sentence pointing at the fork
            first = summary.split(". ")[0].strip()
            if first and not first.endswith("."):
                first += "."
            limit = (" ⚠ SCOPE-LIMITED — read the SCOPE LIMIT for this fork in the module docstring "
                     "before citing it; it supports LESS than the headline suggests."
                     if fk["scope_limit"] else "")
            ap(f"/-- NO-GO [`{fk['fid']}`] — do NOT re-derive. FALSE: {first} "
               f"Backing refutation: `{fq}`.{limit} -/")
            ap(f"alias {handle} := {fq}")
            ap("")
    if not any_alias:
        ap("-- (no kernel-backed no-gos resolved; every registry entry is structural/prose.)")
        ap("")
    ap("end SKEFTHawking.KernelNoGos")
    out = "\n".join(lines)
    if not out.endswith("\n"):
        out += "\n"
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true",
                    help="exit 1 (without writing) if the on-disk module differs from a fresh render")
    args = ap.parse_args(argv)
    fresh = render()
    if args.check:
        current = OUT.read_text(encoding="utf-8") if OUT.exists() else ""
        if current != fresh:
            print(f"STALE: {OUT.relative_to(ROOT)} differs from a fresh render of KERNEL_NOGO_REGISTRY")
            return 1
        print(f"fresh: {OUT.relative_to(ROOT)}")
        return 0
    OUT.write_text(fresh, encoding="utf-8")
    n_forks = len(KERNEL_NOGO_REGISTRY)
    n_alias = fresh.count("\nalias ")
    print(f"wrote {OUT.relative_to(ROOT)}  ({n_forks} forks, {n_alias} backing-theorem aliases)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
