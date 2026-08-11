"""Bundle substrate closure — the DERIVED half of the publication-intake design.

A bundle DECLARES its apex theorems (`apex_theorems` in `papers/<bundle>/bundle_metadata.json`)
— the results it claims, a handful of names. Its **substrate is derived**: the transitive closure
of those apexes over `name_deps_project`. Nothing about the substrate is hand-maintained, so
nothing about it can drift.

Everything else falls out of that one join: what a bundle rests on, when it must absorb, what is
un-homed, whether two bundles overlap, and whether a bundle has enough substrate to be the tier
it claims. Design: `docs/architecture/.working-docs/PUBLICATION_INTAKE_{DESIGN,SHAPE}.md`.

⚠️ **An undeclared bundle is UNMEASURABLE, never clean.** A closure over no apexes is empty, and
every universal over an empty set is true — the monotone-in-emptiness failure this branch exists
to remove. `BundleClosure.declared` records whether anyone actually said what the bundle claims,
and callers must branch on it rather than on `len(closure)`.

⚠️ **Closure truncates at `private` declarations.** `ExtractDeps` omits them, so a walk reaching
one stops and loses whatever sits beneath it. Measured over the live corpus: 553 distinct private
targets, 1 278 edges, 0.46 % of all dependency edges — bounded, but `truncated_private` travels
with every closure so no consumer can report a size as if it were complete.
"""
from __future__ import annotations

import json
import sys
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))

#: The key a bundle declares its apexes under, in its existing metadata file. Co-located with the
#: bundle deliberately: merging two bundles concatenates apex lists and splitting partitions them,
#: which a central registry would turn into an unchecked remote edit.
APEX_KEY = "apex_theorems"

PROJECT_NAMESPACE = "SKEFTHawking"
PRIVATE_PREFIX = "_private."


@dataclass
class BundleClosure:
    """One bundle's declared apexes and the substrate derived from them."""

    bundle: str
    #: Did anyone declare what this bundle claims? False => UNMEASURABLE, not clean.
    declared: bool
    apexes: list[str] = field(default_factory=list)
    #: Declared apexes naming no live declaration — the §7-Q3 hand-maintenance risk.
    unresolved_apexes: list[str] = field(default_factory=list)
    #: Declared apexes that resolve to something other than a theorem. A bundle claims
    #: results; a `def` or `structure` is machinery the results are stated over.
    non_theorem_apexes: list[str] = field(default_factory=list)
    closure: set[str] = field(default_factory=set)
    modules: set[str] = field(default_factory=set)
    max_depth: int = 0
    #: Dependency edges whose target is a `private` declaration ExtractDeps omits: the walk
    #: STOPPED there. Report alongside any closure size.
    truncated_private: int = 0
    #: Edges whose target is absent for any other reason — proof-internal artifacts and
    #: constructors, which are leaves, so nothing is lost. Kept for the ratio.
    truncated_other: int = 0

    @property
    def measurable(self) -> bool:
        # ⚠️ `bool(self.closure)`, not just `bool(self.apexes)`. `apexes` is the
        # DECLARED list; names that fail to resolve are filed into
        # `unresolved_apexes` and contribute nothing to the closure. Without the
        # third conjunct a bundle whose apexes ALL dangle (a module rename, a
        # typo) was `measurable` with an EMPTY closure, and `render_bundle_counts`
        # emitted `\bundleTheorems{0}` into the draft — the exact confident wrong
        # number its own docstring says must never be printed.
        return self.declared and bool(self.apexes) and bool(self.closure)


def load_apex_declarations(papers_root: Path) -> dict[str, dict]:
    """`{bundle: {"declared": bool, "apexes": [name, ...]}}` for every bundle on disk.

    Reads the bundle's own metadata file. A bundle whose file is missing the key is reported
    `declared=False` rather than skipped — an absent declaration is a fact about the bundle,
    and dropping it here is how "no bundles have a problem" gets manufactured.
    """
    out: dict[str, dict] = {}
    if not papers_root.exists():
        return out
    for meta_path in sorted(papers_root.glob("*/bundle_metadata.json")):
        bundle = meta_path.parent.name
        try:
            meta = json.loads(meta_path.read_text())
        except (OSError, json.JSONDecodeError):
            # An unreadable metadata file is an undeclared bundle, not an absent one.
            out[bundle] = {"declared": False, "apexes": [], "unreadable": True}
            continue
        raw = meta.get(APEX_KEY)
        if raw is None:
            out[bundle] = {"declared": False, "apexes": []}
            continue
        names = []
        for entry in raw:
            if isinstance(entry, str):
                names.append(entry)
            elif isinstance(entry, dict) and entry.get("name"):
                names.append(entry["name"])
        out[bundle] = {"declared": True, "apexes": names}
    return out


def _index(records) -> tuple[dict, dict]:
    """`(by_name, autogen)` — the two lookups every closure walk needs."""
    from validate_helpers import autogen_index
    by_name = {r["name"]: r for r in records if r.get("name")}
    return by_name, autogen_index(records)


def compute_closure(seeds, by_name, autogen) -> tuple[set, int, int, int]:
    """Transitive closure of `seeds` over `name_deps_project`.

    Returns `(author_written_closure, max_depth, truncated_private, truncated_other)`.
    Compiler-generated declarations are walked THROUGH but not counted: they carry no research
    content, and omitting them from the walk would sever real dependencies that route through
    a structure's eliminator.
    """
    seen: set[str] = set()
    depth: dict[str, int] = {}
    trunc_private = trunc_other = 0
    q: deque[str] = deque()
    for s in seeds:
        if s in by_name and s not in seen:
            seen.add(s)
            depth[s] = 0
            q.append(s)
    while q:
        cur = q.popleft()
        for dep in by_name[cur].get("name_deps_project") or []:
            if dep in seen:
                continue
            if dep not in by_name:
                if dep.startswith(PRIVATE_PREFIX):
                    trunc_private += 1
                else:
                    trunc_other += 1
                continue
            seen.add(dep)
            depth[dep] = depth[cur] + 1
            q.append(dep)
    author = {n for n in seen if not autogen.get(n)}
    return author, (max(depth.values()) if depth else 0), trunc_private, trunc_other


def build_closures(records, declarations: dict[str, dict]) -> dict[str, BundleClosure]:
    """One `BundleClosure` per bundle, declared or not."""
    by_name, autogen = _index(records)
    out: dict[str, BundleClosure] = {}
    for bundle, decl in sorted(declarations.items()):
        bc = BundleClosure(bundle=bundle, declared=decl["declared"],
                           apexes=list(decl["apexes"]))
        seeds = []
        for name in bc.apexes:
            rec = by_name.get(name)
            if rec is None:
                bc.unresolved_apexes.append(name)
                continue
            if rec.get("kind") != "theorem":  # census-exempt: apex-kind
                bc.non_theorem_apexes.append(name)
            seeds.append(name)
        (bc.closure, bc.max_depth,
         bc.truncated_private, bc.truncated_other) = compute_closure(seeds, by_name, autogen)
        bc.modules = {by_name[n]["module"] for n in bc.closure}
        out[bundle] = bc
    return out


def homing_index(closures: dict[str, BundleClosure]) -> dict[str, list[str]]:
    """`{declaration: [bundles whose closure contains it]}`. `[]` => un-homed."""
    out: dict[str, list[str]] = {}
    for bundle, bc in sorted(closures.items()):
        for name in bc.closure:
            out.setdefault(name, []).append(bundle)
    return out


def project_declarations(records, autogen=None) -> set[str]:
    """Author-written declarations in the project namespace — the un-homed DENOMINATOR.

    Derived from the record set, never from a module list: a denominator that enumerates known
    forms is the defect this design replaces.
    """
    if autogen is None:
        _by_name, autogen = _index(records)
    return {r["name"] for r in records
            if r.get("name") and not autogen.get(r["name"])
            and (r.get("module") or "").startswith(PROJECT_NAMESPACE)}


def load_records():
    from extract_lean_deps import load_lean_deps
    return load_lean_deps()


def main(argv: list[str] | None = None) -> int:
    import argparse
    ap = argparse.ArgumentParser(description="Bundle substrate closure (publication intake).")
    ap.add_argument("--papers", default=str(PROJECT_ROOT / "papers"))
    ap.add_argument("--json", action="store_true", help="emit machine-readable output")
    args = ap.parse_args(argv)

    records = load_records()
    decls = load_apex_declarations(Path(args.papers))
    closures = build_closures(records, decls)
    homed = homing_index(closures)
    project = project_declarations(records)
    unhomed = project - set(homed)

    if args.json:
        print(json.dumps({
            "bundles": {b: {"declared": c.declared, "apexes": len(c.apexes),
                            "unresolved": c.unresolved_apexes,
                            "non_theorem": c.non_theorem_apexes,
                            "closure": len(c.closure), "modules": len(c.modules),
                            "max_depth": c.max_depth,
                            "truncated_private": c.truncated_private}
                        for b, c in closures.items()},
            "project_declarations": len(project),
            "homed": len(project) - len(unhomed),
            "un_homed": len(unhomed),
        }, indent=2))
        return 0

    undeclared = [b for b, c in closures.items() if not c.measurable]
    print(f"{'bundle':<8}{'apexes':>8}{'closure':>9}{'modules':>9}{'depth':>7}{'trunc':>7}")
    print("-" * 48)
    for b, c in closures.items():
        if not c.measurable:
            continue
        print(f"{b:<8}{len(c.apexes):>8}{len(c.closure):>9}{len(c.modules):>9}"
              f"{c.max_depth:>7}{c.truncated_private:>7}")
    print(f"\nproject author-written declarations: {len(project)}")
    print(f"  homed by >=1 bundle closure      : {len(project) - len(unhomed)}")
    print(f"  UN-HOMED                         : {len(unhomed)}")
    if undeclared:
        print(f"\n⚠ UNMEASURABLE — {len(undeclared)} bundle(s) declare no apexes, so their "
              f"substrate is unknown, NOT empty:\n    {', '.join(undeclared)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
