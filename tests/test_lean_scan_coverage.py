"""Every Lean-scanning site in the enforcement path must see the WHOLE tree.

Audit finding **QI-01** (`docs/audits/2026-08-04-qa-qi-infrastructure/README.md`).

WHAT WENT WRONG
---------------
Five sites globbed ``*.lean`` instead of ``**/*.lean``. Measured 2026-08-04:
**1,373 of 2,039** files were in scope — a third of the Lean library was invisible.

The one with teeth is ``build_graph.extract_placeholder_marker_nodes``: **112
placeholder-bodied theorems in subdirectories minted no PlaceholderMarker node**
(e.g. ``APSEta/Predicate.lean::isSakharovConsistent_BECAcoustic``). P1 **Gate 5
(LeanProofSubstance)** decides by membership in exactly those nodes, so it reported
"no placeholder theorems cited" having never looked at those packages. That is the
`QA_QI_INFRASTRUCTURE_MAP` §7 shape — absence of measurement rendered as success —
living inside a P1 gate.

The class was NOT new: ADR-004 W7 finding M2 fixed exactly this in
``freshness.py:_counts_is_stale`` ("a *.lean in a subdirectory must also mark counts
stale") and the sweep stopped there.

WHY A STRUCTURAL LEG, NOT ONLY A COUNT
--------------------------------------
A count assertion catches a REGRESSION of the sites that exist. It cannot catch a
NEW site added with ``glob``, which is how this arrived in the first place —
`freshness.py` was already correct while five siblings were not. The third test
below scans the enforcement surface for the non-recursive form, so a new site fails
on arrival rather than after someone measures a gate.

MUTATION-VERIFIED 2026-08-04, both directions:
  * revert any site to ``glob("*.lean")``
        -> test_no_enforcement_site_uses_a_non_recursive_lean_glob FAILS (names it)
  * revert ``extract_placeholder_marker_nodes`` to ``glob``
        -> test_subdirectory_placeholders_mint_nodes FAILS (707 -> 593)
  * make ``compute_source_hash`` ignore nested files
        -> test_source_hash_responds_to_a_subdirectory_only_edit FAILS
Clean negative control: unmutated tree, all three pass.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

LEAN_DIR = SK_ROOT / "lean" / "SKEFTHawking"

#: Files that decide, or feed something that decides, a gate verdict. The
#: provenance dashboard is deliberately EXCLUDED — it is a read-only human surface,
#: not an enforcement path, and holds its own non-recursive globs by choice.
_ENFORCEMENT_SOURCES: tuple[Path, ...] = (
    SK_ROOT / "scripts" / "build_graph.py",
    SK_ROOT / "scripts" / "graph_integrity.py",
    SK_ROOT / "scripts" / "readiness_gates.py",
    SK_ROOT / "scripts" / "bundle_readiness.py",
    *sorted((SK_ROOT / "scripts" / "validation").rglob("*.py")),
)

#: `.glob("*.lean")` / `.glob('*.lean')` — the non-recursive form, on any receiver.
_NON_RECURSIVE_LEAN_GLOB = re.compile(r"""\.glob\(\s*["']\*\.lean["']\s*\)""")


class TestPlaceholderScanCoversWholeTree:
    """`extract_placeholder_marker_nodes` must scan every Lean file, not just the
    top level. Its output is the population P1 Gate 5 reads."""

    def test_subdirectory_placeholders_mint_nodes(self):
        from build_graph import (
            _PLACEHOLDER_BODY_PATTERNS,
            _scan_lean_theorem_bodies,
            extract_placeholder_marker_nodes,
        )
        from src.core.constants import PLACEHOLDER_LEAN_NAMES

        registered = set(PLACEHOLDER_LEAN_NAMES.keys())

        def independent_scan(files) -> set[str]:
            """Re-derive the expected population WITHOUT calling the extractor, so
            this asserts against the Lean tree rather than against production
            agreeing with itself."""
            found: set[str] = set()
            for f in files:
                try:
                    src = f.read_text()
                except (OSError, UnicodeDecodeError):
                    continue
                for name, _line, body in _scan_lean_theorem_bodies(src):
                    if name in registered:
                        continue
                    if any(rx.search(body) for rx, _ in _PLACEHOLDER_BODY_PATTERNS):
                        found.add(f"{f}::{name}")
            return found

        top_only = independent_scan(sorted(LEAN_DIR.glob("*.lean")))
        whole_tree = independent_scan(sorted(LEAN_DIR.rglob("*.lean")))

        # Guard the guard: if the tree ever flattens, the two scans coincide and
        # this test becomes vacuous. Say so instead of passing silently.
        assert len(whole_tree) > len(top_only), (
            "no placeholder-bodied theorem lives in a subdirectory, so this test "
            "cannot distinguish a recursive scan from a non-recursive one. It is "
            "vacuous as written — re-derive it against something that still varies."
        )

        nodes = extract_placeholder_marker_nodes()
        assert len(nodes) == len(whole_tree), (
            f"{len(whole_tree)} placeholder-bodied theorems exist across "
            f"{len(list(LEAN_DIR.rglob('*.lean')))} Lean files, but "
            f"extract_placeholder_marker_nodes minted {len(nodes)} nodes. A "
            f"non-recursive glob leaves {len(whole_tree) - len(top_only)} of them "
            f"unminted, and P1 Gate 5 (LeanProofSubstance) decides by membership "
            f"in exactly this set — so a paper citing one of them clears the gate "
            f"against an incomplete population (audit QI-01)."
        )

    def test_node_ids_are_unique_across_subdirectories(self):
        """Two same-named modules in different packages must not collide.

        Recursion makes this reachable: `A/Foo.lean` and `B/Foo.lean` both keyed on
        the bare stem would mint one id and `seen_ids` would drop the second —
        reintroducing here the class-omitted-from-the-key defect that silently lost
        66 PythonTest nodes (ADR-009 §Deferred item 7).
        """
        from build_graph import extract_placeholder_marker_nodes

        ids = [n["id"] for n in extract_placeholder_marker_nodes()]
        dupes = sorted({i for i in ids if ids.count(i) > 1})
        assert not dupes, (
            f"{len(dupes)} PlaceholderMarker id(s) minted more than once: "
            f"{dupes[:5]}. The id must carry the module PATH, not the bare file "
            f"stem, or same-named modules in different packages collide and the "
            f"later one is silently dropped."
        )

    def test_every_node_names_a_file_that_exists(self):
        """`meta.lean_file` must stay a real on-disk path once the dotted module
        name and the filesystem path stop being the same string."""
        from build_graph import extract_placeholder_marker_nodes

        missing = [
            n["meta"]["lean_file"]
            for n in extract_placeholder_marker_nodes()
            if not (SK_ROOT / n["meta"]["lean_file"]).is_file()
        ]
        assert not missing, (
            f"{len(missing)} PlaceholderMarker node(s) point at a path that does "
            f"not exist, e.g. {missing[:3]}. `module` is the DOTTED Lean module "
            f"name (`APSEta.Predicate`); `lean_file` must remain the real path."
        )


class TestSourceHashCoversWholeTree:
    """`compute_source_hash` is the graph's staleness key. A change anywhere in the
    Lean tree must move it."""

    def test_source_hash_responds_to_a_subdirectory_only_edit(self, tmp_path, monkeypatch):
        import build_graph

        nested = tmp_path / "Pkg" / "Nested.lean"
        nested.parent.mkdir(parents=True)
        nested.write_text("theorem a : True := trivial\n")
        (tmp_path / "Top.lean").write_text("theorem b : True := trivial\n")

        monkeypatch.setattr(build_graph, "LEAN_DIR", tmp_path)
        before = build_graph.compute_source_hash()

        nested.write_text("theorem a : True := by trivial\n")   # subdirectory ONLY
        after = build_graph.compute_source_hash()

        assert before != after, (
            "editing a Lean file in a SUBDIRECTORY did not change the source hash. "
            "The hash is the graph's staleness key, so a third of the library "
            "could drift without the graph noticing (audit QI-01)."
        )


class TestNoEnforcementSiteUsesNonRecursiveLeanGlob:
    """Structural leg: catch a NEW site added with the non-recursive form.

    The count assertions above only protect the sites that exist today. This is the
    one that would have caught the original defect, because `freshness.py` was
    already correct while five siblings were not.
    """

    def test_no_enforcement_site_uses_a_non_recursive_lean_glob(self):
        offenders: list[str] = []
        for path in _ENFORCEMENT_SOURCES:
            if not path.is_file():
                continue
            for lineno, line in enumerate(path.read_text().splitlines(), 1):
                if _NON_RECURSIVE_LEAN_GLOB.search(line):
                    offenders.append(f"{path.relative_to(SK_ROOT)}:{lineno}")

        assert not offenders, (
            f"non-recursive `.glob('*.lean')` in the enforcement path: {offenders}. "
            f"Measured 2026-08-04: that form sees 1,373 of 2,039 files, so a third "
            f"of the Lean library is unscanned. Use `rglob('*.lean')`. If a site "
            f"genuinely wants top-level-only, say so in a comment and add it to an "
            f"explicit exemption here rather than leaving the call bare "
            f"(audit QI-01)."
        )

    def test_the_scanner_actually_matches_the_forbidden_form(self):
        """Guard the seam. A regex that matched nothing would make the assertion
        above vacuous — the same trap `test_cannot_measure_baseline` guards.
        """
        assert _NON_RECURSIVE_LEAN_GLOB.search('for f in d.glob("*.lean"):')
        assert _NON_RECURSIVE_LEAN_GLOB.search("sorted(LEAN_DIR.glob('*.lean'))")
        assert not _NON_RECURSIVE_LEAN_GLOB.search('for f in d.rglob("*.lean"):')
        assert not _NON_RECURSIVE_LEAN_GLOB.search('d.glob("*.py")')
