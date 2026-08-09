"""TODO-D25: one serializer for per-bundle JSON blobs.

Eleven call sites across five scripts disagreed on `ensure_ascii`, so whichever
tool touched a blob last decided its encoding and a 9-line edit could produce a
98-insertion / 91-deletion diff. These tests pin the corpus in the canonical
form and pin every writer to the shared serializer.

The population was measured, not taken from the TODO entry, which scoped itself
to `bundle_metadata.json` and named four writers. Both blob types carry the
defect in OPPOSITE majority directions:
    bundle_metadata.json  21 files  20 raw-unicode /  1 escaped
    append_log.json       20 files   2 raw-unicode / 19 escaped
"""
from __future__ import annotations

import ast
import json
import pathlib
import re
import sys

import pytest

REPO = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))

BLOBS = sorted(REPO.glob("papers/*/bundle_metadata.json")) + \
        sorted(REPO.glob("papers/*/append_log.json"))

# Every module that writes a per-bundle blob. Kept as a list because the point
# of the test is that each one routes through the serializer.
WRITER_MODULES = [
    "bundle_append.py",
    "bundle_source_manifest.py",
    "bundle_readiness.py",
    "compile_bundle_pdf.py",
    "record_review.py",
    # ⚠️ Added 2026-08-09. This one was MISSING while it wrote
    # `json.dumps(md, indent=2)` (ensure_ascii defaulted True) into all 21
    # `bundle_metadata.json` files under `write_metadata=True`. Every one of
    # those carries non-ASCII in its apex `claims` strings, so a single CLI run
    # re-escaped the corpus and reintroduced the oscillation this file closed.
    # The AST guard below was right; the roster it ran over was incomplete.
    "check_bundle_source_freshness.py",
]


class TestCorpusIsCanonical:
    def test_no_blob_carries_escaped_unicode(self):
        """`\\u00a7` is not review-legible, and the apex `claims` strings carry
        `§` and `—`. A reviewer must be able to read the claim they are
        approving."""
        offenders = [str(f.relative_to(REPO)) for f in BLOBS
                     if re.search(r'\\u[0-9a-fA-F]{4}', f.read_text(encoding="utf-8"))]
        assert offenders == [], f"escaped-unicode blobs: {offenders}"

    @pytest.mark.parametrize("blob", BLOBS, ids=lambda p: str(p.relative_to(REPO)))
    def test_blob_is_byte_stable_through_the_serializer(self, blob):
        """Round-trip is a fixed point: load, re-serialize, bytes identical.
        This is what makes `git diff` usable as evidence of what a tool changed."""
        from bundle_json import dump_bundle_json
        text = blob.read_text(encoding="utf-8")
        assert dump_bundle_json(json.loads(text)) == text


class TestEveryWriterRoutesThroughTheSerializer:
    @pytest.mark.parametrize("mod", WRITER_MODULES)
    def test_no_direct_json_dumps_to_a_bundle_blob(self, mod):
        """Structural, via `ast` rather than grep: no `.write_text(json.dumps(...))`
        survives in a bundle-blob writer. A new writer added later that open-codes
        the dump reintroduces the oscillation, and this is what catches it."""
        src = (REPO / "scripts" / mod).read_text(encoding="utf-8")
        tree = ast.parse(src)
        bad = []
        for node in ast.walk(tree):
            if not (isinstance(node, ast.Call)
                    and isinstance(node.func, ast.Attribute)
                    and node.func.attr == "write_text"):
                continue
            for arg in ast.walk(node):
                if (isinstance(arg, ast.Attribute) and arg.attr == "dumps"
                        and isinstance(arg.value, ast.Name) and arg.value.id == "json"):
                    bad.append(node.lineno)
        # compile_bundle_pdf writes a non-bundle gate cache; allow it explicitly
        allowed = {"compile_bundle_pdf.py"}
        if mod in allowed:
            pytest.skip(f"{mod} retains a non-bundle cache writer by design")
        assert bad == [], f"{mod} still open-codes json.dumps at line(s) {bad}"

    @pytest.mark.parametrize("mod", WRITER_MODULES)
    def test_writer_imports_the_serializer(self, mod):
        src = (REPO / "scripts" / mod).read_text(encoding="utf-8")
        assert "from bundle_json import write_bundle_json" in src


class TestWriterSkipsIdenticalBytes:
    def test_identical_write_is_a_noop(self, tmp_path):
        """mtime must not move on a no-op write — other freshness checks key on
        it, so rewriting identical content makes a no-op look like a change."""
        from bundle_json import write_bundle_json
        p = tmp_path / "b.json"
        obj = {"a": "§ and — unicode", "n": 1}
        assert write_bundle_json(p, obj) is True      # first write
        m1 = p.stat().st_mtime_ns
        assert write_bundle_json(p, obj) is False     # unchanged
        assert p.stat().st_mtime_ns == m1

    def test_real_change_is_written(self, tmp_path):
        from bundle_json import write_bundle_json
        p = tmp_path / "b.json"
        write_bundle_json(p, {"a": 1})
        assert write_bundle_json(p, {"a": 2}) is True
        assert json.loads(p.read_text(encoding="utf-8"))["a"] == 2


# ── TODO-D14: an empty lift must not count as an absorption ───────────────

class TestEmptyLiftEventsAreMarked:
    """`append_log.json` recorded `Lift-section` for events that inserted a
    heading and zero rendered words, so any absorption count taken from the log
    over-counted. The events are real history and are NOT deleted; they carry
    `content_inserted: false`, which is what a count must filter on.

    ⚠️ Measured 43 Lift-section events across D1-D4, 17 of them empty. The TODO
    said 16 (D3 7, D4 3); the true split is D3 6, D4 5."""

    LOGS = ["D1", "D2", "D3", "D4"]

    def test_every_lean_only_lift_is_marked_empty(self):
        import json
        for b in self.LOGS:
            d = json.loads((REPO / f"papers/{b}/append_log.json").read_text(encoding="utf-8"))
            for e in d.get("events", []):
                if ("Lift-section" in str(e.get("lift_action", ""))
                        and "lean_only" in str(e.get("source_paper", ""))):
                    assert e.get("content_inserted") is False, \
                        f"{b}: {e.get('source_paper')} not marked empty"

    def test_genuine_lifts_are_not_marked(self):
        """The flag must discriminate, not blanket-apply."""
        import json
        genuine = 0
        for b in self.LOGS:
            d = json.loads((REPO / f"papers/{b}/append_log.json").read_text(encoding="utf-8"))
            for e in d.get("events", []):
                if ("Lift-section" in str(e.get("lift_action", ""))
                        and e.get("content_inserted") is not False):
                    genuine += 1
        assert genuine > 0, "all lifts marked empty — the flag stopped discriminating"

    def test_lift_action_is_unchanged(self):
        """`lift_action` is parsed by sentence_state and bundle_source_manifest;
        rewriting it would break them. The new field is additive."""
        import json
        for b in self.LOGS:
            d = json.loads((REPO / f"papers/{b}/append_log.json").read_text(encoding="utf-8"))
            for e in d.get("events", []):
                assert "Lift-section-empty" not in str(e.get("lift_action", ""))
