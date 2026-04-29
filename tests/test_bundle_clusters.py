"""
test_bundle_clusters.py — Phase 6i Wave 7.1 cross-bundle cluster tests
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

from bundle_clusters import build_index, INDEX_PATH


class TestBundleClusters:
    def test_build_index_returns_schema(self):
        idx = build_index()
        assert idx["schema_version"] == 1
        assert "clusters" in idx
        assert "cluster_count" in idx
        assert "cross_bundle_count" in idx
        assert idx["cluster_count"] == len(idx["clusters"])

    def test_each_cluster_has_required_fields(self):
        idx = build_index()
        required = {
            "id", "label", "match_kind", "member_papers",
            "members", "per_paper_bundles", "bundle_destinations",
            "bundle_destinations_excluding_flagship", "cross_bundle",
        }
        for c in idx["clusters"]:
            assert required.issubset(set(c.keys())), (
                f"missing fields: {required - set(c.keys())}"
            )

    def test_flagship_excluded_from_cross_bundle(self):
        # Every paper lifts into the flagship F. If F counted toward
        # cross_bundle, every cluster spanning ≥2 papers would be
        # cross-bundle, defeating the metric.
        idx = build_index()
        for c in idx["clusters"]:
            if c["cross_bundle"]:
                # Cross-bundle is computed on bundle set MINUS flagship.
                assert "F" not in c["bundle_destinations_excluding_flagship"]
                assert (
                    len(c["bundle_destinations_excluding_flagship"]) >= 2
                )

    def test_cross_bundle_count_matches_filter(self):
        idx = build_index()
        recomputed = sum(1 for c in idx["clusters"] if c["cross_bundle"])
        assert recomputed == idx["cross_bundle_count"]

    def test_per_paper_bundles_keys_match_member_papers(self):
        idx = build_index()
        for c in idx["clusters"]:
            assert (
                set(c["per_paper_bundles"].keys())
                == set(c["member_papers"])
            )

    def test_idempotent_writes(self, tmp_path):
        # Running build_index twice must produce identical output (modulo
        # JSON key ordering, which we control via json.dumps).
        a = json.dumps(build_index(), sort_keys=True)
        b = json.dumps(build_index(), sort_keys=True)
        assert a == b

    def test_index_file_writes_exist_after_main(self):
        # The CLI writes a sidecar at papers/cluster_bundle_index.json.
        # We expect the file to exist (it was written by Wave 7.1).
        assert INDEX_PATH.exists(), (
            f"missing {INDEX_PATH}; run `bundle_clusters.py` to build."
        )
        data = json.loads(INDEX_PATH.read_text())
        assert "clusters" in data
