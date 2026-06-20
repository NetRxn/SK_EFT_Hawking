"""Unit tests for the lab-notebook lifecycle tooling (notebook_lib).
Run: uv run python -m pytest SK_EFT_Hawking/.claude/plugins/skeft-qa/tests/ -v"""
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS))
import notebook_lib as nb  # noqa: E402


# ---- new (bootstrap-if-missing) --------------------------------------------

def test_new_creates_both_files_with_all_blocks(tmp_path):
    r = nb.op_new(tmp_path)
    assert set(r["created"]) == {nb.ACTIVE_NAME, nb.INDEX_NAME}
    idx = (tmp_path / nb.INDEX_NAME).read_text()
    # all four live blocks + posture/objective present
    for kw in ["standing posture", "objective", "deliverables checklist", "frontier",
               "decisions & dead-ends", "shard index"]:
        assert nb._has_block(idx, kw.split()[0]) or kw in idx.lower(), kw
    # the DECISIONS block is the two-layer addition — must be present from birth
    assert nb._has_block(idx, "decision")
    # the active shard is registered in the shard index
    assert nb.ACTIVE_NAME in idx
    assert (tmp_path / nb.ACTIVE_NAME).exists()


def test_new_is_idempotent_and_never_clobbers(tmp_path):
    (tmp_path / nb.ACTIVE_NAME).write_text("# pre-existing active\n\n## 2026-01-01 brick\nbody\n")
    (tmp_path / nb.INDEX_NAME).write_text("# pre-existing index\n")
    r = nb.op_new(tmp_path)
    assert r["created"] == []  # nothing created
    assert "pre-existing active" in (tmp_path / nb.ACTIVE_NAME).read_text()
    assert "pre-existing index" in (tmp_path / nb.INDEX_NAME).read_text()


def test_new_creates_only_the_missing_file(tmp_path):
    (tmp_path / nb.ACTIVE_NAME).write_text("# already here\n")
    r = nb.op_new(tmp_path)
    assert r["created"] == [nb.INDEX_NAME]
    assert "already here" in (tmp_path / nb.ACTIVE_NAME).read_text()


def test_new_seeds_checklist_from_roadmap(tmp_path):
    rm = tmp_path / "roadmap.md"
    rm.write_text("# Roadmap\n- [x] L1 fundamental class\n- [ ] L2 poincare duality\nprose\n")
    nb.op_new(tmp_path, roadmap=str(rm))
    idx = (tmp_path / nb.INDEX_NAME).read_text()
    assert "L1 fundamental class" in idx and "L2 poincare duality" in idx
    assert "- [x]" not in idx.split("Deliverables checklist")[1].split("Frontier")[0]  # reset to unchecked


# ---- check (read-only) ------------------------------------------------------

def test_check_flags_oversize_active(tmp_path):
    nb.op_new(tmp_path)
    (tmp_path / nb.ACTIVE_NAME).write_text("# big\n\n## s\n" + ("x" * 5000))
    r = nb.op_check(tmp_path, budget_bytes=1000)
    assert r["over_budget"] is True
    assert any("shard" in w for w in r["warnings"])


def test_check_under_budget_clean(tmp_path):
    nb.op_new(tmp_path)
    r = nb.op_check(tmp_path, budget_bytes=100_000)
    assert r.get("over_budget") is False
    assert not any("over budget" in w.lower() for w in r["warnings"])


def test_check_flags_missing_decisions_block(tmp_path):
    nb.op_new(tmp_path)
    # simulate a pre-two-layer index by stripping the decisions block
    idx = tmp_path / nb.INDEX_NAME
    txt = idx.read_text()
    txt = txt.replace(nb.H_DECISIONS, "## ⚖ (old placeholder header)")
    idx.write_text(txt)
    r = nb.op_check(tmp_path)
    assert r.get("missing_decisions") is True


# ---- sync (mechanical scaffold maintenance) --------------------------------

def test_sync_inserts_missing_decisions_block(tmp_path):
    nb.op_new(tmp_path)
    idx = tmp_path / nb.INDEX_NAME
    idx.write_text(idx.read_text().replace(nb.H_DECISIONS, "## ⚖ (old placeholder header)"))
    assert not nb._has_block(idx.read_text(), "decision")
    r = nb.op_sync(tmp_path)
    assert any("DECISIONS" in c for c in r["changed"])
    assert nb._has_block(idx.read_text(), "decision")


def test_sync_adds_missing_shard_rows(tmp_path):
    nb.op_new(tmp_path)
    (tmp_path / "LAB_NOTEBOOK_W1.md").write_text("# old wave\n")
    r = nb.op_sync(tmp_path)
    assert any("shard-index row" in c for c in r["changed"])
    assert "LAB_NOTEBOOK_W1.md" in (tmp_path / nb.INDEX_NAME).read_text()


def test_sync_idempotent(tmp_path):
    nb.op_new(tmp_path)
    nb.op_sync(tmp_path)
    before = (tmp_path / nb.INDEX_NAME).read_text()
    r2 = nb.op_sync(tmp_path)
    assert r2["changed"] == []
    assert (tmp_path / nb.INDEX_NAME).read_text() == before


# ---- shard (self-leveling to under budget) ---------------------------------

def _active_with_sections(n, body_bytes):
    out = ["# T — Lab Notebook (ACTIVE shard)\n", "\n"]
    for i in range(1, n + 1):
        out.append(f"## 2026-06-{i:02d} — brick {i}\n")
        out.append("x" * body_bytes + "\n")
    return "".join(out)


def test_shard_rolls_oldest_until_under_budget(tmp_path):
    nb.op_new(tmp_path)
    (tmp_path / nb.ACTIVE_NAME).write_text(_active_with_sections(5, 400))
    r = nb.op_shard(tmp_path, budget_bytes=900)
    assert r["moved"] >= 1
    assert (tmp_path / "LAB_NOTEBOOK_W1.md").exists()
    active = (tmp_path / nb.ACTIVE_NAME).read_text()
    assert len(active.encode()) <= 900 or active.count("## ") == 1  # under budget or one section left
    # newest section is retained in the active shard, oldest moved out
    assert "brick 5" in active
    assert "brick 1" in (tmp_path / "LAB_NOTEBOOK_W1.md").read_text()
    assert "brick 1" not in active
    # the new frozen shard is registered in the INDEX
    assert "LAB_NOTEBOOK_W1.md" in (tmp_path / nb.INDEX_NAME).read_text()


def test_shard_noop_when_under_budget(tmp_path):
    nb.op_new(tmp_path)
    (tmp_path / nb.ACTIVE_NAME).write_text(_active_with_sections(2, 50))
    r = nb.op_shard(tmp_path, budget_bytes=100_000)
    assert r["moved"] == 0
    assert not (tmp_path / "LAB_NOTEBOOK_W1.md").exists()


def test_shard_numbers_sequentially(tmp_path):
    nb.op_new(tmp_path)
    (tmp_path / "LAB_NOTEBOOK_W1.md").write_text("# w1\n")
    (tmp_path / nb.ACTIVE_NAME).write_text(_active_with_sections(5, 400))
    r = nb.op_shard(tmp_path, budget_bytes=900)
    assert r["shard"] == "LAB_NOTEBOOK_W2.md"  # W1 exists -> next is W2


def test_shard_warns_when_single_oversize_section(tmp_path):
    nb.op_new(tmp_path)
    (tmp_path / nb.ACTIVE_NAME).write_text("# T\n\n## one huge\n" + ("x" * 5000) + "\n")
    r = nb.op_shard(tmp_path, budget_bytes=1000)
    assert r["moved"] == 0
    assert "warning" in r


# ---- extract_frontier (zero-Read SessionStart digest) ----------------------

def test_extract_frontier_returns_block_from_index_home_or_active(tmp_path):
    nb.op_new(tmp_path)
    idx = tmp_path / nb.INDEX_NAME
    idx.write_text(idx.read_text().replace(
        "- **NEXT BRICK:** (the single next action — numbered).",
        "- **NEXT BRICK:** prove lemma_foo via cover-partition."))
    # resolves from the INDEX path, the home dir, AND the active-shard path
    for arg in (str(idx), str(tmp_path), str(tmp_path / nb.ACTIVE_NAME)):
        fr = nb.extract_frontier(arg)
        assert "Frontier" in fr and "NEXT BRICK" in fr and "lemma_foo" in fr


def test_extract_frontier_caps_length(tmp_path):
    nb.op_new(tmp_path)
    idx = tmp_path / nb.INDEX_NAME
    idx.write_text(idx.read_text().replace(
        "- **Where:** (current sub-target / file).", "- **Where:** " + "y" * 5000))
    fr = nb.extract_frontier(str(idx), max_chars=800)
    assert len(fr) <= 900 and "truncated" in fr


def test_extract_frontier_absent_returns_empty(tmp_path):
    assert nb.extract_frontier(str(tmp_path / "nope")) == ""
    (tmp_path / "LAB_NOTEBOOK.md").write_text("# active, no index\n")
    assert nb.extract_frontier(str(tmp_path / "LAB_NOTEBOOK.md")) == ""  # no INDEX -> ''


# ---- roll (freeze-all escape for blobs / wave boundaries) ------------------

def test_roll_freezes_active_and_starts_fresh(tmp_path):
    nb.op_new(tmp_path)
    blob = "# T — Lab Notebook (ACTIVE shard)\n\n## 2026-06-18 wave\n" + ("x" * 9000) + "\n"
    (tmp_path / nb.ACTIVE_NAME).write_text(blob)
    r = nb.op_roll(tmp_path)
    assert r["frozen"] == "LAB_NOTEBOOK_W1.md"
    assert "x" * 9000 in (tmp_path / "LAB_NOTEBOOK_W1.md").read_text()  # blob preserved
    fresh = (tmp_path / nb.ACTIVE_NAME).read_text()
    assert "ACTIVE shard" in fresh and "xxxx" not in fresh  # active reset to a clean template
    assert "LAB_NOTEBOOK_W1.md" in (tmp_path / nb.INDEX_NAME).read_text()  # registered


def test_roll_noop_on_empty_active(tmp_path):
    nb.op_new(tmp_path)
    (tmp_path / nb.ACTIVE_NAME).write_text("   \n")
    r = nb.op_roll(tmp_path)
    assert r.get("frozen") is None


# ---- round-trip integrity ---------------------------------------------------

def test_shard_preserves_all_content(tmp_path):
    nb.op_new(tmp_path)
    original = _active_with_sections(6, 300)
    (tmp_path / nb.ACTIVE_NAME).write_text(original)
    nb.op_shard(tmp_path, budget_bytes=800)
    combined = (tmp_path / "LAB_NOTEBOOK_W1.md").read_text() + (tmp_path / nb.ACTIVE_NAME).read_text()
    for i in range(1, 7):
        assert f"brick {i}" in combined  # no brick lost across the split
