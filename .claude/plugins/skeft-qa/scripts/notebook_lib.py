#!/usr/bin/env python3
"""Lab-notebook lifecycle tooling for the skeft-qa dev-harness.

One source-of-truth brick log per /goal loop, **progressively disclosed** via a
two-layer model:

  LAB_NOTEBOOK_INDEX.md  -- the DURABLE, always-loaded entry point. Bounded + topical;
                            never sharded away. Four live blocks: FRONTIER (current),
                            DELIVERABLES CHECKLIST (status), DECISIONS & DEAD-ENDS
                            (append-only — the antidote to re-attempting a known-wrong
                            path / re-deriving a settled rationale), SHARD INDEX
                            (topic-tagged pointers). Plus standing posture + objective.
  LAB_NOTEBOOK.md        -- the ACTIVE chronological shard (most-recent bricks; oldest first).
  LAB_NOTEBOOK_W<n>.md   -- frozen historical shards = the AUDIT layer (read on demand).

Why two layers: sharding fixes *size*, not *retrieval*. The expensive recurring
failures (re-exploring a dead-end, re-deriving a decision, frontier drift) are
retrieval failures — writes are chronological but reads are topical. So the topical,
high-value content (FRONTIER / CHECKLIST / DECISIONS) lives in the bounded INDEX that
is always loaded and never sharded; the chronological shards carry the deep trail.

Ops (deterministic, idempotent, stdlib-only):
  new   -- bootstrap-if-missing: create a correct active notebook + INDEX (never clobbers).
  sync  -- refresh the MECHANICAL INDEX scaffold (shard rows; ensure the DECISIONS block
           exists — migration for pre-two-layer indexes) + flag FRONTIER staleness.
           Never writes judgement content (FRONTIER/CHECKLIST/DECISIONS prose stay
           agent-authored; the tool maintains and validates the scaffold around them).
  shard -- roll the OLDEST sections out of the active shard into a new W<n> until the
           active shard is under the token budget (keeps it well under the ~25k Read guard).
  check -- read-only: sizes, over-budget?, missing DECISIONS block?, FRONTIER stale vs
           git HEAD? (feeds the SessionStart + pre-commit read-only warnings).

Stdlib only; runs under the repo's uv Python >=3.14. Self-leveling on invoke; no hook
mutates the notebook (harness principle: self-improving, never self-mutating).
"""
import os
import re
import subprocess
import sys
from pathlib import Path

INDEX_NAME = "LAB_NOTEBOOK_INDEX.md"
ACTIVE_NAME = "LAB_NOTEBOOK.md"
SHARD_RE = re.compile(r"^LAB_NOTEBOOK_W(\d+)\.md$")

# Token budget: the active shard must stay well under the ~25k-token Read/Edit guard.
# Estimate tokens as bytes/4; shard when the active shard exceeds ~18k tokens (~72 KB),
# leaving margin so a post-compaction re-read of the active shard never chokes.
BUDGET_BYTES = 72_000
INDEX_BUDGET_BYTES = 24_000  # the INDEX itself stays glanceable (<~6k tokens)


def _tok(nbytes):
    return nbytes // 4


# Canonical block headers (emoji-tolerant; matched elsewhere by keyword, case-insensitive).
H_POSTURE = "## ⛔ Standing posture (binding — every entry)"
H_OBJECTIVE = "## \U0001f3af Objective"
H_CHECKLIST = "## ✅ Deliverables checklist (synced to present state — update each brick)"
H_FRONTIER = "## ▶ Frontier (the single next action + live state — edit every brick)"
H_DECISIONS = (
    "## ⚖ Decisions & dead-ends (append-only — never sharded; "
    "promote out of FRONTIER when settled)"
)
H_SHARDS = "## \U0001f5c2 Shard index (read on demand — newest first)"

_DECISIONS_SEED = (
    "- (append-only; one line per settled fork / kernel-checked no-go: "
    "`DATE — claim → CHOSEN/REJECTED/NO-GO: why [lemma|commit]`.)\n"
)


def nb_paths(home):
    home = Path(home)
    shards = sorted(
        [p for p in home.glob("LAB_NOTEBOOK_W*.md") if SHARD_RE.match(p.name)],
        key=lambda p: int(SHARD_RE.match(p.name).group(1)),
    )
    return {
        "home": home,
        "index": home / INDEX_NAME,
        "active": home / ACTIVE_NAME,
        "shards": shards,
    }


def _index_path_from(notebook_path):
    """Resolve the INDEX path from a marker's notebook_path (which may already BE the INDEX,
    or the active shard, or the home dir)."""
    p = Path(notebook_path)
    if p.is_dir():
        return p / INDEX_NAME
    if p.name == INDEX_NAME:
        return p
    return p.parent / INDEX_NAME


def extract_frontier(notebook_path, max_chars=1600):
    """Return the INDEX FRONTIER block (its `## ▶ Frontier …` header + body, up to the next
    `## `), trimmed and capped at `max_chars`. Used by the SessionStart re-injection to land the
    live next-brick digest in-context so a post-compaction turn needs ZERO Reads to re-ground.
    Returns '' if the INDEX or its FRONTIER block is absent (so the caller degrades to the
    INDEX pointer). Pure read; fail-soft."""
    try:
        idx = _index_path_from(notebook_path)
        if not idx.exists():
            return ""
        _, sections = _split_sections(idx.read_text(errors="ignore"), "## ")
        for h, b in sections:
            if "frontier" in h.lower():
                block = (h + b).strip()
                if len(block) > max_chars:
                    block = block[:max_chars].rstrip() + "\n…(FRONTIER truncated — open the INDEX for the rest)"
                return block
    except Exception:
        return ""
    return ""


def _default_title(home):
    return Path(home).name or "Lab Notebook"


def _checklist_from_roadmap(roadmap):
    """Best-effort seed: lift existing GFM checkbox rows from the roadmap, reset to
    unchecked. Returns a list of '- [ ] ...' lines, or None if nothing usable."""
    if not roadmap:
        return None
    try:
        txt = Path(roadmap).read_text(errors="ignore")
    except Exception:
        return None
    seeds = []
    for ln in txt.splitlines():
        if re.match(r"\s*- \[[ xX]\] ", ln):
            seeds.append(re.sub(r"- \[[xX]\]", "- [ ]", ln.strip()))
        if len(seeds) >= 12:
            break
    return seeds or None


def _index_template(title, checklist_lines=None):
    cl = checklist_lines or [
        "- [ ] (seed deliverables from the roadmap — one GFM checkbox per acceptance criterion)"
    ]
    parts = [
        f"# {title} — Lab Notebook INDEX (session-start entry point)",
        "",
        "> **Read this FIRST every session / post-compaction.** It is the single-glance digest; detail",
        "> lives in the shards (read on demand). Keep this file small (≤ ~150 lines / ≆24 KB). Each brick:",
        "> edit FRONTIER + flip any completed CHECKLIST row HERE, append the long detail bullet to the active",
        "> `LAB_NOTEBOOK.md` (terse — one tight paragraph, not a 1 KB single line), and when you SETTLE a fork",
        "> or hit a kernel-checked no-go, append ONE line to DECISIONS (promote it out of the transient FRONTIER).",
        "",
        H_POSTURE,
        "- (standing posture for this loop — settled scope; legitimate stops only; kernel-purity; never re-pollute.)",
        "",
        H_OBJECTIVE,
        "- (the one-line settled objective + a pointer to the roadmap.)",
        "",
        H_CHECKLIST,
        *cl,
        "",
        H_FRONTIER,
        "- **Where:** (current sub-target / file).",
        "- **NEXT BRICK:** (the single next action — numbered).",
        "- **Open blocker:** (any wall / error, or 'none').",
        "- **Commit state:** HEAD=<sha> · (uncommitted / untracked state).",
        "",
        H_DECISIONS,
        _DECISIONS_SEED.rstrip("\n"),
        "",
        H_SHARDS,
        f"- **`{ACTIVE_NAME}`** (ACTIVE) — current bricks. (topic tags)",
        "",
    ]
    return "\n".join(parts)


def _active_template(title):
    return (
        f"# {title} — Lab Notebook (ACTIVE shard)\n\n"
        "> Chronological brick log (oldest first). The INDEX is the entry point; this shard holds the\n"
        "> most-recent bricks only — older waves roll into `LAB_NOTEBOOK_W<n>.md`. Keep entries terse.\n"
    )


def op_new(home, title=None, roadmap=None):
    p = nb_paths(home)
    p["home"].mkdir(parents=True, exist_ok=True)
    title = title or _default_title(p["home"])
    created = []
    if not p["active"].exists():
        p["active"].write_text(_active_template(title))
        created.append(p["active"].name)
    if not p["index"].exists():
        p["index"].write_text(_index_template(title, _checklist_from_roadmap(roadmap)))
        created.append(p["index"].name)
    return {
        "op": "new",
        "created": created,
        "index": str(p["index"]),
        "active": str(p["active"]),
    }


def _find_header_idx(lines, keyword):
    for i, ln in enumerate(lines):
        if ln.startswith("## ") and keyword in ln.lower():
            return i
    return None


def _has_block(text, keyword):
    for ln in text.splitlines():
        if ln.startswith("## ") and keyword in ln.lower():
            return True
    return False


def _frontier_stale(index_path, repo):
    """Return a warning string if the FRONTIER's recorded HEAD=<sha> differs from git
    HEAD, else None. Best-effort: no token / no git / unresolved -> None (skip)."""
    try:
        if not index_path.exists():
            return None
        m = re.search(r"HEAD=([0-9a-f]{7,40})", index_path.read_text(errors="ignore"))
        if not m:
            return None
        recorded = m.group(1)
        cmd = ["git", "rev-parse", "--short", "HEAD"]
        if repo:
            cmd = ["git", "-C", str(repo), "rev-parse", "--short", "HEAD"]
        out = subprocess.run(cmd, capture_output=True, text=True)
        if out.returncode != 0:
            return None
        head = out.stdout.strip()
        if head and not (recorded.startswith(head) or head.startswith(recorded)):
            return (
                f"INDEX FRONTIER records HEAD={recorded} but git HEAD is {head} "
                "— FRONTIER may be stale; reconcile it."
            )
    except Exception:
        return None
    return None


def op_check(home, budget_bytes=BUDGET_BYTES, repo=None):
    p = nb_paths(home)
    warns = []
    res = {"op": "check", "warnings": warns}
    if not p["index"].exists():
        warns.append(f"no {INDEX_NAME} in {p['home']} — run `notebook new` to scaffold it.")
    else:
        isz = p["index"].stat().st_size
        res["index_bytes"] = isz
        if isz > INDEX_BUDGET_BYTES:
            warns.append(
                f"{INDEX_NAME} is ~{isz // 1000} KB (> ~{INDEX_BUDGET_BYTES // 1000} KB) "
                "— trim it; the INDEX must stay glanceable."
            )
        if not _has_block(p["index"].read_text(errors="ignore"), "decision"):
            res["missing_decisions"] = True
            warns.append(
                f"{INDEX_NAME} has no DECISIONS & DEAD-ENDS block — run `notebook sync`."
            )
    if not p["active"].exists():
        warns.append(f"no {ACTIVE_NAME} in {p['home']} — run `notebook new`.")
    else:
        asz = p["active"].stat().st_size
        res["active_bytes"] = asz
        res["active_tokens_est"] = _tok(asz)
        res["over_budget"] = asz > budget_bytes
        if asz > budget_bytes:
            warns.append(
                f"{ACTIVE_NAME} is ~{_tok(asz) // 1000}k tokens "
                f"(> budget ~{_tok(budget_bytes) // 1000}k) — run `notebook shard`."
            )
    stale = _frontier_stale(p["index"], repo)
    if stale:
        res["frontier_stale"] = True
        res["frontier_stale_msg"] = stale   # the exact message — lets consumers demote it
                                            # reword-proof (finding m4), not by substring sniffing
        warns.append(stale)                 # kept in `warnings` for `notebook check`/`sync` (hygiene)
    return res


def _insert_block_before_shards(text, block):
    lines = text.splitlines(keepends=True)
    idx = _find_header_idx(lines, "shard index")
    if idx is None:
        idx = len(lines)
    block_lines = (block if block.endswith("\n") else block + "\n").splitlines(keepends=True)
    return "".join(lines[:idx] + block_lines + ["\n"] + lines[idx:])


def _ensure_shard_rows(text, p):
    lines = text.splitlines(keepends=True)
    idx = _find_header_idx(lines, "shard index")
    if idx is None:
        return text, 0
    to_add = []
    for path in [p["active"]] + p["shards"]:
        if path.exists() and path.name not in text:
            if path.name == ACTIVE_NAME:
                to_add.append(f"- **`{ACTIVE_NAME}`** (ACTIVE) — current bricks. (topic tags)\n")
            else:
                to_add.append(f"- **`{path.name}`** — frozen. (topic tags · dates)\n")
    if not to_add:
        return text, 0
    return "".join(lines[: idx + 1] + to_add + lines[idx + 1 :]), len(to_add)


def op_sync(home, budget_bytes=BUDGET_BYTES, repo=None):
    p = nb_paths(home)
    if not p["index"].exists():
        return {"op": "sync", "error": f"no {INDEX_NAME}; run `notebook new` first."}
    txt = p["index"].read_text()
    new = txt
    changed = []
    if not _has_block(new, "decision"):
        new = _insert_block_before_shards(new, H_DECISIONS + "\n" + _DECISIONS_SEED)
        changed.append("inserted DECISIONS & DEAD-ENDS block")
    new, added = _ensure_shard_rows(new, p)
    if added:
        changed.append(f"added {added} shard-index row(s)")
    if new != txt:
        p["index"].write_text(new)
    chk = op_check(home, budget_bytes, repo)
    return {"op": "sync", "changed": changed, "warnings": chk.get("warnings", [])}


def _split_sections(txt, prefix="## "):
    """Return (title_block, [(header_line, body), ...]) splitting on headings at the
    exact `prefix` level (e.g. '## ', '### '). Exact-prefix match so a '### ' line is
    not treated as a '## ' boundary and vice-versa."""
    lines = txt.splitlines(keepends=True)
    i = 0
    while i < len(lines) and not lines[i].startswith(prefix):
        i += 1
    title = "".join(lines[:i])
    sections = []
    cur_h, cur_b = None, []
    for ln in lines[i:]:
        if ln.startswith(prefix):
            if cur_h is not None:
                sections.append((cur_h, "".join(cur_b)))
            cur_h, cur_b = ln, []
        else:
            cur_b.append(ln)
    if cur_h is not None:
        sections.append((cur_h, "".join(cur_b)))
    return title, sections


def _dates_in(sections):
    dates = sorted(re.findall(r"\d{4}-\d{2}-\d{2}", "".join(h for h, _ in sections)))
    if not dates:
        return ""
    return dates[0] if dates[0] == dates[-1] else f"{dates[0]}→{dates[-1]}"


def _next_shard_num(p):
    nums = [int(SHARD_RE.match(s.name).group(1)) for s in p["shards"]]
    return (max(nums) + 1) if nums else 1


def _add_shard_row(index_path, name, dates):
    txt = index_path.read_text()
    if name in txt:
        return
    lines = txt.splitlines(keepends=True)
    idx = _find_header_idx(lines, "shard index")
    if idx is None:
        return
    insert_at = idx + 1
    for j in range(idx + 1, len(lines)):
        if ACTIVE_NAME in lines[j]:
            insert_at = j + 1
            break
        if lines[j].startswith("## "):
            insert_at = j
            break
    row = f"- **`{name}`** — frozen{(' · ' + dates) if dates else ''}. (topic tags)\n"
    lines.insert(insert_at, row)
    index_path.write_text("".join(lines))


def op_shard(home, budget_bytes=BUDGET_BYTES):
    p = nb_paths(home)
    if not p["active"].exists():
        return {"op": "shard", "error": f"no {ACTIVE_NAME}."}
    txt = p["active"].read_text()
    if len(txt.encode()) <= budget_bytes:
        return {"op": "shard", "moved": 0, "note": "active shard under budget; no-op."}
    # Cascade: split at the SHALLOWEST heading level that yields >1 section, so a
    # well-formed notebook shards by '##' (per-wave) while a monster single-'##'
    # section still shards finely by '###'/'####' instead of refusing.
    title = sections = None
    for pref in ("## ", "### ", "#### "):
        t, s = _split_sections(txt, pref)
        if len(s) > 1:
            title, sections = t, s
            break
    if sections is None:
        return {
            "op": "shard",
            "moved": 0,
            "warning": (
                "active over budget but has no splittable headings — either break the entry into "
                "per-brick ## / ### headings, or use `notebook roll` to freeze the whole active shard."
            ),
        }

    def cur_size():
        return len((title + "".join(h + b for h, b in sections)).encode())

    moved = []
    while cur_size() > budget_bytes and len(sections) > 1:
        moved.append(sections.pop(0))
    if not moved:
        return {"op": "shard", "moved": 0, "note": "nothing moved."}
    n = _next_shard_num(p)
    shard_path = p["home"] / f"LAB_NOTEBOOK_W{n}.md"
    dates = _dates_in(moved)
    hdr = f"# {p['home'].name} — Lab Notebook shard W{n} (frozen{(' · ' + dates) if dates else ''})\n\n"
    shard_path.write_text(hdr + "".join(h + b for h, b in moved))
    p["active"].write_text(title + "".join(h + b for h, b in sections))
    if p["index"].exists():
        _add_shard_row(p["index"], shard_path.name, dates)
    return {
        "op": "shard",
        "moved": len(moved),
        "shard": shard_path.name,
        "active_tokens_est": _tok(len(p["active"].read_text().encode())),
    }


def op_roll(home):
    """Freeze the ENTIRE active shard into a new W<n> and start a fresh active shard.
    Use at a clean wave boundary, or to escape a too-big active that isn't headed
    finely enough for `shard` to split. The INDEX FRONTIER carries current state, so a
    fresh active is fine; the just-frozen detail is one shard-index hop away."""
    p = nb_paths(home)
    if not p["active"].exists():
        return {"op": "roll", "error": f"no {ACTIVE_NAME}."}
    txt = p["active"].read_text()
    if not txt.strip():
        return {"op": "roll", "frozen": None, "note": "active shard already empty; no-op."}
    m = re.match(r"#\s+(.*)", txt)
    title = (m.group(1).split(" — ")[0].strip() if m else _default_title(home))
    dates = _dates_in(_split_sections(txt, "## ")[1]) or _dates_in(_split_sections(txt, "### ")[1])
    n = _next_shard_num(p)
    shard_path = p["home"] / f"LAB_NOTEBOOK_W{n}.md"
    shard_path.write_text(txt)
    p["active"].write_text(_active_template(title))
    if p["index"].exists():
        _add_shard_row(p["index"], shard_path.name, dates)
    return {"op": "roll", "frozen": shard_path.name, "active_reset": True}


def _home_from_marker():
    """Convenience for the /skeft-qa:notebook command: if no <home> is passed, resolve
    the active loop's notebook home (the marker's notebook_path parent) from the current
    session's marker. Best-effort + guarded so notebook_lib stays importable (and unit-
    testable) even when harness_common / a marker is absent."""
    try:
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import harness_common as hc

        m = hc.read_marker({"session_id": os.environ.get("CLAUDE_SESSION_ID", "")})
        if m and m.get("notebook_path"):
            return str(Path(m["notebook_path"]).parent)
    except Exception:
        return None
    return None


def _parse_opts(rest):
    opts = {}
    i = 0
    while i < len(rest):
        a = rest[i]
        if a.startswith("--"):
            key = a[2:]
            if i + 1 < len(rest) and not rest[i + 1].startswith("--"):
                opts[key] = rest[i + 1]
                i += 2
            else:
                opts[key] = True
                i += 1
        else:
            i += 1
    return opts


def _print_result(r):
    op = r.get("op", "?")
    if r.get("error"):
        print(f"[notebook {op}] ERROR: {r['error']}")
        return
    if op == "new":
        print(
            f"[notebook new] created: {', '.join(r['created']) if r['created'] else '(nothing — already present)'}"
        )
        print(f"  INDEX:  {r['index']}")
        print(f"  ACTIVE: {r['active']}")
    elif op == "sync":
        print(f"[notebook sync] changed: {', '.join(r['changed']) if r['changed'] else '(no scaffold changes)'}")
    elif op == "shard":
        if r.get("moved"):
            print(f"[notebook shard] moved {r['moved']} section(s) → {r['shard']}; active now ~{r.get('active_tokens_est', 0) // 1000}k tokens")
        else:
            print(f"[notebook shard] {r.get('note') or r.get('warning')}")
    elif op == "roll":
        if r.get("frozen"):
            print(f"[notebook roll] froze active → {r['frozen']}; started a fresh active shard")
        else:
            print(f"[notebook roll] {r.get('note', 'no-op')}")
    elif op == "check":
        bits = []
        if "active_tokens_est" in r:
            bits.append(f"active ~{r['active_tokens_est'] // 1000}k tok")
        if r.get("over_budget"):
            bits.append("OVER BUDGET")
        print(f"[notebook check] {'; '.join(bits) if bits else 'ok'}")
    for w in r.get("warnings", []):
        print(f"  ⚠ {w}")


def main(argv):
    if len(argv) < 1 or argv[0] in ("-h", "--help"):
        print("usage: notebook_lib.py <new|sync|shard|roll|check> <home> [--title T] [--roadmap P] [--repo R]")
        return 2
    op, rest = argv[0], argv[1:]
    home = rest[0] if rest and not rest[0].startswith("--") else None
    opts = _parse_opts(rest)
    home = home or opts.get("home") or _home_from_marker()
    if not home:
        print(
            "[notebook] ERROR: <home> required — pass the per-loop notebook directory, "
            "or run inside a managed /goal session (resolved from the marker's notebook_path)"
        )
        return 2
    if op == "new":
        r = op_new(home, opts.get("title"), opts.get("roadmap"))
    elif op == "sync":
        r = op_sync(home, repo=opts.get("repo"))
    elif op == "shard":
        r = op_shard(home)
    elif op == "roll":
        r = op_roll(home)
    elif op == "check":
        r = op_check(home, repo=opts.get("repo"))
    else:
        print(f"[notebook] ERROR: unknown op '{op}' (use new|sync|shard|roll|check)")
        return 2
    _print_result(r)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
