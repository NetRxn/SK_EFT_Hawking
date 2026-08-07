#!/usr/bin/env python3
"""Derive the project's QA/process SURFACE INVENTORY from the code, not from memory.

    uv run python scripts/architecture_inventory.py            # print
    uv run python scripts/architecture_inventory.py --write    # write the tracked doc
    uv run python scripts/architecture_inventory.py --json     # machine-readable

WHY THIS EXISTS
---------------
`docs/architecture/END_TO_END_MAP.md` is the narrative — the story of how work moves from a
roadmap to a signed-off publication. Narrative rots. Every count in it, every roster, every
"there are N checks" is a fact about the tree at one moment, and this project has repeatedly
been bitten by exactly that: a pipeline doc still saying "12 stages" and "all 16 checks"
against a live 14 and 64, a roster frozen at 18 targets against a live 21, an ADR describing
a toolchain two pins behind.

So the map SPLITS. The narrative explains and links; **this script derives every enumerable
fact** and writes `docs/architecture/SURFACE_INVENTORY.md`. A check
(`architecture_inventory_fresh`) fails when the tracked doc no longer matches a fresh run, so
the inventory cannot silently drift from the system it describes.

⚠️ **Nothing here is hand-listed.** Every population below is read from the artifact that
owns it — the check registry, the gate roster, the plugin manifest, the AST of the graph
builder. If a section needs a literal, that is a defect in this script, not a shortcut to
take: a hand-listed inventory of a system whose whole failure mode is silent drift would be
the failure mode wearing a lab coat.
"""
from __future__ import annotations

import argparse
import ast
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(SCRIPT_DIR))

OUT_PATH = PROJECT_ROOT / "docs" / "architecture" / "SURFACE_INVENTORY.md"
PLUGIN = PROJECT_ROOT / ".claude" / "plugins" / "skeft-qa"


# ─────────────────────────────────────────────────────────────────────────
# Derivations — each reads the artifact that OWNS the population
# ─────────────────────────────────────────────────────────────────────────

def checks() -> list[dict]:
    """Every registered validation check, in execution order, with its owning module."""
    import validate
    out = []
    for i, spec in enumerate(validate._CHECKS):
        mod = getattr(spec.func, "__module__", "?")
        # `_memo` wraps some checks; the wrapper hides the real owner.
        inner = getattr(spec.func, "__memo_body__", None)
        if inner is not None:
            mod = getattr(inner, "__module__", mod)
        out.append({"order": i, "name": spec.name,
                    "module": mod.rsplit(".", 1)[-1],
                    "description": spec.description})
    return out


def gates() -> list[dict]:
    """The readiness-gate roster, from the roster itself."""
    import readiness_gates
    return [{"gate": g, "priority": p, "evaluator": fn.__name__}
            for g, p, fn in readiness_gates.GATES]


def _string_constants_in_calls(path: Path, attrs: set[str]) -> dict[str, int]:
    """`{literal: first lineno}` for uppercase string args to `x.<attr>(...)` calls."""
    out: dict[str, int] = {}
    for node in ast.walk(ast.parse(path.read_text())):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and node.func.attr in attrs):
            for arg in node.args:
                if isinstance(arg, ast.Constant) and isinstance(arg.value, str) \
                        and arg.value.isupper():
                    out.setdefault(arg.value, node.lineno)
    return out


def _emitted_edge_types(graph_py: Path) -> set[str]:
    """Edge types `build_graph.py` emits, scoped STRUCTURALLY.

    An edge dict is one carrying `source` and `target` alongside `type`. Node dicts
    use the same `type` key, so a scan keyed on `type` alone collects the whole node
    taxonomy too — 40 "edge types" against a true 22 (measured 2026-08-06).

    This function previously did that wide scan and then **subtracted the node types
    afterwards**, which produced the right list by cancellation rather than by scope,
    and left two live hazards: an edge type sharing a name with a node type would be
    silently dropped from `edges_emitted`, and — worse — the
    `edges_consumed_but_never_emitted` comparison ran against the *unsubtracted* set,
    so such an edge would read as emitted and its gate would never be reported dead.

    `validate.py --check gate_edge_types_are_emitted` derives the same population and
    `tests/test_architecture_inventory.py` asserts the two agree, so the census and
    the gate cannot drift apart.
    """
    emitted: set[str] = set()
    for node in ast.walk(ast.parse(graph_py.read_text())):
        if not isinstance(node, ast.Dict):
            continue
        keys = {k.value for k in node.keys
                if isinstance(k, ast.Constant) and isinstance(k.value, str)}
        if not {"source", "target"} <= keys:
            continue
        for k, v in zip(node.keys, node.values):
            if (isinstance(k, ast.Constant) and k.value == "type"
                    and isinstance(v, ast.Constant) and isinstance(v.value, str)):
                emitted.add(v.value)
    return emitted


def graph_types() -> dict:
    """Node types, emitted edge types, and edge types the gates CONSUME.

    The third population is the one that matters: an edge type consumed but never emitted is
    a gate returning a verdict it did not compute (see `gate_edge_types_are_emitted`).
    """
    import build_graph
    emitted: set[str] = _emitted_edge_types(SCRIPT_DIR / "build_graph.py")
    consumed = _string_constants_in_calls(
        SCRIPT_DIR / "readiness_gates.py", {"outgoing", "incoming"})
    return {
        "node_types": sorted(build_graph.SHAPE_MAP),
        "edges_emitted": sorted(emitted),
        "edges_consumed_by_gates": sorted(consumed),
        "edges_consumed_but_never_emitted": sorted(
            t for t in consumed if t not in emitted),
    }


def hooks() -> list[dict]:
    """Claude-Code hooks from the plugin manifest, plus git hooks on disk."""
    out: list[dict] = []
    manifest = PLUGIN / "hooks" / "hooks.json"
    if manifest.exists():
        try:
            data = json.loads(manifest.read_text())
        except json.JSONDecodeError:
            data = {}
        for event, entries in (data.get("hooks") or {}).items():
            for entry in entries:
                for h in entry.get("hooks", []):
                    out.append({"kind": "claude-code", "event": event,
                                "matcher": entry.get("matcher", "*"),
                                "command": h.get("command", "")[:200],
                                "timeout": h.get("timeout")})
    git_hooks = PROJECT_ROOT / ".git" / "hooks"
    if git_hooks.is_dir():
        for f in sorted(git_hooks.iterdir()):
            if f.is_file() and not f.name.endswith(".sample"):
                out.append({"kind": "git", "event": f.name,
                            "matcher": "-", "command": str(
                                f.relative_to(PROJECT_ROOT)), "timeout": None})
    return out


def _frontmatter(path: Path) -> dict:
    """YAML frontmatter reader for `key: value` AND folded/literal block scalars.

    ⚠️ The block-scalar case is not a nicety. Five of the eight agents write
    `description: >` and continue on indented lines; a reader that takes only the value on
    the key's own line records their purpose as the literal string `>`. The first version
    of this function did exactly that, and the rendered inventory said `>` for
    adversarial-reviewer, claims-reviewer, figure-reviewer, lean-worker and research-scout —
    an inventory that silently blanks the majority of a population is worse than none.
    """
    text = path.read_text()
    if not text.startswith("---"):
        return {}
    end = text.find("\n---", 3)
    body = text[3:end if end > 0 else len(text)]
    out: dict[str, str] = {}
    key: str | None = None
    folded: list[str] = []

    def flush() -> None:
        if key is not None and folded:
            out[key] = " ".join(s.strip() for s in folded if s.strip())

    for line in body.splitlines():
        if line[:1] not in (" ", "\t", "") and ":" in line and not line.startswith("#"):
            flush()
            k, _, v = line.partition(":")
            key, v = k.strip(), v.strip()
            if v in (">", "|", ">-", "|-"):      # block scalar: value is on the next lines
                folded = []
            else:
                out[key] = v
                key, folded = None, []
        elif key is not None:
            folded.append(line)
    flush()
    return out


def agents_and_commands() -> dict:
    out: dict[str, list] = {"agents": [], "commands": []}
    for kind, sub in (("agents", "agents"), ("commands", "commands")):
        d = PLUGIN / sub
        if not d.is_dir():
            continue
        for f in sorted(d.glob("*.md")):
            fm = _frontmatter(f)
            out[kind].append({
                "name": fm.get("name", f.stem),
                "path": str(f.relative_to(PROJECT_ROOT)),
                "model": fm.get("model", ""),
                "description": (fm.get("description", "") or "")[:180],
            })
    return out


def registries() -> list[dict]:
    """The canonical hand-maintained registries, sized. HAND-MAINTAINED is the point:
    these are the surfaces that can drift, so the inventory records their size over time."""
    out = []
    probes = [
        ("src.core.constants", ["ARISTOTLE_THEOREMS", "AXIOM_METADATA",
                                "HYPOTHESIS_REGISTRY", "PLACEHOLDER_THEOREMS",
                                "KERNEL_NOGO_REGISTRY", "MODELING_ASSUMPTION_THEOREMS",
                                "TRACKED_HYPOTHESIS_NON_LOAD_BEARING"]),
        ("src.core.provenance", ["PARAMETER_PROVENANCE", "PAPER_DEPENDENCIES"]),
        ("src.core.citations", ["CITATION_REGISTRY"]),
    ]
    for mod_name, names in probes:
        try:
            mod = __import__(mod_name, fromlist=["*"])
        except Exception as exc:  # noqa: BLE001
            out.append({"registry": mod_name, "size": None, "note": f"import failed: {exc}"})
            continue
        for n in names:
            reg = getattr(mod, n, None)
            if reg is None:
                continue
            out.append({"registry": f"{mod_name.rsplit('.', 1)[-1]}.{n}",
                        "size": len(reg) if hasattr(reg, "__len__") else None,
                        "note": ""})
    return out


def bundles() -> list[dict]:
    """The publication roster, from the registry that owns it."""
    try:
        import bundle_registry
    except Exception:  # noqa: BLE001
        return []
    out = []
    # `BY_CODE` is the registry's own code→Bundle map; `BUNDLES` is a tuple of records, so
    # indexing it by code raises. Read the map the registry publishes rather than rebuilding
    # one here — a second index is a second thing to drift.
    by_code = getattr(bundle_registry, "BY_CODE", {})
    for code in bundle_registry.BUNDLE_CODES:
        b = by_code.get(code)
        meta = PROJECT_ROOT / "papers" / code / "bundle_metadata.json"
        apex = 0
        if meta.exists():
            try:
                apex = len(json.loads(meta.read_text()).get("apex_theorems") or [])
            except json.JSONDecodeError:
                apex = 0
        out.append({"code": code,
                    "tier": getattr(b, "tier", None) if b else None,
                    "title": (getattr(b, "title", "") if b else "")[:60],
                    "apex_theorems": apex})
    return out


def collect() -> dict:
    return {"checks": checks(), "gates": gates(), "graph": graph_types(),
            "hooks": hooks(), **agents_and_commands(),
            "registries": registries(), "bundles": bundles()}


# ─────────────────────────────────────────────────────────────────────────
# Rendering
# ─────────────────────────────────────────────────────────────────────────

def render(inv: dict) -> str:
    L: list[str] = []
    a = L.append
    a("# Surface inventory — DERIVED, do not hand-edit")
    a("")
    a("> Generated by `scripts/architecture_inventory.py`. Each table's VALUES are read from")
    a("> the artifact that owns them — the check registry, the gate roster, the plugin manifest,")
    a("> the AST of the graph builder, the bundle registry. Their MEMBERSHIP is derived the same")
    a("> way, with one exception: the registries table lists a curated set named in the")
    a("> generator, because which collections count as tracked registries is an editorial call,")
    a("> not a mechanical property. **Do not edit this file**: run")
    a("> `uv run python scripts/architecture_inventory.py --write`.")
    a(">")
    a("> The narrative that explains how these pieces fit together is")
    a("> [`END_TO_END_MAP.md`](END_TO_END_MAP.md). This file is the *census*; that one is the")
    a("> *story*. They are split because the story is stable and the census is not, and a")
    a("> stale count inside a narrative is how this project has repeatedly lost its own map.")
    a("")
    a("**No timestamp is recorded here on purpose** — a date would make the file dirty on")
    a("every run and turn the freshness check into noise. The tree state IS the timestamp.")
    a("")

    ck = inv["checks"]
    a(f"## Validation checks — {len(ck)}, in execution order")
    a("")
    a("Execution order is semantic: the `*_fresh` regenerators rewrite artifacts that later")
    a("checks read. See `validate._CANONICAL_ORDER`.")
    a("")
    by_mod: dict[str, int] = {}
    for c in ck:
        by_mod[c["module"]] = by_mod.get(c["module"], 0) + 1
    a("| module | checks |")
    a("|---|---:|")
    for m, n in sorted(by_mod.items(), key=lambda kv: (-kv[1], kv[0])):
        a(f"| `{m}` | {n} |")
    a("")
    a("<details><summary>All checks in execution order</summary>")
    a("")
    a("| # | check | module | what it asserts |")
    a("|---:|---|---|---|")
    for c in ck:
        a(f"| {c['order']} | `{c['name']}` | `{c['module']}` | {c['description']} |")
    a("")
    a("</details>")
    a("")

    g = inv["gates"]
    a(f"## Readiness gates — {len(g)}")
    a("")
    a("| gate | priority | evaluator |")
    a("|---|---:|---|")
    for x in g:
        a(f"| `{x['gate']}` | P{x['priority']} | `{x['evaluator']}` |")
    a("")

    gr = inv["graph"]
    a("## Knowledge graph — types")
    a("")
    a(f"- **Node types:** {len(gr['node_types'])} — {', '.join('`%s`' % t for t in gr['node_types'])}")
    a(f"- **Edge types emitted:** {len(gr['edges_emitted'])} — "
      f"{', '.join('`%s`' % t for t in gr['edges_emitted'])}")
    a(f"- **Edge types the gates query:** {len(gr['edges_consumed_by_gates'])} — "
      f"{', '.join('`%s`' % t for t in gr['edges_consumed_by_gates'])}")
    a("")
    dead = gr["edges_consumed_but_never_emitted"]
    if dead:
        a(f"⚠️ **{len(dead)} edge type(s) are queried by a gate and emitted by nothing:** "
          f"{', '.join('`%s`' % t for t in dead)}. A gate reading a dead edge type returns a")
        a("verdict it did not compute — for a `passed` default that is absence rendered as")
        a("success; for a `blocked` default it is a blocker no evidence supports. Guarded by")
        a("`validate.py --check gate_edge_types_are_emitted`.")
    else:
        a("✅ Every edge type the gates query is emitted by some extractor.")
    a("")

    h = inv["hooks"]
    a(f"## Hooks — {len(h)}")
    a("")
    a("| kind | event | matcher | command |")
    a("|---|---|---|---|")
    for x in h:
        a(f"| {x['kind']} | `{x['event']}` | `{x['matcher']}` | `{x['command']}` |")
    a("")

    a(f"## Agents — {len(inv['agents'])}")
    a("")
    a("| agent | model | purpose |")
    a("|---|---|---|")
    for x in inv["agents"]:
        a(f"| [`{x['name']}`]({_rel(x['path'])}) | {x['model'] or '—'} | {x['description']} |")
    a("")

    a(f"## Commands — {len(inv['commands'])}")
    a("")
    a("| command | purpose |")
    a("|---|---|")
    for x in inv["commands"]:
        a(f"| [`{x['name']}`]({_rel(x['path'])}) | {x['description']} |")
    a("")

    a("## Hand-maintained registries")
    a("")
    a("These are the surfaces that CAN drift — every one is a human-edited list that some")
    a("check compares against reality. Sizes are recorded so a silent shrink is visible.")
    a("")
    a("| registry | entries |")
    a("|---|---:|")
    for x in inv["registries"]:
        a(f"| `{x['registry']}` | {x['size'] if x['size'] is not None else x['note']} |")
    a("")

    b = inv["bundles"]
    declared = sum(1 for x in b if x["apex_theorems"])
    a(f"## Publication roster — {len(b)} bundles, {declared} with declared apexes")
    a("")
    a("| bundle | tier | apexes | title |")
    a("|---|---:|---:|---|")
    for x in b:
        a(f"| `{x['code']}` | {x['tier'] if x['tier'] is not None else '—'} "
          f"| {x['apex_theorems'] or '—'} | {x['title']} |")
    a("")
    return "\n".join(L) + "\n"


def _rel(path: str) -> str:
    """Path relative to docs/architecture/, where the rendered file lives."""
    return "../../" + path


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Derive the QA/process surface inventory.")
    ap.add_argument("--write", action="store_true", help=f"write {OUT_PATH}")
    ap.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if the tracked doc differs from a fresh render")
    args = ap.parse_args(argv)

    inv = collect()
    if args.json:
        print(json.dumps(inv, indent=2))
        return 0
    text = render(inv)
    if args.check:
        current = OUT_PATH.read_text() if OUT_PATH.exists() else ""
        if current != text:
            print(f"STALE — {OUT_PATH} differs from a fresh render", file=sys.stderr)
            return 1
        print("fresh")
        return 0
    if args.write:
        OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
        OUT_PATH.write_text(text)
        print(f"wrote {OUT_PATH}")
        return 0
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
