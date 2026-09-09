#!/usr/bin/env python3
"""Create and check local Codex assignment snapshots (ADR-017).

No dispatch, notebook mutation, lease acquisition, build or completion authority.
The selected checkout supplies candidate state; Git identifies its primary checkout.
Use repo_state_probe for orientation and orchestrate for finding-driven planning.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

SCHEMA = "codex-continuity/v1"
ROLES = {"root", "team-lead", "leaf", "reviewer"}
DEFAULT_AUTHORITIES = (
    "AGENTS.md", "CLAUDE.md", "docs/WAVE_EXECUTION_PIPELINE.md",
    "docs/adrs/ADR-008-shared-lean-slot-control-plane.md",
    "docs/adrs/ADR-017-codex-continuity.md", "docs/dev-loops/CODEX_CONTINUITY.md",
)


class ContinuityError(ValueError):
    """Invalid or unavailable assignment input; never interpreted as fresh."""


def git(root: Path, *args: str) -> bytes:
    result = subprocess.run(["git", "-C", str(root), *args], capture_output=True, timeout=30)
    if result.returncode:
        raise ContinuityError(f"Git input unavailable: {' '.join(args)}")
    return result.stdout


def roots(repo: Path) -> tuple[Path, Path]:
    checkout = Path(os.fsdecode(git(repo, "rev-parse", "--show-toplevel")).strip()).resolve()
    common = Path(os.fsdecode(git(checkout, "rev-parse", "--git-common-dir")).strip())
    common = (checkout / common).resolve() if not common.is_absolute() else common.resolve()
    primary = common.parent
    if common.name != ".git" or not (primary / ".git").is_dir():
        raise ContinuityError("Only ordinary primary repositories and their linked worktrees are supported")
    if Path(os.fsdecode(git(primary, "rev-parse", "--show-toplevel")).strip()).resolve() != primary:
        raise ContinuityError("Cannot establish canonical primary checkout")
    return checkout, primary


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_state(path: Path) -> dict:
    if path.is_symlink():
        return {"kind": "symlink", "sha256": digest(os.fsencode(os.readlink(path)))}
    if not path.exists():
        return {"kind": "missing"}
    if not path.is_file():
        raise ContinuityError(f"Not a regular input file: {path}")
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(block)
    return {"kind": "file", "sha256": h.hexdigest()}


def source_state(checkout: Path) -> dict:
    """HEAD, index semantics and bytes of dirty/untracked nonignored files.

    Ignored files do not participate except when explicitly bound as references.
    Gitlinks are refused rather than falsely certifying nested repository state.
    """
    stage = git(checkout, "ls-files", "--stage", "-z")
    if any(row.startswith(b"160000 ") for row in stage.split(b"\0")):
        raise ContinuityError("Submodule state requires a separate assignment snapshot")
    changed = set()
    for args in (("diff", "--name-only", "-z"), ("diff", "--cached", "--name-only", "-z"),
                 ("ls-files", "--others", "--exclude-standard", "-z")):
        changed.update(os.fsdecode(p) for p in git(checkout, *args).split(b"\0") if p)
    return {
        "head": git(checkout, "rev-parse", "HEAD").decode().strip(),
        "index_sha256": digest(stage),
        "status_sha256": digest(git(checkout, "status", "--porcelain=v1", "-z", "--untracked-files=all")),
        "changed_files": {name: file_state(checkout / name) for name in sorted(changed)},
    }


def inside(path: Path, root: Path) -> bool:
    return path == root or root in path.parents


def reference(path: Path, primary: Path, *, external: bool = False) -> dict:
    resolved = path.resolve()
    if (not external and not inside(resolved, primary)) or ".git" in resolved.parts:
        raise ContinuityError(f"Reference must be within primary checkout: {path}")
    if not resolved.is_file():
        raise ContinuityError(f"Required reference missing: {resolved}")
    return {"path": str(resolved), "input_path": str(path.absolute()), **file_state(resolved)}


def assignment_scope(paths: list[str], checkout: Path) -> list[str]:
    if not paths:
        raise ContinuityError("At least one owned file is required")
    result = []
    for raw in paths:
        p = Path(raw)
        if p.is_absolute() or ".." in p.parts or ".git" in p.parts or not p.parts:
            raise ContinuityError(f"Owned path must be checkout-relative: {raw}")
        resolved = (checkout / p).resolve()
        if not inside(resolved, checkout) or resolved.is_dir() or (checkout / p).is_symlink():
            raise ContinuityError(f"Owned file escapes checkout or is a directory: {raw}")
        result.append(p.as_posix())
    return sorted(set(result))


def packet_output(path: Path, primary: Path, references: list[dict]) -> Path:
    path = path.absolute()
    if path.is_symlink() or path.exists():
        raise ContinuityError("Packet output already exists; choose a new revision path")
    resolved = path.resolve()
    if not inside(resolved, primary) or resolved == primary:
        raise ContinuityError("Packet must be local to the primary checkout")
    rel = resolved.relative_to(primary).as_posix()
    if ".git" in resolved.relative_to(primary).parts:
        raise ContinuityError("Packet cannot be written into Git metadata")
    if git(primary, "ls-files", "--", rel):
        raise ContinuityError("Packet output is tracked")
    probe = subprocess.run(["git", "-C", str(primary), "check-ignore", "-q", "--", rel], capture_output=True)
    if probe.returncode != 0:
        raise ContinuityError("Packet output must already be gitignored")
    if str(resolved) in {r["path"] for r in references}:
        raise ContinuityError("Packet cannot overwrite an authority input")
    return resolved


def make_packet(*, repo: Path, output: Path, task: str, parent: str, role: str,
                owner: str, writer: str, objective: str, reviewer: str, evidence: str,
                roadmap: Path, notebook: Path, owned: list[str], authorities: list[Path]) -> dict:
    for key, value in {"task": task, "parent": parent, "owner": owner, "writer": writer,
                       "objective": objective, "reviewer": reviewer, "evidence": evidence}.items():
        if not isinstance(value, str) or not value.strip():
            raise ContinuityError(f"Missing {key}")
    if role not in ROLES:
        raise ContinuityError("Unknown role")
    if role in {"leaf", "reviewer"} and writer == owner:
        raise ContinuityError("Leaf/reviewer cannot own the shared notebook writer role")
    checkout, primary = roots(repo)
    refs = {"roadmap": reference(roadmap, primary), "notebook": reference(notebook, primary)}
    authority_paths = [primary / p for p in DEFAULT_AUTHORITIES[:2]]
    authority_paths.extend(primary / p for p in DEFAULT_AUTHORITIES[2:] if (primary / p).is_file())
    authority_paths.extend(authorities)
    refs["authorities"] = [reference(p, primary, external=True) for p in dict.fromkeys(authority_paths)]
    all_refs = [refs["roadmap"], refs["notebook"], *refs["authorities"]]
    dest = packet_output(output, primary, all_refs)
    scope = assignment_scope(owned, checkout)
    if role in {"leaf", "reviewer"} and any(str((checkout / p).resolve()) == refs["notebook"]["path"] for p in scope):
        raise ContinuityError("Leaf/reviewer cannot own the shared notebook file")
    if any((checkout / p).resolve() == dest for p in scope):
        raise ContinuityError("Packet output cannot be an assigned source file")
    packet = {
        "schema": SCHEMA, "task": task, "parent": parent, "role": role,
        "owner": owner, "notebook_writer": writer, "objective": objective,
        "acceptance_reviewer": reviewer, "required_evidence": evidence,
        "checkout": str(checkout), "primary": str(primary),
        "owned_files": scope, "owned_state": {p: file_state(checkout / p) for p in scope}, "references": refs,
        "source": source_state(checkout),
        "authority": "Snapshot only; no lease, build, dispatch, review or completion authorization.",
    }
    dest.parent.mkdir(parents=True, exist_ok=True)
    # Link creation is atomic and exclusive: never replace an existing assignment.
    fd, tmp = tempfile.mkstemp(prefix=".continuity-", dir=dest.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            json.dump(packet, handle, indent=2, ensure_ascii=True)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.link(tmp, dest)
    finally:
        Path(tmp).unlink(missing_ok=True)
    return packet


def check_packet(path: Path) -> dict:
    """Read-only comparison. Malformed and missing inputs never pass."""
    try:
        packet = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(packet, dict) or packet.get("schema") != SCHEMA or packet.get("role") not in ROLES:
            raise ContinuityError("Unsupported packet schema/role")
        for name in ("task", "parent", "owner", "notebook_writer", "objective", "acceptance_reviewer", "required_evidence"):
            if not isinstance(packet.get(name), str) or not packet[name].strip():
                raise ContinuityError(f"Missing packet field: {name}")
        if packet["role"] in {"leaf", "reviewer"} and packet["owner"] == packet["notebook_writer"]:
            raise ContinuityError("Invalid notebook ownership")
        checkout, primary = roots(Path(packet["checkout"]))
        if str(primary) != packet["primary"] or str(checkout) != packet["checkout"]:
            raise ContinuityError("Repository identity changed")
        if assignment_scope(packet["owned_files"], checkout) != packet["owned_files"]:
            raise ContinuityError("Invalid owned scope")
        refs = packet["references"]
        if not isinstance(refs["authorities"], list) or not refs["authorities"]:
            raise ContinuityError("Missing authority references")
        changed = []
        for label, old in [("roadmap", refs["roadmap"]), ("notebook", refs["notebook"]),
                           *[(f"authority[{i}]", r) for i, r in enumerate(refs["authorities"])]]:
            if reference(Path(old["input_path"]), primary, external=label.startswith("authority[")) != old:
                changed.append(label)
        if {p: file_state(checkout / p) for p in packet["owned_files"]} != packet["owned_state"]:
            changed.append("owned-files")
        if source_state(checkout) != packet["source"]:
            changed.append("source")
        return {"fresh": not changed, "changed": changed, "task": packet["task"],
                "meaning": "Input snapshot matches; no execution or completion authority." if not changed else
                           "Reconciliation required; lead must inspect current inputs and explicitly issue a new revision."}
    except (OSError, ValueError, KeyError, TypeError, subprocess.TimeoutExpired) as exc:
        return {"fresh": False, "changed": ["unavailable-or-invalid"], "error": str(exc)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("packet")
    create.add_argument("--repo", type=Path, default=Path.cwd())
    create.add_argument("--output", type=Path, required=True)
    for name in ("task", "parent", "role", "owner", "writer", "objective", "reviewer", "evidence"):
        create.add_argument(f"--{name}", required=True)
    create.add_argument("--roadmap", type=Path, required=True)
    create.add_argument("--notebook", type=Path, required=True)
    create.add_argument("--owned", action="append", required=True)
    create.add_argument("--authority", type=Path, action="append")
    check = commands.add_parser("check")
    check.add_argument("packet", type=Path)
    args = parser.parse_args()
    if args.command == "check":
        result = check_packet(args.packet)
        print(json.dumps(result, indent=2))
        return 0 if result["fresh"] else 1
    try:
        values = vars(args).copy()
        del values["command"]
        _, primary = roots(args.repo)
        values["authorities"] = values.pop("authority") or []
        make_packet(**values)
        print(json.dumps({"packet": str(args.output.resolve()), "created": True,
                          "meaning": "Assignment snapshot only; no execution authorization."}))
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as exc:
        print(json.dumps({"created": False, "error": str(exc)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
