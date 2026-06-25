#!/usr/bin/env python3
"""
src/core/aristotle_submit.py — SafeAristotleRunner (ADR-006).

The SAFE Aristotle workflow that replaces the archived full-project process
(scripts/archive/submit_to_aristotle.py, disabled). See
docs/adrs/ADR-006-aristotle-submission-rewrite.md.

Design principles (ADR-006):

  1. PARTIAL submission. We stage a MINIMAL Lean project = only the transitive
     SKEFTHawking import-closure of the target sorry file(s), never the full
     ~1,172-file / 17 MB project. (L2 worked example: 138 modules ≈ 8 %.)

  2. ASYNC / non-blocking. `aristotle submit` defaults to NOT waiting, so we
     submit, capture the project id, persist a manifest, and RETURN — we never
     `--wait`. Retrieval is a SEPARATE step (`aristotle result <id>`). This is
     the property that makes future autonomy safe: a /goal loop fires a
     submission and keeps doing other work; it never blocks on Aristotle's
     ~1-day turnaround and never falls into a "stop-hook=go -> nothing to do
     (waiting on Aristotle) -> stop-hook=go" spin.

  3. VERIFY-THEN-GRAFT re-incorporation. Retrieve -> review diff -> graft ONLY
     the target theorem bodies -> run the verification gauntlet
     (lake build zero-sorry + kernel-purity/axiom audit + validate.py + tests).
     We NEVER whole-file-overwrite the tree (that was the old --integrate
     foot-gun). A returned proof that fails any gate is rejected, not grafted.

  4. PRIMITIVE sorry detection. "Does decl X still have a sorry?" is answered by
     the Lean kernel primitive — `sorryAx` in the declaration's axiom closure
     (lean_deps.json `axiom_deps_core`) and `declaration uses 'sorry'` build
     warnings — never by text-matching source lines.

This module deliberately keeps SUBMISSION gated behind an explicit
`authorized=True` argument (Stage 4: "user gets first & last call"). The gate
is a single chokepoint so the policy can later be loosened to a pre-decision
once the concept is proven (efficiency + re-integration safety + goal-loop
integration), without re-plumbing the workflow.
"""

from __future__ import annotations

import difflib
import json
import os
import re
import shutil
import subprocess
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

# src/core/aristotle_submit.py -> parent.parent.parent = project root
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
LEAN_DIR = PROJECT_ROOT / "lean"
LEAN_SRC = LEAN_DIR / "SKEFTHawking"
LEAN_DEPS = LEAN_DIR / "lean_deps.json"
RESULTS_DIR = PROJECT_ROOT / "docs" / "aristotle_results"
STAGING_DIR = RESULTS_DIR / "staging"
MANIFESTS_DIR = RESULTS_DIR / "manifests"

# Kernel-trust baseline (ADR-002), kept in sync with scripts/atlas_view.py.
KERNEL_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
_SORRY_TOKENS = ("sorryAx", "sorry")
_NATIVE_DECIDE_RE = re.compile(r"\._native\.native_decide")
_IMPORT_RE = re.compile(r"^\s*import\s+(SKEFTHawking(?:\.[A-Za-z0-9_']+)+)")


# --------------------------------------------------------------------------- #
# Module <-> file resolution
# --------------------------------------------------------------------------- #
def _module_to_path(module: str) -> Optional[Path]:
    """`SKEFTHawking.Foo.Bar` -> lean/SKEFTHawking/Foo/Bar.lean (if it exists)."""
    rel = Path(*module.split(".")).with_suffix(".lean")
    p = LEAN_DIR / rel
    return p if p.exists() else None


def _path_to_module(path: Path) -> str:
    """lean/SKEFTHawking/Foo/Bar.lean -> SKEFTHawking.Foo.Bar."""
    rel = path.resolve().relative_to(LEAN_DIR.resolve()).with_suffix("")
    return ".".join(rel.parts)


def _normalize_target(target: str) -> str:
    """Accept a module name (``SKEFTHawking.Foo``), a path
    (``SKEFTHawking/Foo.lean``, absolute or repo-relative), a bare file name
    (``Foo.lean``), or a bare module leaf (``Foo``); return the module name."""
    # Dotted module name (no .lean suffix) -> use as-is.
    if target.startswith("SKEFTHawking") and not target.endswith(".lean") and "/" not in target:
        return target

    # Otherwise resolve to a file, then derive the module name from its path.
    fname = target if target.endswith(".lean") else target + ".lean"
    p = Path(fname)
    cand: Optional[Path] = None
    if p.is_absolute() and p.exists():
        cand = p
    elif (LEAN_DIR / p).exists():
        cand = LEAN_DIR / p
    elif (LEAN_SRC / p).exists():
        cand = LEAN_SRC / p
    else:
        matches = list(LEAN_SRC.rglob(Path(fname).name))
        if len(matches) == 1:
            cand = matches[0]
        elif not matches:
            raise FileNotFoundError(f"No Lean file found for target {target!r}")
        else:
            raise ValueError(f"Ambiguous target {target!r}: {[str(m) for m in matches]}")
    return _path_to_module(cand)


# --------------------------------------------------------------------------- #
# Transitive import closure
# --------------------------------------------------------------------------- #
def _direct_imports(module: str) -> list[str]:
    p = _module_to_path(module)
    if p is None:
        return []
    out = []
    for line in p.read_text().splitlines():
        m = _IMPORT_RE.match(line)
        if m:
            out.append(m.group(1))
    return out


def transitive_import_closure(targets: list[str]) -> set[str]:
    """All SKEFTHawking modules reachable from `targets` via `import` edges,
    including the targets themselves. Mathlib/Physlib/repl imports are not
    SKEFTHawking modules and are intentionally excluded — Aristotle resolves
    them from the staged lake-manifest."""
    seen: set[str] = set()
    stack = [_normalize_target(t) for t in targets]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        for dep in _direct_imports(m):
            if dep not in seen:
                stack.append(dep)
    return seen


# --------------------------------------------------------------------------- #
# Sorry detection — Lean primitive (axiom closure), not text scanning
# --------------------------------------------------------------------------- #
def _rec_has_sorry(rec: dict) -> bool:
    return any(any(tok in a for tok in _SORRY_TOKENS) for a in rec.get("axiom_deps_core", []))


def _rec_uses_native_decide(rec: dict) -> bool:
    return any(_NATIVE_DECIDE_RE.search(a) for a in rec.get("axiom_deps_project", []))


def _rec_project_axioms(rec: dict) -> list[str]:
    return [a for a in rec.get("axiom_deps_project", []) if not _NATIVE_DECIDE_RE.search(a)]


def _rec_is_kernel_pure(rec: dict) -> bool:
    core = set(rec.get("axiom_deps_core", []))
    return (not _rec_project_axioms(rec) and not _rec_uses_native_decide(rec)
            and core.issubset(KERNEL_AXIOMS) and not _rec_has_sorry(rec))


def _load_lean_deps() -> list[dict]:
    if not LEAN_DEPS.exists():
        raise FileNotFoundError(
            f"{LEAN_DEPS} not found — run `lake build SKEFTHawking.ExtractDeps` first."
        )
    return json.loads(LEAN_DEPS.read_text())


def lean_deps_stale_for(modules: set[str]) -> list[str]:
    """Module(s) whose source `.lean` is NEWER than lean_deps.json — i.e. the
    cached axiom-closure view may not reflect their current sorries. Returned so
    callers never silently trust a stale planning view (the WIP case)."""
    if not LEAN_DEPS.exists():
        return sorted(modules)
    deps_mtime = LEAN_DEPS.stat().st_mtime
    stale = []
    for m in modules:
        p = _module_to_path(m)
        if p and p.stat().st_mtime > deps_mtime:
            stale.append(m)
    return sorted(stale)


def sorry_decls_in_modules(modules: set[str]) -> dict[str, list[str]]:
    """{module: [decl names whose kernel axiom closure contains sorry]}.

    Primitive-based (sorryAx in axiom_deps_core), reflecting the last
    ExtractDeps build. Pair with `lean_deps_stale_for` — for modules flagged
    stale this view may under-report; the verification gauntlet re-checks
    against a fresh build. This is the (fast, cached) planning view.
    """
    out: dict[str, list[str]] = {}
    for rec in _load_lean_deps():
        if rec.get("module") in modules and _rec_has_sorry(rec):
            out.setdefault(rec["module"], []).append(rec.get("name", "<?>"))
    return out


# --------------------------------------------------------------------------- #
# Staging a minimal project
# --------------------------------------------------------------------------- #
def _staged_lakefile(src_lakefile: str) -> str:
    """Our lakefile with the `[[lean_exe]]` stanzas stripped (their roots —
    ExtractDeps / AxiomAudit — are metaprograms outside any proof closure, so
    keeping them would reference missing roots). Requires + lean_lib are kept;
    Mathlib/Physlib/repl resolve from the copied lake-manifest."""
    out, skip = [], False
    for line in src_lakefile.splitlines():
        if line.strip().startswith("[[lean_exe]]"):
            skip = True
            continue
        if skip and line.strip().startswith("[["):
            skip = False
        if not skip:
            out.append(line)
    return "\n".join(out).rstrip() + "\n"


@dataclass
class StagedProject:
    root: Path
    targets: list[str]
    closure: list[str]
    closure_hash: str


def _closure_hash(modules: set[str]) -> str:
    """Content hash of the closure (sorted module names + each file's bytes) —
    the dedup key, so an identical re-stage is detectable."""
    import hashlib
    h = hashlib.sha256()
    for m in sorted(modules):
        h.update(m.encode())
        p = _module_to_path(m)
        if p:
            h.update(p.read_bytes())
    return h.hexdigest()[:16]


def stage_minimal_project(targets: list[str], dest: Optional[Path] = None) -> StagedProject:
    """Assemble a minimal, buildable Lean project containing ONLY the targets'
    transitive SKEFTHawking import-closure. Returns a StagedProject."""
    norm_targets = [_normalize_target(t) for t in targets]
    closure = transitive_import_closure(norm_targets)

    if dest is None:
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        dest = STAGING_DIR / f"stage_{ts}"
    dest = Path(dest)
    if dest.exists():
        shutil.rmtree(dest)
    (dest / "SKEFTHawking").mkdir(parents=True)

    # toolchain + manifest verbatim (Mathlib pin resolves from the manifest)
    shutil.copy2(LEAN_DIR / "lean-toolchain", dest / "lean-toolchain")
    manifest = LEAN_DIR / "lake-manifest.json"
    if manifest.exists():
        shutil.copy2(manifest, dest / "lake-manifest.json")
    (dest / "lakefile.toml").write_text(_staged_lakefile((LEAN_DIR / "lakefile.toml").read_text()))

    # only the closure files (preserving nested module paths)
    for m in closure:
        src = _module_to_path(m)
        if src is None:
            continue
        rel = src.resolve().relative_to(LEAN_SRC.resolve())
        out = dest / "SKEFTHawking" / rel
        out.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, out)

    return StagedProject(root=dest, targets=norm_targets, closure=sorted(closure),
                         closure_hash=_closure_hash(closure))


# --------------------------------------------------------------------------- #
# Submission manifest (v2) + dedup
# --------------------------------------------------------------------------- #
@dataclass
class SubmissionManifest:
    job_id: str
    timestamp: str
    targets: list[str]
    closure_modules: int
    closure_hash: str
    prompt: str
    status: str = "SUBMITTED"            # SUBMITTED | RETRIEVED | GRAFTED | REJECTED
    submission_type: str = "safe-partial"

    def path(self) -> Path:
        return MANIFESTS_DIR / f"{self.job_id}.json"

    def save(self) -> Path:
        MANIFESTS_DIR.mkdir(parents=True, exist_ok=True)
        self.path().write_text(json.dumps(self.__dict__, indent=2))
        return self.path()


def find_duplicate_submission(closure_hash: str) -> Optional[dict]:
    """Return a prior manifest (read-on-start dedup) whose closure_hash matches
    and is still open (SUBMITTED/RETRIEVED) — so we never resubmit identical
    work. Fixes the old write-only-manifest gap."""
    if not MANIFESTS_DIR.exists():
        return None
    for f in MANIFESTS_DIR.glob("*.json"):
        try:
            man = json.loads(f.read_text())
        except (json.JSONDecodeError, OSError):
            continue
        if man.get("closure_hash") == closure_hash and man.get("status") in ("SUBMITTED", "RETRIEVED"):
            return man
    return None


# --------------------------------------------------------------------------- #
# Async submission (gated) + retrieval
# --------------------------------------------------------------------------- #
def _api_key() -> str:
    key = os.environ.get("ARISTOTLE_API_KEY")
    if not key:
        env = PROJECT_ROOT / ".env"
        if env.exists():
            for line in env.read_text().splitlines():
                if line.startswith("ARISTOTLE_API_KEY="):
                    key = line.split("=", 1)[1].strip()
                    break
    if not key:
        raise ValueError("ARISTOTLE_API_KEY not found in env or .env")
    return key


_PROJECT_ID_RE = re.compile(r"\b([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})\b")


def submit_async(staged: StagedProject, prompt: str, *, authorized: bool = False,
                 force: bool = False) -> SubmissionManifest:
    """Submit the staged minimal project to Aristotle WITHOUT waiting, persist a
    manifest, and return immediately.

    `authorized=True` is REQUIRED — this is the single human-in-the-loop
    chokepoint (Stage 4). The full-project foot-gun is gone, but a real run
    still costs budget + ~1 day, so submission is never implicit. When the
    policy is later loosened to a pre-decision, only this gate changes.
    """
    if not authorized:
        raise PermissionError(
            "Aristotle submission requires authorized=True (ADR-006 Stage-4 gate). "
            "Stage + review the closure first; submit only on explicit go."
        )
    dup = find_duplicate_submission(staged.closure_hash)
    if dup and not force:
        raise RuntimeError(
            f"Identical closure already submitted as job {dup['job_id']} "
            f"(status {dup['status']}). Use force=True to resubmit."
        )

    cmd = ["aristotle", "submit", prompt, "--project-dir", str(staged.root),
           "--api-key", _api_key()]   # NOTE: no --wait -> returns immediately (async)
    proc = subprocess.run(cmd, capture_output=True, text=True, cwd=str(PROJECT_ROOT))
    out = proc.stdout + proc.stderr
    if proc.returncode != 0:
        raise RuntimeError(f"aristotle submit failed (exit {proc.returncode}):\n{out}")

    m = _PROJECT_ID_RE.search(out)
    job_id = m.group(1) if m else f"unparsed_{datetime.now():%Y%m%d_%H%M%S}"
    man = SubmissionManifest(
        job_id=job_id, timestamp=datetime.now().isoformat(),
        targets=staged.targets, closure_modules=len(staged.closure),
        closure_hash=staged.closure_hash, prompt=prompt,
    )
    man.save()
    return man


def retrieve(job_id: str, dest: Optional[Path] = None) -> Path:
    """Download a completed run's tar.gz and extract it. Does NOT integrate —
    review + graft are separate, deliberate steps."""
    if dest is None:
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        dest = RESULTS_DIR / f"run_{ts}_{job_id[:8]}"
    dest = Path(dest)
    dest.mkdir(parents=True, exist_ok=True)
    tar = dest / "result.tar.gz"
    # aristotlelib v2.1.0+ (API v3): `download` replaces the old `result` subcommand.
    subprocess.run(["aristotle", "download", job_id, "--destination", str(tar),
                    "--api-key", _api_key()], check=True, cwd=str(PROJECT_ROOT))
    extracted = dest / "extracted"
    extracted.mkdir(exist_ok=True)
    subprocess.run(["tar", "xzf", str(tar), "-C", str(extracted)], check=True)
    return extracted


# --------------------------------------------------------------------------- #
# Graft — apply ONLY the target file(s), reviewably, with auto-revert
# --------------------------------------------------------------------------- #
@dataclass
class GraftPlan:
    target_files: list[Path]            # our-tree paths that would change
    other_files_changed: list[str]      # closure modules Aristotle edited beyond the targets
    diffs: dict[str, str]               # target module -> unified diff (ours -> aristotle)
    retrieved_root: Path

    @property
    def safe(self) -> bool:
        """Safe to auto-apply only if Aristotle confined its edits to the named
        targets (the old --integrate foot-gun was that it copied ANY differing
        file). If other closure files changed, a human reviews."""
        return not self.other_files_changed and bool(self.diffs)


def _retrieved_module_file(retrieved_root: Path, module: str) -> Optional[Path]:
    rel = Path("SKEFTHawking", *module.split(".")[1:]).with_suffix(".lean")
    for cand in retrieved_root.rglob(rel.name):
        if cand.as_posix().endswith(rel.as_posix()):
            return cand
    return None


def plan_graft(retrieved_root: Path, targets: list[str]) -> GraftPlan:
    """Diff our target file(s) against Aristotle's returned versions, and detect
    whether Aristotle modified any OTHER closure file (which would make a blind
    apply unsafe). Surfaces the diffs for review — never applies anything."""
    norm = [_normalize_target(t) for t in targets]
    closure = transitive_import_closure(norm)
    target_set = set(norm)

    diffs: dict[str, str] = {}
    target_files: list[Path] = []
    for m in norm:
        ours, theirs = _module_to_path(m), _retrieved_module_file(retrieved_root, m)
        if ours is None or theirs is None:
            continue
        a = ours.read_text().splitlines(keepends=True)
        b = theirs.read_text().splitlines(keepends=True)
        if a != b:
            diffs[m] = "".join(difflib.unified_diff(a, b, fromfile=f"ours/{m}", tofile=f"aristotle/{m}"))
            target_files.append(ours)

    other_changed = []
    for m in closure - target_set:
        ours, theirs = _module_to_path(m), _retrieved_module_file(retrieved_root, m)
        if ours and theirs and ours.read_text() != theirs.read_text():
            other_changed.append(m)

    return GraftPlan(target_files=target_files, other_files_changed=sorted(other_changed),
                     diffs=diffs, retrieved_root=retrieved_root)


def apply_graft(plan: GraftPlan) -> dict[Path, str]:
    """Write Aristotle's target file(s) into our tree; return {path: original}
    backups for revert. Refuses if Aristotle touched non-target files."""
    if plan.other_files_changed:
        raise RuntimeError(
            f"Refusing to graft: Aristotle modified non-target files "
            f"{plan.other_files_changed}. Review manually."
        )
    backups: dict[Path, str] = {}
    for ours in plan.target_files:
        theirs = _retrieved_module_file(plan.retrieved_root, _path_to_module(ours))
        backups[ours] = ours.read_text()
        shutil.copy2(theirs, ours)
    return backups


def revert_graft(backups: dict[Path, str]) -> None:
    for path, original in backups.items():
        path.write_text(original)


# --------------------------------------------------------------------------- #
# Verification gauntlet (run BEFORE keeping any grafted proof)
# --------------------------------------------------------------------------- #
@dataclass
class GauntletResult:
    build_ok: bool = False
    zero_sorry: bool = False
    kernel_pure: bool = False
    validate_ok: bool = False
    tests_ok: bool = False
    details: list[str] = field(default_factory=list)

    @property
    def passed(self) -> bool:
        return all((self.build_ok, self.zero_sorry, self.kernel_pure,
                    self.validate_ok, self.tests_ok))


def run_verification_gauntlet(targets: list[str], *, run_tests: bool = True) -> GauntletResult:
    """Run the full gate a grafted proof must pass before we keep it:
    lake build (zero new sorry) -> fresh ExtractDeps -> kernel-purity/axiom
    audit of the target decls -> validate.py -> tests. Reuses the existing
    validate checks rather than re-implementing them.
    """
    res = GauntletResult()
    norm = [_normalize_target(t) for t in targets]

    # 1. library build + sorry-warning scan (the kernel primitive)
    build = subprocess.run(["lake", "build", "SKEFTHawking"], capture_output=True,
                           text=True, cwd=str(LEAN_DIR))
    res.build_ok = build.returncode == 0
    sorry_warns = [ln for ln in (build.stdout + build.stderr).splitlines()
                   if "declaration uses 'sorry'" in ln]
    res.zero_sorry = res.build_ok and not sorry_warns
    res.details.append(f"build exit={build.returncode}; sorry-warnings={len(sorry_warns)}")
    if not res.build_ok:
        res.details.append((build.stdout + build.stderr).strip()[-1500:])
        return res

    # 2. fresh ExtractDeps so the axiom closure reflects the grafted proof
    subprocess.run(["lake", "build", "SKEFTHawking.ExtractDeps"], capture_output=True,
                   text=True, cwd=str(LEAN_DIR))

    # 3. kernel-purity / axiom audit of the target decls (no sorry, no
    #    native_decide regression, no un-signed-off project axiom)
    target_recs = [r for r in _load_lean_deps() if r.get("module") in set(norm)]
    impure = [r["name"] for r in target_recs if not _rec_is_kernel_pure(r)]
    res.kernel_pure = not impure
    res.details.append(f"target decls checked={len(target_recs)}; impure={impure[:10]}")

    # 4. validate.py kernel-trust gates (authoritative, project-wide)
    val = subprocess.run(["uv", "run", "python", "scripts/validate.py",
                          "--check", "axiom_closure_allowlist",
                          "--check", "native_decide_regression"],
                         capture_output=True, text=True, cwd=str(PROJECT_ROOT))
    res.validate_ok = val.returncode == 0
    res.details.append(f"validate(axiom+native_decide) exit={val.returncode}")

    # 5. tests
    if run_tests:
        tst = subprocess.run(["uv", "run", "python", "-m", "pytest",
                              "tests/test_lean_integrity.py", "-q"],
                             capture_output=True, text=True, cwd=str(PROJECT_ROOT))
        res.tests_ok = tst.returncode == 0
        res.details.append(f"tests exit={tst.returncode}")
    else:
        res.tests_ok = True
    return res


# --------------------------------------------------------------------------- #
# Orchestrator — verify-then-graft (autonomy-ready, never worsens the tree)
# --------------------------------------------------------------------------- #
@dataclass
class ReintegrationResult:
    grafted: bool
    plan: GraftPlan
    gauntlet: Optional[GauntletResult] = None
    reverted: bool = False
    note: str = ""


def graft_and_verify(retrieved_root: Path, targets: list[str], *,
                     run_tests: bool = True) -> ReintegrationResult:
    """Safe re-incorporation: plan -> apply (target files ONLY) -> gauntlet ->
    KEEP on pass, AUTO-REVERT on fail. Never leaves the tree worse than found —
    the property that makes this safe to run unattended in a /goal loop.
    Caller registers attribution (ADR-006 D4) only when grafted is True.
    """
    plan = plan_graft(retrieved_root, targets)
    if not plan.diffs:
        return ReintegrationResult(False, plan, note="No changes in target files to graft.")
    if plan.other_files_changed:
        return ReintegrationResult(
            False, plan,
            note=f"Aristotle modified non-target files {plan.other_files_changed}; "
                 f"manual review required (not auto-grafted).")
    backups = apply_graft(plan)
    gauntlet = run_verification_gauntlet(targets, run_tests=run_tests)
    if gauntlet.passed:
        return ReintegrationResult(True, plan, gauntlet, note="Gauntlet passed; graft kept.")
    revert_graft(backups)
    return ReintegrationResult(False, plan, gauntlet, reverted=True,
                               note="Gauntlet FAILED; graft reverted — tree unchanged.")
