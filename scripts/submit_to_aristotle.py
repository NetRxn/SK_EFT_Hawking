#!/usr/bin/env python3
"""
Submit SK-EFT Hawking Paper Lean sorries to Aristotle.

This script submits sorry gaps to Aristotle, waits for results, extracts
the returned tar.gz, diffs against our source, and optionally integrates
the filled proofs back into the codebase.

IMPORTANT: Every submission sends the ENTIRE Lean project to Aristotle.
The prompt only guides where Aristotle focuses its effort. Submitting
multiple jobs in parallel = duplicate full-project uploads with overlapping
work. Prefer ONE well-crafted submission with prioritized hints.

Usage:
    # From project root:

    # Submit all unfilled sorry gaps (single job, recommended):
    python scripts/submit_to_aristotle.py --submit

    # Dry run (show what would be submitted without submitting):
    python scripts/submit_to_aristotle.py --dry-run

    # Retrieve a previous run by project ID:
    python scripts/submit_to_aristotle.py --retrieve 082e6776 --integrate

    # Resume from an OUT_OF_BUDGET run:
    python scripts/submit_to_aristotle.py --resume 082e6776

    # DEPRECATED: --priority and --target still work but are not recommended.
    # Use the aristotle CLI directly for targeted prompts:
    #   cd lean && source ../.env && aristotle submit "prompt" --project-dir .

Requires:
    - aristotlelib installed: pip install aristotlelib
    - ARISTOTLE_API_KEY in .env or environment
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from src.core.aristotle_interface import SORRY_GAPS, AristotleRunner

PROJECT_ROOT = Path(__file__).parent.parent
LEAN_DIR = PROJECT_ROOT / "lean"
RESULTS_DIR = PROJECT_ROOT / "docs" / "aristotle_results"
MANIFESTS_DIR = RESULTS_DIR / "manifests"


def load_api_key():
    """Load Aristotle API key from .env or environment."""
    key = os.environ.get("ARISTOTLE_API_KEY")
    if not key:
        env_file = PROJECT_ROOT / ".env"
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith("ARISTOTLE_API_KEY="):
                    key = line.split("=", 1)[1].strip()
                    os.environ["ARISTOTLE_API_KEY"] = key
                    break
    if not key:
        print("ERROR: ARISTOTLE_API_KEY not found. Set in .env or environment.")
        sys.exit(1)
    return key


def check_running_jobs(api_key: str) -> list[dict]:
    """Check for already-running Aristotle jobs. Returns list of running jobs."""
    try:
        result = subprocess.run(
            ["uv", "run", "aristotle", "list", "--limit", "5"],
            capture_output=True, text=True, timeout=30,
            env={**os.environ, "ARISTOTLE_API_KEY": api_key},
        )
        running = []
        for line in result.stdout.splitlines():
            if "IN_PROGRESS" in line:
                parts = line.split()
                if parts:
                    running.append({"id": parts[0], "line": line.strip()})
        return running
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return []


def find_sorry_files() -> dict[str, list[str]]:
    """Scan Lean files for sorry gaps. Returns {filename: [sorry_line_contexts]}."""
    sorry_files = {}
    lean_dir = LEAN_DIR / "SKEFTHawking"
    for f in sorted(lean_dir.glob("*.lean")):
        lines = f.read_text().splitlines()
        sorrys = []
        for i, line in enumerate(lines):
            stripped = line.strip()
            if stripped == "sorry" or stripped == "by sorry" or stripped.endswith(":= by sorry"):
                # Find the theorem name above this sorry
                for j in range(i, max(i - 10, -1), -1):
                    if "theorem " in lines[j] or "private theorem" in lines[j] or "lemma " in lines[j]:
                        sorrys.append(lines[j].strip())
                        break
                else:
                    sorrys.append(f"line {i+1}")
        if sorrys:
            sorry_files[f.name] = sorrys
    return sorry_files


def build_prompt(sorry_files: dict[str, list[str]]) -> str:
    """Build a comprehensive prompt listing all sorry gaps with hints."""
    total = sum(len(v) for v in sorry_files.values())
    lines = [f"Fill in all the sorry gaps in this project. There are {total} sorry gaps across {len(sorry_files)} files.\n"]

    for filename, sorrys in sorted(sorry_files.items(), key=lambda x: -len(x[1])):
        lines.append(f"\n{filename} ({len(sorrys)} sorry):")
        for s in sorrys:
            lines.append(f"  - {s}")
        lines.append("  See PROVIDED SOLUTION hints in each theorem's docstring.")

    lines.append("\nFocus on files with the most sorry gaps first. Use helper lemmas already proved in each file.")
    return "\n".join(lines)


def save_manifest(job_id: str, prompt: str, sorry_files: dict[str, list[str]]):
    """Save a manifest recording what was submitted, for dedup on next run."""
    MANIFESTS_DIR.mkdir(parents=True, exist_ok=True)
    manifest = {
        "job_id": job_id,
        "timestamp": datetime.now().isoformat(),
        "prompt_preview": prompt[:500],
        "files_with_sorry": {k: len(v) for k, v in sorry_files.items()},
        "total_sorry": sum(len(v) for v in sorry_files.values()),
    }
    path = MANIFESTS_DIR / f"{job_id[:8]}.json"
    with open(path, "w") as f:
        json.dump(manifest, f, indent=2)
    print(f"Manifest saved: {path}")


def retrieve_result(project_id, dest_dir, api_key):
    """Retrieve Aristotle result into dest_dir. Returns path to extracted lean files."""
    dest_dir.mkdir(parents=True, exist_ok=True)
    tar_path = dest_dir / "result.tar.gz"

    subprocess.run(
        ["uv", "run", "aristotle", "result", project_id, "--destination", str(tar_path)],
        env={**os.environ, "ARISTOTLE_API_KEY": api_key},
        check=True,
    )

    # Extract
    lean_out = dest_dir / "lean_aristotle"
    lean_out.mkdir(exist_ok=True)
    subprocess.run(["tar", "xzf", str(tar_path), "-C", str(lean_out)], check=True)
    return lean_out


def generate_diff(patched_dir, lean_dir, diff_path):
    """Generate unified diff between Aristotle output and our source."""
    result = subprocess.run(
        ["diff", "-ru", str(lean_dir / "SKEFTHawking"), str(patched_dir / "SKEFTHawking")],
        capture_output=True, text=True,
    )
    diff_text = result.stdout
    if diff_text:
        diff_path.write_text(diff_text)
    return diff_text


def count_sorries(patched_dir):
    """Count sorry occurrences in patched Lean files."""
    counts = {}
    for f in sorted(patched_dir.rglob("*.lean")):
        text = f.read_text()
        # Count sorry as tactic (not in comments)
        count = sum(1 for line in text.splitlines() if line.strip() in ("sorry", "by sorry") or line.strip().endswith(":= by sorry"))
        if count:
            counts[str(f.relative_to(patched_dir))] = count
    return counts


def print_summary(patched_dir):
    """Print summary of Aristotle result."""
    for summary in sorted(patched_dir.rglob("ARISTOTLE_SUMMARY*")):
        print(f"\n{'=' * 60}\nARISTOTLE SUMMARY\n{'=' * 60}")
        print(summary.read_text()[:3000])


def integrate_proofs(patched_dir: Path, lean_dir: Path) -> list[str]:
    """Copy patched Lean files into the project, returning list of updated files."""
    updated = []
    for patched_file in sorted(patched_dir.rglob("*.lean")):
        rel_path = patched_file.relative_to(patched_dir)
        target = lean_dir / rel_path
        if not target.exists():
            continue
        if patched_file.read_text() != target.read_text():
            shutil.copy2(patched_file, target)
            updated.append(str(rel_path))
    return updated


def main():
    parser = argparse.ArgumentParser(
        description="Submit Lean sorry gaps to Aristotle for automated proof filling"
    )
    parser.add_argument(
        "--submit",
        action="store_true",
        help="Submit all unfilled sorry gaps as a single job (recommended)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would be submitted without submitting",
    )
    parser.add_argument(
        "--retrieve",
        type=str,
        default=None,
        help="Retrieve results for a previous project ID",
    )
    parser.add_argument(
        "--integrate",
        action="store_true",
        help="Auto-integrate patched files into lean/ (review diff first!)",
    )
    parser.add_argument(
        "--resume",
        type=str,
        default=None,
        help="Resume from an OUT_OF_BUDGET run",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Submit even if jobs are already in progress",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=3600,
        help="Timeout in seconds. Default: 3600 (1 hour). Job continues server-side.",
    )
    parser.add_argument(
        "--priority",
        type=int,
        default=None,
        help="Submit sorry gaps up to this priority level (1=highest). "
             "Uses SORRY_GAPS registry in aristotle_interface.py.",
    )
    parser.add_argument("--target", type=str, default=None, help=argparse.SUPPRESS)

    args = parser.parse_args()

    api_key = load_api_key()

    # --- Dry run ---
    if args.dry_run:
        sorry_files = find_sorry_files()
        prompt = build_prompt(sorry_files)
        print("DRY RUN — would submit:\n")
        print(f"Files with sorry ({len(sorry_files)}):")
        for fname, sorrys in sorted(sorry_files.items(), key=lambda x: -len(x[1])):
            print(f"  {fname}: {len(sorrys)} sorry")
            for s in sorrys:
                print(f"    {s}")
        print(f"\nTotal: {sum(len(v) for v in sorry_files.values())} sorry gaps")
        print(f"\nPrompt preview:\n{prompt[:1000]}...")
        return

    # --- Retrieve mode ---
    if args.retrieve:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        dest = RESULTS_DIR / f"run_{timestamp}_{args.retrieve[:8]}"
        patched_dir = retrieve_result(args.retrieve, dest, api_key)
        print_summary(patched_dir)

        diff_path = dest / "diff.patch"
        diff_text = generate_diff(patched_dir, LEAN_DIR, diff_path)
        if diff_text:
            print(f"\nDiff saved to: {diff_path}")
            print(f"\n{'=' * 60}\nDIFF PREVIEW (first 3000 chars)\n{'=' * 60}")
            print(diff_text[:3000])
        else:
            print("\nNo differences found.")

        sorries = count_sorries(patched_dir)
        if sorries:
            print(f"\nRemaining sorries in patched files:")
            for f, c in sorries.items():
                print(f"  {f}: {c}")
        else:
            print("\nNo sorries remaining!")

        if args.integrate:
            updated = integrate_proofs(patched_dir, LEAN_DIR)
            if updated:
                print(f"\nIntegrated {len(updated)} files:")
                for f in updated:
                    print(f"  {f}")
                print("\nWARNING: If Uqsl2Hopf.lean was modified, review carefully —")
                print("it may have been cherry-picked from a prior run.")
                print("\nRun `lake build` to verify!")
            else:
                print("\nNo files needed updating.")
        return

    # --- Resume mode ---
    if args.resume:
        print(f"Resuming from OUT_OF_BUDGET run: {args.resume}")
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        dest = RESULTS_DIR / f"run_{timestamp}_{args.resume[:8]}_partial"
        patched_dir = retrieve_result(args.resume, dest, api_key)
        print_summary(patched_dir)
        diff_path = dest / "diff.patch"
        diff_text = generate_diff(patched_dir, LEAN_DIR, diff_path)
        if diff_text:
            print(f"\nPartial diff saved to: {diff_path}")
            print(diff_text[:2000])
        sorries = count_sorries(patched_dir)
        if sorries:
            print(f"\nRemaining sorries:")
            for f, c in sorries.items():
                print(f"  {f}: {c}")
        updated = integrate_proofs(patched_dir, LEAN_DIR)
        if updated:
            print(f"\nIntegrated {len(updated)} partially-filled files:")
            for f in updated:
                print(f"  {f}")
            print("\nRun `lake build` then resubmit with --submit")
        return

    # --- Submit mode ---
    if not args.submit and not args.priority and not args.target:
        print("Use --submit to submit, --dry-run to preview, or --retrieve <ID> to fetch results.")
        print("Run with --help for all options.")
        return

    # Deprecated path warnings
    if args.target is not None:
        print("WARNING: --target is deprecated. Use --submit instead.")
        print("         For targeted prompts, use the aristotle CLI directly:")
        print("         cd lean && source ../.env && aristotle submit 'prompt' --project-dir .")

    print("=" * 60)
    print("SK-EFT Hawking: Aristotle Submission")
    print("=" * 60)

    # Pre-flight: check for running jobs
    running = check_running_jobs(api_key)
    if running:
        print(f"\nWARNING: {len(running)} job(s) already in progress:")
        for j in running:
            print(f"  {j['line']}")
        if not args.force:
            print("\nSubmitting now would duplicate work (Aristotle always receives the full project).")
            print("Wait for running jobs to complete, or use --force to submit anyway.")
            return
        print("\n--force specified, submitting anyway.\n")

    # Scan for sorry gaps directly from files (not the registry)
    sorry_files = find_sorry_files()
    if not sorry_files:
        print("\nNo sorry gaps found in Lean files!")
        return

    prompt = build_prompt(sorry_files)
    total = sum(len(v) for v in sorry_files.values())
    print(f"\nSubmitting {total} sorry gaps across {len(sorry_files)} files:")
    for fname, sorrys in sorted(sorry_files.items(), key=lambda x: -len(x[1])):
        print(f"  {fname}: {len(sorrys)}")

    # Handle deprecated paths
    runner = AristotleRunner()
    if args.target:
        gap = next((g for g in SORRY_GAPS if g.name == args.target), None)
        if gap is None:
            print(f"ERROR: No sorry gap named '{args.target}'")
            sys.exit(1)
        result = runner.submit_targeted(gap, timeout_seconds=args.timeout)
    elif args.priority is not None:
        result = runner.submit_priority_batch(max_priority=args.priority, timeout_seconds=args.timeout)
    else:
        # New path: submit with comprehensive prompt
        result = runner.submit_and_wait(prompt, timeout_seconds=args.timeout)

    # Save manifest for dedup
    if result.project_id:
        save_manifest(result.project_id, prompt, sorry_files)

    # Report
    print(f"\n{'=' * 60}\nRESULTS\n{'=' * 60}")
    print(f"Project ID: {result.project_id}")
    print(f"Status: {result.status}")

    if result.is_out_of_budget:
        print(f"\nOUT_OF_BUDGET: Partial results may be available.")
        print(f"  python scripts/submit_to_aristotle.py --retrieve {result.project_id}")
        print(f"  python scripts/submit_to_aristotle.py --resume {result.project_id}")

    if result.status and "error" in result.status.lower():
        print(f"\nErrors/Warnings:")
        if result.raw_output:
            for line in result.raw_output.splitlines():
                if "error" in line.lower() or "warning" in line.lower():
                    print(f"  - {line.strip()}")

    print(f"\nRetrieve results with:")
    print(f"  python scripts/submit_to_aristotle.py --retrieve {result.project_id}")


if __name__ == "__main__":
    main()
