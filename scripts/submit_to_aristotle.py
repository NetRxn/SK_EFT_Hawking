#!/usr/bin/env python3
"""
Submit SK-EFT Hawking Paper Lean sorries to Aristotle.

This script submits sorry gaps to Aristotle, waits for results, extracts
the returned tar.gz, diffs against our source, and optionally integrates
the filled proofs back into the codebase.

Usage:
    # From project root:
    python scripts/submit_to_aristotle.py

    # With explicit priority level (1=algebraic, 2=moderate, 3=all):
    python scripts/submit_to_aristotle.py --priority 2

    # Targeted single sorry:
    python scripts/submit_to_aristotle.py --target acousticMetric_det

    # Auto-integrate filled proofs (copies patched files into lean/):
    python scripts/submit_to_aristotle.py --priority 1 --integrate

    # Retrieve a previous run by project ID:
    python scripts/submit_to_aristotle.py --retrieve 082e6776-42d7-469d-be9d-064c328540cf

    # Resume from an OUT_OF_BUDGET run (retrieve partial, integrate, resubmit):
    python scripts/submit_to_aristotle.py --resume 082e6776-42d7-469d-be9d-064c328540cf

Requires:
    - aristotlelib installed: pip install aristotlelib
    - ARISTOTLE_API_KEY in .env or environment

Output:
    Results saved to docs/aristotle_results/<run_id>/ with:
    - ARISTOTLE_SUMMARY_*.md  — what Aristotle changed
    - Patched .lean files     — ready for review/integration
    - diff.patch              — unified diff against our lean/ source
"""

import argparse
import os
import shutil
import subprocess
import sys
import tarfile
from datetime import datetime
from pathlib import Path

# Project paths
PROJECT_ROOT = Path(__file__).parent.parent
LEAN_DIR = PROJECT_ROOT / "lean"
RESULTS_DIR = PROJECT_ROOT / "docs" / "aristotle_results"

sys.path.insert(0, str(PROJECT_ROOT))
from src.aristotle_interface import AristotleRunner, SORRY_GAPS


def load_api_key() -> str:
    """Load API key from .env or environment."""
    env_file = PROJECT_ROOT / ".env"
    if env_file.exists():
        for line in env_file.read_text().splitlines():
            if line.startswith("ARISTOTLE_API_KEY="):
                return line.split("=", 1)[1].strip()
    key = os.environ.get("ARISTOTLE_API_KEY")
    if key:
        return key
    raise ValueError("No ARISTOTLE_API_KEY found. Set it in .env or environment.")


def retrieve_result(project_id: str, destination: Path, api_key: str) -> Path:
    """Retrieve and extract Aristotle results by project ID.

    Returns the path to the extracted result directory.
    """
    destination.mkdir(parents=True, exist_ok=True)
    tar_path = destination / "result.tar.gz"

    print(f"Retrieving project {project_id}...")
    cmd = [
        "aristotle", "result", project_id,
        "--wait",
        "--destination", str(tar_path),
        "--api-key", api_key,
    ]
    subprocess.run(cmd, check=True)

    # Extract tar.gz
    extracted_dir = extract_tarball(tar_path, destination)
    return extracted_dir


def extract_tarball(tar_path: Path, destination: Path) -> Path:
    """Extract tar.gz and return path to the lean project inside.

    Aristotle returns a tar.gz containing a directory (e.g., 'lean_aristotle/')
    with the patched Lean project files.
    """
    if not tar_path.exists():
        # Maybe the destination itself is the extracted directory
        # (aristotle CLI sometimes extracts directly)
        lean_dirs = list(destination.glob("*/SKEFTHawking"))
        if lean_dirs:
            return lean_dirs[0].parent
        raise FileNotFoundError(f"No tar.gz at {tar_path} and no extracted files found")

    print(f"Extracting {tar_path}...")
    with tarfile.open(tar_path, "r:gz") as tar:
        tar.extractall(path=destination)

    # Find the extracted lean project directory
    # Aristotle typically names it 'lean_aristotle/' or similar
    for child in destination.iterdir():
        if child.is_dir() and (child / "SKEFTHawking").exists():
            return child
        if child.is_dir() and any(child.glob("*.lean")):
            return child

    raise FileNotFoundError(f"Could not find Lean project in extracted files at {destination}")


def generate_diff(patched_dir: Path, original_dir: Path, output_path: Path) -> str:
    """Generate a unified diff between patched and original Lean files.

    Returns the diff as a string and saves to output_path.
    """
    diff_lines = []
    for patched_file in sorted(patched_dir.rglob("*.lean")):
        rel_path = patched_file.relative_to(patched_dir)
        original_file = original_dir / rel_path
        if not original_file.exists():
            continue

        result = subprocess.run(
            ["diff", "-u", str(original_file), str(patched_file),
             "--label", f"a/{rel_path}", "--label", f"b/{rel_path}"],
            capture_output=True, text=True
        )
        if result.stdout:
            diff_lines.append(result.stdout)

    diff_text = "\n".join(diff_lines)
    output_path.write_text(diff_text)
    return diff_text


def print_summary(patched_dir: Path) -> None:
    """Print Aristotle's summary if available."""
    summaries = list(patched_dir.glob("ARISTOTLE_SUMMARY_*.md"))
    if summaries:
        print("\n" + "=" * 60)
        print("ARISTOTLE SUMMARY")
        print("=" * 60)
        print(summaries[0].read_text())
    else:
        print("\nNo Aristotle summary file found.")


def count_sorries(directory: Path) -> dict[str, int]:
    """Count remaining 'sorry' occurrences in Lean files."""
    counts = {}
    for lean_file in directory.rglob("*.lean"):
        text = lean_file.read_text()
        # Count sorry that appears as a tactic (not in comments)
        sorry_count = 0
        for line in text.splitlines():
            stripped = line.strip()
            if stripped.startswith("--") or stripped.startswith("/-"):
                continue
            if "sorry" in stripped and not stripped.startswith("--"):
                sorry_count += 1
        if sorry_count > 0:
            counts[str(lean_file.relative_to(directory))] = sorry_count
    return counts


def integrate_proofs(patched_dir: Path, lean_dir: Path) -> list[str]:
    """Copy patched Lean files into the project, returning list of updated files.

    Only copies files that actually differ from the originals.
    """
    updated = []
    for patched_file in sorted(patched_dir.rglob("*.lean")):
        rel_path = patched_file.relative_to(patched_dir)
        target = lean_dir / rel_path
        if not target.exists():
            continue

        # Only copy if content differs
        if patched_file.read_text() != target.read_text():
            shutil.copy2(patched_file, target)
            updated.append(str(rel_path))

    return updated


def main():
    parser = argparse.ArgumentParser(
        description="Submit Lean sorry gaps to Aristotle for automated proof filling"
    )
    parser.add_argument(
        "--priority", type=int, default=1, choices=[1, 2, 3],
        help="Maximum priority level to submit (1=algebraic, 2=moderate, 3=all). Default: 1"
    )
    parser.add_argument(
        "--target", type=str, default=None,
        help="Target a specific sorry by name (e.g., 'acousticMetric_det')"
    )
    parser.add_argument(
        "--timeout", type=int, default=3600,
        help="Timeout in seconds per submission. Default: 3600 (1 hour)"
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Print what would be submitted without actually submitting"
    )
    parser.add_argument(
        "--retrieve", type=str, default=None,
        help="Retrieve results for a previous project ID instead of submitting new"
    )
    parser.add_argument(
        "--integrate", action="store_true",
        help="Auto-integrate patched files into lean/ (review diff first!)"
    )
    parser.add_argument(
        "--resume", type=str, default=None,
        help="Resume from an OUT_OF_BUDGET run: retrieve partial results, integrate, resubmit"
    )
    args = parser.parse_args()

    api_key = load_api_key()

    if args.dry_run:
        print("DRY RUN — would submit the following:\n")
        runner = AristotleRunner()
        runner.print_sorry_summary()
        if args.target:
            gaps = [g for g in SORRY_GAPS if g.name == args.target]
            print(f"\nTargeted: {args.target}")
            if not gaps:
                print(f"  ERROR: No sorry gap named '{args.target}'")
        else:
            gaps = [g for g in SORRY_GAPS if g.priority <= args.priority and not g.filled]
            filled = [g for g in SORRY_GAPS if g.priority <= args.priority and g.filled]
            print(f"\nWould submit {len(gaps)} unfilled gaps at priority ≤ {args.priority}")
            if filled:
                print(f"  (Skipping {len(filled)} already-filled gaps)")
        return

    # --- Retrieve mode ---
    if args.retrieve:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        dest = RESULTS_DIR / f"run_{timestamp}_{args.retrieve[:8]}"
        patched_dir = retrieve_result(args.retrieve, dest, api_key)
        print_summary(patched_dir)

        # Generate diff
        diff_path = dest / "diff.patch"
        diff_text = generate_diff(patched_dir, LEAN_DIR, diff_path)
        if diff_text:
            print(f"\nDiff saved to: {diff_path}")
            print(f"\n{'='*60}\nDIFF PREVIEW (first 3000 chars)\n{'='*60}")
            print(diff_text[:3000])
        else:
            print("\nNo differences found (files identical).")

        # Sorry count
        sorries = count_sorries(patched_dir)
        if sorries:
            print(f"\nRemaining sorries in patched files:")
            for f, c in sorries.items():
                print(f"  {f}: {c}")
        else:
            print("\nNo sorries remaining in patched files!")

        # Integrate if requested
        if args.integrate:
            updated = integrate_proofs(patched_dir, LEAN_DIR)
            if updated:
                print(f"\nIntegrated {len(updated)} files:")
                for f in updated:
                    print(f"  ✓ {f}")
                print("\nRun `lake build` to verify!")
            else:
                print("\nNo files needed updating.")
        return

    # --- Resume mode (for OUT_OF_BUDGET recovery) ---
    if args.resume:
        print(f"Resuming from OUT_OF_BUDGET run: {args.resume}")
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        dest = RESULTS_DIR / f"run_{timestamp}_{args.resume[:8]}_partial"
        patched_dir = retrieve_result(args.resume, dest, api_key)

        # Show what Aristotle managed before budget exhaustion
        print_summary(patched_dir)
        diff_path = dest / "diff.patch"
        diff_text = generate_diff(patched_dir, LEAN_DIR, diff_path)
        if diff_text:
            print(f"\nPartial progress diff saved to: {diff_path}")
            print(f"\n{'='*60}\nPARTIAL DIFF PREVIEW (first 2000 chars)\n{'='*60}")
            print(diff_text[:2000])
        else:
            print("\nNo partial progress found (files identical). Nothing to resume.")
            return

        sorries = count_sorries(patched_dir)
        if sorries:
            print(f"\nRemaining sorries in partial output:")
            for f, c in sorries.items():
                print(f"  {f}: {c}")

        # Integrate partial results
        updated = integrate_proofs(patched_dir, LEAN_DIR)
        if updated:
            print(f"\nIntegrated {len(updated)} partially-filled files:")
            for f in updated:
                print(f"  ✓ {f}")
            print("\n⚠️  Run `lake build` to verify partial progress compiles!")
            print("Then resubmit remaining sorries with:")
            print(f"  python scripts/submit_to_aristotle.py --priority 3")
        else:
            print("\nNo files changed from partial results.")
        return

    # --- Submit mode ---
    print("=" * 60)
    print("SK-EFT Hawking Paper: Aristotle Submission")
    print("=" * 60)

    runner = AristotleRunner()

    if args.target:
        gap = next((g for g in SORRY_GAPS if g.name == args.target), None)
        if gap is None:
            print(f"ERROR: No sorry gap named '{args.target}'")
            unfilled = [g for g in SORRY_GAPS if not g.filled]
            print(f"Available (unfilled): {', '.join(g.name for g in unfilled)}")
            sys.exit(1)
        if gap.filled:
            print(f"WARNING: '{gap.name}' is already filled. Skipping.")
            return
        print(f"\nSubmitting targeted sorry: {gap.name}")
        print(f"  Module: {gap.module}")
        print(f"  Priority: {gap.priority}")
        print(f"  Description: {gap.description}")
        result = runner.submit_targeted(gap, timeout_seconds=args.timeout)
    else:
        gaps = [g for g in SORRY_GAPS if g.priority <= args.priority and not g.filled]
        filled = [g for g in SORRY_GAPS if g.priority <= args.priority and g.filled]
        if not gaps:
            print(f"\nNo unfilled sorry gaps at priority ≤ {args.priority}.")
            if filled:
                print(f"  All {len(filled)} gaps at this level are already filled!")
            return
        print(f"\nSubmitting {len(gaps)} unfilled sorry gaps (priority ≤ {args.priority}):")
        for g in gaps:
            print(f"  [{g.priority}] {g.module}.{g.name}")
        if filled:
            print(f"\n  (Skipping {len(filled)} already-filled: {', '.join(g.name for g in filled)})")
        result = runner.submit_priority_batch(
            max_priority=args.priority,
            timeout_seconds=args.timeout,
        )

    # Report
    print(f"\n{'='*60}\nRESULTS\n{'='*60}")
    print(f"Project ID: {result.project_id}")
    print(f"Status: {result.status}")

    # Handle OUT_OF_BUDGET — partial results may still be usable
    if result.is_out_of_budget:
        print(f"\n⚠️  OUT_OF_BUDGET: Aristotle exhausted its compute budget.")
        print(f"   Partial results may be available. Next steps:")
        print(f"   1. Retrieve partial output:")
        print(f"      aristotle result {result.project_id} --destination partial.tar.gz")
        print(f"   2. Or use this script:")
        print(f"      python scripts/submit_to_aristotle.py --retrieve {result.project_id}")
        print(f"   3. Inspect the diff for any useful partial progress")
        print(f"   4. Resubmit the (partially-filled) project to continue\n")

    if result.errors:
        print(f"\nErrors/Warnings:")
        for e in result.errors:
            print(f"  - {e}")
        if "Timed out" in str(result.errors):
            print(f"\nJob may still be running. Check with:")
            print(f"  aristotle list --limit 5")
            print(f"Then retrieve with:")
            print(f"  python scripts/submit_to_aristotle.py --retrieve <PROJECT_ID>")

    # If there are no usable results at all, stop here
    if not result.has_partial_results and result.errors:
        return

    # Try to find and process the result files
    # (Both COMPLETE and OUT_OF_BUDGET runs may have downloadable artifacts)
    patched_dirs = list(RESULTS_DIR.glob(f"patched_*"))
    if patched_dirs:
        latest = sorted(patched_dirs)[-1]
        # Look for extracted lean files
        lean_dirs = list(latest.rglob("SKEFTHawking"))
        if lean_dirs:
            patched_dir = lean_dirs[0].parent
            print_summary(patched_dir)

            diff_path = latest / "diff.patch"
            diff_text = generate_diff(patched_dir, LEAN_DIR, diff_path)
            if diff_text:
                print(f"\nDiff: {diff_path}")

            sorries = count_sorries(patched_dir)
            total = sum(sorries.values())
            print(f"\nRemaining sorries: {total}")

            if args.integrate:
                updated = integrate_proofs(patched_dir, LEAN_DIR)
                if updated:
                    print(f"\nIntegrated {len(updated)} files. Run `lake build` to verify!")

    print(f"\nFull results saved to {RESULTS_DIR}/")


if __name__ == "__main__":
    main()
