# Existing architecture inventory loses the shared hook catalog in linked worktrees

### 1.1 — 🟡 REQUIRED — Resolve the Git hook catalog through the target Git context

- **Severity:** major
- **Lane:** `infra`
- **Location:** `scripts/architecture_inventory.py`, affected architecture owners and inventory/export tests
- **Verify:** `.venv/bin/python -B -m pytest -m '' tests/test_architecture_inventory.py tests/test_architecture_claims.py tests/test_validate_public_surface.py::TestExternalSurface -q`

The NJL linked checkout at ec53782f has a Git file rather than a physical `.git`
directory. The existing inventory collector's `.git/hooks` guess omits the
known-present shared `pre-commit` entry. An initial existing-writer run derived
six rows instead of the tracked seven. That output was rejected and the original
stale census restored; writing the omitted population is not a repair.

Reuse the existing D1–D5 inventory component from 1550f5ff, isolated from that
commit's G4 changes. Keep the single inventory owner and existing freshness
checker. Resolve Git's actual target administrative and configured catalog context,
refuse foreign or unreadable/partial observations, preserve metadata membership,
and publish logical locators without reading or executing private hook bodies.
Update the actual schema-pointer and affected owners. Add this already-used
`validate.check_architecture_inventory_fresh` export to the existing public-surface
contract, retaining every previous entry. No new checker, gate, exception, floor
or scientific mapping is required.

Owner: ROOT, NJL integration dependency. Acceptance reviewer:
`njl_dependencies_whole_review`, independently of the source author. The existing
publication remediation plan and inventory worktree D1–D5 specification own the
scope; the current repair is not a physical or publication acceptance.

Acceptance requires independent whole source/intent review before the corrected
canonical writer; inspection of every generated delta; real journalled old-source
and generated-output faults through the original reader; targeted RED followed
by exact bytes/fullmode/nsmtime restoration, targeted GREEN and an empty journal;
complete affected tests and registration-site reconciliation; then independent
whole current-evidence review and the existing closure writer. Preserve unsuccessful
attempts. Metadata/configuration presence does not establish hook activation.
The complete delivery gate, main integration, inherited scientific R1 and all
original scientific BUILDs remain separate and owed.
