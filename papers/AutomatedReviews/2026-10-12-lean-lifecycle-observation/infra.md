# Lifecycle observation source defects

This report records the original six source defects as F1 through F6, using canonical numeric sections 1 through 6. The source package has received bounded independent review; actual integration, current verification and closure are recorded separately through the existing process. Historical observation failures and alternative launch failures establish source risks without proving the exact historical metadata-deletion time or an exclusive incident cause.

All six findings use canonical **major** severity because their source contracts are required for safe lifecycle operations. This is an explicit risk assignment, not a conversion of historical high/medium labels into advisory findings.

The findings below concern SOURCE behavior. Native eligibility, client RPC completion, known-owner process identity, loaded runtime and matching-lease MCP admission remain separate pending gates in [ADR-008](../../../docs/adrs/ADR-008-shared-lean-slot-control-plane.md) and the [operator guide](../../../docs/dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md). Passing these source checks does not establish live quiescence, authorize adoption of unknown processes or certify backend admission.

## Findings

### 1 — F1: Unavailable observation becomes absence before registration cleanup

- **Severity:** major
- **Lane:** infra
- **Gate:** ADR-008 lifecycle SOURCE integration
- **Location:** `scripts/lean_slots/state.py`, `scripts/lean_slots/supervisor.py`, `tests/test_lean_lifecycle_observation.py`
- **Observed:** The earlier source collapsed observation errors into absence, allowing destructive registration cleanup without a capable process-absence witness. The source branch is established; the exact historical release branch and metadata-deletion time remain unresolved.
- **Expected:** Keep present, absent, mismatch and unavailable observations distinct. Only coherent owned identity authorizes process management; unavailable native or filesystem evidence reserves resources and preserves records rather than proving death.
- **Fix:** Preserve structured observation capability, identity and census checks at actual cleanup consumers. Controls `test_control_01_observation_and_absence`, `test_control_02_pid_mismatch_and_owned_tree`, `test_control_03_post_signal_unavailable`, and the R4/R6 witness and filesystem-denial controls cover the source contract.
- **Verify:** `.venv/bin/python3 -m pytest tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py -q`

### 2 — F2: Cache transition can precede actual resource quiescence

- **Severity:** major
- **Lane:** infra
- **Gate:** ADR-008 lifecycle SOURCE integration
- **Location:** `scripts/lean_slots/supervisor.py`, `scripts/lean_slots/controller.py`, `tests/test_lean_lifecycle_observation.py`
- **Observed:** The earlier prepare, paired switch and cache paths could begin transitions while unregistered endpoint or project resources remained. Historical refusal and quarantine establish that unknown processes blocked prepare; they do not prove that every preceding reset or copy operation completed.
- **Expected:** Require capable target and paired backend-endpoint, project and retained-child quiescence before cache reset, restore, preparation or yield. Unknown or unavailable evidence must refuse before mutation. Cache-hit discovery performs no backend borrow; actual temporary borrowing requires guarded admission and owned cleanup, retaining residual reservations on cleanup failure.
- **Fix:** Enforce the common observation contract at every transition consumer. Controls `test_control_04_prepare_quiescence`, `test_control_05_paired_switch_restore`, `test_control_11_tool_borrow_and_cache_hit` and `test_six_r2_paired_corruption_refuses_before_yield` cover ordering and paired record corruption.
- **Verify:** `.venv/bin/python3 -m pytest tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py -q`

### 3 — F3: Post-launch failures can leave unregistered live resources

- **Severity:** major
- **Lane:** infra
- **Gate:** ADR-008 lifecycle SOURCE integration
- **Location:** `scripts/lean_slots/supervisor.py`, `scripts/lean_slots/state.py`, `tests/test_lean_lifecycle_observation.py`
- **Observed:** Earlier failures after `Popen` could leave a live process without a durable registration. These are source-derived alternative failure paths; their existence does not identify the exclusive historical cause of an unregistered process.
- **Expected:** Write pending provenance before launch, establish coherent selected-process and complete-census identity before durable PID/signature readiness, and roll back only an exact owned creation. Failed or unavailable cleanup retains durable uncertainty and reserves capacity. Never infer generic ownership or signal unknown descendants.
- **Fix:** Use transactional pending/running/uncertain-residual records with the narrow exact-unreaped-handle fallback. Preserve retained uncertainty across failed writes and completed exits with corrupt resource observations. Controls 06, 07, 08 and `test_six_r1_actual_completed_exit_retains_corrupt_resources` cover these paths. Source readiness remains distinct from actual MCP admission; no SIGKILL recovery is authorized.
- **Verify:** `.venv/bin/python3 -m pytest tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py -q`

### 4 — F4: Registry counts and down status understate occupied capacity

- **Severity:** major
- **Lane:** infra
- **Gate:** ADR-008 lifecycle SOURCE integration
- **Location:** `scripts/lean_slots/supervisor.py`, `scripts/lean_slots/controller.py`, `tests/test_lean_lifecycle_observation.py`
- **Observed:** Earlier resource reporting and admission relied on registration counts or down status despite unknown live resources. A small registry count or FREE lease alone does not establish physical capacity, listener ownership or project absence.
- **Expected:** Count capable physical occupancy across both repository roles and retain unknown listeners, project roots, reparented descendants, conflicting inventories and malformed or unavailable observations as reservations. Enforce the existing three-slot limit without adopting unknown resources.
- **Fix:** Use complete resource observations and shared record validation for status, doctor, health, acquire and dispatch. Controls 09, 10, 12, 17 and R3/R5/R6 retain unknown occupancy and reject garbage or malformed census results. The separately recorded ND1/ND2 findings refine linked-domain and ancestry accounting without weakening this contract.
- **Verify:** `.venv/bin/python3 -m pytest tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py -q`

### 5 — F5: A global supervisor command silently ignores slot selection

- **Severity:** major
- **Lane:** infra
- **Gate:** ADR-008 lifecycle SOURCE integration
- **Location:** `scripts/lean_slots/cli.py`, `tests/test_lean_lifecycle_observation.py`
- **Observed:** The earlier CLI accepted `--slot` for global start, stop and status commands although it did not restrict their scope. This source semantic defect does not prove an unintended restart occurred in a particular historical invocation.
- **Expected:** Reject ignored slot selection before inventory construction or any supervisor action. Keep documented global command scope and require an exact slot for probe. Preserve existing internal number APIs without introducing a new CLI recovery verb.
- **Fix:** Validate command/slot combinations before constructor execution. `test_control_15_cli_rejects_ignored_slots_before_constructor` verifies all three global commands and their actual early rejection behavior. Global restart is not authorized as recovery for occupied or unknown resources.
- **Verify:** `.venv/bin/python3 -m pytest tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py -q`

### 6 — F6: Lease release and base-reference compatibility are conflated

- **Severity:** major
- **Lane:** infra
- **Gate:** ADR-008 lifecycle SOURCE integration
- **Location:** `scripts/lean_slots/controller.py`, `scripts/lean_slots/supervisor.py`, `docs/adrs/ADR-008-shared-lean-slot-control-plane.md`, `tests/test_lean_lifecycle_observation.py`
- **Observed:** Earlier release reporting and literal-SHA versus branch-name absorption semantics did not clearly separate lease success, residual resource reservation and base-reference compatibility. The compatibility issue is source-established; no historical absorb failure or unimplemented retarget action is asserted.
- **Expected:** Preserve owner, containment, cleanliness, paired epoch and ancestry checks. A resolvable literal SHA may acquire and prepare; clean contained no-change work may release under normal checks. Absorption requires the actual current primary branch name to equal the lease's recorded base reference, so a literal SHA does not satisfy that branch-name check. Refusal preserves READY state and source work. Successful lease unlink may report a nonfatal residual-resource warning while still reserving uncertain resources; it must not imply backend quiescence or admission.
- **Fix:** Preserve the existing branch-name requirement for absorption and literal-SHA mismatch refusal, alongside truthful post-unlink resource reporting. Controls 13, 14, 16 and 17 distinguish owner checks, residual reservations, literal-SHA acquisition/preparation and contained release, branch-based absorption, and status/doctor/health. No retarget action, lease hand editing, broadened SHA absorption or bypass of canonical ownership checks is authorized.
- **Verify:** `.venv/bin/python3 -m pytest tests/test_lean_lifecycle_observation.py tests/test_lean_slots.py tests/test_codex_lean_slot_policy.py -q`
