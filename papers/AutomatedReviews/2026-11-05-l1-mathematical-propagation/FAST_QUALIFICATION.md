# Broad fast qualification remains RED

The actual bare fast run on the pre-closure candidate reports7169passed,35failed,8skipped,92deselected in634.26s. Its tracked sources were frozen: the complete midrun5634-file byte snapshot still matched at termination. HEAD remained3c56. This is a dirty reviewed-source run, not a claim of a clean committed-head run or final qualification after later catalog/closure/document intake.

All7204 historical01d72 test identities remain in7212 current cases. The eight added scientific cases pass. All29 prior failure identities still fail; six additional identities fail. One cannot infer equal causes merely from identity equality. Original stdout/JUnit and complete snapshot bytes are preserved in FAST_QUALIFICATION_EVIDENCE.zip; exact differential and six failure messages are in FAST_DIFFERENTIAL.json.

The six additional failures are a counts test whose uv subprocess cannot access the default cache, three temporary loopback proxy bind PermissionErrors, and two temporary process-signature assertions. A targeted rerun of those exact six with the existing populated environment/cache and sandbox-external loopback/process access passes6/6 in3.04s, without any source or harness fix or live slot mutation. This is separate scoped evidence, not a rewritten full-suite receipt or a new broad green run. The original29 failures remain unwaived.

Main/full-tree qualification remains open. No infrastructure repair or security/runtime configuration change is part of this package. The reviewed numerical/mathematical repair can be preserved as a draft checkpoint with its explicit qualification debt.
