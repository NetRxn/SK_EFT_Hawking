# Frozen4a0d canonical qualification

The canonical bare fast suite ran on clean committed
4a0d736866adb4cdc006d6835f2895254bc942cb. It finished with7159 passed,
29 failed,8 skipped,92 deselected and7 warnings in631.52s; parent633.91s.
The [actual receipt](FROZEN_4A0D_FAST_EXIT.json) proves unchanged HEAD and clean
status before and after. Original [stdout](FROZEN_4A0D_FAST.txt),
[JUnit archive](FROZEN_4A0D_FAST_JUNIT.zip),
[JUnit byte manifest](FROZEN_4A0D_FAST_JUNIT_MANIFEST.json),
[preflight](FROZEN_4A0D_FAST_PREFLIGHT.json) and
[exact-case comparison](FROZEN_4A0D_FAST_VERIFICATION.json) are preserved.

All previous7161 testcase identities are present. Of the previous34 failing
identities,29 still fail and five pass. There are no new failing identities;
all35 added cases pass. The five newly passing cases are the existing
undeclared-ceiling zero-headroom, declaration-removal and DOI-on-declared-class
controls, the logical repository-prefixed planner target, and the missing
citation-registry invariant. This result does not waive the remaining29
failures or infer their causes from matching identities alone. Their full
messages and identities remain in the comparison and original outputs.

The earlier explicit slow affected-scope run remains separate:89 passed,
including the slow zero-orphan extractor. The broad fast suite's92 default
deselections do not supersede that coverage or establish full/native checks.

The [canonical all-bundle payload](FROZEN_4A0D_GATE_READBACK.json) was measured
on the same clean committed source before the broad run, using the existing
bundle registry and graph producer. All21 bundles and231 gates are present:
159 passed,25 blocked,28 open and19 requiring recheck. CitationIntegrity
improves blocked to passed for D1,D3,D4,D9,E1 versus16fde9. No bundle is
newly green. L1's remaining physical B3 blocking finding is not discharged.
The graph fingerprint is limited; full payload and original graph hashes,
timestamps, machine-local evidence limits and diagnostic correction are explicit.

Portable234/272 scientific coverage remains unchanged. The unrestricted79
pilot failed its admitted deadline and yielded no coefficient; its separate
archive retains that failure. This qualification remains RED. Main integration,
native/security checks, full scientific acceptance and final human publication
review remain open.
