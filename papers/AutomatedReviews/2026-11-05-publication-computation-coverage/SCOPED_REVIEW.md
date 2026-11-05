# Independent finding intake

Reviewer `/root/l1_transport` checked the three finding statements,
ROOT's separate extraction/evaluator reproduction, the implementation
source hashes and the declared acceptance commands. All three
commands ran and failed with the expected AssertionError. The
findings remain open; the broad suites must gain regression cases
during implementation. This is acceptance of the diagnosis and
repair obligation, not acceptance of a gate implementation or pass.

The first intake identified overly broad Verify commands; ROOT
replaced them with direct invariant assertions and preserved their
actual failures in FAILING_ACCEPTANCE.json. Final reviewed paths
and bound implementation hashes matched the revised packet.

A whole-source continuity check observed a temporary seam-probe
directory created by the concurrently running repository test suite.
The directory was absent at subsequent readback and the scoped
reviewed files were unchanged. Broad snapshot freshness is not
asserted from this scoped review. The document validator's basename
selection also included other existing infra.md documents and reported
their prior severity errors; that output is not a validation failure
attributed to this new document. No validator change was made.

The same independent reviewer separately accepted finding1.4 after
checking a fresh source snapshot, the real namespace import and the
scanner's population logic. The module resolves to this repository's
papers/D3/tables.py, while the scanner omits its namespace root. The
existing scalar renderer rounds log10 of the ratio to one decimal;
it cannot replace the full-precision ratio regression. The reviewer
corrected the finding's test-class name before checkpoint. No scanner
implementation or passing dependency suite is asserted.
