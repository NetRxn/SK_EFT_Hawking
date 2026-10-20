---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: Codex-publication-cache-author
model: Codex
review_date: 2026-10-20
readiness_gates_version: 1
kind: targeted-infra
---

# Graph cache I/O-state regression

This author-filed regression is OPEN. ROOT accepts implementation/integration accountability;
the allocated cache author supplies the coherent repair and genuinely nonauthor whole review
remains required. Source construction, declared verification, production regression controls,
full current qualification, canonical closure and protected integration are distinct steps.
The declared Verify has not been executed for this filing.

### 1 — MAJOR — graph fingerprint conflates known absence and unavailable I/O

- **Severity:** major
- **Lane:** `infra`
- **Gate:** `bundle_readiness`
- **Location:** `scripts/provenance_dashboard.py::_graph_fingerprint`, `tests/test_dashboard_graph_cache.py`, `docs/architecture/DASHBOARD.md`
- **Verify:** `uv run python -m pytest -q tests/test_dashboard_graph_cache.py`
- **Observed:** At candidate `dcb9a2c5abe80bf64ab387e649975b4d9359b538`, the actual unchanged
  default profile fails the cache's original stable-key and same-cached-object tests.
  Captured pytest logs explicitly report ENOENT for missing `scripts/__pycache__`;
  the directory entry contains distinct fresh objects on consecutive fingerprint calls.
  The open audit event precedes the syscall, so attempted missing bytecode reads can
  legitimately retain this missing ancestor while bytecode remains disabled.
- **Source countermodel:** Independently of those measured directory failures, the file stat
  branch catches every OSError as stable `(path, 0, -1)`. Thus repeated EACCES/ENFILE/opaque
  errors, or unavailable stat followed by known ENOENT, produce the same file entry.
  This is a static source-level false-hit countermodel, not a native permission or
  descriptor-pressure incident observed by this filing.
- **Evidence:** The actual Q default run returned rc1 with 40 failures, including exactly the
  two original cache positive cases among its original cache tests. Its fingerprint diff
  names the missing directory at index3391; the complete captured warning carries errno2.
  Original source SHA256 is `1e6b308bb501ab22f65cec552083865a40c7427aef963067cae590248a9340d7`.
  The complete local receipt remains separate from this public finding; it is not a new rerun.
- **Expected:** Only syscall-reported ENOENT is stable known absence. Missing file differs
  from successful empty file, and missing directory differs from successful empty listing.
  Every other stat/list OSError remains fresh and nonmatching, including repeated unknown
  and unknown-to-absent transitions. Preserve actual read/code/ancestor populations,
  existing whole-key fail-safes, same-object caching and real served-finding invalidation.
- **Repair:** Extend the existing owner and original test module together, following
  [the reviewed design](../../../docs/superpowers/specs/2026-10-20-graph-cache-known-absence-design.md)
  and [coupled plan](../../../docs/superpowers/plans/2026-10-20-graph-cache-known-absence-plan.md).
  No directory creation, bytecode enablement, input exclusion, empty-error fallback,
  new cache/framework or weakened assertion is an acceptable substitute.
- **Related:** `review:2026-08-14-suite-runtime:infra:2` is already fixed through the original
  read-set repair and follow-up history `d82f237b`/`2f5ede79`. It is not reopened or rewritten.
  This finding records the distinct I/O-state error branches while retaining that repair.
- **Remaining:** Genuine whole source/evidence review; ROOT actual whole-module Verify,
  separate journalled old-directory and old-file production-source 0/1/0 controls with
  exact byte/fullmode/nsmtime restoration and empty journal; unchanged current default/full
  qualification, existing canonical closure and protected-main delivery. All scientific
  BUILD and publication requirements remain full strength.
