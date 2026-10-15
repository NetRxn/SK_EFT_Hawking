# Selected client session values reach the Lean proxy response unchecked

## Findings

### 1.1 — 🔴 The selected session header can retain control bytes and reach buffered success

- **Severity:** major
- **Lane:** infra
- **Gate:** bundle_readiness
- **Location:** `scripts/lean_slots/proxy.py` client-session selection in `make_handler`.
- **Observed:** The previous Handler chose the first parsed `Mcp-Session-Id` occurrence without validating its value, used it as a broker key, and echoed it in a buffered success response. An authorized parsed value retaining a folded line reached HTTP 200 and the response header after successful downstream initialization and ping. Duplicate occurrences were silently reduced to a first value.
- **Evidence:** The original production source hash is `56167aa59d88e2eb16a5408aa28ed2e4b89d84d5ee2e2e19f53c4daad9bcf4ee`. Before adding the guard, the real in-memory Handler negative failed with actual status 200 against expected 400, retained folded bytes in the raw emitted session field, a corresponding broker key, and completed initialize/notification/ping requests. The test transport scripts only the external backend; the Handler, broker and isolated lease authority are real. Separate sole selector-call, duplicate-guard and retained-alphabet bypasses reproduce unsafe 200; exact restoration makes their controls green. This establishes unchecked response emission in that branch, not a victim-client response-splitting exploit.
- **Expected:** After existing authentication and lease checks, select at most one case-insensitive parsed header occurrence. Absence alone is sessionless; reject duplicates and empty values. Strip only outer SP/HTAB and require a nonempty opaque visible-ASCII value before minting, cache, broker or backend work. Return a static 400 without reflecting a rejected session value. Preserve the independently serialized JSON-RPC ID, HEAD ownership, unknown-token adoption, sessionless reuse and single retry. Backend header passthrough and raw framing erased by the HTTP parser are separate boundaries.
- **Fix:** Implement the existing Handler boundary specified by ADR-008 ST-1–ST-8 and the client-session value design and plan. Use one canonical selected token for the broker key and buffered echo, with the existing sentinel reserved for absence. Actual Handler cases cover the positive and negative branches; scoped tests and source integration do not certify loaded runtime or current scanner results.
- **Verify:** `python -B -m pytest tests/test_lean_slots.py -k test_st_ -q -p no:cacheprovider`

The verification command runs in the owning repository's activated canonical Python environment. It exercises the complete selected-value Handler matrix, including the three decisive negatives and opaque punctuation, initialization, authorization precedence, DELETE, sessionless and retry controls. Closure of this source defect does not close project gates or admit a running proxy. ROOT separately owns mathematical/request drain and the existing LO-5 known-ownership, quiescence and locking requirements before replacement and native admission.
