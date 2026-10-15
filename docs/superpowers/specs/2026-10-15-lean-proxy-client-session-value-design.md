# Lean proxy client-session value design

Status: **DRAFT SPECIFICATION / fresh exact tracked-text adversarial and intent
review required before code.** Implementation, actual Handler verification, CodeQL
recognition, source integration and native loading are unverified. This document
alone authorizes no runtime operation. Normative decisions:
[ADR-008 ST-1–ST-8](../../adrs/ADR-008-shared-lean-slot-control-plane.md#client-session-value-boundary-st-amendment).
Execution order and owners: [plan](../plans/2026-10-15-lean-proxy-client-session-value.md).

## Existing owner and source boundary

Source baseline: `d87df4da8943b7e6ad4d67733ad6941ee9b94e08`, read 2026-10-15.
[The existing proxy](../../../scripts/lean_slots/proxy.py) owns `LeaseGate`,
`SessionBroker` and the actual `make_handler` class. `_handle` reads and parses the
body, identifies the client and authorizes the request before local initialization
and forwarding. GET, POST and DELETE alias `_handle`; HEAD separately identifies
the client and returns 401 or 204. The later first-match client header selection
feeds `translation_key` and buffered echo without a selected-value guard.

`SessionBroker.mint` constructs `uuid.uuid4().hex`. `backend_session` adopts unknown
client keys and lazily establishes mappings. `forget` clears a stale mapping for
re-establishment. The Handler retries a buffered request at most once after backend
400/404 or JSON-RPC `-32602`. `None` currently reaches a NUL-prefixed sessionless
sentinel. Preserve these mechanisms rather than add a minted-session allowlist,
second validation framework or session-map migration.

[Existing runner tests](../../../tests/test_lean_slots.py) already construct the
actual Handler over in-memory `Wire` request/response streams. `_post` currently
uses a dictionary and `if session`, so duplicates collapse and explicit empty is
unrepresentable. Extend that same seam compatibly. Pure `offline_handshake` or
selector-only tests cannot establish that the Handler uses the guard.
Architecture-change review already owns specification and intent assessment; the
paper reviewer layer does not enforce this runtime value boundary. No new checker,
registry, agent, CLI, gate or controller operation is needed.

## Selected-value contract (ST-1–ST-3)

One pure `_client_session_id(headers)` function defines the client identity used by
`_handle`. Its logical operation is:

```python
values = headers.get_all("Mcp-Session-Id", [])
if not values:
    return None
if len(values) != 1:
    raise ValueError("invalid Mcp-Session-Id header")
token = values[0].strip(" \t")
if not token or any(not 0x21 <= ord(char) <= 0x7E for char in token):
    raise ValueError("invalid Mcp-Session-Id header")
return token
```

`get_all` is case-insensitive and retains parsed occurrences. Absence is `None`;
explicit empty and OWS-only fields are invalid. Every repeated occurrence refuses,
including identical individually valid values, mixed-case names and either order
of valid/hostile values. No first/last winner, joining or comma splitting is allowed.
A single `alpha,beta` is a valid opaque token; an upstream-coalesced origin cannot
be reconstructed from it.

SP and HTAB at the boundaries are HTTP framing OWS. Strip only those characters,
then require nonempty visible ASCII inclusive of `!` and `~`. Retained interior
SP/HTAB, CR/LF, NUL, remaining C0, DEL and non-ASCII refuse. Quotes, colon, slash,
comma and every other visible punctuation remain valid. A literal `%0D%0A` remains
literal. No case folding, UUID/hex/HTTP-tchar restriction, Unicode normalization,
percent decoding, quote removal, generic whitespace stripping, unfolding,
replacement or token repair is allowed.

This is a contract on the selected value produced by the existing parser. Some
leading folds are erased before selection; bare CR/LF can terminate a field or
parsing instead of surviving as characters. A separate request header is not a
session suffix. Tests must distinguish retained parsed-control negatives from
parser-loss cases. The design adds no raw capture/parser rewrite and makes no
universal malformed-wire rejection or full HTTP-conformance claim.

## Handler ordering and errors (ST-4)

In `_handle`, retain body length/framing, body read, JSON-RPC parsing,
`request_id` extraction, URL/client identification and `gate.authorize` in their
existing order. Immediately after that gate succeeds, call the selector once.
Handle only its validation failure in a separate branch from existing `SlotError`
credential/lease classification. Call `_deny(400, "invalid Mcp-Session-Id header",
request_id)` and return.

The complete error message therefore has the existing fixed lease-gate prefix and
a static detail. It contains no session-header-derived error text and emits no
`Mcp-Session-Id`. No `wants_initialize`, `broker.mint`, `cached_tool_list`,
`HTTPConnection` construction, `broker.backend_session` or `broker.forget` may occur
on this failure path. The body has already been read under the current ordering;
this change introduces no unread-body/keepalive behavior.

Keep the independent JSON-RPC ID through `_deny`'s existing `json.dumps` behavior.
A client may independently put the same string in that ID and its session header;
therefore do not assert that an entire error body cannot contain that string.
Assert static `error.message`, absent session echo and zero prohibited side effects;
use an independent request ID when checking the absence of session-derived detail.

Existing body/JSON errors and auth/lease 401/403 have their current precedence.
Malformed session input receives 400 only after the gate succeeds. Discovery stays
available without a lease under the existing policy. A valid token grants no lease
or identity authority. GET, POST and DELETE all use this boundary. HEAD does not
consume a session; preserve its current auth/401-or-204 and no-echo behavior even
when an invalid session field is supplied. Unsupported methods retain existing
`BaseHTTPRequestHandler` behavior.

## Canonical consumers and lifecycle (ST-5)

Remove the later `next(... self.headers.items() ...)` selection. Reuse the selected
canonical string for both broker key and buffered non-GET echo. Map `None` alone to
the existing `"\x00sessionless"` key. No accepted client token can contain NUL or
alias that internal key. Retain a common mapping across repeated absent-session
requests, using the same Handler/broker instance in the control.

On initialize, absent or valid supplied input still mints and returns a fresh
32-character UUID-hex client ID locally, with cached tools and no backend forwarding.
The supplied valid value does not become the initialize response token. Invalid
supplied input refuses before mint/cache. Unknown well-formed values remain
adoptable after broker replacement; no minted-only recognition is introduced.
Backend session rejection still forgets/re-establishes the same canonical key and
retries at most once, including when the retry is rejected again. The client token
remains stable on buffered responses.

Continue to remove incoming client session fields from outbound request headers,
then send the separately established backend session. Preserve lease/client/auth,
repository role, worktree, endpoint, dependency and process-owner checks, GET lease
requirements and `lean_build` denial. Notification-only offline 202, cached
`tools/list`, ping and no-backend failure behavior remain unchanged, except that
malformed supplied session input is rejected after a successful gate before any
fallback work.

## Parser bounds and separate backend surface (ST-6–ST-7)

The protocol default remains `2025-06-18`. Its
[MCP Session Management](https://modelcontextprotocol.io/specification/2025-06-18/basic/transports#session-management)
contract supplies the visible-ASCII alphabet rather than UUID grammar or a numeric
length cap. [RFC 9110 field limits](https://www.rfc-editor.org/rfc/rfc9110.html#section-5.4)
and [field values](https://www.rfc-editor.org/rfc/rfc9110.html#section-5.5) distinguish
implementation limits and framing OWS. No protocol migration is part of this work.

CPython 3.14.8's existing `_MAXLINE = 65536` accepts 65518 token bytes in the canonical
single line `Mcp-Session-Id: <token>\r\n` and raises `LineTooLong` at 65519.
`BaseHTTPRequestHandler` handles that parser exception as 431 before `_handle`.
This is a measured framing-specific example, not a universal token maximum; different
framing consumes different bytes. `_MAXHEADERS = 100` counts read records including
the terminator and is not a universal allowance of that many physical fields. Keep
these existing parser limits, without truncation or a lower application cap.
Recheck the runtime/parser when verifying the actual wire cases. Source UUID and
fixture lengths do not justify an arbitrary lower cap or claim a client population.
Many valid mappings and large accepted tokens remain separate resource-policy
concerns; this correction does not establish bounded broker cardinality or complete
DoS prevention.

Buffered non-GET responses already discard all backend session fields and emit the
selected client value, if present. Verify distinct client/backend values and repeated
backend session header pairs. GET streaming still passes backend session headers
through. Backend initialization's first returned session selection, backend reason
phrases, other backend response headers and other forwarded client headers retain
their existing separate boundaries. They are outside this client-value guarantee;
no blanket header-safety, response-splitting exploit or scanner-green claim follows.

## Binding actual Handler cases

All rows exercise the actual `make_handler` output through the extended existing
`Wire` seam, with raw emitted bytes retained. Simulate external `HTTPConnection`
responses and inventory/lease fixtures; do not replace the Handler or its admission
verdict with a second implementation. Use side-effect spies, scripted request/retry
counts and raw response headers as independent oracles.

| ID | Input and path | Required outcome and decisive observable |
|---|---|---|
| H01 | Absent header on ping and authorized GET/tool calls; repeated calls on one Handler/broker. | Exact existing NUL-prefixed sessionless key and mapping reuse; no client-derived echo. GET backend response session remains separate. Existing lease gate applies. |
| H02 | Explicit empty and OWS-only fields after successful gate. | Static 400, no session response field or session-derived detail, unchanged independent JSON-RPC ID, no mint/cache/broker/connection activity. Raw presence must survive the helper. |
| H03 | Identical valid duplicates, different valid duplicates, mixed-case names, valid/hostile in either order. | 400 with no winner or echo/side effects. Preserve ordered raw fields. An independent duplicate-guard bypass must make the identical-valid case red. |
| H04 | Ordinary token, UUID hex, unknown non-UUID, complete visible-ASCII range, quotes/comma/colon and literal `%0D%0A`; include raw successful DELETE. | Successful scripted buffered response uses the exact canonical broker key and one identical client echo; punctuation/case retained and no decoding. |
| H05 | Outer SP/HTAB, interior SP/HTAB and non-OWS boundary characters such as VT/FF/NBSP. | Only outer SP/HTAB canonicalize; key and echo agree. Interior whitespace and retained non-OWS refuse. Generic `strip()` must not pass. |
| H06 | Retained folded CRLF/LF/bare-CR continuations and trailing folds; each retained C0 including NUL/VT/FF, DEL and Latin-1 non-ASCII; include raw invalid DELETE. | 400 before broker/backend/echo after gate. Parameterize retained controls through actual parsed bytes; do not claim every raw bare CR/LF survives parsing. |
| H07 | Leading fold erased to `alpha`; bare CR/LF parser-loss cases; `alpha` followed by a separate request field. | Validate only the actual selected `alpha`. Emit only canonical `alpha` as client session. Do not claim detection of erased folds or validation of the separate field. |
| H08 | Canonical single-line token lengths 65518 and 65519 under the measured parser. | First reaches successful Handler path with exact raw key/echo; second receives parser 431 before Handler work. Record exact framing/runtime and raw output; no universal cap claim. |
| H09 | Initialize with absent, valid supplied and malformed supplied session. | First cases mint distinct valid UUID-hex IDs locally, with backend fail-on-touch; malformed gives static 400 before mint/cache/backend. Exercise actual Handler rather than only `offline_handshake`. |
| H10 | Valid session plus unleased, wrong-client/role/worktree/endpoint, changed dependency or stale process-owner tool/GET requests. | Retain current isolated gate fixtures and identity tests. At least actual Handler unleased tools/call and GET refuse with existing 401/403 and no backend. Disabled `lean_build` stays denied. |
| H11 | Unknown well-formed token with fresh broker, then backend 400/404/`-32602`; also repeated rejection. | Adopt/re-establish and retry at most once; count establish/forget/forward order and keep the canonical client value. Broker-only tests do not establish Handler retry. |
| H12 | Notification-only offline, cached/offline tools/list, ping, no-backend failures and HEAD with malformed session. | Preserve 202/discovery/failure shapes, with malformed `_handle` input refusing before fallback. HEAD retains auth/204 or 401 without token selection/reflection; no sockets. |
| H13 | Buffered POST/DELETE with distinct client/backend session values and repeated backend session headers; authorized GET stream. | Buffered response drops every backend session header and echoes one canonical client value. GET preserves existing backend passthrough, with no broader validation claim. |
| H14 | Invalid token plus missing bearer or denied lease. | Existing credential/lease failure precedes selection. Preserve 401/403 and zero backend/mint/echo; do not require 400 before gate success. |

## Non-vacuity, review and runtime admission (ST-8)

Before implementing the guard, drive a retained folded token through the actual old
Handler with a scripted successful backend. The rejection oracle must fail on old
code because the real buffered branch is reached; backend unavailability or a
helper-only test is insufficient. After implementation the corresponding control
must pass and prove refusal before key/cache/broker/backend/echo. Preserve positive
initialize, unknown-session, absent-session, punctuation and retry controls.

In a later authorized isolated candidate, separately bypass the production selector
call, duplicate guard and alphabet guard. Each corresponding actual Handler negative
must turn red for its unsafe behavior, then restore exact source bytes through
`scripts/seed_journal.py` and rerun green. Mutations are sole changes, not test-only
assertion changes or unrelated exceptions. Keep original/mutant/restored evidence.
No source mutation, test execution or native operation is claimed by this document.

Fresh independent adversarial review and intent assessment must cover the exact
tracked ADR, this design, the plan and operator guide before code, then the complete
implementation and controls. This design makes no population-shape assertion; a
later such assertion owes the existing architecture-change pilot. Measure current
collected/executed gate counts and exact-head results; earlier recovery receipts
cannot stand in for current verification. Full project and scientific/publication
acceptance remain distinct.

Source edits, source review, passing tests, commits and expected launch-source
fingerprints do not prove loaded process memory or completed requests. ROOT alone
owns later mathematical lease/request drain and runtime transition under existing
[operator guidance](../../dev-loops/LEAN_SLOT_OPERATOR_GUIDE.md#observation-failures-and-residual-resources)
and ADR-008 LO-5. Known ownership, reliable FREE, capable both-role backend/project/
retained-descendant absence, target-slot then lifecycle lock and actual owned-request
completion accounting are required. TCP/thread samples, a closed socket, a timeout
or FREE alone do not prove drain. Unknown resources remain reserved and untouched.
Use existing unlocked internals under held locks; add no lifecycle command.

Native acceptance separately measures loaded-code evidence, initialize/list,
unleased refusal, matching-lease dispatch, release/reconnect/recovery and paired
epoch evidence where applicable. Proxy replacement loses in-memory mappings; S-Q
backend rotation under a persistent proxy is not proof of active-client continuity
through replacement. Do not reload beneath active mathematical work or infer native
acceptance from source/scan results.
