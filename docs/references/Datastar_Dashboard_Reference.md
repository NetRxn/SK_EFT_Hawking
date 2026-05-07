# Datastar Dashboard Reference

**Purpose:** single reference for implementing the SK-EFT provenance dashboard in Datastar. Datastar is new and not in LLM training data — read this doc **before** writing any dashboard template or Flask view. Upstream docs at <https://data-star.dev> are the source of truth; this document distills them to exactly what's needed for this repo.

Referenced by:
- `docs/roadmaps/Phase5v_Roadmap.md` §Wave 9h (Datastar realignment)
- `feedback_dashboard_datastar_stack.md` memory (why vanilla-JS drift happened and how to avoid)

---

## 1. Stack decision and why

Declared in `project_knowledge_graph_status.md` (2026-04-02): **PG 17 + Apache AGE + D3.js + Datastar (replaces HTMX) + Flask**. Datastar owns the reactive layer across all interactive tabs in `scripts/provenance_dashboard.py` + `scripts/templates/`.

**Rationale:** HTML-first reactivity, SSE-driven server push, zero build step, 40 KB runtime. Signals + attributes replace ~200 LOC of per-tab imperative JS. Pair with `datastar-py` SDK server-side to emit typed SSE events.

### Working CDN URL (pinned 2026-04-24)

```html
<script type="module"
        src="https://cdn.jsdelivr.net/gh/starfederation/datastar@v1.0.1/bundles/datastar.js"></script>
```

**Why v1.0.1 not beta.11.** `datastar-py` 0.8.0 (the SDK) emits `datastar-patch-elements` / `datastar-patch-signals` SSE events. The v1.0.0-beta.11 client (which this repo originally pinned) uses the older `datastar-merge-fragments` / `datastar-merge-signals` event names and ignores the SDK's output silently — fetches fire, DOM never morphs. The event-name rename landed in v1.0.0-RC.x; v1.0.0 (2026-04-16) and v1.0.1 (2026-04-20) consume the new names. **Any SDK+client version mismatch around this rename produces the "no visible error but nothing updates" failure mode** — the fetch succeeds, the response is structurally correct, the client just doesn't recognise the event.

The older `https://cdn.jsdelivr.net/npm/@starfederation/datastar` URL **404s** — don't use it. That was the cause of the initial silent drift: CDN failed, no one noticed, tabs shipped without Datastar.

### Signal access from vanilla JS (escape hatch)

Datastar v1 doesn't expose `window.ds` / `window.Datastar` globals for direct signal read/write. If a tab has JS that must coexist with Datastar (e.g., D3 force sim in `graph_tab`), keep that JS in charge of its own state and bridge via `data-*` attributes + `data-effect` rather than reaching for signals from script. Don't try to poll `window.ds` — that's what failed in my Wave 9g attempt.

---

## 2. Attribute reference (complete)

All attributes take expressions that can reference signals via `$name`. Modifiers use `__` delimiter.

| Attribute | Purpose | Example |
|---|---|---|
| `data-signals:foo="1"` | Declare / patch a signal | `<div data-signals:count="0">` |
| `data-signals:foo__ifmissing="v"` | Only set if signal doesn't exist | `<div data-signals:theme__ifmissing="'dark'">` |
| `data-bind:foo` | Two-way bind input → signal | `<input data-bind:search />` |
| `data-text="expr"` | Bind element text content | `<span data-text="$count">` |
| `data-show="expr"` | Toggle `display` (element must have `style="display:none"` default if starting hidden) | `<div data-show="$loading" style="display:none">` |
| `data-attr:name="expr"` | Reactive HTML attribute | `<button data-attr:disabled="$busy">` |
| `data-class:name="expr"` | Toggle a class | `<div data-class:active="$tab == 'graph'">` |
| `data-style:prop="expr"` | Reactive inline style | `<div data-style:color="$ok ? 'green' : 'red'">` |
| `data-computed:name="expr"` | Read-only derived signal | `<div data-computed:total="$a + $b">` |
| `data-effect="expr"` | Run expression on signal change | `<div data-effect="console.log($count)">` |
| `data-init="expr"` | Run on element init / page load | `<body data-init="@get('/api/bootstrap')">` |
| `data-init__delay.500ms="expr"` | Delayed init | |
| `data-ref:name` | Create reference signal for element | `<canvas data-ref:chart>` |
| `data-indicator:name` | Tracks fetch in-flight state | `<button data-indicator:loading data-on-click="@get('/x')">` |
| `data-ignore` | Skip Datastar processing on subtree | |
| `data-ignore-morph` | Preserve during morph | |
| `data-preserve-attr="open"` | Keep attr value during morph | `<details open data-preserve-attr="open">` |
| `data-on:click="expr"` | Click handler | `<button data-on:click="$count++">` |
| `data-on:input`/`submit`/`change`/`focus`/`blur` | Standard events | |
| `data-on:keydown__key.ArrowRight` | Key filter modifier | `<div data-on:keydown__key.ArrowRight__window="next()">` |
| `data-on:event__once` | Fire once then detach | |
| `data-on:event__prevent` | `preventDefault()` | `<form data-on:submit__prevent="@post('/save')">` |
| `data-on:event__stop` | `stopPropagation()` | |
| `data-on:event__debounce.500ms` | Debounce | `<input data-on:input__debounce.300ms="@post('/search')">` |
| `data-on:event__throttle.500ms` | Throttle | |
| `data-on:event__delay.Nms` | Delay execution | |
| `data-on:event__window` | Attach to `window` | |
| `data-on:event__document` | Attach to `document` | |
| `data-on:event__outside` | Fire on clicks outside element | `<div data-on:click__outside="close()">` |
| `data-on:event__passive` | Non-blocking listener | |
| `data-on:event__capture` | Capture phase | |
| `data-on-interval` | Default 1s interval | `<div data-on-interval="@get('/poll')">` |
| `data-on-interval__duration.500ms__leading` | Custom interval + leading fire | |
| `data-on-intersect` | Fire when viewport intersects | |
| `data-on-intersect__half`/`__full`/`__exit`/`__once` | Intersection variants | |
| `data-on-signal-patch` | React to any signal change | |
| `data-on-signal-patch-filter="{include:/re/}"` | Filtered signal watch | |
| `data-json-signals` | Dump signals as JSON (debugging) | `<pre data-json-signals>` |

**Signal naming:** `$foo` inside expressions. Attribute casing converts hyphens to camelCase in signal names.
**Evaluation order:** depth-first, DOM order.

---

## 3. Actions (called from within expressions)

### Fetch actions

All return SSE by default; can also handle HTML / JSON / JavaScript responses.

```html
<button data-on:click="@get('/api/graph/status')"></button>
<button data-on:click="@post('/api/papers/p12/vet', {payload: {claim: 'cs-value'}})"></button>
<button data-on:click="@put('/api/...')"></button>
<button data-on:click="@patch('/api/...')"></button>
<button data-on:click="@delete('/api/...')"></button>
```

Common options (same for all fetch actions):

```javascript
{
  contentType: 'json' | 'form',          // default 'json'
  filterSignals: {include: /^foo\./, exclude: /_temp$/},
  selector: null | 'css-selector',
  headers: {'X-Csrf-Token': 'abc'},
  openWhenHidden: true,                   // default false for GET, true for others
  payload: {...},                         // custom request body
  retry: 'auto' | 'error' | 'always' | 'never',
  retryInterval: 1000,  retryScaler: 2,
  retryMaxWait: 30000,  retryMaxCount: 10,
  requestCancellation: 'auto' | 'cleanup' | 'disabled' | AbortController,
}
```

Response handling (based on response `Content-Type`):

- `text/event-stream` — default; Datastar processes the stream.
- `text/html` — requires `datastar-selector` + `datastar-mode` (`outer|inner|remove|replace|prepend|append|before|after`) response headers.
- `application/json` — patches signals directly; add `datastar-only-if-missing: true` header to patch only missing signals.
- `text/javascript` — executes; can add attrs via `datastar-script-attributes` JSON header.

### State-mutation actions

```html
<!-- Access signals without subscribing -->
<div data-text="$foo + @peek(() => $bar)"></div>

<!-- Set many signals at once -->
<button data-on:click="@setAll(true, {include: /^is/})"></button>

<!-- Toggle all matching boolean signals -->
<button data-on:click="@toggleAll({include: /^show/})"></button>
```

### Pro actions (available in v1+)

```html
<button data-on:click="@clipboard('Hello')"></button>
<div data-computed:rgb="@fit($slider, 0, 100, 0, 255)"></div>
<div data-text="@intl('number', 1000000, {style: 'currency', currency: 'USD'})"></div>
```

### Fetch lifecycle events

```html
<div data-on:datastar-fetch="console.log(evt.detail)"></div>
```

Event types in `evt.detail.type`: `started | finished | error | retrying | retries-failed`.

---

## 4. SSE events (server side)

Servers reply with `Content-Type: text/event-stream`. Each event ends with **two** newlines.

### `datastar-patch-elements`

Morph or replace DOM elements (matched by ID or selector).

```
event: datastar-patch-elements
data: elements <div id="pp-meter"><span>NEW CONTENT</span></div>

```

Optional fields (each on its own `data:` line):
- `selector <css>` — target by selector instead of ID match
- `mode outer|inner|replace|prepend|append|before|after|remove` — default `outer`
- `namespace svg|mathml` — XML namespace handling
- `useViewTransition true` — opt into View Transitions API

**Removal:**
```
event: datastar-patch-elements
data: selector #pp-detail
data: mode remove

```

### `datastar-patch-signals`

Update signal values.

```
event: datastar-patch-signals
data: signals {currentPaper: "paper12_polariton", counts: {pass: 35}}

```

Optional:
- `onlyIfMissing true` — only patch signals that don't yet exist
- Setting a signal to `null` deletes it

### Critical mechanics

- Each event **MUST** end with `\n\n` (one blank line).
- Flask needs `mimetype='text/event-stream'` + `Cache-Control: no-cache` + `X-Accel-Buffering: no` headers.
- Morph matches by `id=` — put IDs on every top-level element AND on anything that needs event listeners / CSS transitions preserved across morphs.

---

## 5. `datastar-py` SDK (server side)

### Install

```bash
uv pip install datastar-py
# or add to pyproject.toml under [project] dependencies
```

### Flask integration (preferred pattern for this repo)

Flask isn't in the SDK's first-class framework list (Quart, FastAPI, FastHTML, Litestar, Sanic, Starlette, Django all are). For Flask we use the plain `ServerSentEventGenerator` + a manual `Response` with streaming generator.

```python
from flask import Response, request
from datastar_py import ServerSentEventGenerator as SSE

@app.route("/api/papers/<paper_id>/provenance", methods=["GET", "POST"])
def api_paper_provenance(paper_id: str):
    def generate():
        # Patch the paper title into the DOM
        yield SSE.patch_elements(
            f'<div id="pp-title">{title}</div>'
        )
        # Patch signals so dependent attributes re-evaluate
        yield SSE.patch_signals({
            'currentPaper': paper_id,
            'counts': counts,
            'claimsTotal': len(claims),
        })
    return Response(
        generate(),
        mimetype='text/event-stream',
        headers={'Cache-Control': 'no-cache', 'X-Accel-Buffering': 'no'},
    )
```

### Reading signals from the request

Datastar sends the current signal state with every fetch (in the query string for GET, JSON body for POST). Without the framework-specific `read_signals` helper for Flask, do it manually:

```python
import json

def read_signals():
    if request.method == 'GET':
        raw = request.args.get('datastar', '{}')
    else:
        raw = request.get_data(as_text=True) or '{}'
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        return {}
```

### `attribute_generator` for server-rendered HTML

When the server renders HTML (e.g. a Jinja partial), the SDK's attribute helper gives you editor-completed data-* attributes:

```python
from datastar_py import attribute_generator as data

# In a Jinja custom filter, or inline in a Flask response:
html = f'<button {data.on("click", "@get(`/api/graph/rebuild`)").debounce(500)}>Rebuild</button>'
```

Jinja-friendly (no IDE completion but functionally identical):
```jinja
<button {{ data.on("click", "@get('/api/graph/rebuild')").debounce(500) }}>Rebuild</button>
```

---

## 6. SK-EFT-specific conventions

### Shared signal vocabulary

Pick once; use consistently across tabs:

| Signal | Tab | Purpose |
|---|---|---|
| `$activeTab` | all | Current tab key (mirrors URL `?tab=...`) |
| `$activePaper` | paper, readiness, chains | Currently-focused paper id |
| `$activeChain` | chains, graph | Focused chain id |
| `$activeClaim` | paper | Focused claim id within Paper Provenance |
| `$filterLayers` | paper | Comma-joined set of active 8-layer filters |
| `$graphFocus` | graph | Focused node id in KG tab |
| `$counts` | paper, readiness, qi | {pass, warn, fail, info} verdict counts |
| `$loading` | all | Global fetch-in-flight indicator |

### Security policy (binding)

- **No `innerHTML` with untrusted data.** The dashboard has a `PreToolUse:Write` hook that refuses templates containing that pattern. Datastar's `data-text` escapes by design — use it.
- **Server-side: `datastar-py` SDK sanitises its own output.** Hand-writing raw HTML in `SSE.patch_elements()` is allowed; hand-writing raw HTML strings that inline user-submitted data is not. Run any user input through `html.escape()` before embedding.
- Only `MATCH / RETURN`-style Cypher permitted on `/api/graph/cypher` (already enforced by the server-side regex guard).

### Signal-name-to-camelCase quirk

**Two-part rule (verified 2026-04-24):**

1. **Inside expression bodies**: use `$activePaper` (camelCase). Datastar expressions run as JS, so this is standard identifier matching against the signals declared in `data-signals`.

2. **After the colon in `data-bind:X` / `data-class:X` / `data-attr:X` / `data-signals:X`**: use **kebab-case** (`data-bind:active-paper`). HTML5 parsers lowercase attribute names, so `data-bind:activePaper` becomes `data-bind:activepaper` in the DOM and Datastar binds to a NEW signal `$activepaper`, leaving your declared `$activePaper` stuck at its initial value. Datastar converts `active-paper` → `activePaper` (hyphens→camelCase), so the kebab form correctly resolves to your declared camelCase signal.

```html
<!-- WRONG: DOM lowercases → binds $activepaper, not $activePaper -->
<select data-bind:activePaper data-on:change="@get(`/api/papers/${$activePaper}/x`)">

<!-- RIGHT: hyphens preserved → Datastar camelCases → binds $activePaper -->
<select data-bind:active-paper data-on:change="@get(`/api/papers/${$activePaper}/x`)">
```

Symptom when this is wrong: the URL-embedded signal snapshot on the fetch shows **two** signals (e.g. `"activePaper":"","activepaper":"paper12"`) and the `@get` template-literal expansion produces `/api/papers//provenance` (empty paper id) → 404. Watch the network tab for the signal snapshot in the `?datastar=...` query param.

Server-side when patching signals, use camelCase directly (no kebab conversion):

```python
yield SSE.patch_signals({'activePaper': paper_id})  # camelCase
```

### IDs on every morph target

Datastar's morph finds targets by `id=`. Every top-level element in a morphable region needs an ID; anything with an event listener or CSS transition also needs one or it'll get replaced on morph and lose state.

```html
<!-- WRONG: morph will replace the <details>, losing open state -->
<div id="pp-wrap">
    <details><summary>Blocking</summary>...</details>
</div>

<!-- RIGHT -->
<div id="pp-wrap">
    <details id="pp-blocking" data-preserve-attr="open"><summary>...</summary>...</details>
</div>
```

---

## 7. Migration checklist per tab

For each tab being ported from vanilla JS to Datastar (Wave 9h):

1. **Audit interactivity:** list every fetch, every DOM mutation, every event listener.
2. **Map to signals:** for each piece of state, pick a signal name (shared from §6 table if applicable).
3. **Rewrite HTML:** replace imperative DOM construction with server-rendered markup + `data-*` attrs; inline event handlers via `data-on:click="..."` / `data-on:keydown__key.X`.
4. **Rewrite endpoint:** use `datastar-py` SDK to emit SSE stream; replace JSON responses with `SSE.patch_elements` + `SSE.patch_signals`. Keep a JSON variant if programmatic callers (tests, scripts) need it.
5. **Delete the vanilla-JS block:** target 60%+ LOC reduction per tab.
6. **Playwright smoke test:** verify Datastar attached (document has `data-signals` attributes, fetches fire, filters work, keyboard nav works, deep-link via URL param preselects state).

**Order:** readiness → qi → chains → paper → graph (graph may stay vanilla-wrapped because D3 force-directed sim owns imperative state).

**Status (2026-05-07):** migration complete for **Parameters / Formulas / Proof Architecture / Paper Claims / Citation Registry / Readiness / QI / Chains / Paper Provenance v2 / Bundles** tabs. Only the **Knowledge Graph** tab remains non-Datastar (vanilla-JS + D3, by design — the force-directed simulation owns imperative state and Datastar v1 has no canvas / SVG bridge that would let it manage it idiomatically). Keep this configuration until Datastar v2 ships canvas / SVG bridges.

---

## 8. Gotchas

1. **CDN URL:** only `gh/starfederation/datastar@<tag>/bundles/datastar.js` works on jsdelivr. The `npm/@starfederation/datastar` path 404s.
2. **SSE double-newline:** every event must end with `\n\n`. Forgetting this makes the client silently ignore the event.
3. **Flask response must NOT buffer:** add `X-Accel-Buffering: no` header; if behind nginx/Cloudflare, confirm they honor it.
4. **Signal camelCase:** attribute names collapse hyphens. Signal `$activePaper`, not `$active-paper`.
5. **Cloudflare email-obfuscation:** if a `@` appears in any `href`/`src` attribute that flows through Cloudflare, it may be rewritten to `[email protected]` before the browser receives it. Fix: use direct CDN or drop `@`-tagged paths through your own server. Historical bug from 2026-04-24 session.
6. **Morph IDs:** every top-level morph target needs `id=`. Elements with event listeners / CSS transitions need IDs OR `data-ignore-morph` / `data-preserve-attr`.
7. **`data-show` default-hidden state:** elements starting hidden need `style="display:none"` — Datastar only toggles the property, doesn't set it.
8. **Expression escaping:** inside `data-on:click="..."` expressions, `'` escape is `\\'`. Watch Jinja2 interaction — use `|tojson` filter when injecting Python values.
9. **Signal filter regex:** `filterSignals` uses real JS regex objects; escape `.` and other metachars when filtering namespaced signals.
10. **`@peek()` for non-reactive reads:** inside a reactive expression, use `@peek(() => $foo)` to read `$foo` without re-running the expression when `$foo` changes.

---

## 9. Upstream doc links (read before scope-creep questions)

- Attributes: <https://data-star.dev/reference/attributes>
- Actions: <https://data-star.dev/reference/actions>
- SSE events: <https://data-star.dev/reference/sse_events>
- Security: <https://data-star.dev/reference/security>
- Examples: <https://data-star.dev/examples/>
- Python SDK: <https://github.com/starfederation/datastar-python>
- Getting started: <https://data-star.dev/guide/getting_started>

This reference is frozen at `datastar@v1.0.1` + `datastar-py@0.8.0`. Update the tag + re-check this doc when bumping — and run a full dashboard smoke test (readiness + qi + chains + paper-provenance tabs) because event-name renames have happened and will happen again.

> **Note (2026-05-07).** `pyproject.toml` declares `datastar-py>=0.5` (lower bound), so the *resolved* version locally floats. The pin in this doc is the *target / verified-tested* version; if you bump the lower bound or the resolved version drifts away from `0.8.0`, re-run §7's smoke checklist before treating the new combination as stable.

---

## 10. Wave 9h closing note _(2026-05-07)_

Datastar adoption is complete across the Parameters / Formulas / Proof Architecture / Paper Claims / Citation Registry tabs (Phase 5v Wave 9h closed) and has since been carried forward to the Readiness, QI, Chains, Paper Provenance v2, and Bundles tabs added in Phase 5v Waves 4–10 and Phase 6i Wave 7.5.

The **Knowledge Graph** tab remains vanilla-JS-wrapped: the D3 force-directed simulation owns imperative state (per-tick node positions, drag offsets, alpha decay), and Datastar v1 doesn't yet expose the canvas / SVG bridges that would let it idiomatically host that mutation pattern. Keep this arrangement — don't try to retrofit Datastar onto the KG tab — until Datastar v2 ships those bridges. The `data-*` ↔ D3 boundary is documented in §1 ("Signal access from vanilla JS") and §6 ("IDs on every morph target") above.
