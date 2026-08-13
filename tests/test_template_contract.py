"""Template contract gate for the provenance dashboard (ADR-012 P9a, Task 7).

⚠️ **THIS GATE IS NECESSARY AND NOT SUFFICIENT.**

A Flask ``test_client`` never executes page JavaScript. Every panel on this dashboard that
matters — the readiness heatmap, the QI item list, the paper-provenance sentence stream, the
knowledge graph — is populated over **Datastar SSE** after load, by JS this gate cannot run.
So a green run here proves the *server-side* half only: that the template compiled, that every
variable it dereferences was actually passed, and that the tab's panel container was emitted
and marked active. **It does not prove any panel renders content.** Reading a pass here as
"the panel renders" is precisely the inference this file exists to make impossible.

The other half of the gate is ``tests/e2e/`` (Playwright, ``-m e2e``), which boots the real
dashboard and executes the JS. **Both are required** — ADR-012 D2. Neither substitutes for
the other: this one catches an undeclared template variable that the browser test would
silently render as an empty panel; the browser test catches an empty panel that this one
would silently render as a 200.

What it actually asserts
------------------------
1. **Variable coverage.** ``jinja2.meta.find_undeclared_variables`` over ``dashboard.html``
   and every partial, minus the names the template assigns itself (``{% set %}``/``{% for %}``/
   ``{% with %}``/``{% macro %}``), must be covered by the kwargs the single ``render_template``
   call site passes, plus the app's context-processor injections, plus Jinja/Flask globals.
   Because the app leaves Jinja's default ``Undefined`` (not ``StrictUndefined``), an
   uncovered name is *silent* at runtime — it renders as empty string and the request still
   returns 200.
2. **Tab reachability.** Every ``?tab=`` value the application's own nav emits is driven
   through ``app.test_client()`` and must return 200 with **its own** panel container marked
   active and **no other tab's** panel active.

Anti-vacuity
------------
This repo's signature defect is absence rendered as success. Every population this file
scans — templates, template variables, tabs, partial markers — is floored, and a scan that
finds zero (or fewer than the floor) **fails as unverified** rather than passing over nothing.
The floors are down-only ratchets: lower one only with a stated reason.

The rosters are **derived**, never hand-written: templates come from the templates directory,
the tab list comes from the nav links in ``dashboard.html``, the panel sentinel for each tab
comes from that tab's own block in ``dashboard.html``, and the per-partial marker comes from
the partial's own ``<style>`` block.

Per ``docs/architecture/CHECK_AUTHORING_GUIDE.md`` §2.5 the assertions target the **decider**:
the panel ``<div>``'s ``active`` class as emitted by the server, not a substring proxy such as
``"Blockers" in html``.
"""

from __future__ import annotations

import ast
import re
import sys
from pathlib import Path

import pytest
from jinja2 import meta, nodes

PROJECT_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS_DIR = PROJECT_ROOT / "scripts"
TEMPLATE_DIR = SCRIPTS_DIR / "templates"
DASHBOARD_PY = SCRIPTS_DIR / "provenance_dashboard.py"

for _p in (str(PROJECT_ROOT), str(SCRIPTS_DIR)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

# ── Down-only population floors ────────────────────────────────────────────────────────
# Measured 2026-08-12 on this tree. A scan that drops below one of these has rotted (a
# renamed directory, a narrowed regex, a partial that stopped being found) and must fail as
# UNVERIFIED, not pass over a shrunken population. Raising a floor after adding a template /
# tab is routine; lowering one requires a stated reason in the commit.
TEMPLATE_FLOOR = 7          # dashboard.html + 6 partials
PARTIAL_FLOOR = 6           # partials/*.html
NAV_TAB_FLOOR = 10          # distinct ?tab= values in dashboard.html's nav
REQUIRED_VAR_FLOOR = 14     # template variables the server must supply
PANEL_BLOCK_FLOOR = 10      # comment-anchored tab-content blocks reachable from the nav


# ══════════════════════════════════════════════════════════════════════════════════════
# Derivation helpers — every roster below comes from the application, never a hand list
# ══════════════════════════════════════════════════════════════════════════════════════

def _template_files() -> list[Path]:
    """Every Jinja template on disk, dashboard.html first."""
    return sorted(TEMPLATE_DIR.rglob("*.html"))


def _assigned_names(node: nodes.Node) -> set[str]:
    """Names a template binds for itself: ``{% set %}``, ``{% for %}``, ``{% with %}``,
    ``{% macro %}``, ``{% import %}``.

    ⚠️ Load-bearing. ``find_undeclared_variables`` conservatively reports a ``{% set %}``
    made *inside a loop body* as undeclared, because the loop frame resolves its symbols
    from the parent frame on entry. ``dashboard.html:879`` (``{% set ppct = ... %}`` inside
    ``{% for p in papers %}``) is exactly that shape and is **not** a defect — the assignment
    executes before the read in the same iteration. Subtracting template-bound names removes
    that false positive without weakening the real check: a name the template never binds and
    the server never passes is still reported (see the seeded negative control below).
    """
    def _targets(t) -> set[str]:
        if isinstance(t, nodes.Name):
            return {t.name}
        if isinstance(t, nodes.NSRef):
            return {t.name}
        if isinstance(t, (nodes.Tuple, nodes.List)):
            out: set[str] = set()
            for item in t.items:
                out |= _targets(item)
            return out
        return set()

    found: set[str] = set()
    for n in node.find_all((nodes.Assign, nodes.AssignBlock, nodes.For, nodes.With,
                            nodes.Macro, nodes.Import, nodes.FromImport)):
        if isinstance(n, (nodes.Assign, nodes.AssignBlock, nodes.For)):
            found |= _targets(n.target)
        elif isinstance(n, nodes.With):
            for t in n.targets:
                found |= _targets(t)
        elif isinstance(n, nodes.Macro):
            found.add(n.name)
            for a in n.args:
                found |= _targets(a)
        elif isinstance(n, nodes.Import):
            if isinstance(n.target, str):
                found.add(n.target)
        elif isinstance(n, nodes.FromImport):
            for nm in n.names:
                found.add(nm[1] if isinstance(nm, tuple) else nm)
    return found


def _scan_sources(env, sources: dict[str, str]) -> dict[str, dict[str, set[str]]]:
    """{name: {'undeclared', 'assigned', 'required'}} for each template source."""
    out: dict[str, dict[str, set[str]]] = {}
    for name, src in sources.items():
        parsed = env.parse(src)
        undeclared = set(meta.find_undeclared_variables(parsed))
        assigned = _assigned_names(parsed)
        out[name] = {
            "undeclared": undeclared,
            "assigned": assigned,
            "required": undeclared - assigned,
        }
    return out


def _render_template_kwargs() -> tuple[set[str], int]:
    """The kwargs the view passes, via ``ast`` over the dashboard source.

    Returns ``(kwargs, n_call_sites)``. Read via AST rather than a substring scan
    (CHECK_AUTHORING_GUIDE §2.5): the string ``render_template`` also appears in a comment
    at ``provenance_dashboard.py:1152``, so a text scan would locate the wrong thing.
    """
    tree = ast.parse(DASHBOARD_PY.read_text(encoding="utf-8"))
    calls = [
        c for c in ast.walk(tree)
        if isinstance(c, ast.Call)
        and ((isinstance(c.func, ast.Name) and c.func.id == "render_template")
             or (isinstance(c.func, ast.Attribute) and c.func.attr == "render_template"))
    ]
    kwargs: set[str] = set()
    for c in calls:
        kwargs |= {k.arg for k in c.keywords if k.arg}
    return kwargs, len(calls)


def _nav_tabs(dashboard_src: str) -> list[str]:
    """The tab roster, derived from the nav links the application itself renders."""
    nav = re.search(r'<div class="tabs">(.*?)</div>', dashboard_src, re.S)
    assert nav, "the nav block <div class=\"tabs\"> vanished from dashboard.html — " \
                "the tab roster cannot be derived, so this gate is UNVERIFIED"
    seen: list[str] = []
    for t in re.findall(r'href="\?tab=([A-Za-z_][\w-]*)', nav.group(1)):
        if t not in seen:
            seen.append(t)
    return seen


# Each tab's panel is preceded in dashboard.html by a banner comment, then either
#   <!-- ═══ X TAB ═══ -->  {% if tab == 'x' %} <div class="tab-content active">   (partial)
# or
#   <!-- ═══ X TAB ═══ -->  <div class="tab-content {% if tab == 'x' %}active{% endif %}">
# The rendered ``active`` class on that div is the server's decision about which tab is
# showing — i.e. the decider, not a proxy.
_PANEL_RE = re.compile(
    r'(?P<raw><!--\s*═+[^>]*?═+\s*-->)\s*'
    r"(?:\{%\s*if\s+tab\s*==\s*'(?P<iftab>\w+)'\s*%\}\s*)?"
    r'<div class="tab-content(?P<cls>[^"]*)"',
    re.S,
)


def _panel_blocks(dashboard_src: str) -> dict[str, str]:
    """{tab: the exact HTML comment that anchors its panel}."""
    out: dict[str, str] = {}
    for m in _PANEL_RE.finditer(dashboard_src):
        tab = m.group("iftab")
        if not tab:
            inline = re.search(r"tab\s*==\s*'(\w+)'", m.group("cls"))
            tab = inline.group(1) if inline else None
        if tab:
            out[tab] = m.group("raw")
    return out


def _panel_class(html: str, anchor_comment: str) -> str | None:
    """The class attribute of the ``tab-content`` div immediately after ``anchor_comment``
    in a *rendered* page, or ``None`` when no such div was emitted."""
    idx = html.find(anchor_comment)
    if idx < 0:
        return None
    tail = html[idx + len(anchor_comment): idx + len(anchor_comment) + 400]
    m = re.match(r'\s*<div class="(?P<c>tab-content[^"]*)"', tail)
    return m.group("c") if m else None


def _partial_markers() -> dict[str, str]:
    """{partial filename: a CSS class selector it defines unconditionally in its <style>}.

    Derived from the partial's own source. A ``<style>`` rule sits at the partial's top level,
    outside every ``{% if %}``, so it is emitted whenever the include runs — which makes it a
    marker that discriminates *this* partial from every other one.
    """
    out: dict[str, str] = {}
    for p in sorted((TEMPLATE_DIR / "partials").glob("*.html")):
        style = re.search(r"<style>(.*?)</style>", p.read_text(encoding="utf-8"), re.S)
        if not style:
            continue
        sels = re.findall(r"^\s*(\.[A-Za-z][\w-]*)", style.group(1), re.M)
        if sels:
            out[p.name] = sels[0]
    return out


def _tab_to_partial(dashboard_src: str) -> dict[str, str]:
    """{tab: partial filename} for the tabs whose panel is an ``{% include %}``."""
    out: dict[str, str] = {}
    for m in re.finditer(
        r"\{%\s*if\s+tab\s*==\s*'(?P<tab>\w+)'\s*%\}(?P<body>.*?)\{%\s*endif\s*%\}",
        dashboard_src, re.S,
    ):
        inc = re.search(r"\{%\s*include\s*'partials/(?P<f>[\w.]+)'\s*%\}", m.group("body"))
        if inc:
            out[m.group("tab")] = inc.group("f")
    return out


# ══════════════════════════════════════════════════════════════════════════════════════
# Fixtures
# ══════════════════════════════════════════════════════════════════════════════════════

@pytest.fixture(scope="module")
def dash():
    """The real dashboard module (and therefore the real Flask app)."""
    import provenance_dashboard
    return provenance_dashboard


@pytest.fixture(scope="module")
def dashboard_src() -> str:
    return (TEMPLATE_DIR / "dashboard.html").read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def scan(dash) -> dict[str, dict[str, set[str]]]:
    sources = {
        str(p.relative_to(TEMPLATE_DIR)): p.read_text(encoding="utf-8")
        for p in _template_files()
    }
    return _scan_sources(dash.app.jinja_env, sources)


@pytest.fixture(scope="module")
def provided(dash) -> set[str]:
    """Every name a template may legally dereference: the view's kwargs, the app's
    context-processor injections, and the Jinja/Flask globals."""
    kwargs, n_sites = _render_template_kwargs()
    assert n_sites == 1, (
        f"expected exactly ONE render_template call site in {DASHBOARD_PY.name}, found "
        f"{n_sites}. This gate unions the kwargs of every site, which is only sound while "
        f"there is one — with two routes, a name supplied by only one of them would be "
        f"wrongly treated as provided for both. Split this check per route before merging."
    )
    app = dash.app
    injections: set[str] = set()
    processors = app.template_context_processors[None]
    assert processors, "no context processors registered — GATE_DEFS/PP_PAPERS_LIST would " \
                       "be undefined at render time and this gate is UNVERIFIED"
    with app.test_request_context("/"):
        for proc in processors:
            injections |= set(proc())
    return kwargs | injections | set(app.jinja_env.globals)


@pytest.fixture(scope="module")
def rendered(dash, dashboard_src) -> dict[str, tuple[int, str]]:
    """{tab: (status_code, html)} for every tab the nav offers.

    One pass, module-scoped: the first request warms the dashboard's mtime-fingerprinted
    graph cache and the bundles tab loads its summary, so this is the slow part of the file.
    """
    client = dash.app.test_client()
    out: dict[str, tuple[int, str]] = {}
    for tab in _nav_tabs(dashboard_src):
        resp = client.get(f"/?tab={tab}")
        out[tab] = (resp.status_code, resp.get_data(as_text=True))
    return out


# ══════════════════════════════════════════════════════════════════════════════════════
# Population guards — an empty scan is a FAILURE, never a pass
# ══════════════════════════════════════════════════════════════════════════════════════

def test_the_template_population_is_non_empty_and_at_its_floor():
    """A scan that found no templates has not verified anything."""
    files = _template_files()
    assert files, f"no templates found under {TEMPLATE_DIR} — UNVERIFIED, not clean"
    assert len(files) >= TEMPLATE_FLOOR, (
        f"template population shrank to {len(files)} (floor {TEMPLATE_FLOOR}): "
        f"{[str(f.relative_to(TEMPLATE_DIR)) for f in files]}"
    )
    names = {str(f.relative_to(TEMPLATE_DIR)) for f in files}
    assert "dashboard.html" in names
    partials = {n for n in names if n.startswith("partials/")}
    assert len(partials) >= PARTIAL_FLOOR, (
        f"only {len(partials)} partials found (floor {PARTIAL_FLOOR}): {sorted(partials)}"
    )


def test_every_partial_the_dashboard_includes_is_actually_scanned(dashboard_src, scan):
    """The seam is the existence check, not the walk (CHECK_AUTHORING_GUIDE §2.5). A partial
    that is included but not on disk, or on disk but missed by the walk, would leave its
    variables unchecked while this file reported a clean bill."""
    included = set(re.findall(r"\{%\s*include\s*'(partials/[\w.]+)'\s*%\}", dashboard_src))
    assert included, "dashboard.html includes no partials — the include scan has rotted"
    for name in sorted(included):
        assert (TEMPLATE_DIR / name).exists(), f"{name} is included but absent from disk"
        assert name in scan, f"{name} is included but was not scanned"


def test_the_variable_population_is_non_empty_and_at_its_floor(scan):
    required = set().union(*(v["required"] for v in scan.values()))
    assert required, (
        "the Jinja analysis found ZERO template variables. That is not a clean contract, it "
        "is a broken scan — fail as UNVERIFIED."
    )
    assert len(required) >= REQUIRED_VAR_FLOOR, (
        f"only {len(required)} template variables found (floor {REQUIRED_VAR_FLOOR}): "
        f"{sorted(required)} — the parse or the walk has narrowed"
    )
    # Sanity: the names the view demonstrably passes must be among them, or the analysis is
    # looking at the wrong thing entirely.
    for anchor in ("tab", "summary", "params"):
        assert anchor in required, f"{anchor!r} missing from the analysed variable set"


def test_the_tab_roster_is_derived_and_non_empty(dashboard_src):
    tabs = _nav_tabs(dashboard_src)
    assert tabs, "no ?tab= links found in the nav — the roster is UNVERIFIED"
    assert len(tabs) >= NAV_TAB_FLOOR, (
        f"nav offers only {len(tabs)} tabs (floor {NAV_TAB_FLOOR}): {tabs}"
    )
    panels = _panel_blocks(dashboard_src)
    assert len(panels) >= PANEL_BLOCK_FLOOR, (
        f"only {len(panels)} comment-anchored panel blocks found (floor "
        f"{PANEL_BLOCK_FLOOR}): {sorted(panels)}"
    )
    missing = [t for t in tabs if t not in panels]
    assert not missing, f"nav offers tabs with no panel block in dashboard.html: {missing}"


# ══════════════════════════════════════════════════════════════════════════════════════
# 1. Variable coverage
# ══════════════════════════════════════════════════════════════════════════════════════

def test_every_template_variable_is_provided_by_the_server(scan, provided):
    """⚠️ THE DEFECT THIS GATE EXISTS FOR.

    The app leaves Jinja's default ``Undefined`` rather than ``StrictUndefined``, so a
    template that dereferences a key the server never passes renders an **empty panel** and
    still returns 200. Nothing else in the suite drives a template at all, so that failure is
    invisible everywhere else.
    """
    drift: dict[str, list[str]] = {}
    for name, info in sorted(scan.items()):
        missing = sorted(info["required"] - provided)
        if missing:
            drift[name] = missing
    assert not drift, (
        "template variables no one provides (they render as empty string, silently):\n"
        + "\n".join(f"  {n}: {v}" for n, v in drift.items())
        + "\nEither pass them from index()'s render_template call / a context processor, "
          "or stop dereferencing them."
    )


def test_the_gate_catches_a_seeded_undeclared_variable(dash, provided):
    """Negative control — proof the check above can go red.

    Runs the *same* analyser over a copy of ``dashboard.html`` carrying one variable the
    server does not pass. If this ever stops reporting the seeded name, the coverage test
    above is passing vacuously and must not be trusted.
    """
    seeded = "zz_seeded_variable_no_route_passes"
    src = (TEMPLATE_DIR / "dashboard.html").read_text(encoding="utf-8")
    mutated = src.replace("<div class=\"tabs\">",
                          "<div class=\"tabs\">{{ " + seeded + " }}", 1)
    assert mutated != src, "could not seed the mutant — the anchor moved; fix this control"

    clean = _scan_sources(dash.app.jinja_env, {"dashboard.html": src})
    dirty = _scan_sources(dash.app.jinja_env, {"dashboard.html": mutated})

    assert seeded not in clean["dashboard.html"]["required"]
    assert seeded in dirty["dashboard.html"]["required"], (
        "the analyser did not see a variable that is plainly undeclared — it cannot be "
        "relied on to see a real one"
    )
    assert seeded in (dirty["dashboard.html"]["required"] - provided), (
        "the seeded variable was treated as provided; the coverage assertion is vacuous"
    )


def test_a_template_bound_name_is_not_reported_as_server_drift(scan):
    """The complement of the control above: ``{% set %}`` inside a ``{% for %}`` body is a
    known false positive of ``find_undeclared_variables`` and must not be reported as a
    server obligation, or this gate would cry wolf and get switched off.

    ``dashboard.html`` sets ``ppct`` inside ``{% for p in papers %}`` and reads it two lines
    later; that is correct code.
    """
    dash_scan = scan["dashboard.html"]
    assert dash_scan["assigned"], "no template-bound names found — the assignment walk rotted"
    overlap = dash_scan["undeclared"] & dash_scan["assigned"]
    assert overlap, (
        "no loop-scoped {% set %} false positive observed. If dashboard.html genuinely no "
        "longer has one this assertion should be retired deliberately — but while it holds "
        "it is what proves the subtraction is doing work rather than hiding a real gap."
    )
    assert not (overlap & dash_scan["required"])


# ══════════════════════════════════════════════════════════════════════════════════════
# 2. Tab reachability — app.test_client() over every ?tab= value
# ══════════════════════════════════════════════════════════════════════════════════════

def test_the_render_population_is_non_empty(rendered):
    assert rendered, "no tabs were rendered — UNVERIFIED"
    assert len(rendered) >= NAV_TAB_FLOOR


def test_each_tab_returns_200_with_its_own_panel_active(rendered, dashboard_src):
    """The decider is the ``active`` class the server puts on that tab's ``tab-content`` div,
    anchored to that tab's own banner comment — not a substring like ``'Blockers' in html``,
    which would pass on any page that happens to contain the word.

    ⚠️ A 200 here says the template compiled and the container was emitted. It says nothing
    about the panel having content: everything inside these containers arrives over SSE.
    """
    panels = _panel_blocks(dashboard_src)
    failures: list[str] = []
    for tab, (status, html) in sorted(rendered.items()):
        if status != 200:
            failures.append(f"{tab}: HTTP {status}")
            continue
        if len(html) < 1000:
            failures.append(f"{tab}: response only {len(html)} bytes — suspiciously empty")
        cls = _panel_class(html, panels[tab])
        if cls is None:
            failures.append(f"{tab}: its tab-content panel was not emitted at all")
        elif "active" not in cls:
            failures.append(f"{tab}: panel emitted but not active (class={cls!r})")
    assert not failures, "tab render failures:\n  " + "\n  ".join(failures)


def test_exactly_one_panel_is_active_per_request(rendered, dashboard_src):
    """Discrimination check. If every panel were always active the assertion above would pass
    for the wrong reason, which is the vacuous-scan failure mode in template form."""
    panels = _panel_blocks(dashboard_src)
    for tab, (status, html) in sorted(rendered.items()):
        assert status == 200, f"{tab}: HTTP {status}"
        active = [t for t, anchor in panels.items()
                  if (c := _panel_class(html, anchor)) and "active" in c]
        assert active == [tab], (
            f"?tab={tab} activated {active!r}; exactly [{tab!r}] was expected"
        )


def test_a_partial_backed_tab_carries_its_own_partials_marker(rendered, dashboard_src):
    """Each ``{% include %}``-backed tab must carry a marker unique to its partial, and must
    NOT carry another partial's marker. Proves the include actually ran for that tab rather
    than the shell rendering with an empty body."""
    tab_partial = _tab_to_partial(dashboard_src)
    markers = _partial_markers()
    assert tab_partial, "no include-backed tabs found — the include scan has rotted"
    assert len(markers) >= PARTIAL_FLOOR, (
        f"only {len(markers)} partial markers derivable (floor {PARTIAL_FLOOR}): {markers}"
    )
    checked = 0
    for tab, partial in sorted(tab_partial.items()):
        marker = markers.get(partial)
        assert marker, f"no <style> marker derivable from {partial}"
        status, html = rendered[tab]
        assert status == 200
        assert marker in html, f"?tab={tab} did not render {partial} (marker {marker})"
        # …and the marker discriminates: some other tab must not carry it.
        others = [t for t in tab_partial if t != tab]
        assert others, "need at least two include-backed tabs to prove discrimination"
        control = others[0]
        assert marker not in rendered[control][1], (
            f"marker {marker} for {partial} also appears on ?tab={control} — it is boilerplate, "
            f"not a sentinel, so the assertion above proves nothing"
        )
        checked += 1
    assert checked >= PARTIAL_FLOOR, f"only {checked} include-backed tabs verified"


def test_the_default_tab_matches_the_servers_own_default(dash, dashboard_src):
    """``/`` with no query string must land on the same panel as the explicit default."""
    default = re.search(r"request\.args\.get\('tab',\s*'(\w+)'\)",
                        DASHBOARD_PY.read_text(encoding="utf-8"))
    assert default, "could not derive index()'s default tab — UNVERIFIED"
    panels = _panel_blocks(dashboard_src)
    resp = dash.app.test_client().get("/")
    assert resp.status_code == 200
    cls = _panel_class(resp.get_data(as_text=True), panels[default.group(1)])
    assert cls and "active" in cls, (
        f"/ did not activate the declared default tab {default.group(1)!r} (class={cls!r})"
    )


def test_the_retired_papers_tab_still_redirects(dash):
    """``?tab=papers`` was retired in Wave 10g and 302s to ``?tab=paper``. Pinned because the
    template still carries a ``{% if tab == 'papers' %}`` block that this redirect makes
    unreachable — if the redirect is ever removed, that dead block silently comes back to
    life as the rendered panel."""
    resp = dash.app.test_client().get("/?tab=papers")
    assert resp.status_code == 302
    assert resp.headers["Location"].startswith("/?tab=paper")
