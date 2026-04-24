"""Flask ↔ Datastar glue.

datastar-py 0.8.0 does not ship a Flask submodule (first-class support is
Quart / FastAPI / FastHTML / Litestar / Sanic / Starlette / Django). This
module provides the missing pieces so the dashboard endpoints can
auto-negotiate between SSE (Datastar) and JSON (tests, scripts) without
duplicating routes.

Reference: docs/references/Datastar_Dashboard_Reference.md §5
"""
from __future__ import annotations

import html
import json
from collections.abc import Callable, Iterable, Iterator
from typing import Any

from flask import Response, request

from datastar_py import ServerSentEventGenerator as SSE

__all__ = [
    "SSE",
    "is_datastar_request",
    "read_signals",
    "sse_response",
    "esc",
]


def is_datastar_request() -> bool:
    """True when the client is a Datastar fetch (wants SSE).

    Datastar fetch actions (@get/@post/...) send `Accept: text/event-stream`.
    Plain `curl`, `pytest`, browser reloads without the library, etc. get JSON.
    """
    return "text/event-stream" in request.headers.get("Accept", "")


def read_signals() -> dict[str, Any]:
    """Read the Datastar signal snapshot that every fetch carries.

    For GET: signals are JSON-encoded in the `datastar` query param.
    For POST/PUT/PATCH/DELETE: signals are the JSON request body.

    Returns an empty dict on parse failure — the endpoint then falls back
    to server-side defaults rather than 400-ing.
    """
    if request.method == "GET":
        raw = request.args.get("datastar", "{}")
    else:
        raw = request.get_data(as_text=True) or "{}"
    try:
        data = json.loads(raw)
    except json.JSONDecodeError:
        return {}
    return data if isinstance(data, dict) else {}


def sse_response(
    generator: Callable[[], Iterable[Any]] | Iterator[Any],
) -> Response:
    """Wrap a generator of DatastarEvent in a Flask streaming Response.

    The generator yields `SSE.patch_elements(...)` / `SSE.patch_signals(...)`
    values, each of which is already a complete SSE event terminated with
    `\\n\\n`. We str()-ify them for the wire. Headers prevent buffering by
    proxies and browsers so the client sees each event as it fires.
    """
    def stream():
        it = generator() if callable(generator) else generator
        for event in it:
            yield str(event)

    return Response(
        stream(),
        mimetype="text/event-stream",
        headers={
            "Cache-Control": "no-cache",
            "X-Accel-Buffering": "no",
            "Connection": "keep-alive",
        },
    )


def esc(value: Any) -> str:
    """HTML-escape any value before embedding in a `patch_elements` fragment.

    SDK output is NOT auto-escaped when we hand-build HTML strings —
    Datastar's own `data-text` attribute handles escaping for client-side
    signal rendering, but any server-rendered HTML that interpolates
    user-facing strings (paper titles, claim quotes, notes) MUST go
    through this helper. The security hook in the repo rejects templates
    that interpolate without escaping.
    """
    if value is None:
        return ""
    return html.escape(str(value), quote=True)
