"""Test-only real dashboard startup with independent disposable artifact roots."""
from __future__ import annotations

import json
import faulthandler
import importlib
import time
import os
from pathlib import Path
import signal
import sys


def paper_fixture_audit(project, root, record, save):
    """Refuse paper reads outside the disposable root before the actual open."""
    family = {"paper_draft.tex", "claims_review.json", "figure_review_report.json",
              "prose_state.json", "audit_log.jsonl"}
    corpus = project.resolve() / "papers"
    papers = root.resolve() / "papers"

    def audit(event, args):
        if event != "open" or not args or not isinstance(args[0], (str, bytes, os.PathLike)):
            return
        lexical = Path(os.fsdecode(args[0]))
        mode = args[1] if len(args) > 1 else None
        reading = mode is None or isinstance(mode, str) and ("r" in mode or "+" in mode)
        resolved = None
        reason = None
        if not lexical.is_absolute():
            # Python's audit event omits dir_fd; cwd is not an established base.
            if reading and (lexical.name in family or "papers" in lexical.parts):
                reason = "ambiguous_relative_paper_open"
        else:
            lexical = Path(os.path.abspath(lexical))
            resolved = lexical.resolve()
            if lexical.is_relative_to(corpus) or resolved.is_relative_to(corpus):
                reason = "real_corpus_origin_or_target"
            elif (reading and (lexical.name in family or resolved.name in family)
                  and not resolved.is_relative_to(papers)):
                reason = "escaped_paper_artifact"
        if reason is not None:
            record["violations"].append({"lexical": str(lexical),
                                         "resolved": str(resolved) if resolved is not None else None,
                                         "reason": reason})
            save()
            raise AssertionError(f"Dummy paper fixture refused: {reason}")

    return audit


def main() -> None:
    project = Path(__file__).resolve().parents[2]
    root = Path(sys.argv[1]).resolve()
    port = int(sys.argv[2])
    stacks = (root / "server-stacks.log").open("w")
    faulthandler.enable(file=stacks)
    faulthandler.dump_traceback_later(15, repeat=True, file=stacks)
    observations = root / "server-observations.json"
    record = {"violations": [], "db_connect_attempts": 0}

    def save():
        observations.write_text(json.dumps(record, indent=2) + "\n")

    sys.addaudithook(paper_fixture_audit(project, root, record, save))
    sys.path[:0] = [str(project / "scripts"), str(project)]
    os.environ["SK_EFT_GRAPH_SOURCE"] = "json"
    os.environ.pop("SK_EFT_DASHBOARD_READ_DSN", None)
    import provenance_dashboard as dashboard
    import build_graph
    import readiness_gates
    import sentence_state
    import sentence_findings
    import verification_state
    import psycopg

    for module in (dashboard, build_graph, readiness_gates, sentence_state, sentence_findings):
        module.PROJECT_ROOT = root
    build_graph.LEAN_DIR = root / "lean" / "SKEFTHawking"
    readiness_gates.PAPERS_DIR = root / "papers"
    sentence_state.PAPERS_ROOT = root / "papers"
    verification_state.LOG_PATH = root / "docs" / "verification_log.jsonl"
    verification_state.LOCK_PATH = root / "docs" / "verification_log.lock"

    # Reuse the whole-template fixture's import-bound path isolation before
    # CLI prewarm or any request. These are real readers over synthetic files.
    for name in ("dashboard_flow", "bundle_readiness", "check_bundle_source_freshness",
                 "bundle_migration", "dashboard_attention", "dashboard_loops", "datastar_bundles",
                 "qi_register", "extract_lean_deps", "scripts.extract_lean_deps",
                 "atlas_view"):
        module = importlib.import_module(name)
        for attr, value in list(vars(module).items()):
            if isinstance(value, Path) and value.is_relative_to(project):
                target = root / value.relative_to(project)
                setattr(module, attr, target)
                record.setdefault("bindings", []).append({"module": name, "name": attr,
                    "source": str(value), "target": str(target)})
    dashboard.app.config["PG_SYNC_ENABLED"] = False

    def forbidden_connect(*args, **kwargs):
        record["db_connect_attempts"] += 1
        save()
        raise AssertionError("Database access forbidden in dummy browser fixture")

    psycopg.connect = forbidden_connect
    from flask import request
    from werkzeug.serving import WSGIRequestHandler

    class DiagnosticHandler(WSGIRequestHandler):
        def parse_request(self):
            result = super().parse_request()
            record.setdefault("http_parsed", []).append({"method": self.command,
                "path": self.path, "version": self.request_version,
                "content_length": self.headers.get("Content-Length"),
                "transfer_encoding": self.headers.get("Transfer-Encoding"),
                "client": list(self.client_address), "at": time.monotonic()})
            save()
            return result

        def finish(self):
            record.setdefault("http_finished", []).append({
                "client": list(self.client_address), "at": time.monotonic()})
            save()
            return super().finish()


    @dashboard.app.before_request
    def observe_request_start():
        record.setdefault("request_started", []).append({"method": request.method,
            "path": request.path, "at": time.monotonic()})
        save()

    @dashboard.app.after_request
    def observe_paper_request(response):
        if response.mimetype == "text/event-stream":
            record.setdefault("sse_responses", []).append({"path": request.path,
                "status": response.status_code, "headers": dict(response.headers)})
            save()
        if request.path.startswith("/api/papers/"):
            record.setdefault("paper_requests", []).append({
                "method": request.method, "path": request.path,
                "query": request.query_string.decode(),
                "json": request.get_json(silent=True), "status": response.status_code,
            })
            save()
        return response

    original_run = dashboard.app.run

    def observed_run(*args, **kwargs):
        record["PG_SYNC_ENABLED"] = dashboard.app.config.get("PG_SYNC_ENABLED")
        record["graph_source"] = dashboard._graph_source()
        assert record["PG_SYNC_ENABLED"] is False and record["graph_source"] == "json"
        save()
        return original_run(*args, request_handler=DiagnosticHandler, **kwargs)

    dashboard.app.run = observed_run
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(0))
    sys.argv = [str(project / "scripts" / "provenance_dashboard.py"),
                "--port", str(port), "--no-browser", "--no-pg-sync"]
    try:
        dashboard.main()
    finally:
        faulthandler.cancel_dump_traceback_later()
        record["server_exit"] = True
        save()


if __name__ == "__main__":
    main()
