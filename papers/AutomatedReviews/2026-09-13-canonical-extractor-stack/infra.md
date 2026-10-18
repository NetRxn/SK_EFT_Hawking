---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: Codex root with independent growth_review diagnosis
review_date: 2026-09-13T05:14:00Z
kind: targeted-infra
---

# Canonical extraction aborts before refreshing the inventory

### 1.1 — REQUIRED — canonical extractor reproducibly aborts with stack overflow

- **Severity:** required
- **Lane:** `infra`
- **Verify:** `python3 scripts/extract_lean_deps.py`
- **Gate:** Lean
- **Location:** `scripts/extract_lean_deps.py:161`; runtime path through `lean/SKEFTHawking/ExtractDeps.lean`
- **Observed:** At aggregate commit `2e05f917d84e8b3e5cd5ae07563a30598816dd75`, the authoritative build succeeds but two unchanged canonical extraction runs abort with `Stack overflow detected. Aborting.` The canonical inventory therefore remains the prior accepted inventory. No fresh count or current-cycle acceptance is established.
- **Evidence:** Original local logs `round19-public-extraction.log` and `round19-public-extraction-retry.log` in the root continuity directory; independent read-only assessment `round19-extractor-diagnosis.md`. Original caches also parse through the matching Lean MCP. The guarded canonical-entry phase probe returns 134 after `immref-array-built` and before the rendered-string marker, isolating failure to the original whole-cache pretty serialization. Its complete child result and stderr are retained in `round19-extractor-save-phase-result.json` and `round19-extractor-save-phase-stderr.txt`; primary canonical, hash and cache bytes are unchanged. The diagnostic is not a canonical refresh.
- **Required correction:** Localize the failure while preserving the exact input caches, pins and proof sources; apply the smallest justified repair through the existing extraction path. Retain single-writer locking, complete axiom/dependency coverage and cold/warm result equivalence. Validate a fresh canonical inventory against the accepted baseline; do not substitute stale counts or filter out failing declarations.
- **Acceptance:** Independent review of the localized repair and original execution evidence, successful authoritative extraction, ordinary-axiom and prior-record reconciliation, and closure through the existing finding writer. No repair has been implemented at filing.
