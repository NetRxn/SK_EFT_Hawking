# Canonical declaration corpus remote delivery

ROOT observed the real remote rejection after independently accepted native/canonical review. Owner ROOT accepts remediation; existing architecture-change process applies before any writer/storage change. No source/physics weakening or deferral is authorized.

### 1.1 — Canonical declaration blob exceeds the remote Git limit

- **Severity:** major
- **Lane:** infra
- **Gate:** `FixPropagation`
- **Location:** `lean/lean_deps.json`, `scripts/extract_lean_deps.py`, existing Git/canonical artifact delivery
- **Observed:** Normal push of25b5f229c was rejected by GitHub GH001:105862394byte blob exceeds104857600bytes. All54298declarations and six canonical derivatives are independently accepted; no scientific defect or missing substrate follows. Source/native4672e9fec remains pushed. Exact derivative commit is preserved as ORIGINAL_EQ10_CANONICAL_CORPUS_R1.bundle, not normally integrated remotely.
- **Expected:** Deliver the complete same-value canonical corpus through supported remote/clone/CI/cloud workflows and preserve current readers, freshness, complete type/axiom/dependency/provenance data and independent review. Main integration remains qualified separately.
- **Fix:** Reconcile existing architecture/storage/clone authority first, then specify/review the smallest durable compatible storage or serialization correction. Current serializer already writes compact one-record-per-line JSON. UTF8pilot preserves every parsed value but only76729bytesheadroom; it is not an accepted durable resolution. Do not truncate declarations/fields, silently freeze stale data, weaken gates or introduce a parallel registry. Test actual affected consumers and remote readback.
- **Evidence:** ORIGINAL_TASK2_FULL_SCIENCE_ADMISSION_R1.md and its exact recovery bundle; canonical generated review and actual size pilot in ORIGINAL_EQ10_CORPUS_AND_FULL_RUN_ADMISSION_R1_EVIDENCE.zip. The Verify below is a delivery-size/local-readable-shape control only; closure additionally requires independent full-corpus conservation, supported-checkout validation and actual remote push/readback.
- **Verify:** `uv run python -c 'import json,subprocess; from pathlib import Path; assert isinstance(json.loads(Path("lean/lean_deps.json").read_text()),list); assert 0 < int(subprocess.check_output(["git","cat-file","-s","HEAD:lean/lean_deps.json"])) < 104857600'`
