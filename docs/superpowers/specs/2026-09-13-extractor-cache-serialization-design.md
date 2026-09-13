# Compact extractor cache persistence

Status: design independently reviewed; original serialization failure localized and isolated real-data pilot passed. Authoritative integration and cold/warm validation pending.
Decision owner: ADR-005 D-G.3, extending D-G.1 and D-G.2.

## Contract

The existing saveImmRefCache, saveMathlibCache, saveTypeStrCache and saveJsonCache in lean/SKEFTHawking/ExtractDeps.lean retain their constructed Json values and write Json.compress of those values instead of toString. The existing Python wrapper remains the only canonical writer under its existing regeneration lock. Cache readers, paths, schemas, array order, string-valued hashes, embedded JSON/type strings, pin computation and dependency/axiom coverage are unchanged. The source edit intentionally invalidates the source-keyed caches on the first authoritative run.

The mechanism avoids construction and layout of a whole-cache pretty Format tree. It does not claim constant memory, a proved stack bound, or a general fix for arbitrary recursive extraction failures. No runtime stack, Lean proof option, traversal algorithm, deadline, dependency pin or toolchain change is included.

## Evidence and admission

The tracked finding papers/AutomatedReviews/2026-09-13-canonical-extractor-stack/infra.md owns the incident. The current guarded canonical-entry diagnostic has reached the first cache save after completing dependency closure and declaration rendering. Before implementation, finer markers must establish that the same original Json value is constructed successfully and that the original serialization fails before yielding a string. A compact replacement must complete under the same --run entry mode on actual cache data, with all saves redirected away from accepted primary artifacts.

For each real cache, compare parsed old and compact values exactly, preserving array order and all decoded strings; confirm the original Lean readers accept compact files and matching pins. Exercise empty and nested values and escaped quotes, backslashes, newlines and Unicode. Record source/input/output hashes, original subprocess results and all primary pre/post hashes. Diagnostic results do not constitute canonical acceptance.

## Acceptance

Independent specification and implementation review; bounded real-data pilot; normal controller build; successful authoritative cold and warm extraction with byte-identical canonical results; complete prior-record and axiom reconciliation, accounting separately for extractor self-declarations; existing wrapper and extraction-scope tests; applicable full round gate. Close the original finding through scripts/close_finding.py only after verification. Root retains integration and acceptance authority.

## Alternatives

Raising runtime stack size changes deployment assumptions and leaves the pretty-tree growth mechanism. Streaming a new cache format or rewriting Tarjan introduces unrelated changes after closure already completed in the reproducer. Compact JSON uses the pinned serializer already used by per-declaration canonical output and leaves reader contracts intact. If finer evidence locates failure outside serialization, this proposal is not admitted.
