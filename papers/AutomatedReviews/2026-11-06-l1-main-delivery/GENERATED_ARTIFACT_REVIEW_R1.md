# Independent generated-artifact review r1

Verdict: **REVISE**. Candidate `9d0d7fc3c6ab01ab58118cd474cabda43260c158`.

The packet remained fresh at initial and final comparison, including HEAD, index semantics, dirty artifact bytes, governing authorities, roadmap, notebook, producer files, and declaration JSON. No source or authority drift was found.

## Required revision

**P2 — `docs/counts.tex:19` publishes `\totaltests{6891}` while `docs/counts.json` and the exact-writer collection receipt report 7019.** The existing `scripts/update_counts.py` producer writes both artifacts; committing only the three current diffs would leave its paper-facing companion stale. The LaTeX header also retains the older generated timestamp. Of 17 direct headline count macros compared with JSON, only `totaltests` differed; full derived/per-module LaTeX regeneration is not certified by this review.

After the active CI measurement completes, ROOT should run the existing producer, include every resulting artifact in a deliberately reissued packet, and obtain a fresh exact-byte review. No hand edits or machinery changes are needed. The r1 packet and this rejection must remain preserved.

## Individually verified artifacts

- `docs/counts.json`: all 21 Lean fields equal the unchanged canonical `count_lean(..., preloaded=loaded_json)` result, including module-name and axiom/native-cluster structures. All cheap Python fields equal `count_python_cheap`; both Aristotle fields equal `count_aristotle`. Registry inputs were literal AST values from the actual constants source, supplied to the unchanged helpers without importing scientific `src.core` modules. Verified totals include 41034 declarations, 22851 theorems, 2047 modules, 12900 definitions, 530 native-decide declaration closures, zero project axioms/sorry, and 313 Aristotle-proved entries across 40 registry run values. These are index/registry counts, not new proof or scientific acceptance.
- The retained exact-writer collection stdout ends `6927/7019 tests collected (92 deselected) in 7.50s`. Applying the actual producer regex yields **7019**, not selected-only 6927. No collection was repeated. JSON changes are exclusively `generated`, `lean_deps_source`, and `python.pytest_cases`; all old remaining fields are preserved. The new absolute source path names this actual checkout. Timestamp is producer metadata, not build/extraction/acceptance evidence.
- `lean/lean_deps.json.hash`: unchanged source-only `compute_lean_hash()` yields `1d45fd4918bfe9c6`, exactly the current artifact. The declaration JSON remains SHA-256 `942279d0b9a4480b6396acd0717a1709a763aeee1a74289bfefbdb41d0664e6d`. Existing native extraction receipt records rc0 and 41034 declarations; existing freshness stdout says fresh. Receipt-candidate-to-current HEAD comparison contains no Lean or extractor source change. This review did not invoke extraction or a load/refresh helper.
- Paper15 `table2_checks.tex`: byte-exact canonical `render_table(TABLES['table2_checks'])`, 89 AST-derived registered rows, SHA-256 `585507d8f6a1ab80373b2597a57666fbb2eab7350f9cdf811f93a6e93776e8a1`. Only readiness row 14 description changes. Actual decorator, classifier, partition, and consumer source agree: literal blocked at either priority makes RED/fails; outstanding nonblocked states remain advisory; absent gate population fails; ComputationCorrectness metadata reports state/measurement/evidence/blockers. **YELLOW/OPEN is not human-ready; human submission requires GREEN.** No thresholds or policy are altered by the artifact diff.

## Boundaries

Only read-only source/AST metadata, unchanged safe count/hash/render helpers, Git reads, continuity comparisons, and retained receipts were used. No native/Lean/build/scientific evaluator, tests/validators/fullgraph, collection repeat, source/index/ledger/notebook/runtime mutation, or peer branch absorption occurred. Only `/tmp/l1-generated-artifacts-review-r1.md` and `.json` were written. This is independent producer/source review, not full-profile PASS, full merge, scientific production, human submission, or publication acceptance.
