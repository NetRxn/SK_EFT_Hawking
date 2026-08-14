# Suite runtime — root cause, measured 2026-08-14

**Found by** profiling the declared fast gate (`uv run python -m pytest -q`, which applies
`addopts = "-m 'not slow and not e2e'"`) with `--durations=40` after it came in at 11m58s.

---

## Findings

### 1 — 🔵 64% of the gate is one graph build, and each build re-derives its extractors 4-6 times

- **Severity:** minor
- ⚠️ **Severity is a judgement call worth overruling.** Nothing here produces a wrong result,
  blocks a bundle, or fails a gate — it is developer velocity. That is why it is `minor` and
  not `major`, on the same impact test used for the ADR-008 residue findings: a functional
  dead-end (an unreclaimable lease) was major; a resource posture with no demonstrated
  failure was minor. **Re-rate it upward the moment it changes behaviour** — if the gate gets
  slow enough that it stops being run before a commit, the defect has become correctness.
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `tests/test_template_contract.py::rendered`,
  `tests/test_d5_bundles_readiness.py::TestTheOpenRequiredPopulationRatchets`,
  `tests/test_readiness_blocker_refs.py`, `tests/test_readiness_cannot_measure.py`,
  `tests/test_d5_reviews.py`, `tests/test_d5_prose_lean_refs.py`,
  `tests/test_bundles_dashboard.py`
- ⚠️ **CORRECTED 2026-08-14 — THIS FINDING NAMED THE WRONG TWO FUNCTIONS, and the fix it
  prescribed would have been both unaffordable and unsafe.** The correction is recorded in
  place rather than as a second finding, because this document's own numbers were the input
  to the remediation and a reader re-deriving them must land on the measured ones. Both errors
  came from the same shortcut: the durations report was read as an attribution, and no
  function named in it was ever timed on its own.

  | claim as filed | measured at HEAD |
  |---|---|
  | `extract_review_finding_nodes()` is a co-dominant cost | **0.26 s**, 1,702 nodes — not a contributor |
  | `_readiness_aggregate()` rebuilds "the bundle aggregation" | 14.6 s, of which **14.4 s is `build_graph_json()`** |
  | the two are rebuilt "by five test families" | true, but the shared cost is the **graph build**, not either named function |
  | fix = memoize both on a corpus mtime+size key | unaffordable and unsafe — see below |

  The real chain is `_readiness_aggregate()` -> `aggregate_by_bundle()` ->
  `_blocked_p1_gates_by_paper()` -> `evaluate_all_gates(build_graph_json())`. Every consumer
  of bundle readiness triggers **a full knowledge-graph rebuild**, and that rebuild is the
  entire cost. `extract_review_finding_nodes` appears in the profile only because the build
  calls it six times.

  ⛔ **The prescribed cross-consumer cache is withdrawn, on two independent grounds.**
  *Unaffordable:* keying it correctly needs a fingerprint over everything the graph reads,
  and that surface measured **254,887 files / 16.5 GB** — 57 s to content-hash, 3.7 s merely
  to `stat`, against the 14.4 s it would save. *Unsafe:* any affordable key is therefore a
  hand-listed PROXY for the real input set, and this repo already has one such proxy that is
  demonstrably wrong — see finding 2. A cache whose key misses an input is strictly worse
  than no cache, because it manufactures a green that survives the very change it should
  have caught. `scripts/validation/_memo.py`'s docstring states this hazard, and
  `tests/conftest.py` disables that memo suite-wide for exactly this reason, which is also
  why it could never have been the vehicle here.

- **Observed:** ~40 of 6,712 tests account for ~570 s of the 748 s gate. The shared cost is
  `build_graph_json()` at **14.4 s per call**, invoked once per readiness-consuming test. The
  build re-derives its own argument-free extractors **4-6 times each**, because the graph is
  assembled at several sites that each derive from scratch: the pre-gate view inside
  `extract_readiness_gate_nodes`, the real node list, and the edge extractors
  (`extract_verifies_edges` re-runs `extract_python_test_nodes`;
  `extract_depends_on_axiom_edges` re-runs `extract_lean_declaration_nodes`).
  `extract_python_test_nodes` alone re-parses and re-walks the whole test suite's AST four
  times per build — 10.5 M `ast.walk` calls, 22.9 s of a profiled build.

  | site | graph builds | cost |
  |---|---|---|
  | `test_template_contract.py::rendered` | one per dashboard tab, via real HTTP GETs | 86s |
  | `TestTheOpenRequiredPopulationRatchets` (10 tests) | one **per test** (~16s each) | ~210s |
  | `readiness_blocker_refs` / `readiness_cannot_measure` | one each | ~90s |
  | `d5_reviews` / `d5_prose_lean_refs` | one each | ~60s |
  | `test_bundles_dashboard` (1 test) | one in setup, one in call | 38s |

  Measured baseline for these seven files together: **267 tests, 419.88 s**.

- **Evidence:** `uv run python -m pytest -q --durations=40`, 2026-08-14, output preserved in
  the session record. The `rendered` fixture's own docstring already concedes the point —
  *"the first request warms the dashboard's mtime-fingerprinted graph cache and the bundles
  tab loads its summary, so this is the slow part of the file"* — so the cost is known
  locally at each site; what is missing is that the SAME work is repeated across sites.
- ⚠️ **This is why suite time "explodes every once in a while", but the growth term is not
  the one first claimed.** Each build is O(repo), and the dominant contributor is
  `extract_python_test_nodes` — 1.27 s per call, four calls per build — which walks the AST
  of **the test suite itself**. Suite time therefore grows fastest with the number of tests,
  and every readiness-consuming test pays for every other test's AST four times over. Review
  documents contribute through `extract_review_finding_nodes`, but that is 0.26 s per call:
  real, and an order of magnitude below the test-count term. The original "every finding
  filed makes all five families slower" was directionally right and quantitatively
  misleading. It is continuous growth crossing a noticing threshold, not a cliff.
- ⚠️ **Ruled out, so nobody re-derives it:** the dashboard *import* is 0.076s
  (`python -X importtime`), the fixtures in `test_template_contract.py` are **already**
  `scope="module"`, and no Lean/Lake process is spawned by the gate. The cost is data
  derivation, not import, not repetition of an unscoped fixture, not a Lean rebuild.
  `tests/test_lean_slots.py` — 82 tests, 7 git subprocesses each — is ~32s total and is
  **not** a significant contributor despite looking expensive.
- **Expected:** a build should derive each argument-free extractor once. Nothing about the
  corpus can change while one `build_graph_json()` call is on the stack, so re-deriving
  inside it buys no freshness — only time.
- **Fix (shipped):** a memo scoped strictly to the dynamic extent of one `build_graph_json()`
  call — `build_graph._BUILD_MEMO`, entered by `_build_memo_scope()`. Every argument-free
  extractor is memoized while a build is on the stack and computes normally outside one, so a
  direct caller (`load_findings_by_paper` calls `extract_review_finding_nodes` with no build
  in progress) always reads live state. Results are handed out as copies, because the two
  assembly sites hold their node lists independently and `_overlay_atlas` / `_overlay_closure`
  annotate in place.

  ⛔ **The constraint that makes this non-trivial, and why the scope is the answer to it.** A
  large family of these tests *deliberately mutates a production artifact* to prove a check
  goes red — that seeded-mutation discipline is what makes every non-vacuity claim in this
  repo worth anything. Any cache outliving a build would answer the post-seeding read from a
  pre-seeding snapshot, and the test would pass **for the wrong reason**: strictly worse than
  a slow suite, and invisible, because a check that cannot fire is indistinguishable from a
  check that found nothing. Build-scoping does not *solve* the invalidation problem — it
  **removes it**, since there is no key to get wrong and no input that can be missed.

  Guarded by `tests/test_build_graph_memo.py`, which seeds a real review document into
  `papers/AutomatedReviews/` and requires the very next build to see it. Both directions are
  mutation-proven against the production module: making the memo outlive its build turns 5
  tests red (including both seeded-corpus guards); removing the copy turns the aliasing guard
  red.
- **Measured result:** `build_graph_json()` **14.4 s -> 7.1 s** (2.01x), with the memoized
  graph verified byte-identical to the unmemoized one across 50,278 nodes and 16,300 links.
  ⚠️ The equivalence check must normalise `built_at` / `last_evaluated`: two *unmemoized*
  builds already differ in 704 gate nodes on those timestamps alone, so an un-normalised
  comparison would assert a determinism the code never had.
- **Verify:** `uv run python -m pytest -q tests/test_build_graph_memo.py`

  (The runtime itself is re-measured with `uv run python -m pytest -q --durations=20`; that
  is a measurement, not a pass/fail gate, so it is deliberately not the `Verify:` command.)

---

### 2 — 🟡 the dashboard's graph cache is keyed on a proxy that misses the review corpus

- **Severity:** minor
- ⚠️ **Rated minor only because the blast radius is one read surface.** It produces a WRONG
  ANSWER, not merely a slow one, which is the line finding 1 explicitly does not cross — so
  it is the more serious of the two on kind, and lower only on reach. Re-rate to major if
  anything downstream of the dashboard's `/api/graph*` is ever treated as authoritative for
  a readiness or closure decision; at that point a stale finding set decides a gate.
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `scripts/provenance_dashboard.py:207` (`_graph_fingerprint`)
- **Observed:** `_GRAPH_CACHE` is invalidated by `_graph_fingerprint()`, a hand-listed set of
  13 files plus two globs (`papers/paper*_*/paper_draft.tex`, `lean/SKEFTHawking/*.lean`).
  **`papers/AutomatedReviews/**/*.md` and `docs/review_finding_supersessions.json` are in
  neither** — yet `build_graph_json` embeds a `ReviewFinding` node per finding and applies the
  supersession ledger's status overrides. Filing a finding, or closing one through
  `scripts/close_finding.py`, therefore does not invalidate the dashboard's graph. It serves
  the pre-change finding set until some *unrelated* keyed input happens to move.
- **Evidence:** measured directly against the live function, 2026-08-14 —

  ```
  corpus file: papers/AutomatedReviews/2026-08-14-suite-runtime/infra.md
  fingerprint moved after touching the review corpus? False
  fingerprint moved after touching the ledger?       False
  targets in fingerprint: 1428
  ```

- ⚠️ **This is the same defect class as finding 1's withdrawn fix, which is why it is filed
  here rather than separately.** A cache key that enumerates inputs by hand asserts a PROXY
  for the decider (what the derivation actually reads); it is correct only until someone adds
  an input, and then it fails silently and in the green direction. `_graph_fingerprint`'s own
  docstring says it stats "the canonical inputs that `build_graph_json` consumes" — that
  claim is false today, and nothing checks it.
- **Expected:** either the key covers every input the build reads, or the cache does not
  claim to.
- **Fix:** ⚠️ **Do not simply append two globs.** That repeats the mistake one input later
  and re-arms the same silent failure. The measured constraint is that a complete key is
  unaffordable — the graph's full input surface is 254,887 files / 16.5 GB — so the honest
  options are (a) derive the key from the read-set the build actually opens, plus the
  directory listings of everything it globs, so a new input enters the key by construction,
  or (b) keep a hand-listed key and add a guard that FAILS when `build_graph_json` reads a
  path the fingerprint does not cover. Either way the invariant must be asserted by a test,
  not by a docstring. Pending design; not attempted in this wave.
- **Verify:** a test that writes a finding into `papers/AutomatedReviews/`, calls
  `get_cached_graph()` twice around it, and requires the second call to reflect the change.
