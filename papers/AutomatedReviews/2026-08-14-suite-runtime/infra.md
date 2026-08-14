# Suite runtime — root cause, measured 2026-08-14

**Found by** profiling the declared fast gate (`uv run python -m pytest -q`, which applies
`addopts = "-m 'not slow and not e2e'"`) with `--durations=40` after it came in at 11m58s.

---

## Findings

### 1 — 🔵 64% of the gate is one graph build, and each build re-derives its extractors up to 8 times

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
  calls it five times.

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
  build re-derives its own argument-free extractors **1-8 times each** (`{1: 5, 2: 10, 4: 4,
  5: 1, 6: 1, 8: 1}` — five run once, where the memo only costs a copy), because the graph is
  assembled at several sites that each derive from scratch: the pre-gate view inside
  `extract_readiness_gate_nodes`, the real node list, and the edge extractors
  (`extract_verifies_edges` re-runs `extract_python_test_nodes`;
  `extract_depends_on_axiom_edges` re-runs `extract_lean_declaration_nodes`).
  `extract_python_test_nodes` alone re-parses and re-walks the whole test suite's AST four
  times per build. ⚠️ That is **10.5 M AST nodes visited** across 62,308 `ast.walk`
  invocations — an earlier draft called 10.5 M a count of `ast.walk` CALLS, off by ~168x.
  Under `cProfile` it accounts for 22.9 s; unprofiled it is ~1.3 s per call, ~5.1 s per build.

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
  graph verified **identical modulo timestamps** to the unmemoized one across ~50,3k nodes
  and 16,300 links. ⚠️ Not literally byte-identical, and the next bullet says so — 704 gate
  nodes differ on `last_evaluated` between ANY two builds. Node counts drift as findings are
  filed into the corpus this document lives in, so they are given to the nearest hundred.
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
- **Location:** `scripts/provenance_dashboard.py` (`_graph_fingerprint`; line 207 at
  `dc7ebb4c`, since moved — resolve by name, not by line)
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
- ⚠️ **CORRECTED — "a complete key is unaffordable" was measuring the wrong set.** This
  finding first deferred the fix on the grounds that the graph's input surface is
  254,887 files / 16.5 GB. That is the surface a build *could* read (`papers/**` and
  `docs/**` include PDFs, figures and build artifacts). The set it *actually opens* is
  **2,945 files / 127.5 MB across 236 directories** — 5.1 ms to `stat`, 9.5 ms to list,
  ~15 ms total against the 7.1 s rebuild it gates. Option (a) was affordable all along;
  the deferral rested on a figure that answered a different question.
- **Fix (shipped):** the key is derived from the read set the last build actually opened,
  captured through a `sys.addaudithook` `open` recorder, plus the sorted directory listing
  of every **ancestor** directory of every read file. A newly-read input therefore enters
  the key by construction, and nobody has to remember to add it.
  - ⚠️ **Ancestors, not immediate parents — this was a real bug, caught by its own test
    before shipping.** Findings live in `papers/AutomatedReviews/<date>/*.md`, so the
    immediate parents are the `<date>` directories and `papers/AutomatedReviews/` itself
    went unwatched. Creating a new `<date>/` — which is exactly what filing a finding does,
    the single most common way this corpus changes — invalidated nothing.
  - **Fail-safe:** with no read set (before the first build, or after a build whose reads
    could not be recorded), the key contains a fresh `object()` and can never match, so the
    cache always rebuilds. It must not be `None`: `_GRAPH_CACHE['fingerprint']` is itself
    initialised to `None`, and the two would compare equal — turning a cold cache into a hit.
  - **Mid-build writes discard the read set.** The key is computed after the build, so a file
    written during it would otherwise be baked in as "already accounted for" and the next
    request would serve a graph built from pre-change data. Not hypothetical: this repo's
    seeded-mutation tests write production artifacts, and a test run concurrent with a build
    was observed doing so during this very wave.
  - `st_mtime_ns` + size rather than content hashing: hashing the same read set is 116 ms
    versus 5.1 ms and buys only same-nanosecond-same-size edits. Left as a one-line change.
- **Measured result:** cold build 7.4 s, warm hit **16 ms**. Editing a review document,
  editing the ledger, creating a new dated directory and deleting one all now rebuild;
  an unchanged tree still serves the cached object.
- **Verify:** `uv run python -m pytest -q tests/test_dashboard_graph_cache.py`

  Nine guards, mutation-proven twice against the production module: reverting to
  immediate-parent-only directories turns 3 red, and reintroducing the original blind spot
  (dropping the review corpus and ledger from the watched set) turns 6 red. Both include the
  end-to-end seam test, which requires the graph the dashboard **serves** to contain a
  newly-filed finding rather than merely that a fingerprint moved.

  ⚠️ Mutation testing also caught a **vacuity bug in these tests themselves**: the
  new-directory test originally compared against a module-scoped baseline, and because
  earlier tests in the file touch files, the key had already moved for unrelated reasons —
  so it stayed green under the very mutation it existed to catch. Each invalidation test now
  captures its baseline immediately before its own change.

---

### 3 — 🟡 `test_production_seeded_a_wrong_published_count_is_stale` rests on two unstated premises about the working copy

- **Severity:** minor
- ⚠️ **WAS FILED UNEXPLAINED; NOW EXPLAINED AND FIXED.** It was recorded with evidence and
  ruled-out causes but no mechanism, because two attempts to explain it were already wrong
  and a third guess written as fact would be worse than an open question. That was the right
  call: the mechanism, found by a `pr-review-toolkit` pass, is **not nondeterminism at all**.
  It is two unstated premises about the state of the working copy, and both were true during
  this session.
- **Lane:** infra
- **Gate:** `bundle_readiness`
- **Location:** `tests/test_d5_freshness.py::TestCountsFreshness::test_production_seeded_a_wrong_published_count_is_stale`
- **Observed:** the test bumps `docs/counts.json`'s `python.test_files` by one and asserts
  `_counts_is_stale()` is True. It returned **False** in two full-gate runs — meaning the
  live count equalled `published + 1` at that moment — and passes everywhere else.

  | run | `update_counts.py` immediately before? | result |
  |---|---|---|
  | full gate, 705.66s | no (counts stale by one — a real, explained failure) | FAILED |
  | full gate, 716.64s | **yes**, same shell command | FAILED |
  | full gate, 725.82s (`-x`) | no | **passed** (6,731) |
  | alphabetical prefix through this file, 1,671 tests | no | passed |
  | the file alone (71), the test alone | no | passed |

- **Ruled out, so nobody re-derives it:** it is not the ADR-008-era memo or the dashboard
  cache — this test reads `counts.json` against a directory listing and touches neither.
  `tests/test_build_graph_memo.py` runs before it and the two pass together (81).
  `tests/test_dashboard_graph_cache.py` sorts **after** it and cannot pollute it.
  Nothing in `tests/` before it pollutes it, since the whole alphabetical prefix passes.
  `testpaths` puts the plugin suite after `tests/`, so that cannot be upstream either.
  No stray `tests/test_gone.py` — the one temp test file any test creates — existed at the
  stop point of the `-x` run.
- ⚠️ **The `update_counts.py`-ran-immediately-before correlation was a RED HERRING.** It was
  recorded here as a hypothesis and it does not survive: the real trigger is what the working
  copy looked like, and running `update_counts.py` only changed that state incidentally.
- **Root cause — TWO premises, neither stated, both false at times during this session:**
  1. **The isolation stamp covered one tree out of five.** `_counts_is_stale` returns on its
     FIRST stale reason and walks `_COUNTS_SOURCES`, `lean/**/*.lean`, `src/**/*.py`,
     **`tests/**/*.py`**, `notebooks/**/*.ipynb` and `papers/**/paper_draft.tex`. The test
     stamped `counts.json` newer than **`src/**/*.py` alone**, so editing any TEST file — what
     one does while working on the suite — left the `tests/` leg firing first. The count leg
     was never reached and the failure read as a defect in the subject under test. That is
     the stamp asserting a PROXY for the decider, inside a test written to catch that class.
  2. **It assumes `published == live` before seeding.** It seeds `published + 1` and expects
     a mismatch; when the live tree is already one ahead — which is the state between adding
     a test file and regenerating — the seed lands on the TRUE value, every leg goes quiet,
     and the check correctly reports fresh. Reproduced deliberately: setting published to
     live-1 turns it red with no defect anywhere.

  Both states were live here: `55f3e5a1` published 195 while adding `test_build_graph_memo.py`,
  and `d82f237b` published 196 while adding `test_dashboard_graph_cache.py`.
- **Expected:** a gate test either passes deterministically or names the state it depends on.
- **Fix (shipped):** the stamp now covers **every tree `_counts_is_stale` consults**, and the
  test **verifies its isolation instead of assuming it** — it asserts the artifact is NOT
  stale before seeding anything. A future leg added to the checker and not to the stamp now
  fails there, naming that leg, instead of silently making the assertions below exercise
  something other than the count leg. The same assertion catches premise 2, reporting the
  live-vs-published drift and the remedy rather than "was reported FRESH".
  ⚠️ Do NOT "fix" this by regenerating counts; that was tried first and the failure recurred
  on the very next run, because it treats a symptom of premise 2 and leaves premise 1 intact.
- **Verify:** `uv run python -m pytest -q tests/test_d5_freshness.py`
