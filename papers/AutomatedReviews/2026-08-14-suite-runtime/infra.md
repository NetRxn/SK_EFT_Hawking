# Suite runtime — root cause, measured 2026-08-14

**Found by** profiling the declared fast gate (`uv run python -m pytest -q`, which applies
`addopts = "-m 'not slow and not e2e'"`) with `--durations=40` after it came in at 11m58s.

---

## Findings

### 1 — 🔵 64% of the gate is two corpus derivations, recomputed from scratch in five places

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
- **Observed:** `extract_review_finding_nodes()` (the review-finding graph) and
  `_readiness_aggregate()` (the bundle aggregation) are rebuilt independently, from scratch,
  by five separate test families. About **40 of 6,712 tests account for ~570s of the 748s
  gate**, and roughly 480s of that is these two derivations.

  | site | what it rebuilds | cost |
  |---|---|---|
  | `test_template_contract.py::rendered` | graph + bundles summary, one real HTTP GET **per dashboard tab** | 86s |
  | `TestTheOpenRequiredPopulationRatchets` (10 tests) | both, **per test** (~19s each; one at 38s) | ~210s |
  | `readiness_blocker_refs` / `readiness_cannot_measure` | both | ~90s |
  | `d5_reviews` / `d5_prose_lean_refs` | both | ~60s |
  | `test_bundles_dashboard` (1 test) | both, setup + call | 38s |

- **Evidence:** `uv run python -m pytest -q --durations=40`, 2026-08-14, output preserved in
  the session record. The `rendered` fixture's own docstring already concedes the point —
  *"the first request warms the dashboard's mtime-fingerprinted graph cache and the bundles
  tab loads its summary, so this is the slow part of the file"* — so the cost is known
  locally at each site; what is missing is that the SAME work is repeated across sites.
- ⚠️ **This is why suite time "explodes every once in a while".** Each rebuild is
  **O(corpus)**, so every finding filed and every review document added makes all five
  families slower at once. It is not a cliff; it is continuous growth that crosses a
  noticing threshold. Five findings filed on 2026-08-13/14 moved it measurably.
- ⚠️ **Ruled out, so nobody re-derives it:** the dashboard *import* is 0.076s
  (`python -X importtime`), the fixtures in `test_template_contract.py` are **already**
  `scope="module"`, and no Lean/Lake process is spawned by the gate. The cost is data
  derivation, not import, not repetition of an unscoped fixture, not a Lean rebuild.
  `tests/test_lean_slots.py` — 82 tests, 7 git subprocesses each — is ~32s total and is
  **not** a significant contributor despite looking expensive.
- **Expected:** the two derivations are pure functions of the on-disk corpus and should be
  computed once per distinct corpus state, not once per consumer.
- **Fix:** memoize both, keyed on a cheap fingerprint of the corpus (mtime + size over
  `papers/AutomatedReviews/` and the ledger), **not** on a session-scoped fixture and not on
  a manual `cache_clear()`.

  ⛔ **The constraint that makes this non-trivial, and the way to get it wrong.** A large
  family of these tests *deliberately mutates production artifacts* to prove a check goes
  red — that seeded-mutation discipline is what makes every non-vacuity claim in this repo
  worth anything. A session-scoped cache would silently defeat it: the check would run
  against a pre-mutation snapshot and the test would pass **for the wrong reason**, which is
  strictly worse than a slow suite. Keying on the corpus's own mtime+size makes a seeding
  write invalidate the cache automatically — assert the decider (the corpus state), never a
  proxy (a flag someone must remember to clear).

  Verify the fix by seeding a mutation and confirming the dependent check still turns red.
- **Verify:** `uv run python -m pytest -q --durations=20`
