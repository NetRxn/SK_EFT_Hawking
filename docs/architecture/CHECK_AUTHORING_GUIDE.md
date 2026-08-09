# Authoring a validation check — the obligations you inherit

> **Answers:** I am writing a new check — what do I owe?
>
> *(TODO-D8: this line is the required-content contract. `README.md`'s ownership
> table assigns this question to this document; `architecture_inventory_fresh`
> asserts the two agree verbatim, so the assignment cannot drift silently.)*

**Living document.** Start at [`README.md`](README.md). States no counts — the check roster is
in [`SURFACE_INVENTORY.md`](SURFACE_INVENTORY.md).

Every rule below exists because the project shipped its violation; the citation after each is
the incident, not a style preference.

**Companions:** [`VALIDATION_ARCHITECTURE.md`](VALIDATION_ARCHITECTURE.md) (how the suite is
built) · [`VALIDATION_GATE_TOPOLOGY.md`](VALIDATION_GATE_TOPOLOGY.md) (when gates run, what
each computes) · [`QA_QI_INFRASTRUCTURE_MAP.md`](QA_QI_INFRASTRUCTURE_MAP.md) (the quality
layer's interior) · [`END_TO_END_MAP.md`](END_TO_END_MAP.md) (the spine).

---

## The one defect this suite exists to prevent

> **Absence of measurement rendered as success.**

A check that reports PASS while measuring nothing is worse than no check: it manufactures
confidence. Repeated audit passes have found it in many distinct forms, including **inside
the guards written to prevent it**. Everything below is a consequence.

## 1. Skeleton

```python
@register_check("my_check", "One line: what must be TRUE for this to pass")
def check_my_thing() -> CheckResult:
    """What defect this catches, and how it would fail."""
    if not _H.SOME_ARTIFACT.is_file():
        return CheckResult(passed=False, measured=False, details=[Detail(
            "artifact", False, "SKIPPED — artifact absent; UNVERIFIED, not passing")])
    ...
    return CheckResult(passed=(n_bad == 0), details=details)
```

## 2. The seven obligations

### 2.1 Decide what absence means — and say so with `measured`

If a branch returns `passed=True` **without examining the artifact**, it must set
`measured=False`. Two consumers depend on it: `--ci`'s coverage floor counts *measurements, not
invocations*, and `_memo` **refuses to cache a non-measurement**.

⚠️ Prefer **FAIL** on cannot-measure. "I could not find the substrate" is not evidence that the
substrate is fine. `tests/test_cannot_measure_baseline.py` freezes the population that passes
anyway, and a new silent PASS fails on arrival.

*(The failure this prevents: a cache whose guard is "only PASS is cached" is defeated by a
fail-open SKIP, because **a fail-open SKIP is a PASS**. It gets stored under a key
byte-identical to the real measurement and replayed once the toolchain returns.)*

### 2.2 Never discard a computed verdict

Compute `all_pass` and then `return CheckResult(passed=True, ...)` is the single most common form
here, and it has shipped repeatedly. If a leg cannot block yet, say so in the message and
ratchet it; do not throw the answer away.

### 2.3 Ratchets carry ZERO headroom

A threshold above the current population cannot fire. Measure the live value, set the ceiling to
exactly it, and add a test asserting the two agree.

⚠️ **Assert against what the code DOES, not against what it counted.** The distinction is
narrow and the two forms look alike:

- **Self-sealing.** Comparing the floor to the number of checks that *ran*, where `run_checks`
  fills a result for every spec — the count is identically `registered - skipped`, so the
  assertion is an identity and can never fire. Unfireable and invisible at once.
- **A working ratchet.** Comparing a **hardcoded constant** to `len(_CHECKS) - len(CI_SKIP)`.
  This fires the moment the roster changes without the constant, which is exactly its job.

So the formula is not the problem; comparing a quantity to *the same expression that produced
it* is. What no formula can catch is a check that registers, is not skipped, and still measures
nothing — that needs the registry **executed** and `measured` counted, which is why the floor
carries a second, slow test that does precisely that.

### 2.4 Prove it with a PRODUCTION-seeded mutation (QI-30)

Seed the defect into the **real artifact the check reads**, run the check, watch it fail, restore.

A mutation caught against a constructed fixture proves the *test* works, not that the *check* can
fail in production. Checks have satisfied every fixture test and still been unable to fail in
production (QI-31…34).

`tests/test_d5_mutation_obligation.py` is authoritative for the split, and **this guide does
not restate it.** Read `PRODUCTION_SEEDED` and `FIXTURE_ONLY_CEILING` there; the ceiling may
only shrink.

⚠️ Seed the artifact the guard *protects*, not a helper it *uses*. A key test that seeds the
fingerprint helpers, without asserting that any check's key calls them, passes while an input is
deleted from a live `key_fn`.

### 2.5 Guard the seam — a scan that matches nothing passes vacuously

Any check that greps, globs or walks needs a companion assertion that the population is non-empty
and plausible.

⚠️ **A source-substring scan is defeatable by prose.** A guard that asserts a helper is called
by searching the source finds the name **in a comment** and passes over a seeded regression. Use
`ast`, and assert the **call**.

### 2.6 Reach paths and flags correctly (H1 / H5)

- Paths: `_H.<NAME>` **at each use**. Never a module-level alias (an import-time copy defeats
  monkeypatching), never derived from `__file__`.
- Flags: `_cfg.STRICT_MODE` by **attribute**. `from ... import STRICT_MODE` binds a copy and makes
  the flag a silent no-op.

### 2.7 Register the mutation obligation

Add the check to `MUTATION_VERIFIED` (with the test that proves it) or `AWAITING_MUTATION_TEST` in
`tests/test_d5_mutation_obligation.py`. The backlog is ratcheted at its live floor, so adding a
name to it breaks the ceiling in the same commit. That is the intended cost.

## 3. Where the check goes

| the question it asks | module |
|---|---|
| does this theorem prove anything / is an assumption disclosed | `lean_substrate.py` |
| does it build; what does it trust | `lean_toolchain.py` |
| is the statement substantive | `lean_statements.py` |
| do the numbers agree | `physics.py` |
| does the prose agree with the numbers | `papers_prose.py` |
| do cited Lean names resolve | `prose_lean_refs.py` |
| citations and parameter provenance | `citations.py` |
| bundle / readiness verdicts, reviews | `bundles_readiness.py`, `reviews.py` |
| graph and proof atlas | `graph_atlas.py` |
| generated-artifact freshness | `freshness.py` |
| notebooks | `notebooks.py` |

If it regenerates an artifact another check reads, its position in
`validate._CANONICAL_ORDER` is **semantic** — declare it there.

## 4. Before you commit

```bash
uv run python scripts/validate.py --check <name> --no-archive   # it runs
uv run python -m pytest tests/ -q                               # nothing regressed
# then: seed the defect in production, watch it fail, restore
```

## 5. The systemic pattern — the shapes it has actually taken

Independent mechanisms, one shape: **absence of measurement rendered as success.** This
ledger is the empirical backing for §1–§4; each row is a mechanism that reported health over
a population it never reached.

**The status column is load-bearing** — read it before quoting a row. Most of these are
repaired, and a reader who takes the table as a list of live defects will chase ghosts. Each
`fixed` claim below was re-verified against the code, not inherited.

| mechanism | reported | actually | status |
|---|---|---|---|
| `readiness_submission_gate` | pass | **inverted** — failed only when *zero* gate nodes existed, and passed when it measured RED | **fixed** — returns `passed=False` on any blocked gate |
| `paper_latex_compiles` | pass | computed its verdict and discarded it; then remained *slow-gated* to a default SKIP, so a fatal LaTeX error stayed invisible for months | **fixed** — verdict derived; slow gate deleted |
| `--ci`'s coverage floor | "the suite cannot silently shrink" | counted checks **invoked**, not measured — `run_checks` fills a result for every spec, so the count was identically the floor and it **could never fire** | **fixed** — counts `CheckResult.measured` |
| `_memo` | "only PASS is cached, so a red check re-runs" | **a fail-open SKIP *is* a PASS** — it cached `SKIPPED — lake not found` under a key byte-identical to the real measurement and replayed it after the toolchain returned | **fixed** — `_memo` refuses to cache a non-measurement |
| the memo's key tests | "production-seeded" | seeded the fingerprint **helpers**, never asserting any check's key called them — deleting an input from a live `key_fn` still passed | **fixed** — `TestCheckKeysSpanTheirInputs` seeds through the real key |
| `test_ci_mode.py`'s floor test | "the floor is asserted" | asserted the floor against **its own definition**, which is what made it unfireable and invisible at once | **fixed** — the hardcoded constant is now held to the live derived population, so a new check fails it on arrival, and a second (slow) test EXECUTES the registry and counts `measured` — the half no formula can cover |
| `check_bundle_source_freshness` | "fresh: all N source paper(s)…" | returned `None` for sourceless keys, compared zero files, and **wrote `freshness_stale: false`** | **fixed** — an absent source directory now reports UNMEASURABLE |
| `evaluate_all_gates` | `open` | an evaluator that CRASHED aggregated to YELLOW, indistinguishable from a mild advisory | **fixed** — an evaluator exception records `state='blocked'` |
| `_blocked_p1_gates_by_paper` | `{}` | "could not compute" and "nothing blocked" shared one value | **fixed** — returns `None`, and GREEN is withheld in that case |
| the dead-edge guard | "derived on both sides" | its emitted-set scan collected **node** types too, so its population was wider than its subject and it could not fail on the case it was built for | **fixed** — the scan is scoped structurally to dicts carrying `source`/`target` |
| `harness_lock` on contention | "regenerate: succeeded" | callers discarded the lock's contention signal and reported success over work that did not happen | **fixed** — `sync.py` prints `sync INCOMPLETE` naming the skipped artifacts; `load_lean_deps()` warns with the blast radius |
| AI-Defense Tier 1 | an *"Implementation:"* line named two scripts | neither script was written; the document described a system nobody had built | **fixed** — retitled a design proposal, with a measured coverage map; the one uncovered soundness item (`@[csimp]`) is named as such |

**The generalisable lesson, and why it is here rather than in a changelog:** in the memo's
case all four guards policed *how the cache is used*; none audited *whether the key spans the
inputs*. **Guarding at the wrong layer is indistinguishable from guarding, right up until the
measurement.**

**The shape of every fix above is the same:** the verdict must be *derived* from what the
check measured, never asserted alongside it — in each repaired row the code had computed the
right answer and then discarded it.

⚠️ **The AI-Defense row was a different shape, and "derive the verdict" was never its fix.**
It was not a measurement failure at all — it was a document describing files nobody had
written, which is why the repair was editorial (say what it is, map what covers it) rather than
a code change. A specification and a description are not interchangeable, and a document that
blurs them gets quoted as evidence.

The `harness_lock` row is worth keeping visible even though it is fixed: the lock itself was
always correct, and the defect lived entirely in what its *callers* did with an honest signal.
A guard that reports accurately can still produce absence-as-success one layer up.

⚠️ **The obvious type-system fix was tried and rejected, with the measurement.**
`CheckResult.passed` is a bare `bool` with no `UNEVALUATED` state, and adding one was ADR-009
§Deferred item 4. **DECLINED**: `passed` is an ADR-009 D2 contract item. The `--json` payload reads the
field; `gate_precheck.py` and `pre-commit-sync.sh` consume the **exit code** that
`validate.main()` derives from it. A third state forces an exit-code mapping decision on both,
so it is a contract change rather than a local refactor. `measured` was added as a *separate
additive field* instead, precisely so every existing reader stayed correct.

## 6. The failure modes, as a checklist

- [ ] a leg that cannot fire on any input
- [ ] a computed verdict discarded
- [ ] `passed=True` on a branch that measured nothing, without `measured=False`
- [ ] a ratchet with headroom, or one whose test asserts its own definition
- [ ] a glob/regex that silently narrows the population
- [ ] a hand-maintained list parallel to a registry
- [ ] a docstring claim no test enforces
- [ ] a cache or skip that hits across the change it should have caught
- [ ] remediation advice naming a script that does not own the field
