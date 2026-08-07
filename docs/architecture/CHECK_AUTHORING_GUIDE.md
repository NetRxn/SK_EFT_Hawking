# Authoring a validation check — the obligations you inherit

**Production document.** Written 2026-08-05. Every rule below exists because the project shipped
its violation; the citation after each is the incident, not a style preference.

**Companions:** [`VALIDATION_ARCHITECTURE.md`](VALIDATION_ARCHITECTURE.md) ·
[`VALIDATION_GATE_TOPOLOGY.md`](VALIDATION_GATE_TOPOLOGY.md) ·
[`QA_QI_INFRASTRUCTURE_MAP.md`](QA_QI_INFRASTRUCTURE_MAP.md)

---

## The one defect this suite exists to prevent

> **Absence of measurement rendered as success.**

A check that reports PASS while measuring nothing is worse than no check: it manufactures
confidence. Two audit passes found it in eleven distinct forms, including **inside the guards
written to prevent it**. Everything below is a consequence.

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

*(Why: `_memo` cached a `SKIPPED — lake not found` PASS and replayed it after the toolchain
returned. Five reviewers, independently. The guard "only PASS is cached" was defeated because
**a fail-open SKIP is a PASS**.)*

### 2.2 Never discard a computed verdict

Compute `all_pass` and then `return CheckResult(passed=True, ...)` is the single most common form
here — eight checks shipped it. If a leg cannot block yet, say so in the message and ratchet it;
do not throw the answer away.

### 2.3 Ratchets carry ZERO headroom

A threshold above the current population cannot fire. Measure the live value, set the ceiling to
exactly it, and add a test asserting the two agree.

⚠️ **A ratchet whose test asserts its own definition is self-sealing.** `test_ci_mode.py`
asserted `CI_MIN_CHECKS_RUN == len(_CHECKS) - len(CI_SKIP)` — the definition of the quantity being
compared — which *guaranteed* the floor could never fire. Assert against the **live measured
population**, never against the formula.

### 2.4 Prove it with a PRODUCTION-seeded mutation (QI-30)

Seed the defect into the **real artifact the check reads**, run the check, watch it fail, restore.

A mutation caught against a constructed fixture proves the *test* works, not that the *check* can
fail in production. Four checks satisfied every fixture test and could not fail in production
(QI-31…34).

`tests/test_d5_mutation_obligation.py` is authoritative for the split, and **this guide does not
restate it** — the sentence that used to sit here said *"6 of 61 production-seeded"* while
declaring the test file authoritative in the same breath, and by 2026-08-06 the live values were
**10 of 65**. Read `PRODUCTION_SEEDED` and `FIXTURE_ONLY_CEILING` there; the ceiling may only
shrink.

⚠️ Seed the artifact the guard *protects*, not a helper it *uses*. The memo's key tests seeded
the fingerprint helpers and never asserted any check's key called them — deleting an input from a
live `key_fn` returned `24 passed`.

### 2.5 Guard the seam — a scan that matches nothing passes vacuously

Any check that greps, globs or walks needs a companion assertion that the population is non-empty
and plausible.

⚠️ **A source-substring scan is defeatable by prose.** A guard asserting a helper is called found
its name **in a comment** and passed over a seeded regression. Use `ast`, and assert the **call**.

### 2.6 Reach paths and flags correctly (H1 / H5)

- Paths: `_H.<NAME>` **at each use**. Never a module-level alias (an import-time copy defeats
  monkeypatching), never derived from `__file__`.
- Flags: `_cfg.STRICT_MODE` by **attribute**. `from ... import STRICT_MODE` binds a copy and makes
  the flag a silent no-op.

### 2.7 Register the mutation obligation

Add the check to `MUTATION_VERIFIED` (with the test that proves it) or `AWAITING_MUTATION_TEST` in
`tests/test_d5_mutation_obligation.py`. The backlog is **empty** and `AWAITING_CEILING` is 0 — so
adding a name there breaks the ceiling immediately. That is the intended cost.

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

## 5. The failure modes, as a checklist

- [ ] a leg that cannot fire on any input
- [ ] a computed verdict discarded
- [ ] `passed=True` on a branch that measured nothing, without `measured=False`
- [ ] a ratchet with headroom, or one whose test asserts its own definition
- [ ] a glob/regex that silently narrows the population
- [ ] a hand-maintained list parallel to a registry
- [ ] a docstring claim no test enforces
- [ ] a cache or skip that hits across the change it should have caught
- [ ] remediation advice naming a script that does not own the field
