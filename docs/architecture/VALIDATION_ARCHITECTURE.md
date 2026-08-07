# Validation subsystem — architecture

**Living document.** Start at [`README.md`](README.md). States no counts — the check roster
is in [`SURFACE_INVENTORY.md`](SURFACE_INVENTORY.md#validation-checks).

The durable description of how `validate.py` and `scripts/validation/` are built and why.

**Companions:** [`VALIDATION_GATE_TOPOLOGY.md`](VALIDATION_GATE_TOPOLOGY.md) (when each gate
runs, what it blocks, what each computes) · [`CHECK_AUTHORING_GUIDE.md`](CHECK_AUTHORING_GUIDE.md)
(obligations a new check inherits, and the systemic-pattern ledger) ·
[`QA_QI_INFRASTRUCTURE_MAP.md`](QA_QI_INFRASTRUCTURE_MAP.md) (the quality layer's interior) ·
[`END_TO_END_MAP.md`](END_TO_END_MAP.md) (the spine).

---

## 1. The one-sentence shape

`scripts/validate.py` is a **framework** (zero registered checks); the checks live in domain
modules under `scripts/validation/checks/`; three framework modules
(`_registry`, `_config`, `_memo`) and one shared helper (`_tex`) sit below both, and
`scripts/validate_helpers.py` is the single path anchor.

```
scripts/validate.py              # framework: CLI, run_checks, print_results, ordering
scripts/validate_helpers.py      # THE path anchor + artifact loaders (H1, H4)
scripts/validation/
  _registry.py                   # CheckResult / Detail / CheckSpec / register_check
  _config.py                     # runtime flags, reached by ATTRIBUTE (H5)
  _memo.py                       # input-fingerprint memo for expensive checks
  _tex.py                        # shared LaTeX helpers
  checks/                        # domain modules; roster in SURFACE_INVENTORY.md
    lean_substrate.py            #   substance gates (R1-R3)
    lean_toolchain.py            #   build + trust surface
    lean_statements.py           #   statement-level substance
    physics.py                   #   numerics, identities, bounds
    papers_prose.py              #   prose vs numbers; LaTeX compile
    prose_lean_refs.py           #   do cited Lean names resolve
    citations.py                 #   citation + parameter provenance
    bundles_readiness.py         #   bundle/readiness verdicts, reviews
    graph_atlas.py               #   knowledge graph + proof atlas
    freshness.py                 #   generated-artifact freshness
    notebooks.py                 #   notebook execution + viz
    reviews.py                   #   review-document integrity
```

**Why the framework/check split.** A single monolithic `validate.py` made every check's
dependencies implicit and made "does this file fit in one read" unanswerable. ADR-009 D1 set the
criterion: **every module readable in one pass**, and that is the criterion a new module is held
to — not a line threshold, which the modules deliberately do not share.

## 2. The framework contract

### `CheckResult` — what a check returns

```python
@dataclass
class CheckResult:
    passed: bool                  # the verdict
    details: List[Detail]         # per-sub-check evidence, printed in order
    error: Optional[str] = None   # set when the check itself crashed
    measured: bool = True         # False when it returned WITHOUT measuring
```

`passed` is a **bare bool with no third state**, deliberately: it is contract item 5 of ADR-009
D2, read by the `--json` payload, `gate_precheck.py` and `pre-commit-sync.sh`. §Deferred item 4
declined an `UNEVALUATED` value for exactly that reason.

**`measured` is a separate additive field, not a third `passed` value.** It answers a different
question — *did this check look at anything?* — and defaulting it `True` leaves every existing
reader correct. Set it `False` on any branch that returns `passed=True` without examining the
artifact (missing toolchain, absent input, unparseable data). Two consumers depend on it:

* `--ci`'s coverage floor counts **measurements, not invocations**;
* `_memo` **refuses to cache a non-measurement**.

Both were blind before it existed. See §5.

### Registration and ordering

`@register_check("name", "description")` appends to `_registry._CHECKS`. `validate` re-exports
that **same list object** — rebinding it anywhere creates two registries, with registration
filling one and `run_checks` iterating the other, and `all([]) is True`, so the suite would
report success over nothing. `tests/test_validate_public_surface.py` asserts the identity.

**Execution order is data, not import order** (hazard H3). `validate._CANONICAL_ORDER` declares
it and `_apply_canonical_order()` sorts in place. This matters because the regenerators in
`freshness.py` *rewrite artifacts other checks read* — their position relative to their
consumers is semantic.

## 3. The hazards, and how each is structurally prevented

These are ADR-009 D3, which identifies **five**. They are not style rules; each names a
failure the project has shipped.

| | hazard | rule | enforced by |
|---|---|---|---|
| **H1** | a path derived from `__file__` resolves to `scripts/validation/checks/`, so every artifact lookup silently misses | reach paths as `_H.<NAME>` **at each use** — never a module-level alias, never from `__file__` | `test_no_check_derives_a_path_from___file__` |
| **H2** | the roster gate asserts on a module named exactly `validate`, so a split that renames or hollows it breaks the gate silently | `validate` must keep exposing `BUNDLE_CODES` | `bundle_registry_consistency` Leg B (`_ROSTER_CONSUMERS`) + `EXPECTED_DYNAMIC` in `test_validate_public_surface.py` |
| **H3** | import order silently becomes execution order | `_CANONICAL_ORDER` owns it | `test_every_registered_check_has_a_declared_position` + `test_the_sort_runs_after_the_last_registration` |
| **H4** | the same missing artifact means different things in different checks; a shared helper would unify them silently | helpers own *where a thing is*, **never what its absence means** | `test_cannot_measure_baseline` freezes the divergent policies |
| **H5** | `from validate import STRICT_MODE` binds a **copy** at import time; `--strict` becomes a silent no-op | reach flags by **attribute** on `_config` | `test_validate_flag_propagation` |

⚠️ **H5's structural test is not sufficient on its own.** `co_names` records names used for both
`LOAD_GLOBAL` and `LOAD_ATTR`, so an import-time copy still appears there. The guard additionally
requires `_cfg` in `co_names` — an imported copy has no attribute access to show.

**H3 is enforced on two axes, and both are structural.** The two tests above prove every
registered check has a declared position and that the sort runs after the last registration —
that is the *mechanism*. `test_regenerators_precede_their_consumers` proves the *dependency*:
`counts_fresh` runs before every check that reads `docs/counts.json`, with the consumer set
**derived by AST** from the check bodies rather than declared.

⚠️ **It was a hand-written tuple naming two consumers, and that was the bug.** The real
population was larger, and three undeclared readers ran *before* the regenerator — including
`lean_zero_sorry`, the Invariant #4 gate, which therefore evaluated the previous extraction on
any run over changed Lean sources. `counts_fresh` now runs first, and a new consumer
registered ahead of it fails the derived assertion on arrival rather than silently reading
stale counts. A body that reaches `counts.json` through a helper without naming it is still
invisible to the scan — an accepted limit, stated in both the test and the production comment.

## 4. Runtime flags (`_config.py`)

| flag | set by | meaning |
|---|---|---|
| `STRICT_MODE` | `--strict` | promote submission advisories to hard failures |
| `FORCE_LATEX` | `--force-latex` | recompile every bundle draft, bypassing the per-draft cache |
| `FORCE_NOTEBOOK_REEXEC` | `--force-notebooks` | bypass the notebook skip-cache |
| `NO_MEMO` | `--no-memo` | bypass the expensive-check memo; **implied by `--strict`** |
| `CI_MODE` | `--ci` | unattended-runner profile + coverage floor |

## 5. Change-scoping: `_memo.py` and the per-draft LaTeX cache

Almost every check finishes in well under a second; the suite's cost is concentrated in a
couple of them. Two caches scope those to what changed:

* **`_memo.py`** — a check's verdict is reused only while a fingerprint of *every input it reads*
  is unchanged since its last PASS. Applied to `axiom_closure_allowlist` and
  `lean_docstring_refs_resolve`.
* **`paper_latex_compiles`** — per-draft content-hash cache over the draft's full `\input`
  closure. With the cost gone, its **slow gate was deleted**: it had returned `passed=True` with
  `SKIPPED (slow)` by default, which is why a fatal LaTeX error was invisible for months.

Measure rather than quote: `validate.py` prints its own elapsed time, and `--no-memo` gives the
cold number.

### The hazard, and why the guards are where they are

A memoized check reports PASS **without measuring anything** — the defect class this whole
subsystem exists to close. It is sound only if the key spans every input.

1. the key includes the check's **whole defining module** *and* its own body source;
2. `tests/test_validation_memo.py::TestCheckKeysSpanTheirInputs` seeds each declared input **in
   the production tree** and asserts **that check's key** moves;
3. a **non-measurement is never cached**, and evicts any stale green under the same key;
4. a hit **replays the full detail list**, so warnings are not silently dropped;
5. `--no-memo`, and `--strict` implying it; `tests/conftest.py` disables the memo suite-wide so
   no monkeypatched test can poison a developer's cache.

> ⚠️ **The first version had four guards and a review pass found three holes anyway.** The
> generalisable lesson that came out of it is stated once, in
> [`CHECK_AUTHORING_GUIDE.md` §5](CHECK_AUTHORING_GUIDE.md#5-the-systemic-pattern--the-shapes-it-has-actually-taken),
> which owns the systemic-pattern ledger. Read it before adding a guard to anything here.

## 6. What this subsystem does not do

⚠️ **These are coverage GAPS, not absences.** A check exists for most of them; what is true
is that coverage is **per-artifact and partial** rather than corpus-wide:

- **Figure physics is unverified.** `bundle_figure_integrity` compares a bundle figure against
  a fresh render and asserts typeset legibility — real assertions, but structural. The
  `physics_checks` each `FigureSpec` declares (`mach_crosses_one`, `T_H_dominates`, …) are read
  only to be copied into the review manifest for a downstream LLM; nothing evaluates them.
- **Paper-quoted numbers are recomputed, for a few artifacts.** `paper_table` parses the
  *rendered* table the draft actually `\input`s and holds every cell to the canonical evaluator
  at the cell's own displayed precision; `d1_hierarchy_table` and `f_hierarchy_claims` do the
  same for their targets. There is no general mechanism that recomputes an arbitrary number
  quoted in arbitrary prose.
- **Citation content is verified, for cached PDFs.** `bibitem_title_primary_source` extracts
  page-1 text from the primary-source cache and compares it to the registry title, catching
  word-level drift. Entries with no cached PDF are outside its reach.
- **A cited theorem's STATEMENT is still unverified.** `prose_theorem_reference_coverage`
  resolves the *name* against `lean_deps.json`; nothing checks that the theorem's statement
  supports the sentence citing it. This one is a genuine absence, routed to ADR-010.

It does not run in CI. There is deliberately **no scheduled runner** (verified: no
`.github/workflows/`) — see
`docs/audits/2026-08-04-qa-qi-infrastructure/CI_DEFAULTS_ASSESSMENT.md`.

---

*Decision record: [ADR-009](../adrs/ADR-009-validation-suite-modularization.md) (decision +
§Deferred + addenda). The audit passes that produced these rules are under `docs/audits/`.*
