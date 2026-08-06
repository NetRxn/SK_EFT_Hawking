# Validation subsystem — architecture

**Production document.** The durable description of how `validate.py` and
`scripts/validation/` are built and why. Written 2026-08-05, after ADR-009 completed, because
the only accounts of this subsystem were a *decision record* (`ADR-009`) and a *migration note*
in `.working-docs/` — neither of which is where a reader should have to look for the
architecture of a live system.

**Companions:** [`VALIDATION_GATE_TOPOLOGY.md`](VALIDATION_GATE_TOPOLOGY.md) (when each gate
runs and what it blocks) · [`CHECK_AUTHORING_GUIDE.md`](CHECK_AUTHORING_GUIDE.md) (obligations a
new check inherits) · [`QA_QI_INFRASTRUCTURE_MAP.md`](QA_QI_INFRASTRUCTURE_MAP.md) (the defect
landscape this subsystem exists to close).

---

## 1. The one-sentence shape

`scripts/validate.py` is a **framework** (~720 lines, zero registered checks); the **59 checks**
live in twelve modules under `scripts/validation/checks/`; three framework modules
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
  checks/                        # 12 modules, 59 checks, ~8,969 lines
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

**Why the framework/check split.** A single 7,900-line `validate.py` made every check's
dependencies implicit and made "does this file fit in one read" unanswerable. ADR-009 D1 set the
criterion: **every module readable in one pass.** As built: 12 modules averaging ~750 lines.

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
it and `_apply_canonical_order()` sorts in place. This matters because three checks in
`freshness.py` *regenerate artifacts other checks read* — their position relative to their
consumers is semantic.

## 3. The four hazards, and how each is structurally prevented

These are ADR-009 D3. They are not style rules; each names a failure the project has shipped.

| | hazard | rule | enforced by |
|---|---|---|---|
| **H1** | a path derived from `__file__` resolves to `scripts/validation/checks/`, so every artifact lookup silently misses | reach paths as `_H.<NAME>` **at each use** — never a module-level alias, never from `__file__` | `test_no_check_derives_a_path_from___file__` |
| **H3** | import order silently becomes execution order | `_CANONICAL_ORDER` owns it | `test_regenerators_precede_their_consumers` |
| **H4** | the same missing artifact means different things in different checks; a shared helper would unify them silently | helpers own *where a thing is*, **never what its absence means** | `test_cannot_measure_baseline` freezes the divergent policies |
| **H5** | `from validate import STRICT_MODE` binds a **copy** at import time; `--strict` becomes a silent no-op | reach flags by **attribute** on `_config` | `test_validate_flag_propagation` |

⚠️ **H5's structural test is not sufficient on its own.** `co_names` records names used for both
`LOAD_GLOBAL` and `LOAD_ATTR`, so an import-time copy still appears there. The guard additionally
requires `_cfg` in `co_names` — an imported copy has no attribute access to show.

## 4. Runtime flags (`_config.py`)

| flag | set by | meaning |
|---|---|---|
| `STRICT_MODE` | `--strict` | promote submission advisories to hard failures; read by 6 checks |
| `FORCE_LATEX` | `--force-latex` | recompile every bundle draft, bypassing the per-draft cache |
| `FORCE_NOTEBOOK_REEXEC` | `--force-notebooks` | bypass the notebook skip-cache |
| `NO_MEMO` | `--no-memo` | bypass the expensive-check memo; **implied by `--strict`** |
| `CI_MODE` | `--ci` | unattended-runner profile + coverage floor |

## 5. Change-scoping: `_memo.py` and the per-draft LaTeX cache

Measured 2026-08-05: the suite cost **332.6 s**, and **43 of 55 checks finished under one
second**. The cost was three checks. Two caches now scope them to what changed:

* **`_memo.py`** — a check's verdict is reused only while a fingerprint of *every input it reads*
  is unchanged since its last PASS. Applied to `axiom_closure_allowlist` (**171.6 s → 0.1 s**)
  and `lean_docstring_refs_resolve`.
* **`paper_latex_compiles`** — per-draft content-hash cache over the draft's full `\input`
  closure. With the cost gone, its **slow gate was deleted**: it had returned `passed=True` with
  `SKIPPED (slow)` by default, which is why a fatal LaTeX error in D3 was invisible for months.

Full suite: **317.8 s → 134.2 s**, with the LaTeX compile now actually running.

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

> ⚠️ **The lesson worth carrying.** The first version had four guards, and PR-review pass 2 found
> three holes anyway. All four guards policed *how the cache is used*; none audited *whether the
> key spans the inputs*. **Guarding at the wrong layer is indistinguishable from guarding, right
> up until the measurement.**

## 6. What this subsystem does not do

- It does not verify **figure content**, recompute **paper-quoted numbers** from their formulas,
  check that a **cited theorem's statement** supports the prose, or verify **citation content**.
  Those are absent checks (pass-1 R5-C2…C5), routed to ADR-010.
- It does not run in CI. There is deliberately **no scheduled runner** — see
  `docs/audits/2026-08-04-qa-qi-infrastructure/CI_DEFAULTS_ASSESSMENT.md`.

---

*Sources: ADR-009 (decision + §Deferred 0–7 + addendum II), `docs/audits/2026-08-04-qa-qi-infrastructure/`
(pass 1), `docs/audits/2026-08-05-pr-review-2/` (pass 2).*
