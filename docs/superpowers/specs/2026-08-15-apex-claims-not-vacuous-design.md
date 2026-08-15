# Design — `apex_claims_not_vacuous`

**Implements** [ADR-016](../../adrs/ADR-016-apex-claims-and-the-vacuity-registers.md)
D1–D5. Decisions are cited by their ADR numbers; this document does not restate their
rationale.

---

## The decider, written before the assertion (authoring guide §4.5)

**Property the check exists to establish:** every `apex_theorems[].claims` string is backed
by a statement that carries the content it asserts.

**What the assertion actually reads:** whether the declaration the apex resolves to is
recorded, or derivable, as **content-free** — and if it is, whether the `claims` string
says so.

Those differ, and the difference is stated rather than papered over: the check establishes
the *contrapositive floor* only. A green verdict means no apex is backed by a declaration
the project can show proves nothing. It does **not** mean any claim was verified against
its type — ADR-015 D3 established that prose↔type equivalence is not decidable, and
ADR-016 D6 keeps relevance out of scope.

## Inputs

| input | reached via | why not otherwise |
|---|---|---|
| bundle roster | `_H.bundle_codes_or_unmeasured()` | H1: never a literal roster (`no_rehardcoded_rosters`) |
| `papers/<code>/bundle_metadata.json` | `_read_metadata(code)` | the module's existing single reader |
| elaborated types | `lean/lean_deps.json` via `_H.load_lean_deps()` | the one loader; a second 70 MB parse is the duplicate-load defect |
| proof witnesses | `build_graph._scan_lean_theorem_bodies` over `_H.LEAN_DIR` | `lean_deps.json` carries types, **not `def` bodies** — witness triviality is unreachable by any type walk (finding §1.2) |
| registers | `src.core.constants` | — |
| thin-type classifier | `lean_statements._thin_type_label` | ADR-016 D1: reuse, never re-derive |
| trivial-witness patterns | `lean_substrate._TRIVIAL_BODY_RES`, `_NONTRIVIAL_MARKER_RE` | idem |

## Classification — five registers, one row per (bundle, apex)

For each declared apex that **resolves** (unresolved is `bundle_apex_resolves`' hard
failure and is skipped from the scored population, exactly as `apex_theorem_claims_grounded`
does):

| register | test | severity |
|---|---|---|
| `placeholder` | short name ∈ `PLACEHOLDER_LEAN_NAMES` | HARD |
| `thin-hard` | `_thin_type_label(type) ∈ _THIN_HARD` (`True`, reflexive `X=X`) | HARD |
| `thin-soft` | `_thin_type_label(type)` otherwise (`ground-arith`, `reflexive-literal`) | ratcheted |
| `baselined` | short name ∈ `VACUOUS_STATEMENT_BASELINE` | ratcheted |
| `disclosed-modeling` | `MODELING_ASSUMPTION_THEOREMS[…].category ∈ {definitional, vacuous_proxy}` | ratcheted |
| `trivial-witness` | body matches `_TRIVIAL_BODY_RES` and not `_NONTRIVIAL_MARKER_RE`, **name gate removed** (ADR-016 D2) | ratcheted |

A row may carry several registers; it is counted **once**.

## Disclosure predicate (ADR-016 D5)

`_APEX_VACUITY_DISCLOSURE_RE` over the `claims` string: an explicit vacuity/definitional
term — `rfl`, `definitional`, `trivial`, `tautolog*`, `vacuous`, `content-free`,
`scaffold`, `placeholder`, `stub`, `bookkeep*`, `sanity-check`, `closed arithmetic`,
`proves nothing`, `carries no content`, `single-point evaluation`, `retracted`.

⚠️ Deliberately a **vocabulary**, not a hedge-shaped window. `placeholder_not_cited`'s
320-character window exists because prose spreads a hedge across sentences; a `claims`
string is one field about one declaration, so proximity carries no information and a window
would only add a way to pass by accident.

## Legs

1. `apex_not_placeholder` — HARD, no ceiling constant. Live 0.
2. `apex_not_thin_hard` — HARD, no ceiling constant. Live 0 after ADR-016 D7.
3. `vacuity_disclosed` — `len(undisclosed) <= APEX_UNDISCLOSED_VACUITY_CEILING` (15).
4. `flagged_total` — `len(flagged) <= APEX_VACUITY_CEILING` (20).
5. `population` — `scored >= APEX_CLAIMS_SCORED_FLOOR` (635, shared with
   `apex_theorem_claims_grounded` rather than duplicated); below it the check returns `measured=False`
   (authoring guide §2.5).

**Every flagged row is printed by name on every run**, disclosed and undisclosed alike.
That is what makes leg 3 and leg 4 ratchets rather than suppression (ADR-016 D4).

## Cannot-measure branches — all FAIL, none pass (authoring guide §2.1)

| branch | result |
|---|---|
| roster unavailable | `passed=False, measured=False` |
| `lean_deps.json` unreadable | `passed=False, measured=False` |
| zero `.lean` sources read | `passed=False, measured=False` — the witness half is unmeasurable, and a body scan that reads nothing reports every apex clean |
| zero apexes scored | `passed=False, measured=False` |

The third is the seam `elaboration_knob_watchlist` and `proxy_body_audit` both shipped
open: an existing but empty tree scans nothing and issues a clean bill.

## Registration sites

Per `registration_sites.py apex_claims_not_vacuous`: check definition ·
`validate._CANONICAL_ORDER` · `validate.py` re-export · `EXPECTED_CHECKS` in
`tests/test_validate_registry_contract.py` · `MUTATION_VERIFIED` in
`tests/test_d5_mutation_obligation.py` · `verify_scope.py` path map ·
`SURFACE_INVENTORY.md` (regenerated). Plus `CI_MIN_CHECKS_RUN` +1;
`FIXTURE_ONLY_CEILING` unchanged (this check is production-seeded).

Order in `_CANONICAL_ORDER`: immediately after `apex_theorem_claims_grounded`. Not
semantic — neither regenerates an artifact the other reads — but the two share a
population and a floor, and adjacency is how a reader finds the second when they have
found the first.

## Non-vacuity proof (authoring guide §2.4)

`tests/test_d5_bundles_readiness.py`, seeded through `seed_journal.seeded_mutation` into
`papers/<a real bundle>/bundle_metadata.json` — the production artifact the check reads:

1. append an apex naming a `PLACEHOLDER_THEOREMS` declaration → leg 1 red;
2. append an apex naming a `_THIN_HARD` declaration (e.g. `davies_roan_classification`,
   whose statement is `True` and which no bundle declares) → leg 2 red;
3. append an apex naming a trivially-witnessed declaration with a claims string carrying no
   disclosure vocabulary → legs 3 and 4 red.

Each restores through the journal, not a bare `finally`.

## Deliberately out of scope

* relevance / sound-but-irrelevant citations — ADR-016 D6, filed;
* claim↔type equivalence — ADR-015 D3;
* hypothesis parity — `atlas_hypothesis_discipline`, `claims-reviewer` HD;
* remediating the 15 undisclosed rows in bundles other than D2 — filed per bundle.
