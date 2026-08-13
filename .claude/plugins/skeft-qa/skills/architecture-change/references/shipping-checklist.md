# Shipping an infra change — non-vacuity, registration, docs

Step 7 of `SKILL.md`, in detail. Two of these three obligations take the suite down when missed;
the third takes nothing down, which is why it is the one that rots.

`docs/architecture/CHECK_AUTHORING_GUIDE.md` owns what a check must *be* — §2.1–§2.7 and the §6
checklist. This file owns only what a check must be **wired into**, which no single document owns
today, and it exists to be re-derived rather than quoted.

---

## 1. Non-vacuity — the bar a check clears to count as built

`CHECK_AUTHORING_GUIDE.md` §2.4 and §2.5 are authoritative. The two facts that decide whether the
change is shippable at all:

- The mutation is seeded into **the real artifact the check reads**, `validate.py --check <name>`
  observes red, and the artifact is restored. A fixture-only mutation proves the test works, not
  that the check can fail in production.
- `tests/test_d5_mutation_obligation.py` carries the split. `AWAITING_MUTATION_TEST` is empty,
  `AWAITING_CEILING` is `0`, and `FIXTURE_ONLY_CEILING` may only shrink — so **deferral is not
  available** and a fixture-only test is not merely weaker, it is blocked. Verify those three
  values at HEAD before planning around them; they are ratchets and they move.

A check whose population can be empty while it reports PASS does not count as built (ADR-012 §D8).
Guard the seam per §2.5: count what is actually read, and gate on that count.

---

## 2. Registration — derive the sites, never quote them

Every site below was confirmed by reading the code. **Re-derive anyway**, with the commands given:
the set grows, and the failure mode this section exists to prevent is exactly an inherited list.

*In ADR-012:* the plan's global constraints enumerated **six** obligations and omitted
`EXPECTED_CHECKS`. Three tests went red on the first registered check.

| # | site | what missing it does |
|---|---|---|
| 1 | `@register_check(...)` in the right `scripts/validation/checks/<module>.py` | the check does not exist. Module choice: guide §3 |
| 2 | `scripts/validate.py` `_CANONICAL_ORDER` | **raises** — takes the whole suite down. Position is semantic: a regenerator precedes its consumers |
| 3 | the re-export line in `scripts/validate.py` (`check_x = _checks_<mod>.check_x`) | importers that reach the check by name off `validate` break |
| 4 | `CI_MIN_CHECKS_RUN` in `scripts/validation/_config.py` | `--ci`'s coverage floor no longer matches the roster; the floor counts **measurements**, not invocations |
| 5 | `MUTATION_VERIFIED` (naming a real test) in `tests/test_d5_mutation_obligation.py`, plus a `PRODUCTION_SEEDED` entry | the mutation-obligation contract fails on arrival |
| 6 | `EXPECTED_CHECKS` in `tests/test_validate_registry_contract.py` | **the site the plan missed.** Both the count and the ORDER are frozen, so it fails twice |
| 7 | regenerated `docs/architecture/SURFACE_INVENTORY.md` (`uv run python scripts/architecture_inventory.py --write`) | `architecture_inventory_fresh` fails: the census no longer matches a fresh derivation |

**Conditional, and easy to miss because it is silent until it is not:**
`EXPECTED_CHECK_FUNCTIONS` in `tests/test_validate_public_surface.py` freezes the names other test
files import off `validate` **by name**. A check is added there only when something imports it that
way — so the obligation appears later, when the first such importer is written, not at registration.

### Re-derive the set

```bash
# From the repo root. Each command locates the site rather than trusting the row above.
grep -rn "_CANONICAL_ORDER" scripts/validate.py | head -3
grep -n "^check_.* = _checks_" scripts/validate.py | head -3          # the re-export idiom
grep -rn "CI_MIN_CHECKS_RUN" scripts/validation/_config.py scripts/validate.py
grep -n "MUTATION_VERIFIED\|PRODUCTION_SEEDED\|AWAITING_CEILING\|FIXTURE_ONLY_CEILING" \
    tests/test_d5_mutation_obligation.py | head
grep -n "EXPECTED_CHECKS" tests/test_validate_registry_contract.py | head -3
grep -rn "EXPECTED_CHECK_FUNCTIONS" tests/test_validate_public_surface.py | head -3
```

The general form of the derivation, which survives a site being added: **take an existing check's
name and find every file that mentions it.** That set is the obligation set.

```bash
grep -rln "ledger_ids_resolve" scripts/ tests/ docs/architecture/
```

`ledger_ids_resolve` is the right probe because it was registered most recently and carries every
obligation — it is ADR-012's own promoted check (§D13).

### Then run the gates

```bash
uv run python scripts/validate.py --check <name> --no-archive   # it runs at all
uv run python -m pytest -q                                      # repo suite + the plugin's guards
```

The bare `pytest` form is deliberate: it picks up **both** testpaths. Passing an explicit path
scopes the run, which is how the plugin's own surface guards went unrun for a period.

---

## 3. Documents, in the same commit

Architecture rule 2. Not a follow-up, not a cleanup task.

- The `docs/architecture/` document that owns the surface is corrected in the commit that makes it
  wrong. If the change makes one of its statements false, fixing that statement **is** part of the
  change.
- No census count enters a `docs/architecture/` narrative — rule 3, and it is machine-enforced by
  `architecture_inventory_fresh`. Name the mechanism, link to the census.
- A load-bearing prose claim earns an entry in `tests/test_architecture_claims.py`. Those
  assertions bind in **both** directions — the claim's sentence verbatim, and the code fact that
  makes it true — so a reword forces re-verification and a code change forces the document to
  follow. Nothing else in this repository verifies a prose claim.
- Correct a false claim **in place, with its scar**, rather than deleting it silently. ADR-012's
  §P8d records why: a corrected mistake with no scar gets re-litigated.

⚠️ *In ADR-012:* the canonicalization of `DASHBOARD.md` immediately surfaced a third unresolved
reference the design had not predicted — and the file **existed**; the scanner's roots tuple simply
never walked its directory. The fix was the root, not an exception entry. A root missing from that
tuple makes a live file indistinguishable from a deleted one, which inverts the check's purpose.
When a guard fires on arrival, establish which of the two it is before writing an exception.
