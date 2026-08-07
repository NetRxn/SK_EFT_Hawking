# Accuracy verification ledger

**Purpose.** Track assertion-granularity verification of every architecture document, so
scope cannot be silently dropped and "complete" is earned rather than asserted.

**Why this exists.** Two prior passes reported completion and were wrong. The first checked
~20% of the surface and called it 100%. The second checked at **bullet** granularity — for a
compound claim it verified the measurable clause and let the rest ride, then reported the
bullet verified. Three errors survived into documents declared correct:

| escaped claim | how it hid |
|---|---|
| `"Invariant #16 cites the doc under a wrong filename"` | 3 assertions in one sentence; the *adjacent* bullet half (two files absent) was true and checked |
| `"--strict is scoped to submission by Invariant #12"` | `--strict`'s BEHAVIOUR was verified; that the invariant SAYS so was not |
| `"the four hazards … These are ADR-009 D3"` | each named test was verified to exist; the **completeness of the set** was never checked (D3 declares five) |

**The rule this ledger enforces:** an entry is `VERIFIED` only when **every atom** of it has
its own recorded check. A compound sentence is not one entry — it is one entry per assertion.

**Status key:** `TODO` · `IN-PROGRESS` · `VERIFIED` (every atom checked, method recorded) ·
`CORRECTED` (was wrong, fixed, atoms re-checked).

---

## Per-document progress

| document | sections | status |
|---|---|---|
| `README.md` | index table · two rules · scope boundary | TODO |
| `SURFACE_INVENTORY.md` | header prose · derivation sources (tables are derived + gated) | TODO |
| `VALIDATION_ARCHITECTURE.md` | §1–§6 | TODO |
| `CHECK_AUTHORING_GUIDE.md` | thesis · §1–§6 | TODO |
| `VALIDATION_GATE_TOPOLOGY.md` | §1–§7 | TODO |
| `QA_QI_INFRASTRUCTURE_MAP.md` | §1–§6 | TODO |
| `END_TO_END_MAP.md` | §1–§9 | TODO |

## Method, per atom

1. Restate the atom as a single falsifiable proposition.
2. Name the artifact that decides it (file + symbol, or a command).
3. Run the check; record the result verbatim.
4. If the atom is about a **set** (all/every/only/none), verify the set's **completeness**,
   not just that named members exist — that is how the D3 five-vs-four error survived.
5. If the atom cites an invariant/ADR/doc **by number or section**, verify the number resolves
   to that subject — not merely that the cited behaviour is real. That is how the #12 and #16
   errors survived.

---

## Corrections found by this pass

(Appended as found; each carries the atom that failed and the evidence.)
