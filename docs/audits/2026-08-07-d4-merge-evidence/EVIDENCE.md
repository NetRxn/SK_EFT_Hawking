# ADR-010 §D4 — merge/split/retire EVIDENCE

**Running ledger. Evidence only — no recommendation is made here.** ADR-010 §D4's recommendation
comes due when every bundle is declared; until then this file records, for each proposed change,
whether the closure evidence **supports** it, **refutes** it, or **does not decide** it, plus any
**boundary failure** named under §D2's rule.

**Status:** 10 of 21 bundles declared (D1, D2, D3, D6, D9, D10, D11, D12, F, L2).
11 undeclared: D4, D5, D7, D8, E1, E2, I1, I2, I3, L1, L3. **Every "not decided" below is a
statement about what is measurable today, not a verdict.**

**Method.** Each row is an intersection of *declared apex closures* over `name_deps_project`,
computed by `scripts/bundle_closure.py`. A closure intersection is evidence about **shared
substrate**, which is one input to a merge decision and not the whole of it — audience, venue and
framing are the operator's, per ADR-010 C5.

---

## 1. The four proposals ADR-010 names

### D6 + D9 — **supported on its own merits, but the finding was RELOCATED**

The 2026-08-01 audit rests the merge on 78 shared theorems. The retrofit reproduces that number
exactly **and relocates what it means**: D6's and D9's *declared* closures are **disjoint**. D6
cites 133 declarations from D9's namespace and claims almost none of them with its own apexes,
covering only ~19 % of its own citations.

**That is borrowing, not duplication**, and the remedy for borrowing is attribution or absorption,
not necessarily a merge. Recorded in `docs/audits/2026-08-06-d6-retrofit/FINDINGS.md`.

### D6 + D9 + **D12** — **REFUTED**

`D6 ∩ D12 = 0`, `D9 ∩ D12 = 3`. D12 does not belong to the three-way merge the strategy
document's outline proposes. Recorded in `docs/audits/2026-08-06-d12-retrofit/FINDINGS.md`.

### D10 + D11 — **REFUTED**

`D10 ∩ D11 = 0` — no shared substrate at all. The pairing tracks the order the two were
authorized (both 2026-06-29), not their content.

**Where D10 actually couples is D9**: `D10 ∩ D9 = 50`, all in `QuantumNetwork.*`, every one
claimed by D9's own apexes. If a D10 merge or sequencing question is live, it is with D9.
Recorded in `docs/audits/2026-08-07-d10-retrofit/FINDINGS.md` §2.

### E1 + E2 — **NOT DECIDED**

Both undeclared. No closure exists for either, so nothing is measurable. ⚠️ Their shared parent
is D1, whose closure is now known (249 declarations / 18 modules); the E1/E2 question becomes
measurable as soon as either is declared.

### D4 → D8 — **NOT DECIDED**

Both undeclared. The 2026-08-01 audit's evidence pass reported that the evidence *"does not
support the D4→D8 merge as stated"*; that predates any closure for either bundle and is not
reproduced here. ⚠️ **Do not quote the audit's verdict as a closure measurement** — it is not one.

---

## 2. Other intersections, measured incidentally

Recorded because §D4 asks for evidence, and an intersection nobody proposed is still evidence.

| pair | shared | reading |
|---|---|---|
| **F ∩ D3** | **126** | F's substrate is largely D3's. Expected for a survey; see the boundary-failure note below. |
| **L2 ∩ D2** | **391 of L2's 430 (91 %)** | L2 is a near-subset of D2 — the shape a PRL splash extracted from D2 §2 should have. The **39** outside are the Ext-computation modules (`A1Ring`, `A1Resolution`, `A1Ext`, `A1ExtSubstantive`) plus `WangBridge`. |
| **F ∩ D1** | **27** | |
| **D2 ∩ D3** | **3** | All `GenerationConstraint`, reached by exactly one D3 apex (`horizon_wittTrivial_iff_three_generations`). The Witt bridge — see TODO-D16. |
| **D2 ∩ D12** | 3 | All `PauliMatrices`. Shared low-level infrastructure; decides nothing. |
| **D10 ∩ D12** | 1 | Ditto. |
| all other declared pairs | **0** | D1, D3, D6, D9, D10, D11, F, L2 are otherwise mutually disjoint at declaration level. |

---

## 3. Boundary failures named under §D2's rule

> *"A target whose purpose cannot be stated without reference to another target's substrate is a
> boundary failure and must be named as one."*

| target | verdict | basis |
|---|---|---|
| **F** | ⚠️ **YES — by genre** | 126 of its 221 declarations are D3's. A survey's purpose is *definitionally* unstatable without its siblings' substrate, so the rule here is diagnosing the genre rather than a defect. **The actionable consequence is sequencing: F cannot be redrafted until the bundles it surveys are measured.** |
| **D10** | ⚠️ **PARTIAL** | §5.3's contractivity result is not statable without D9's `QuantumNetwork.*` — 50 declarations. The DFT and NEGF pillars are wholly D10's own, so the *target* is viable; one of its three headline layers is not self-contained. |
| **D6** | ⚠️ **PARTIAL** | Cites 133 declarations from D9's namespace while claiming ~19 % of its own citations. |
| D1, D2, D3, D11, D12, L2 | **No** | Each states its purpose on its own substrate. D11 is the strongest case: zero intersection with every other declared bundle. |
| D4, D5, D7, D8, E1, E2, I1, I2, I3, L1, L3 | **not yet measurable** | undeclared |

---

## 4. What this file must NOT be read as

- **Not a recommendation.** ADR-010 §D4's recommendation is assembled once all 21 are declared,
  and the roster number, D10's scope and L1's disposition are operator-owned (ADR-010 §Open).
- **Not a substitute for reading the drafts.** Closure overlap measures shared substrate. Two
  bundles can share nothing and still belong together (different facets of one argument), or share
  a great deal and belong apart (a splash and its parent). C4 stands: the manuscripts decide.
- **Not stable.** Every "0" against an undeclared bundle is *unmeasurable*, not *empty*. Re-run
  each row when its counterpart is declared — **D3 ∩ D2 was 0-by-unmeasurability and turned out to
  be 3** once D2 was declared, which corrected a filed finding (V27 B2).
