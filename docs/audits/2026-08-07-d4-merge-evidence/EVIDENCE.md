# ADR-010 §D4 — merge/split/retire EVIDENCE

**Running ledger. Evidence only — no recommendation is made here.** ADR-010 §D4's recommendation
comes due when every bundle is declared; until then this file records, for each proposed change,
whether the closure evidence **supports** it, **refutes** it, or **does not decide** it, plus any
**boundary failure** named under §D2's rule.

**Status:** 18 of 21 bundles declared (D1–D12, F, I1, I2, I3, L1, L2).
3 undeclared: E1, E2, L3. **Every "not decided" below is a
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

### D4 → D8 — ✅ **RESOLVED AT DECLARATION LEVEL** (both declared 2026-08-07). Merge still NOT recommended here.

**D4 §9 ships the complete quantitative Solovay–Kitaev substrate** — F.21 density, the
Dawson–Nielsen length bound, the eight-module Phase-6t `FKLW/` pipeline, and the Path-A
constructive compiler across three ε-regimes. **D8's charter is the alphabet-agnostic SU(d)
generalisation**, which is the `FKLW/GenericSU2` layer.

Underscore-aware scan over all 21 drafts:

| theorem | named by |
|---|---|
| `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict` | **D4 only** |
| `fibonacci_density_F21_unconditional` | **D4 only** |
| `skLengthExponent` | **D4 only** |
| `…quantitative_cliffordT_strict_constructive_tight_unconditional` | **D4 *and* D8** |

**Resolved by reading D8 in full.** D8 cedes Fibonacci to D4 **explicitly, twice** (§4 and
§Relationship-to-companion-work: *"its universality is the subject of a companion bundle, which
this paper cites for the Fibonacci anchor and generalizes"*), while building its own §§2–3 on the
Clifford+T / `GenericSU2` / `SU(d)` layer that D4 named only in a module list.

| content | owner | basis |
|---|---|---|
| F.21 density, `…quantitative_fibonacci_strict`, Path A | **D4** | D8 cedes it; D4 §9 develops it |
| Clifford+T, trapped-ion, `GenericSU2`, `GenericSUd` | **D8** | D8's §§2–3; D4 listed only |

**Four apexes moved D4 → D8.** The closure corroborates independently: **D4 fell 753 → 620
declarations, 61 → 43 modules**. `D8 ∩ D4 = 280` remains — the shared Lie-algebraic core
(`OneParameterSubgroupSU2` 108, `SU2LieAlgebra` 30, `SolovayKitaevPathA` 27), which is what an
"instantiate, don't re-derive" substrate looks like from both sides.

⚠️ **This settles ownership, NOT the merge.** Two bundles sharing a substrate core by design is an
argument for keeping them separate as much as for merging them; the disposition is the operator's.

**The third claimant is corrected by D8's own text.** F §7 says D6 absorbed *"the Phase 6t
quantitative Solovay–Kitaev tight-ε headline"*. D8 says the sibling FT bundle *"consumes the
quantitative Solovay–Kitaev **developed here**"* — i.e. D8's, not D4's. And **`D8 ∩ D6 = 0` and
`D4 ∩ D6 = 0`**: D6's declared substrate contains neither, so F's absorption claim is unbacked
from both directions.

⚠️ **Do not quote the 2026-08-01 audit's "does not support D4→D8 as stated" as a closure
measurement** — it predates any closure for either bundle.

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
| **D4 ∩ F** | **73** | `QCyc16` 19, `BHEntropyMicroscopic` 17, `FigureEightKnot` 16. |
| **D4 ∩ D3** | **22** | The horizon-MTC cross-bridge — mutual and acknowledged in both drafts. |
| **D4 ∩ D2** | 3 | Only `PauliMatrices`. ⚠️ **Not** the Drinfeld-centre bridge both drafts describe. |
| **D5 ∩ F** | **17** | `EntropicGravityDarkEnergy` 16 — F's §8 dark-sector register is D5's. |
| **D8 ∩ D4** | **280** | The shared Lie-algebraic core after the reassignment — `OneParameterSubgroupSU2` 108, `SU2LieAlgebra` 30. |
| **D8 ∩ D9** | 14 | `QuantumNetwork` diamond-norm infrastructure for D8 §10, acknowledged in the text. |
| **D8 ∩ D10** | 8 | Same layer. |
| **I1 ∩ D1** | **30** | `SKDoubling` 27 — a methodology paper's overlap tracks its case studies' *substrate*, not their subject matter. |
| **I1 ∩ F** | **26** | `SKDoubling`. |
| **D5 ∩ D3** | **11** | `JacobsonThermoGRDarkEnergy` 9, `ADWMechanism` 2 — D5 supplying, not consuming. |
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
| **D4** | ⚠️ **YES, both directions** | *Inbound:* §§7–8 consume D3's `H_HorizonBoundaryCondition` (22 shared declarations) — mutual and acknowledged. *Outbound:* §9's `GenericSU2` layer ships D8's chartered content. |
| D1, D2, D3, D5, D7, D8, D11, D12, I1, I2, I3, L2 | **No** | Each states its purpose on its own substrate. D11 is the strongest case: zero intersection with every other declared bundle. |
| E1, E2, L3 | **not yet measurable** | undeclared |

---

## 3b. Declaration conflicts found and resolved (not merges — ownership)

Two bundles' apex lists overlapped on content a *third* reading showed belonged to one of them.
Both were resolved by reading the second draft in full and letting the drafts' own framing decide,
with the closure as independent corroboration.

| conflict | resolution | corroboration | signal strength |
|---|---|---|---|
| **D4 / D8** — four `GenericSU2` apexes | → **D8**. D8 cedes Fibonacci to D4 *in words, twice*; D4 named the Clifford+T layer only in a module list | D4's closure fell **753 → 620**, modules **61 → 43** | **strong** — a draft ceding explicitly |
| **D1 / D7** — six demarcation apexes | → **D7**. D7's title, abstract and §§2–6 are the content; D1 §8.2 is an *"Independent cross-check"* subsection | D1's closure fell **249 → 171**, modules **18 → 12** | ⚠️ **weaker** — neither draft mentions the other; the decision rests on document position, and should be revisited if the operator reads D1 §8.2 as load-bearing |

**The rule both instances produce:** *the container that develops content owns it; the container
that cites it in a cross-check subsection does not.* **Record the strength of the signal** — a
draft that cedes in words is stronger evidence than document position.

## 4. What this file must NOT be read as

- **Not a recommendation.** ADR-010 §D4's recommendation is assembled once all 21 are declared,
  and the roster number, D10's scope and L1's disposition are operator-owned (ADR-010 §Open).
- **Not a substitute for reading the drafts.** Closure overlap measures shared substrate. Two
  bundles can share nothing and still belong together (different facets of one argument), or share
  a great deal and belong apart (a splash and its parent). C4 stands: the manuscripts decide.
- **Not stable.** Every "0" against an undeclared bundle is *unmeasurable*, not *empty*. Re-run
  each row when its counterpart is declared — **D3 ∩ D2 was 0-by-unmeasurability and turned out to
  be 3** once D2 was declared, which corrected a filed finding (V27 B2).

---

## 6. L1 / D3 / F — a declaration conflict recorded as EVIDENCE, deliberately not resolved

**Found 2026-08-07 at L1's retrofit** (`docs/audits/2026-08-07-l1-retrofit/FINDINGS.md` §3). Not one
of the four proposed merges; it bears on the reserved **`L1 disposition`** STOP-AND-ASK item.

**Measured.** L1's entire closure is 18 declarations in **one** module, `GravitationalWaves.lean`,
at depth 1. That module is already claimed by two siblings:

| | apexes in `GravitationalWaves` | of which L1 also declares |
|---|---|---|
| **L1** | 11 | — |
| **D3** | 8 | **5** |
| **F** | 3 | **3** (all of F's) |

**L1's declaration-level unique content is exactly two things:** the correctness-push biconditional
`c_GW_match_iff_chi_close_to_one`, and the five-theorem `H_VestigialModeIsGraviton` tracked-hypothesis
bundle (one discharge + four falsifiers isolating P1, P2 and P3'). **The falsification headline
itself — both endpoint falsifiers, the bundled corollary, the disjointness theorem and its
frame-independent form — is already declared by D3 and F.**

**Which container develops it, by each draft's own framing:**

- **L1** — the title, the abstract, both `theorem` environments, the figure caption's Lean witness.
  The whole Letter is this result.
- **D3** — one lane closure inside an emergent-gravity survey: *"Volovik's vestigial second-sound
  graviton is falsified by GW170817 to roughly fourteen orders of magnitude"*, listed beside other
  closed lanes. D3 additionally declares three `c_GW_*` lemmas L1 subordinates to its definition,
  using `c_GW_at_chi_one` to close a displayed equation of its own.
- **F** — one example of *"NO-GO results reported as first-class predictive content rather than
  absences."* A survey citation, in a single sentence.

**Why nothing was reassigned.** The D4→D8 and D1→D7 conflicts moved apexes between containers whose
*existence* was settled, and each was decided by the drafts' own words or document position with the
closure corroborating. **This one asks whether L1 exists as a container at all** — the ownership rule
does not reach that far, and under ADR-010 C5 moving declarations here would pre-decide a charter.
The duplicate declarations stand as the evidence.

**Status: NOT DECIDED — reserved to the `L1 disposition` item.** The evidence above is the input;
the decision is not mine. If L1 stands, the six unique theorems are its spine and D3/F should cede
the other five. If L1 folds into D3, D3 already declares most of it.

