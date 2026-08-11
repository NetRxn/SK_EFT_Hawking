# D2 apex retrofit — a bridge I said did not exist, and L2 measured as a near-subset

**Date:** 2026-08-07 · Tenth bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/D2/paper_draft.tex`
(1,403 lines, every line, including the commented stubs after the bibliography),
`bundle_metadata.json`, and — for the findings — per-apex closure walks over `name_deps_project`.

---

## 1. What was declared

**47 apexes → 516 declarations across 60 modules, depth 11, 4 private truncations.**

| thread | apexes |
|---|---|
| (i) modular generation constraint | 6 |
| the 16-convergence and the Rokhlin route | 23 |
| the Schellekens / holomorphic-VOA reading | 3 |
| (ii) SM Z16 anomaly + categorical layer | 2 |
| the NbRe material exhibit | 6 |
| (iii) chirality wall, three pillars | 7 |

**`dai_freed_spin_z4` excluded** — D2 §5.2 calls it *"a trivially-discharged placeholder pending
Mathlib's cobordism infrastructure"*, the same disposition F gave it. Declaring it would make D2
claim what it explicitly disclaims.

---

## 2. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Particle theorists and formal-methods researchers who take anomaly arguments for SM fermion content seriously and want the hypothesis budget itemised rather than asserted. |
| **Venue** | PRD or JHEP, per the metadata. The four-thread scope and the algebraic-topology apparatus fit a long article; neither is PRL-shaped, which is precisely why L2 exists. |
| **The claim only this container can make** | **The convergence itself, with its hypothesis budget exposed.** Paper-length treatments of the modular argument, the Z16 anomaly and the chirality wall exist separately (the draft says so). What D2 alone reports is what happens when all four threads are put inside **one** Lean library: which hypotheses are shared, which are Mathlib-deferrals of established mathematics (H1/H3/H4), which is a genuine open research conjecture (`TPFConjecture`), and which is a trivially-discharged placeholder (`dai_freed_spin_z4`). No sibling can make that claim because no sibling holds all four threads. |
| **Substrate** | `GenerationConstraint`, `ModularInvarianceConstraint`, `WangBridge`, `ChangeOfRings`, `A1Ring`/`A1Resolution`/`A1Ext`, `E8Lattice`, `AlgebraicRokhlin`, `RokhlinClassification`, `RokhlinHMRankFour`, `LatticePrimitive`, `LatticeSignature*`, `SpinRokhlinInterface`, `RokhlinArfNoGo`, `Schellekens/*`, `Z16AnomalyComputation`, `SPTStacking`, `ToricCodeCenter`, `VecGMonoidal`, `CenterEquivalenceZ2`, `NbReTripletSPT`, `GoltermanShamir`, `LatticeHamiltonian`, `TPFEvasion`, `WilsonMass`, `GTCommutation`, `PauliMatrices`, `BdGHamiltonian`, `OnsagerAlgebra`, `OnsagerContraction`, `GTWeylDoublet`, `ChiralityWallMaster`, `VillainHamiltonian`, `FKGappedInterface`, `SPTClassification`. **60 modules, 516 declarations, depth 11** — the second-deepest closure in the portfolio. |
| **Honest size vs charter** | 1,403 lines. Charter for a Tier-1 deep paper is ~40pp; D2 is materially short of that, and the shortfall is **not** a substrate shortfall — its closure is the third largest measured. The gap is between what the Lean holds and what the manuscript reports. |
| **Boundary failure?** | **No.** D2's purpose is statable without reference to another target's substrate. It *cites* D4 for the non-abelian Drinfeld centre and L2 for the PRL extraction, but both are forward references from a self-contained argument, and the closure confirms it: D2 ∩ D4-relevant content is not load-bearing, and D2's own apexes reach all 60 modules by themselves. |

---

## 3. ❌ TODO-D16 must be NARROWED — a bridge does exist, and I said none did

Yesterday's D3 findings stated: *"**no** declaration in D3's heat-kernel / linearised-EFE /
coefficient-match modules depends on any `Z16*`, `Modular*`, `SPT*` or `Chirality*` module"*, and
generalised to *"no D3 gravity-side declaration reaches the anomaly-side tree at all."*

**The second sentence is false.** D2's closure now makes it measurable:

| measurement | result |
|---|---|
| **D2 ∩ D3** | **3** — `div_24_8n_implies_div_3_n`, `div_3_n_implies_div_24_8n`, `generation_constraint_iff`, all in `SKEFTHawking.GenerationConstraint` |
| which D3 apex reaches them | **`horizon_wittTrivial_iff_three_generations`** — and only that one, per a per-apex closure walk over all 89 |
| Sakharov/heat-kernel chain (5 apexes → 19 decls / 4 modules) ∩ D2 | **0**; it never reaches `GenerationConstraint` |

**So D3's §7.3 prose claim is witnessed, and it is the one I should have looked for.** D3 says the
Witt sharpening *"ties the horizon boundary condition to the program's three-generation result
through the **same** Witt invariant."* The closure agrees: `24 ∣ c₋ ⟺ 3 ∣ N_f` is literally
shared between D3's horizon boundary condition and D2's headline.

**What still stands, and it is the narrower claim TODO-D16 should have made:** the `N_f` in the
**Sakharov coefficient** `G_N = 12π/(N_f Λ_UV²)` is a *Dirac-flavour count in a heat-kernel
expansion*; the `N_f` in `c₋ = 8 N_f` is a *generation count*. **Those two are what F asserts to
be the same, and that identity has no witness** — the heat-kernel chain touches nothing D2 claims.
The bridge that exists runs through the horizon central charge, not through the Sakharov
coefficient.

⚠️ **This is the second time in two days that a "nothing reaches X" claim has been too broad.**
The first (`native_decide`, V26) was a wrong instrument; this one was a **narrow probe reported at
wide scope** — I searched D3's *calibration* modules and wrote the conclusion about D3's *gravity
side*. The probe was right; the sentence covering it was not.

---

## 4. ADR-010 §D4 evidence — L2 is a near-subset of D2

**Recording evidence only. The L2 disposition is an operator-owned open item and is not decided
here.**

| measurement | result |
|---|---|
| L2 closure | 430 declarations |
| **L2 ∩ D2** | **391** |
| L2 outside D2 | **39**, in `A1Ext`, `A1ExtSubstantive`, `A1Resolution`, `A1Ring`, `WangBridge` |

**91% of L2's substrate lies inside D2's.** That is exactly the shape a PRL splash extracted from
D2 §2 should have, and it is *not* a boundary failure: a splash is meant to be a subset, and L2's
purpose — the four-page headline result — is statable on its own.

The 39 outside are the interesting part: they are the **Ext-computation modules** and
`WangBridge`. L2 declares `ext_dims_substantive` and `ext_computation_summary` as apexes; D2
describes the same computation in §2.4 but its declared apexes reach it only partially. **If a
merge or an absorption were ever considered, those 39 are what would have to move**, and if D2 is
meant to be the container of record for the Ext computation, its apex list is currently short by
those two results.

**Other pairs, for the §D4 record:** D2 ∩ D12 = 3 (all `PauliMatrices`, shared low-level
infrastructure, decides nothing); D2 ∩ D1, D6, D9, D10, D11, F = **0** each.

---

## 5. Also observed

- **Two more empty section stubs after the bibliography** — *"SymTFT audit substrate"* and
  *"APS η-invariant cross-bridge to Z16 Dai-Freed (Phase 6o W2a)"*, both commented out. TODO-D14
  now spans three bundles.
- **Mathlib pin hardcoded**: `\newcommand{\mathlibcommit}{5e932f97}` (the v4.29.1 tag) against a
  live `81a5d257`. Covered by TODO-D6 and reported by `paper_toolchain_pin_drift`; recorded, not
  re-filed.
- **`native_decide` is used and disclosed** — §2.4 says `A1Ring` relation verification and the
  `A1Resolution` `d² = 0` RREF witnesses are closed by `native_decide`. **True**, and consistent
  with the corpus figure of 546 declarations in the closure. This is the draft that caught my
  withdrawn finding (V26).

---

## 6. What D2 gets right

Its §5 is a five-part accountability structure — *what is proved · what is axiomatised · tracked
hypotheses · what is conjectural and motivational · falsification* — and it makes a distinction
none of the other drafts make: **it separates Mathlib-deferrals of established mathematics
(H1/H3/H4) from a genuine open research conjecture (`TPFConjecture`)**, and says in as many words
that their *"epistemic status is therefore wholly different."* It also states three concrete
falsifiers for its own claims.

Two further scope statements are exemplary and each was checked against the Lean:

- **`sixteen_convergence_full` indexes, it does not unify.** The draft quotes its own Lean
  docstring: the theorem enumerates four independent occurrences of 16 *"without asserting a
  formal common-origin theorem."*
- **The Schellekens chain is labelled a predicate-level scaffold** discharged via `trivial`, with
  the explicit note that the load-bearing `3 ∣ N_f` result **does not depend on it**.

---

## 7. Ledger

| artifact | change |
|---|---|
| `papers/D2/bundle_metadata.json` | `apex_theorems` added — 47 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 12 → 11 |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | **TODO-D16 narrowed**; TODO-D14 extended to three bundles |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V27 |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 367 apexes across 10 bundles.
