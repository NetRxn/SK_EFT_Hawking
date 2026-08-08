# D10 apex retrofit — the D10+D11 merge is answered, and one layer overclaims

**Date:** 2026-08-07 · Sixth bundle retrofitted under ADR-010 §D5a (after D6, D9, L2, D12, D11).

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/D10/paper_draft.tex`
(315 lines, every line), `papers/D10/bundle_metadata.json`, and — for the three DFT modules whose
claims turned out to be the finding — the **full Lean source** of
`HohenbergKohnUniqueness.lean`, `HohenbergKohnVariational.lean` and `LevyLiebFunctional.lean`,
not their extracted signatures. The statement *type* and *axiom profile* of every declared apex
were read from `lean_deps.json`; the two boldest claims in the abstract were checked against the
statement itself rather than against the prose that describes it.

---

## 1. What was declared

**33 apexes → 311 declarations across 17 modules, depth 13, 5 walks stopped at a `private`
declaration.**

| § | layer | apexes |
|---|---|---|
| §3 | NEGF transport — Green's functions, Landauer, quantization certificate | 14 |
| §4 | DFT — self-adjointness, Hohenberg–Kohn, Levy–Lieb | 10 |
| §5 | open systems — GKSL generator, structure theorem, semigroup, damped model | 9 |

Same rule as D11: an apex is a statement the manuscript presents as something this bundle
established. `lindbladGenerator` and `lindbladLiouvillian` are `def`s and excluded;
`molecularHamiltonian_essSelfAdjoint_of_hpot_hrel` is excluded because the draft itself labels it
**superseded** — a retained declaration is not a claimed result (§5).

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Electronic-structure and open-quantum-systems practitioners who rely on NEGF/Landauer, DFT and GKSL as settled foundations, plus formal-methods researchers looking for a reusable reference layer. |
| **Venue** | PRD \| PRX Quantum \| J. Chem. Phys. J. Chem. Phys. is the honest fit for the DFT and open-system content. |
| **The claim only this container can make** | **A single verified stack across three pillars of the simulation literature that are normally formalised — if at all — separately**: NEGF transport, DFT foundations, and Lindblad dynamics. The claim that survives strongest scrutiny is §4.1's *unconditional* essential self-adjointness of the molecular many-body Coulomb Hamiltonian, with all three analytic inputs discharged. No sibling covers this ground. |
| **Substrate** | 17 modules, 311 declarations, depth 13: `NEGFGreenFunction`, `LandauerConductance`, `NEGFTransportCertificate`, `MolecularHamiltonian`, `KineticEssentialSelfAdjoint`, `CoulombRelativeBound`, `HohenbergKohnUniqueness`, `HohenbergKohnVariational`, `LevyLiebFunctional`, `LindbladGenerator`, `GKSLStructure`, `LindbladSemigroup`, `LindbladCPSemigroup`, `DampedTwoLevel`, plus `QuantumNetwork.{MixedState, CPTPChannel, NumericalBounds}`. |
| **Honest size vs charter** | 315 lines against a ~40pp Tier-1 charter — the largest proportional shortfall in the portfolio. The bundle's own metadata says so: *"a tight 4pp synthesis; expansion toward the ~40pp target + figures is future work."* |
| **Boundary failure?** | ⚠️ **Partial, and it must be named.** §5.3's contractivity result is not statable without D9's substrate — **50 declarations in `QuantumNetwork.*`, every one claimed by D9's apexes.** D10's *purpose* survives (the DFT and NEGF pillars are wholly its own), but one of its three headline layers rests on a sibling's container. Per §D2's rule this is a boundary failure of the **partial** kind: the target is viable, one section is not self-contained. |

---

## 2. ✅ ADR-010's second untested merge is answered: **D10 ∩ D11 = 0**

ADR-010 §What-remains pairs D10 with D11 as an untested merge candidate. Both are now declared,
so the question is measured rather than argued:

| pair | shared declarations |
|---|---|
| **D10 ∩ D11** | **0** |
| D10 ∩ D9 | **50** — `QuantumNetwork.MixedState` 41, `CPTPChannel` 8, `NumericalBounds` 1 |
| D10 ∩ D12 | 1 |
| D10 ∩ D6, D10 ∩ L2 | 0 |

**There is no shared substrate between D10 and D11 to consolidate.** The pairing appears to have
come from adjacency in the authorization sequence (both authorized 2026-06-29), not from content.
This is the same shape as the D12 result: a merge hypothesis stated on a strategy document's
outline, and disconfirmed by the closure.

**Where D10 does couple is D9.** Its §5.3 contractivity result is built on
`SKEFTHawking.QuantumNetwork.traceDist` and the project's own CPTP data-processing inequality —
50 declarations, every one of them **claimed by D9's apexes**. This is borrowing *with* an
available attribution, unlike the D6→D9 case where D6 cited declarations D9 does not claim.

The draft acknowledges the dependency in §5.3 ("follows from the project's CPTP data-processing
inequality"). Its §Novelty carve-out, however, frames the pre-existing channel theory as
**external** prior art (PhysLib, CoqQ, Isabelle/AFP) without noting that the specific substrate
consumed here is this project's own D9 layer. Not an error — the external carve-out is separately
true — but a reader cannot tell from the paper that a sister bundle supplies 50 of its
declarations. **If any D10 merge or sequencing question is live, it is with D9, not D11.**

---

## 3. ⚠️ The finding: §4.2–§4.3 claim first-ever DFT formalization over three uninhabited structures

**§4.1 is the real thing, and it verifies.** `molecularHamiltonian_essSelfAdjoint` takes
`N`, `m`, `0 < m` and the nuclei — **and nothing else**. No analytic-hypothesis argument, no
tracked `Prop`, axiom profile exactly `{propext, Classical.choice, Quot.sound}`, over the concrete
`QuantumMechanics.SpaceDQuantumSystem.kineticOperator.closure + potentialOperator`. The abstract's
"unconditional" is **true as stated**, and `coulomb_isRelBounded` is existential in `(a, b)`, so
the relative bound is produced rather than supplied. Likewise `traceDist_lindblad_monotone` takes
no CPTP-realization argument — §5.3's "discharged rather than disclosed" is **true as stated**.
Both were checked against the statement, not the prose.

**§4.2 and §4.3 are a different kind of object.** Their three theorems are stated over data
structures that **have no inhabitant anywhere in the tree**:

| structure | fields carrying the physics | inhabitants in the tree |
|---|---|---|
| `GroundStateData v μ` | `n`, `E`, `F`, **`decomp : E = F + ∫ v·n`** | **none** |
| `DensityVariational X` | `Ev`, `n₀`, **`bddBelow`**, **`ground`**, **`nondegen`** | **none** |
| `LevyLiebData Ψ X` | `TW`, `density`, **`fiber_bddBelow`** | **none** |

Measured by enumerating every declaration in the tree whose type mentions each structure: all of
them are the structure's own auto-generated projections and eliminators, plus the theorems stated
over an arbitrary instance. No `def` produces one; nothing connects any of them to §4.1's
molecular Hamiltonian.

And the theorems reduce to their hosts' own fields:

- `hohenberg_kohn_variational` is `⟨ciInf_le D.bddBelow n, D.nondegen n, fun rfl => D.ground⟩` —
  three lines. The lower bound is the extremal property of an infimum; the equality
  characterization **is** the `nondegen` field.
- `hohenberg_kohn_uniqueness` takes the **two strict Rayleigh–Ritz inequalities as hypotheses**
  and closes by `rw [hn]; linarith` against the `decomp` field. The variational content of HK-I —
  that those inequalities *follow* from variationality and non-degeneracy — is assumed, not
  derived.
- `levyLieb_functional` is `ciInf_le` over `fiber_bddBelow`.

**The Lean is honest; the manuscript is not.** `HohenbergKohnUniqueness.lean:19-21` states
plainly that *"the energy decomposition and the strict variational inequalities are the
load-bearing physical inputs … the reductio itself is proven unconditionally."*
`HohenbergKohnVariational.lean:26-27` states that the module is *"not yet formally connected to
`molecularHamiltonian_essSelfAdjoint`"*. Neither disclosure reaches the paper. What the paper
says instead:

- §4.2: *"is formalized as a **constructive reductio**, not as an axiom"* — true of the reductio,
  and a reader will take it as a claim about HK-I.
- Abstract: *"To our knowledge these are the first formalizations of … **Hohenberg–Kohn/Levy–Lieb
  DFT** … in any proof assistant."*

That novelty claim is the one a referee will test first, and the substrate behind it is a
structural consequence of an uninhabited structure's own axioms. §4.2 does flag `nondegen` as
"(load-bearing)" — one parenthesis, in the middle of a sentence, and nothing anywhere says the
structures are uninstantiated or disconnected from §4.1.

This is the project's own documented anti-pattern, applied prospectively in
`CLAUDE.md` ("defining-the-conclusion check": *if I make the function `:= <obvious target>`, does
the theorem become trivial? If yes, the substantive load is in the definition*). It reached a
manuscript with a first-ever novelty claim attached.

### What this is and is not

**Not a correctness finding.** Every theorem is true and kernel-pure. **Not a reason to withdraw
D10** — §3 and §4.1 and §5 are substantial, and §4.1's unconditional molecular self-adjointness is
the strongest single result in the bundle.

It is a **claim-integrity** finding about §4.2–§4.3's prose, of the class ADR-010 exists to catch.
Two honest repairs are available and both are prose-only:

1. **Say what is proved.** The DFT variational layer is an *axiomatized interface* for
   Hohenberg–Kohn/Levy–Lieb plus its formal consequences, not a formalization of the theorems from
   the molecular Hamiltonian. The novelty sentence narrows accordingly.
2. **Or connect it.** Construct one `DensityVariational` / `GroundStateData` instance from §4.1's
   Hamiltonian. That is real work and would make the current claim true.

Filed as **TODO-D12**. The choice between 1 and 2 is the operator's under ADR-010 C5 (schedule is
flexible; claim strength is not) — but the current prose is not a third option.

---

## 4. Also observed

- **Toolchain pin drift.** `paper_draft.tex:105` states `leanprover/lean4:v4.29.1`; live is
  `v4.32.0` / Mathlib `81a5d257`. Already covered by TODO-D6 (corpus-wide, 29 sites / 11 bundles);
  recorded here, not re-filed.
- **The metadata's own summary is more candid than the paper.** `bundle_metadata.json` notes
  *"Draft is a tight 4pp synthesis; expansion toward the ~40pp target + figures is future work"* —
  which is the §M1 charter-length shortfall, stated by the bundle about itself.
- **`readiness: YELLOW` with `stage13_status: green` and 0 blockers** is the promotion-path state
  documented in `END_TO_END_MAP.md` §8: nothing writes `green` readiness, so YELLOW is the
  terminal state a bundle can reach on its own.

---

## 5. Candidates rejected

| candidate | why rejected |
|---|---|
| `lindbladGenerator`, `lindbladLiouvillian` | `def`s. Reached by the closure, not declared. |
| `molecularHamiltonian_essSelfAdjoint_of_hpot_hrel` | The draft labels it *"retained as the superseded"*. A retained declaration is not a claimed result; declaring it would put a weaker, hypothesis-carrying statement into "what D10 claims" alongside the unconditional one it was replaced by. |

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/D10/bundle_metadata.json` | `apex_theorems` added — 33 entries; the four STRUCTURAL ones say so in their `claims` string |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 16 → 15 |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D12 (the §4.2–§4.3 claim gap) |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V22 |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 161 declared apexes across 6 bundles.
