# D5 apex retrofit — the corpus's best honesty taxonomy, and a shallow closure that explains why

**Date:** 2026-08-07 · Twelfth bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/D5/paper_draft.tex`
(1,527 lines, every line), `bundle_metadata.json`, and — to check a number-cited invariant —
`docs/WAVE_EXECUTION_PIPELINE.md` at Invariant #14.

---

## 1. What was declared

**70 apexes → 216 declarations across 19 modules, depth 3, zero private truncations.**

D5 is a **register of verdicts**, so almost every theorem it names is a claimed result rather
than machinery. The apex list is correspondingly close to the full set of resolved names: 71
`\texttt{}` tokens resolve to theorems and 70 are declared (`IntCongr.rfl` is a token collision,
not a citation).

⚠️ **The closure is the shallowest measured — depth 3, 216 declarations from 70 apexes.** That
ratio is the finding, not a defect: see §3.

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Dark-sector phenomenologists and the emergent-gravity DE community — specifically people deciding which mechanism family is still worth pursuing after DESI DR2. |
| **Venue** | PRD, per the metadata. Appropriate: the content is a survey-plus-verdict register, not a single result. |
| **The claim only this container can make** | **The first complete-mechanism-family unanimous NO-GO closure** — Track B's eight entropic-gravity DE mechanisms, all closed, robust under the `r_d`-anchoring rescue. Around it sit two more track-level verdicts (Track A fully NO-GO with three publishable structural caveats; Track C highest-survival with five-plus CLEARED-R5) and the unified 7-class Gibbs–Duhem taxonomy that organises all three. No sibling holds a mechanism-family closure; D3 owns the substrate's own CC channel, D5 owns the *literature's* DE mechanisms. |
| **Substrate** | 19 modules, 216 declarations, depth 3: `CausalSetDarkEnergy`, `EntropicGravityDarkEnergy`, `JacobsonThermoGRDarkEnergy`, `DarkSectorClassificationExtension`, `GibbsDuhemTheorem`, `DarkEnergyObstructionPrinciple`, `BBN`, `SFDMMergerForecast`, `EquivalencePrinciple`, `StrongCPTopologicalDE`, `DarkSectorSynthesis`, `FangGuTorsionDM`, `ADWMechanism`, `DKMBootstrap`. |
| **Honest size vs charter** | 1,527 lines against ~40pp — mid-range for the portfolio, and the section structure is complete (no empty numbered sections in the body). |
| **Boundary failure?** | **No.** D5 ∩ D3 = 11 (`JacobsonThermoGRDarkEnergy` 9, `ADWMechanism` 2) and D5 ∩ F = 17 (`EntropicGravityDarkEnergy` 16) — both are D5 *supplying* substrate, not consuming it. Its purpose is statable entirely on its own register. |

---

## 2. The corpus's best honesty taxonomy — and it is a three-way split, not a binary

D5 §2.3 defines and then applies throughout a labelling scheme no other draft has:

- **Derived** — the Lean proof carries non-trivial mathematical content; *"the conclusion does not
  reduce to the statement by `rfl` or `decide` on hand-assigned constants."*
- **MCC (machine-checked classification)** — *"the proof verifies internal consistency of an
  author-supplied lookup table or enum assignment"*, and Lean *"does not independently re-derive
  the underlying physics bound."*
- **Heuristic / Empirical** — physically motivated but non-rigorous, or measurement-driven.

**It applies the labels against itself, including where they are unflattering.** The Phase-5x
viability matrix (Fig. 1) is labelled MCC *in its own caption*, "since the flag values are
hand-assigned". The direct-detection caps are MCC. The FG torsion CDM obstruction is called out
as Derived, with the reason (traceless `T^μν`).

**This is the exact distinction TODO-D12 exists because D10 does not draw**, and it is a strictly
better instrument than D4's fix template (§4 of the D4 findings): D4 discloses *one* definitional
encoding at its point of use; D5 defines a **taxonomy**, states the decision rule, and tags
content corpus-wide. **TODO-D12's fix should adopt D5's three-way labels and D4's
point-of-use sentence — they solve different halves.**

Other disclosures, each checked:

- **A withdrawn claim is stated as withdrawn**: *"A prior '≈ 2.8 meV' / '20 % agreement' claim is
  withdrawn in this revision."*
- **A retired biconditional is stated as retired, with the reason**: the Sakharov
  `_iff_`-suffix theorem was renamed to the one-way form because *"no primary source argues the
  converse"* — and the replacement ships a load-bearing depletion-factor witness instead.
- **A renamed theorem is disclosed with its old name**: `barrow_hde_..._bayes_factor` →
  `..._disfavoured_information_criteria`, because the methodology is AIC, not Bayes factors, and
  the registry placeholder 5.5 was replaced by the primary-source 4.7.
- **The aggregators are separated from the proof load**: *"both aggregators are bookkeeping over
  the per-candidate legs, a verified-consistent classification ledger rather than the proof load
  itself"*, with `entropic_gravity_seven_genuine_per_candidate_falsifiers` recording which seven
  of the eight carry their own quantitative falsifier and which one is structural.

---

## 3. Why the closure is shallow, and what that means

**70 apexes → 216 declarations, depth 3** is by far the flattest shape measured (compare D4:
66 → 753, depth 13; D2: 47 → 516, depth 11).

The reason is visible in the draft: **D5's theorems are verdicts, and a verdict has almost no
substrate beneath it.** A statement like `verlinde_2017_no_go_via_cluster_mass_densities…` encodes
a comparison against a published number; it does not rest on a tower of lemmas. That is exactly
what D5's own MCC label warns about — Lean checks the classification's consistency, not the
physics.

**The measurement therefore corroborates the draft's self-description rather than contradicting
it**, which is worth stating plainly: a shallow closure is a defect only when the prose claims
depth. D5's does not. Its §2.3 says so up front, and the aggregator/proof-load separation in §9
says it again at the point where the aggregate is quoted.

⚠️ **Consequence for the portfolio, not for D5:** apex-to-closure ratio is not a quality metric
across bundles of different genres. D11's high ratio was a prose signal; D5's is a genre signal.
**Compare ratios only within a genre.**

---

## 4. Re-measured and NOT filed

D5 cites **Pipeline Invariant #14** twice for the rule *"no 14th+ bundle target spawned"*, while
F cites the same invariant for *"sentence-level `bundle_destination` tags carry over"*. Two
different rules under one number looked like the number-cited-invariant mismatch DONE item 5 asks
to resolve.

**Both are right.** Invariant #14 (`WAVE_EXECUTION_PIPELINE.md:693`) is *"Every paper-shaped output
lifts into a `PAPER_STRATEGY.md` bundle"*, and its body contains **both** sentences — the
authorization rule and the `bundle_destination` schema propagation. Each draft quotes a different
clause of the same invariant. Nothing to file.

*Per the V27 lesson: the probe's scope was stated before the conclusion was written.*

---

## 5. Also observed

- **Two more empty lift stubs.** TODO-D14 now spans **five** bundles.
- **`\substantivetheorems` and `\totaltheorems` used in the abstract** for D5's own content —
  the same project-scoped-macro-as-bundle-figure defect as TODO-D9's D1 case. D5's measured
  substrate is **216** declarations. Recorded under TODO-D9 rather than filed separately.
- **`H_BothActiveGivesInconsistency`** — a tracked Prop encoding the mutual-exclusivity falsifier
  between D5's two CC mechanisms. Correctly excluded from the apex list (`def`), and the draft
  labels the theorem built on it *"Derived content … not MCC"*.

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/D5/bundle_metadata.json` | `apex_theorems` added — 70 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 10 → 9 |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D12 gains D5's taxonomy alongside D4's sentence; TODO-D9 gains D5; TODO-D14 → five bundles |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V30 |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 503 apexes across 12 bundles.
