# D11 apex retrofit — and the substrate the manuscript never mentions

**Date:** 2026-08-07 · Fifth bundle retrofitted under ADR-010 §D5a (after D6, D9, L2, D12).

**Read IN FULL before anything was declared,** per ADR-010 C4:
`papers/D11/paper_draft.tex` (670 lines, every line, including the bibliography),
`papers/D11/bundle_metadata.json`, the `_D11_MODULES` roster and counting rule in
`scripts/update_counts.py`, and the declaration-level record for all 22 modules the bundle
claims (`lean/lean_deps.json` — kinds, modules, statement types, dependency edges).
The statement *type* of every one of the 73 declared apexes was read and checked against the
sentence in the draft that asserts it; four were rejected on that reading (§4 below).

Nothing here rests on a subagent report. A prior agent pass over D11 exists and was treated as
orientation only; where it and a measurement disagree, the measurement is recorded.

---

## 1. What was declared

**73 apexes → 413 declarations across 22 modules, depth 6, 47 walks stopped at a `private`
declaration.**

| § | layer | apexes |
|---|---|---|
| §2 | lattice-invariant core (FHS) | 10 |
| §3 | phononic band gaps | 11 |
| §4 | non-Hermitian / exceptional points | 5 |
| §5 | algebraic effective-medium bounds | 8 |
| §6 | graphene, Dirac expansion, Haldane witness, bilayer | 35 |
| §7 | the two refutations | 4 |

**The declaration rule, stated so the next bundle can apply it.** An apex is a statement the
manuscript presents as *something this bundle established*. That admits negative results
(`dispersion_linear_not_exact`), non-vacuity fixtures the draft offers as evidence
(`latticeChern_Uwit` against `latticeChern_trivial`), and obligations the draft explicitly says
are "not formalities" (`haldane1_pos`, `haldane1_link_ne`). It excludes definitions — a bundle
claims results, not machinery — and lemmas the draft names only as *how* a result was obtained
("the two facts everything downstream uses", "the proof is X plus Y").

**Why 73 and not D9's 25.** D11 has five independent layers and its draft is written as a
theorem catalogue: 73 distinct statements are introduced as results. The apex count is a
faithful reading of the manuscript, and its size is itself a datum about how the manuscript is
written — see §5.

---

## 2. What the closure confirmed

**The derived module set is exactly the hand-maintained roster — both directions, zero
difference.** `scripts/update_counts.py:398` hand-lists 22 modules as "the D11 bundle" to
generate `\dxiModules`/`\dxiLines`/`\dxiTheorems`/`\dxiDefs`. The closure of the 73 apexes
reaches those 22 modules and no others; no roster module is unreached. That list can now be
*derived* rather than hand-listed — filed as TODO-D10 in `ARCHITECTURE_TODOs.MD`.

**D11 borrows nothing.** Its closure intersects the closure of every other declared bundle in
**zero** declarations — D6, D9, D12 and L2 alike. The acknowledgments claim *"no module in this
bundle imports PhysLib: the complete import set is Mathlib plus intra-bundle dependencies"*;
the closure corroborates the intra-bundle half at declaration granularity.

This is the opposite of the D6/D9 result, where the closures showed one bundle citing
declarations from another's namespace. D11 is a self-contained substrate, so no merge, split or
homing question arises from its dependency shape.

---

## 3. ⚠️ The finding: 69 proved declarations, in three coherent families, appear nowhere in any manuscript

Of the bundle's 502 author-written declarations, **89 are outside the closure**. Subtracting
what is not content — 12 structure fields and `def` projections (`IsHoneycombChart.angle_sixty`,
`DiatomicChain.a_pos`, …) and 4 compiler-generated `congr_simp` lemmas the autogen index misses
— leaves **≈69 author-written declarations that the D11 draft never names.**

Verified with an **underscore-aware** scan (the draft writes `\thm{bernal\_effectiveMass\_eq}`,
so a raw-identifier grep returns a false zero — `reference-measurement-traps-false-absence`).
The scan was seeded with two known-present names first and found both.

**Nor are they claimed by any other bundle.** Ten representatives were scanned across all 65
`papers/**/*.tex` files, underscore-aware: **none appears in any draft in the portfolio.**

### The three families

**(a) Bilayer effective mass and band touching — `GrapheneBand/BernalBilayer` (20 theorems + 1 def).**
An effective-mass development (`bernalEffectiveMass`, `bernal_effectiveMass_eq`,
`bernal_effectiveMass_dispersion`, `bernal_lowBand_effectiveMass`, `bernal_sub_linear_of_monolayer`,
`bernal_sub_linear_of_small`) and a band-touching development (`bernal_touching_energy_sq`,
`bernal_touching_energy_enclosure`, `bernal_touching_of_eigenvector`, `bernal_touching_ratio_le`,
`bernal_touching_witness_exists`, `bernal_touching_not_exact_in_ball`), plus
`bernal_gap_enclosure`, `bernal_diracPoint_energies`, `bernal_field_gap_pos`,
`bernal_bands_real`, `bernal_secular_discrim_nonneg`. §6.4 of the draft is nine sentences long.

**(b) Honeycomb symmetry, orbit characterization, and a second model — `GrapheneBand/Honeycomb`
(30 theorems + 3 defs).** A `T`-variant model complete with its own band structure
(`honeycombDT`, `structureFactorT`, `honeycombT_band_secular`, `honeycombT_energy_eq`,
`honeycombT_energy_gamma`); an orbit-level characterization of the zero set
(`structureFactor_eq_zero_iff_orbit`, `structureFactor_eq_zero_iff_dirac_branch`,
`neighbourSum_eq_zero_iff_orbit`) which is *strictly stronger* than the
`structureFactor_eq_zero_iff` the draft does cite; a symmetry family
(`structureFactor_norm_rotate`, `structureFactor_norm_swap`, `norm_neighbourSum_eq`);
high-symmetry-point energies (`honeycomb_energy_gamma`, `honeycomb_energy_mPoint`); and
gapped-away results (`honeycomb_gapped_away`, `honeycomb_gapped_away_of_phase`).

**(c) Dirac-expansion enclosures — `GrapheneBand/DiracExpansion` (7 theorems + 1 def).**
`dispersion_fermiVelocity_enclosure`, `dispersion_linear_enclosure`,
`gapped_gap_strictMono_in_mass`, `gapped_gapless_iff`, `gapped_dirac_gapless_iff_massless`.

### Why this matters, and what it is not

The 2026-08-01 audit's portfolio-level diagnosis is a Tier-1 **length shortfall against charter**,
concentrated where duplication lives. For D11 the shortfall has a different generator: the
physics is proved and the manuscript does not report it. That is a *writing* gap, not a
formalization gap — consistent with the earlier read that D11 is "blocked by prose, not by
physics", and it makes that read specific rather than impressionistic.

**It is not a correctness finding.** Nothing here says a D11 claim is wrong. It says the bundle
under-reports its own substrate by roughly a sixth.

**One small honesty gap does fall out of it.** §6.4 states the Mexican-hat result *at nonzero
bias* and cites `bernal_mexicanHat`, a theorem carrying that bias hypothesis explicitly. The
non-vacuity witness for the hypothesis, `bernal_mexicanHat_witness`, exists and is not cited —
so a reader cannot tell from the draft that the conditional's antecedent is inhabited. Compare
§2.2, where the draft is careful to state `latticeChern_Uwit` against `latticeChern_trivial` for
exactly this reason. Filed as **TODO-D11**.

---

## 4. Four candidates rejected on reading the statement

Recorded because rejection is the part of this exercise that is easy to skip.

| candidate | why rejected |
|---|---|
| `blochFrameOfD`, `blochProj`, `honeycombD`, `Torus` | `def`/`abbrev`, not theorems. A bundle claims results; machinery is reached by the closure, not declared. The check enforces this (`apexes_are_theorems`). |
| `principal_mem_Ioc` | §2.1 introduces it as "the two facts everything downstream uses" — presented as *how*, not *what*. |
| `blochPauli_sq` | §2.3 names it as the reason `blochProj_idem` holds. Same class. |
| `blochPauli_mulVec_lbVec` | §2.3 names it as the eigenvector law `blochFrameOfD` is built on. Same class. |

The last three are cited in the draft and are *not* in the closure, because the results that
would pull them in are `def`s. That is a structural limit of "apexes must be theorems": content
sitting only beneath a definition is reachable only if some declared theorem uses that
definition. Here `BlochFrameOfD` is 17/23 reached via the Haldane apexes, so the loss is small
and visible — but the mechanism is worth stating, because a bundle whose headline is a
*construction* rather than a *theorem* would lose much more.

---

## 5. What the apex count says about the manuscript

D9 declares 25 apexes for a 623-declaration closure. D11 declares **73** for a 413-declaration
closure — nearly three times the apexes over two-thirds the substrate. The ratio is a
measurement of writing style, not of physics: D11 introduces almost every theorem by name in
running prose, so a faithful apex reading of it is long.

That is the same property a reader experiences as a catalogue rather than an argument, and it is
the property the 2026-08-01 audit and the ADR-010 §D5a prose concern both name. It is recorded
here as a **measured** ratio rather than an impression, and it is available as a comparator when
the remaining 16 bundles are retrofitted: an apex-to-closure ratio far above the D9/D12/L2 band
is a prose signal that can be computed before anyone reads the draft.

**No prose was changed in this pass.** Rewriting is a content decision under ADR-010 C5 and
§6a; this pass declares, derives, measures and files.

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/D11/bundle_metadata.json` | `apex_theorems` added — 73 entries, each with the claim it backs |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 17 → 16, with the reason in the ratchet comment |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D10 (derive `_D11_MODULES`), TODO-D11 (`bernal_mexicanHat_witness` citation) |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V21 — the atoms this pass established |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 128 declared apexes across 5 bundles
all resolving to live theorems.
