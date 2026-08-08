# L3 apex retrofit — not a conflict: a DECLARED splash/deep pair, and it corrects the L1 finding

**Date:** 2026-08-07 · Nineteenth bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/L3/paper_draft.tex`
(445 lines, every line, including the commented-out Glorioso–Liu stub after the bibliography),
`bundle_metadata.json`, the full declaration list of `BHThermodynamicsFourLaws.lean`, and — because
the apex lists collided — **`papers/D3/paper_draft.tex`'s §7 and §8 directly**, which is what
produced the correction in §3.

---

## 1. What was declared

**13 apexes → 28 declarations across 1 module, depth 2, zero truncations.**

| thread | apexes |
|---|---|
| the correctness-push theorem (sign of `dT_H/dt` flips at `M_c`) | 1 |
| the three classifier iff-theorems | 3 |
| the Schwarzschild branch profile | 2 |
| the BEC-acoustic branch profile, incl. the load-bearing strict-decreasing claim | 3 |
| the four falsifiers of `H_RegimePartition` | 4 |

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | The analog-gravity community and BH-thermodynamics theorists — readers of Balbinot–Fagnocchi–Fabbri and of Jacobson–Koike who want the two evaporation behaviours stated as one partition rather than two case studies. |
| **Venue** | PRL, per the metadata. Right register: one sign, one critical mass, one figure. |
| **The claim only this container can make** | **That the regime boundary is the *sign-flip of `dT_H/dt` during evaporation*, and that it is a discrete classification rather than a crossover.** Sibling D3 develops the same content at depth; L3 is the container that makes the *discrete* character the headline — D3's own §8 says so. |
| **Substrate** | 1 module, 28 declarations, depth 2: `BHThermodynamicsFourLaws.lean` alone. |
| **Honest size vs charter** | 445 lines against a PRL. Second bundle at or near charter (after L1) — the two Letters are the only ones in the portfolio that are not over. |
| **Boundary failure?** | **No.** L3 needs nothing from any sibling; one self-contained module. Its overlap with D3 is *by design* — see §3. |

---

## 2. ✅ Verified, including the count macro

| L3 says | measured |
|---|---|
| *"`\bhThermoTotal` theorems and lemmas"* (= **20**) | `grep -cE "^(theorem\|lemma) "` on the module = **20** ✓ exact |
| *"zero `sorry`, zero new axioms"* | closure `axiom_deps_core` = exactly `{propext, Classical.choice, Quot.sound}`; 0 `native_decide` ✓ |
| *"zero `maxHeartbeats` overrides"* | 0 ✓ |
| *"`src/wkb/backreaction.py` (line 449) … evolves the full coupled-ODE system rather than assuming the exponential form"* | the file at 447–451 says exactly that, in its own docstring ✓ |
| *"the four laws are NOT bundled into a single Lean Prop structure `H_BCH`"* | ✓ no `H_BCH` exists. There *are* two per-regime predicates (`FourLaws_Schwarzschild`, `FourLaws_ADWExtremality`), which is what *"appear as separate theorems and predicates"* describes. **Re-measured and NOT filed.** |

⚠️ **`\bhThermoTotal` is the fix template TODO-D9 and TODO-D10 are asking for, already built.**
`update_counts.py` derives it per-module (`_module_thm_count("BHThermodynamicsFourLaws.lean")`), so
it **cannot drift** — unlike D1's and D5's use of the *project*-scoped `\totaltheorems` for a bundle
figure, and unlike F's, I1's and I3's hand-typed roster numbers. **A bundle-scoped derived macro is
the answer; one already exists and works.**

*Scope note, so the number is not over-read:* the 20 counts source-level `theorem`/`lemma`
declarations. Two of them are a namespaced positivity theorem (`ADWParams.G_N_emerg_eval_pos`) and
a module summary marker (`_wave5_module_summary_marker`), so the **standalone substantive** theorem
population is **18**. A scope difference, not an error — the macro is exact at its own scope.

---

## 3. ⚠️ CORRECTION to the L1 finding: D3 names BOTH splashes, and calls the duplication intentional

L3's apexes collide with D3's the same way L1's did — D3 declares 4 `BHThermodynamicsFourLaws`
apexes, 3 of them L3's; F declares 1, also L3's. **At L1's retrofit I recorded that collision as an
undecided conflict, on the stated basis that *"neither draft mentions the other."* That basis is
false.** Reading D3's draft directly — which I had not done — finds it saying, in its own words:

> §8, in a subsection headed ***Cross-bundle anchor to L3***: *"the regime-partition criterion
> appear identically in Bundle L3, which ships the regime-partition statement as a four-page
> Physical Review Letters splash. **The Lean theorem name and numerical anchors are
> character-for-character identical between L3 and §8.**"*
>
> §7: *"**Bundle L1 ships the same content as a four-page Physical Review Letters splash**; the same
> numerical anchors are shared."*

**Both L1/D3 and L3/D3 are declared splash/deep companion pairs. The shared declarations are the
design, not a collision.** L3 confirms it from its side too, citing D3 as *"D3 deep companion to
L3"*.

**Consequence for the ownership rule, stated so it does not get misapplied again:** the rule
(*develops → owns; cites in a cross-check → does not*) presumes the containers are making
*different* claims. **A splash/deep pair makes the same claim at two lengths on purpose**, so
shared apexes are correct and neither container should cede. The rule has no jurisdiction here.

**How the error happened, and the standing lesson it re-teaches.** I compared apex lists and
grepped D3 for `GravitationalWaves` / `c_GW` tokens; the sentence that would have shown presence
says *"Bundle~L1"* in prose and matched none of them. **I filed an absence without naming a probe
that could show presence** — the V26 rule verbatim. The probe was available and cheap: search the
sibling draft for the *bundle name*, not the theorem name.

**What does NOT change:** `L1 disposition` remains a reserved STOP-AND-ASK. Whether to *publish* a
splash companion is still a charter decision — but it is now a decision about a deliberate
publication strategy, not an adjudication of an accidental overlap. Corrected in
`docs/audits/2026-08-07-l1-retrofit/FINDINGS.md` §3 and `EVIDENCE.md` §6.

**Not reassigned, for the corrected reason:** shared declarations between a splash and its deep
companion are correct as they stand.

---

## 4. Five standalone theorems are named nowhere in L3 — and D3 names one of them

Unnamed in L3: `M_c_pos`, `delta_ADW_nonzero_iff_alpha_ADW_ne_one`,
`four_laws_consistent_with_acoustic_regime`, `wave1_bridge_G_N_emerg_pos`,
`wave3_bridge_kaul_majumdar_at_e_squared_anchor`.

**Two of these are named by D3 instead** (`M_c_pos` as an apex;
`four_laws_consistent_with_acoustic_regime` in §8: *"certify the register at the Lean level"*).
**That is the splash/deep division working correctly** — the four-page Letter names fewer theorems
than the deep companion, which is what a Letter should do.

So L3 is the **first bundle in this retrofit where unnamed theorems are not a defect**: TODO-D19's
pattern (D11, I3, L1) is "proved content nobody names"; here the content is named, one bundle over,
by the container designed to carry it. Recorded against TODO-D19 as the **negative control** that
tells the pattern apart from legitimate splash/deep division.

⚠️ The two `wave*_bridge_*` theorems are named by **neither** L3 nor D3. Those two are genuine
TODO-D19 residue.

---

## 5. What L3 gets right

- **Three project-original claims are flagged as project-original, in a paragraph titled
  *What is novel*** — the `M_c` functional form (*"no published ADW derivation exists"*), the
  exponential approximation, and the `δ_ADW` ansatz. The abstract flags the first one again.
- **The analytic alias is disclosed as an alias, at the point of use, with the discrepancy named**:
  the Lean anchor is `T_H^(0) exp(-t/τ)` while `backreaction.py` *"evolves the full coupled-ODE
  system rather than assuming the exponential form"* — and the draft says so in the same sentence
  that introduces it. **This is D4's point-of-use disclosure applied to a proof convenience**, and
  it is the most self-damaging of the three because it concedes the Lean layer is easier than the
  Python layer.
- **The contrast case is fenced off from the anchor**: *"We cite Jacobson–Koike only as the
  contrast case, not as the cooling anchor"* — after explaining why ³He-A resembles Schwarzschild.
- **A field is excluded from the falsifier count with its reason**: *"the fifth field `T_H0_pos` is
  a positivity assumption and is not falsifier-witnessed."* Four falsifiers for four physics fields,
  and the arithmetic is shown.
- **Recent literature is scoped rather than name-dropped**: the Kehle–Unger and Reall third-law
  revisions *"do not bear on the Schwarzschild branch; their applicability to the ADW-extremality
  branch is a Phase-6 cross-bridge open question."*
- **The unification claim is bounded twice**: the regime partition is *"not directly equivalent to
  Sakharov-criterion satisfaction"*, and the fluctuation-theorem reading *"does not entail
  Verlinde-class entropic-force gravity."*
- **A ninth lift stub, handled like L1's** — commented out with a dated note explaining that the
  bookkeeping anchor is preserved and no prose changed. TODO-D14 → **nine** bundles, two of them
  handled correctly.

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/L3/bundle_metadata.json` | `apex_theorems` added — 13 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 3 → 2 |
| `docs/audits/2026-08-07-l1-retrofit/FINDINGS.md` | **§3 corrected** — the L1/D3 overlap is a declared splash pair |
| `docs/audits/2026-08-07-d4-merge-evidence/EVIDENCE.md` | §6 corrected + L3 recorded |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D19 gains the splash/deep negative control; TODO-D9/D10 gain `\bhThermoTotal` as the working fix template; TODO-D14 → nine |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V37, including the correction |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 604 apexes across 19 bundles.
