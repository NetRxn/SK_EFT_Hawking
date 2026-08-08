# L1 apex retrofit — a third declaration conflict, and this one is NOT mine to resolve

**Date:** 2026-08-07 · Eighteenth bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/L1/paper_draft.tex`
(391 lines, every line, including the commented-out Kerr–Schild stub after the bibliography),
`bundle_metadata.json`, and — because this bundle collides with two others —
`lean/SKEFTHawking/GravitationalWaves.lean`'s full declaration list plus the `GravitationalWaves`
citations in D3's and F's drafts.

---

## 1. What was declared

**11 apexes → 18 declarations across 1 module, depth 1, zero truncations.**

**The narrowest closure in the portfolio, structurally**: one module, depth 1. Every apex rests
only on `GravitationalWaves.lean`'s own definitions.

**That is the right shape for a falsification Letter, and it is a stronger signal than D5's.** The
claim is `√χ_vest − 1` against a published multi-messenger bound; there is no tower beneath it and
there should not be one. D5's depth-3 register of verdicts was the previous flattest; L1 is flatter
because a single-equation refutation has nothing to stack.

| thread | apexes |
|---|---|
| the correctness-push biconditional locating the GW170817-compatible window | 1 |
| the two endpoint falsifiers + the bundled corollary (the figure's Lean witness) | 3 |
| the `H_VestigialModeIsGraviton` tracked-hypothesis bundle: discharge + four falsifiers | 5 |
| the Phase-5y H1 caveat as disjointness + its frame-independent form | 2 |

**Excluded, and the sentence is why.** §2 introduces `c_GW_pos`, `c_GW_at_chi_one`,
`c_GW_deviation_strict_mono` as *"the positivity / monotonicity / anchor **lemmas**"* attached to
the definition — machinery named as machinery, not results. The D11 declaration rule excludes them.
⚠️ **D3 declares two of them as its own apexes** — see §3.

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Emergent-gravity theorists working in the Volovik / Akama–Diakonov–Wetterich line, and the multi-messenger-constraint community that supplies the bound. |
| **Venue** | PRL, per the metadata. Right register: one equation, one published bound, one sharp conclusion. |
| **The claim only this container can make** | **That a specific, popular kinematic identification is dead at the natural-range level, with the fine-tuning quantified rather than asserted** — `c_GW = c√χ_vest` requires `χ_vest = 1 ± 3×10⁻¹⁵`, a window of measure `4τ ≈ 1.2×10⁻¹⁴` against a natural range of width 9.9. Sibling containers *report* the falsification; L1 is the only one that develops the biconditional locating the surviving window and the tracked-hypothesis bundle whose four falsifiers make the identification refutable. |
| **Substrate** | 1 module, 18 declarations, depth 1: `GravitationalWaves.lean` alone. |
| **Honest size vs charter** | 391 lines against a PRL. **The only bundle in the portfolio at or under its charter length** — every other measured bundle overshoots. |
| **Boundary failure?** | **No inbound.** L1 needs nothing from any sibling; its closure is one self-contained module. ⚠️ **But its content is declared by two siblings** — the reverse problem, and §3 records it as evidence rather than resolving it. |

---

## 2. ✅ Every size and purity claim verifies

| L1 says | measured |
|---|---|
| *"`GravitationalWaves.lean`, 21 theorems"* | **21** — 23 `theorem`-kind declarations minus the 2 compiler-generated `eq_1` equation lemmas ✓ (the autogen marking is what makes this land exactly) |
| *"zero `sorry`, zero new axioms"* | closure's `axiom_deps_core` = exactly `{propext, Classical.choice, Quot.sound}`; 0 `native_decide` ✓ |
| *"zero `maxHeartbeats` overrides"* | 0 occurrences in the file ✓ |
| *"49 `pytest` cases cross-checking every numeric quoted"* | `tests/test_gravitational_waves.py` collects **49** ✓ |
| *"the compatible window has measure `4τ ≈ 1.2×10⁻¹⁴`"* | `4 × 3×10⁻¹⁵ = 1.2×10⁻¹⁴` ✓ |

---

## 3. ⚠️ CORRECTED 2026-08-07 (at L3's retrofit) — this is a DECLARED splash/deep pair, not a conflict

> **Correction.** This section originally recorded the L1/D3 overlap as an undecided *conflict*, on
> the stated basis that *"neither draft mentions the other."* **That basis was false.** Reading
> `papers/D3/paper_draft.tex` directly — which this retrofit did not do — finds D3 §7 saying:
> ***"Bundle L1 ships the same content as a four-page Physical Review Letters splash; the same
> numerical anchors are shared."*** D3 says the same of L3 in a subsection headed *Cross-bundle
> anchor to L3*, calling the two *"character-for-character identical."*
>
> **The shared declarations are the design.** The ownership rule (*develops → owns; cites → does
> not*) presumes the containers make *different* claims; a splash/deep pair makes the same claim at
> two lengths on purpose, so the rule has no jurisdiction and neither container should cede.
>
> **Unchanged:** `L1 disposition` remains a reserved STOP-AND-ASK — but it is a decision about a
> deliberate publication strategy, not an adjudication of an accidental overlap. And nothing was
> reassigned, which remains correct, now for the corrected reason.
>
> **The lesson (V26, again):** the probe that would have shown presence was a search of the sibling
> draft for the **bundle name**, not the theorem name. Filing an absence still requires naming a
> probe that can show presence. Full working: `docs/audits/2026-08-07-l3-retrofit/FINDINGS.md` §3.

### As originally recorded

**D3 declares 8 `GravitationalWaves` apexes; F declares 3. Five of D3's and all three of F's are
theorems L1 also declares.** L1's whole closure — 18 declarations in one module — sits inside
territory D3 already claims.

| | L1 | D3 | F |
|---|---|---|---|
| what it is | **the entire Letter**: title, abstract, both theorem environments, the figure | one lane closure inside an emergent-gravity survey | one example of *"NO-GO results reported as first-class predictive content"* |
| `GravitationalWaves` apexes | 11 | 8 | 3 |
| unique to it | **6** — the biconditional + the five `H_VestigialModeIsGraviton_*` | 3 — the `c_GW_*` lemmas L1 subordinates to its definition | 0 |

**The sharp measurement, and it is the useful one:** *L1's declaration-level unique content is
exactly the correctness-push biconditional and the tracked-hypothesis bundle. The falsification
headline itself — both endpoint falsifiers, the bundled corollary, the disjointness theorem and its
frame-independent form — is **already declared by D3 and F**.*

⚠️ **I resolved the D4→D8 and D1→D7 conflicts; I am NOT resolving this one.** ⚠️ *The original
justification below is superseded by the correction at the head of this section — D3 does mention
L1, and the pair is declared.* Those two moved apexes between containers whose existence was
settled — the drafts' own words (D8) or document position (D1 §8.2 vs D7's title) decided them, and
the closure corroborated. **Here the question is whether L1 exists as a container at all**, which is
the `L1 disposition` item the goal reserves. Under ADR-010 C5 the schedule is flexible and the claim
strength is not: reassigning here would *pre-decide* a charter question by moving declarations.
**Nothing was reassigned.** The duplicate declarations stand, deliberately, as the evidence.

Recorded in `docs/audits/2026-08-07-d4-merge-evidence/EVIDENCE.md`.

---

## 4. ⚠️ Seven of the 21 theorems are named nowhere — and five of them prove a claim the
discussion states in prose

Unnamed in the draft: `c_GW_deviation_zero_iff_chi_one`, `ligo_satisfied_at_chi_one`,
`dispersion_correction_zero_at_no_dissipation`, `dispersion_correction_linear_in_gamma`,
`dispersion_correction_abs_bound`, `dispersion_within_ligo_iff`,
`vestigial_dispersion_below_ligo_at_inspiral_peak`.

The last five matter. §Discussion recovery-path 3 says:

> *"The SK–EFT dispersion correction (formalized in `SecondOrderSK.lean`) is the leading frequency
> dependence in the present framework; at the project's current conservative upper bound
> `|γ| ≤ 10⁻³⁰` on `Γ_H/c_GW²` it does not lift the falsification."*

**That exact quantitative claim is a proved theorem in L1's own module** —
`vestigial_dispersion_below_ligo_at_inspiral_peak {γ} (hγ : |γ| ≤ 1e-30) : |dispersion_correction γ 100| ≤ tolGW170817`
— and the sentence names a *different* module instead.

The attribution is not wrong: `SecondOrderSK.lean` does carry `GammaH`, `gammaH_def`,
`gammaH_nonneg`, `secondOrder_frequency_dependent`. But **the theorem that discharges the sentence's
own claim is one file away, unnamed**, and the prose reads as if the point were argued rather than
proved. Folded into **TODO-D19** — third instance of the same pattern (D11, I3, now L1), which
makes it a portfolio-level defect rather than three bundle-level ones.

✅ **The hypothesis is disclosed honestly.** The theorem is conditional on `|γ| ≤ 10⁻³⁰` and the
draft says so twice, closing *"a derivation of `Γ_H` from a microscopic matching is open."*

---

## 5. What L1 gets right

- **The naturalness window is labelled a project choice, in the paragraph that uses it**:
  *"the window is a modeling choice of this project, not a published derivation — the Vergeles
  lattice analysis establishes unitarity … but does not itself compute `χ_vest` or assign it a
  range."* This is D4's point-of-use disclosure discipline applied to a *prior*, not a definition.
- **The falsification's scope is bounded three ways**: *"a refutation of one specific kinematic
  identification, not of emergent gravity nor of the ADW program"*, plus three named recovery
  paths, plus *"local to the leading-order kinematic identification"* in the abstract.
- **A removed conjunct is recorded with its reason and its replacement**: the original Wave-2 P3
  *"was removed in the 2026-04-25 post-Wave-2 audit as redundant given P1; P3' replaces it with a
  load-bearing quantitative constraint."* And P3' independence is *proved*, not asserted —
  `_fails_at_quarter` sits exactly at the saturating `Δc/c = −1/2`.
- **The two-sided bound is stated as a conservative simplification of an asymmetric one**:
  `−3×10⁻¹⁵ ≤ Δc/c ≤ +7×10⁻¹⁶` is quoted first, then *"conservatively two-sided"*.
- **The companion result's asymmetry is explained rather than smoothed**: why the linearized-EFE
  wave survives at the natural-range level while this one dies, *"only by coincidence"* included.

---

## 6. Also observed

- **An eighth empty lift stub** (Kerr–Schild double-copy, commented out with a note explaining
  the bookkeeping anchor). TODO-D14 → **eight** bundles. ⚠️ L1's is the best-handled instance: the
  heading is commented out *with a dated explanation*, so nothing renders.
- **A citation to a per-paper draft path, not a bundle**: `papers/paper23_linearized_efe/`. The
  directory exists, so the reference resolves — but it points at pre-bundle geography, which is the
  citation-side twin of the roster staleness in TODO-D15. Recorded, not filed.

---

## 7. Ledger

| artifact | change |
|---|---|
| `papers/L1/bundle_metadata.json` | `apex_theorems` added — 11 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 4 → 3 |
| `docs/audits/2026-08-07-d4-merge-evidence/EVIDENCE.md` | new row — the L1/D3/F declaration conflict as evidence for the reserved `L1 disposition` item |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D19 → third instance; TODO-D14 → eight bundles |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V36 |

**Nothing was reassigned.** Gate: `validate.py --check bundle_apex_resolves` — PASS, 591 apexes
across 18 bundles.
