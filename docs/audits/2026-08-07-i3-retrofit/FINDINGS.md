# I3 apex retrofit — the smallest closure in the portfolio, and it is exactly what the draft says it is

**Date:** 2026-08-07 · Seventeenth bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/I3/paper_draft.tex`
(1,349 lines, every line, including the bibliography), `bundle_metadata.json`, and the twelve
Lean modules' declaration list.

---

## 1. What was declared

**12 apexes → 32 declarations across 9 modules, depth 3, zero private truncations.**

**The smallest closure in the portfolio** (next smallest is D7 at 93/8; D8 is 2,290/289). That is
not a defect — it is the direct consequence of I3's stated design, and §3 treats it as evidence.

| § | component | apexes |
|---|---|---|
| §3 | the six Itô modules: witnesses + per-module and overall wave-closures | 9 |
| §5 | the `LDPCompatibleSKEFT` cross-bridge: the continuity lemma, the concrete instance, the LDP overall closure | 3 |
| §4 | the five quantitative-LDP modules | **0** — see §3 |

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Two, and they want different things: Mathlib4 maintainers evaluating a staged upstream contribution in a sub-domain nobody has claimed, and probability-adjacent formalizers who want a stable interface to write against before the quantitative content exists. |
| **Venue** | JOSS \| CPC, per the metadata. JOSS fits; the draft is a software paper with a licence, a build recipe and a replication procedure. |
| **The claim only this container can make** | **That a predicate-substrate release is a legitimate deliverable, and here is one for the two pieces of probability Mathlib4 does not have** — the Itô stochastic integral and the large-deviation principle. Not "we formalized Itô's lemma"; the draft says the opposite, in a section called *Explicit non-claims*. The claim is that the scaffolding-before-content pattern is Mathlib-community practice (Ying–Degenne, Degenne et al.), and that this library instantiates it in a new sub-domain with a per-module upstream plan. |
| **Substrate** | 9 modules, 32 declarations, depth 3: the six `Itô/*` modules, `LDP/LDPCompatibleSKEFT`, and — disclosed by the draft as inherited — `CrooksAnalogHawking/{LDPLinearResponse, SKEFTGallavottiCohen}`. |
| **Honest size vs charter** | 1,349 lines against a JOSS software paper. Long, like I2 and for the same reason: a per-module upstream-PR plan is prose no artifact can carry. |
| **Boundary failure?** | **No — and this is the only bundle in the portfolio whose closure intersects *nothing*.** `I3 ∩ every other declared bundle = 0`, all sixteen. |

---

## 2. ✅ The isolation is a *verified disclosure*, not an accident

I3 §6 states, unprompted and against its own interest:

> *"**The I3 cross-bridge is designed but not yet consumed at release time:** `grep -rn
> "LDPCompatibleSKEFT" lean/SKEFTHawking/` returns matches only inside the I3 module itself …
> no D3, D5, or E1 Lean module currently invokes `LDPCompatibleSKEFT` or any of the Itô-substrate
> predicates."*

**Both halves check.** The grep returns exactly one file, `LDP/LDPCompatibleSKEFT.lean`. And the
derived closure — an instrument the draft knows nothing about — returns **zero shared declarations
with all sixteen other declared bundles**.

**A paper that publishes the grep command whose output would embarrass it, and whose independent
derived measurement agrees, is the strongest form of the disclosure.** D3/D5/E1 are described as
*positioned for* future absorption, three times, each with "as of this release" attached.

Also verified in this pass:

| I3 says | measured |
|---|---|
| 12 modules, *"exact count 775"* lines | **775** ✓ |
| *"15 `Prop`-typed predicates (14 `def Is*` plus the `class`)"* | 14 + 1 = **15** ✓ |
| *"Zero `sorry`; zero new axioms"* | zero `sorry`, zero `axiom`; closure's `axiom_deps_core` = exactly `{propext, Classical.choice, Quot.sound}` ✓ |
| §3.5: a prior redundant `wave_3b_itoBeta_5_itoLemma_closure` *"was retired in the Stage-13 fix-pass"* | **absent** ✓ — instrument seeded: its four sibling `wave_3b_itoBeta_N_*` closures all resolve |
| implied by the kernel claim | **0** `native_decide` markers in the closure; instrument validated at **19** in D4's ✓ |

---

## 3. ⚠️ §4 names no theorem for any of its six modules — thirteen proved theorems are unnamed

**§3 (Itô) and §4 (LDP) are written to different templates, and only §3's is complete.** Every Itô
subsection carries *Substrate-data predicate* → *Non-vacuity witness* → *Wave-closure summary* →
*Mathlib-upstream-PR target*. **Every LDP subsection carries only the first and the last.**

The consequence, measured against the modules' actual declaration list: **13 proved theorems in
I3's own twelve modules are named nowhere in the draft** —

- five LDP witnesses (`cramerIID_subGaussian_witness`, `sanov_methodOfTypes_witness`,
  `isContractionPrinciple_witness`, `isCramerLowerBoundEsscher_witness`,
  `isVaradhanUpperBound_witness`);
- five LDP per-module wave-closures (`wave_3b_ldp_alpha_1_cramerIID_closure` … `_beta_2_varadhan_closure`);
- three Itô witnesses whose subsections skip the heading (`isSemimartingaleDecomposition_zero_witness`,
  `isDoobMeyerUnique_zero_witness`, `isItoIsometry_zero_witness`).

That is why five of the twelve modules — `CramerIID`, `Sanov`, `Contraction`, `CramerLowerBound`,
`Varadhan` — **appear nowhere in the declared closure**. The apex rule ("a statement the manuscript
presents as a result") gives them zero apexes, correctly, and the closure records the consequence.

⚠️ **This is the D11/D7 pattern, and for a software paper it is a sharper defect than for either.**
D11's unnamed content was a prose gap in a results paper; D7's sections were openly unwritten.
**Here the artifact *is* the deliverable, and an unnamed theorem is an unfindable API** — a JOSS
reader who wants the Sanov witness has no name to search for. Recorded as **TODO-D19**.

**A count that follows from the same asymmetry.** §2.3 claims *"11 per-module wave-closure summary
theorems plus 2 overall-wave closures … the `Novikov` module folds its closure into the overall"*.
Probe scope: the `theorem`/`lemma` declarations in the twelve module files. Measured **10**
per-module (4 `itoBeta_*` + `ito_reduces_to_calculus_when_zero_qv` serving as `ItoLemma`'s, as §3.5
says + 5 `ldp_alpha/beta_*`) and 2 overall. **11 counts `LDPCompatibleSKEFT` as having a per-module
closure**, which the same paragraph's own accounting gives to `wave_3b_ldp_overall_closure`. Off by
one, in a hand-maintained count. Filed under TODO-D19 with the naming gap, not separately — they are
one defect.

---

## 4. ⚠️ A declaration-rule refinement: auto-generated structure projections pass the theorem gate

`LDPCompatibleSKEFT`'s five fields — `ldpRateFn`, `cramerCompatible`, `sanovCompatible`,
`contractionCompatible`, `varadhanCompatible` — are named in the draft's §5 as *"five fields that
carry refutable Prop content"*, and each **resolves in `lean_deps.json` with `kind: theorem`**,
because a `Prop`-class field projection is a theorem.

**They would therefore pass `apexes_are_theorems` while not being claimed results at all.** They are
projections of the class, generated by the `class` declaration; the claimed result is the *instance*
(`linearResponseRateFunctionCentered_isLDPCompatibleSKEFT`), which is declared.

The declaration rule established at D11 already excludes them — *"excludes definitions and lemmas
named only as **how** a result was obtained"* — but this is the first case where the exclusion is
**not** enforceable by the kind check. Recorded so the remaining bundles inherit it:
**`kind == theorem` is necessary, not sufficient; a `Prop`-structure's field projections are
machinery.**

---

## 5. Also observed

- **Toolchain drift**: §9.2 says the library *"builds against Lean 4 v4.29.0"*; the project is on
  `v4.32.0`. One of the known post-bump pin-drift sites; recorded, not filed separately.
- **Roster staleness**: the self-citation reads *"14-bundle publication architecture"*. **Third
  bundle with a stale roster number** (after F and I1) → TODO-D15.
- **Line-number citation into another module**: §5.1 cites `LDPLinearResponse.lean` *"lines 597–600"*.
  Same TODO-D3 class as I2's.

---

## 6. What I3 gets right

- **An *Explicit non-claims* subsection.** *"The I3 release does **not** claim to formalize the Itô
  stochastic integral, Itô's lemma, Novikov's condition, the Cramér upper or lower bound, Sanov's
  theorem, the contraction principle, or Varadhan's lemma at the substantive quantitative level."*
  Seven named non-claims, in a paper whose title lists all seven.
- **`Prop := True` is printed, in the body, as the predicate body.** The weakest thing about the
  release is shown in a code block rather than described.
- **An "Out-of-bundle dependency disclosure" that decides an ownership question for me.** It names
  which field is inherited from Phase 6n and which four I3 authored — so
  `linearResponseRateFunctionCentered_zero` is excluded from the apex list **on the draft's own
  instruction**. First time in this retrofit that a draft pre-empted an ownership call.
- **Negative coordination status stated in bold**: *"**We have not, as of this release, opened any
  Zulip thread, GitHub issue, or PR coordination artifact** with the Degenne et al. team or with the
  Mathlib maintainer community."*
- **A misattribution is corrected in the bibliography itself**, with the method and date: the
  Markov-kernels entry records that it *"supersedes the project's carry-forward Phase-6n-era 'Marion
  2025 MarkovKernels' misattribution"*, primary-source-verified by direct arXiv fetch.
- **The prior-art survey states what it did not survey**: *"HOL Light and Mizar were not surveyed
  for this release."*
- **A σ² = 0 edge case is characterised precisely**: *"produces an instance-synthesis failure rather
  than a provable false statement."*

---

## 7. Ledger

| artifact | change |
|---|---|
| `papers/I3/bundle_metadata.json` | `apex_theorems` added — 12 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 5 → 4 |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | **TODO-D19** (§4's missing witness/closure names + the off-by-one count); TODO-D15 → three bundles |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V35 |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 580 apexes across 17 bundles.
