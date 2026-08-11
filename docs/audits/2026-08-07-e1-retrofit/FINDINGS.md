# E1 apex retrofit — a third declared companion pair, found by the corrected probe

**Date:** 2026-08-07 · Twentieth bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/E1/paper_draft.tex`
(583 lines, every line, including the inline provenance comments and the D.2 absorption close-out
block after the bibliography), `bundle_metadata.json`, `PolaritonTier1.lean` +
`DKMBootstrap/PolaritonF3Bound.lean` declaration lists, and — **applying the correction from L3's
retrofit** — `papers/D1/paper_draft.tex` searched for the **bundle name**.

---

## 1. What was declared

**7 apexes → 36 declarations across 8 modules, depth 2, zero truncations.**

| § | thread | apexes |
|---|---|---|
| §2 | the Wave-6v.4 TMD scope demarcation | 1 |
| §2 | the Wave-6v.3 DKM-F3 placement + the bimodal-branch resolution | 2 |
| §3 | the `T_H = ħκ/2πk_B` name-binding (disclosed as a `rfl`-discharge) | 1 |
| §4 / §6 / Ack. | the three `PolaritonTier1` attenuation bounds | 3 |

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | One experimental group, by name — the Paris-LKB polariton team — plus the analog-gravity experimentalists deciding which platform to build next. The paper has a section headed *Request to the LKB team*. |
| **Venue** | PRL \| PRR, per the metadata. Correct: this is a prediction-for-a-specific-device letter, not a theory paper. |
| **The claim only this container can make** | **A falsifiable spectral window at one real device's published parameters, with the platform's scope boundary proved rather than assumed** — `ω/κ ∈ [0.05, 0.30]` at the smooth horizon, plus the two theorems that say which polariton physics the SK-EFT patch governs (`polariton_tier1_fails_tmds`) and which branch of the Phase-6q bimodal disjunction the platform sits on (`polariton_dkm_f3_holds_at_pump_below_threshold`). Those two are E1's alone. |
| **Substrate** | 8 modules, 36 declarations, depth 2: `PolaritonTier1`, `DKMBootstrap/{PolaritonF3Bound, HorizonTransportBootstrap, SKEFTSpecialization, Predicates, E1E2CrossBridge}`, `AcousticMetric`, `Basic`. |
| **Honest size vs charter** | 583 lines against a Tier-4 letter (6 pages target). Over, and the draft knows it — the close-out block declines two absorptions specifically because *"extracting them as separate `\section{}` stubs in E1 would expand the letter beyond Tier-4 scope."* |
| **Boundary failure?** | **No.** `E1 ∩ D1 = 16` and `E1 ∩ D5 = 15` are shared substrate, and D1 declares E1 a companion — see §2. |

---

## 2. ✅ E1 is a DECLARED companion letter of D1 — found by the probe L3's correction installed

**D1's abstract**: *"**Companion experimental letters E1 (Paris-LKB polariton) and E2
(Dean-Kim-Lucas graphene)** carry the experimental-team-targeted implementations."*
**D1's header comment**: *"E1 PRL (polariton) and E2 PRL (graphene) extracted Tier-4 letters
already shipped GREEN."*

**This is the third declared pair in the portfolio** — after L1/D3 and L3/D3 — and the first one
found *deliberately*, by running the probe the L3 correction prescribed: **search the sibling draft
for the bundle name, not for shared theorem names.** A theorem-token grep would have missed it
again; D1's sentence names "E1", not `attenuation_ge_one`.

**The overlap is therefore the design.** D1 §Polariton declares all three attenuation theorems,
calling them *"the Lean infrastructure in `PolaritonTier1` … the foundational theorems"*; E1's
acknowledgments calls the same three *"Polariton-specific bounds"*. Deep paper supplies the
infrastructure framing; letter instantiates it at one device. **Nothing reassigned** — same
disposition as L1 and L3, for the same reason.

**E1's declaration-level unique content is exactly two theorems**, and both are its own labelled
deliverables: `polariton_tier1_fails_tmds` (its inline provenance calls it *"the Wave 6v.4
deliverable"*) and `polariton_dkm_f3_holds_at_pump_below_threshold` (*"the Wave 6v.3 deliverable
**on the E1 side**"*). `polariton_inherits_graphene_uniqueness_result` is also declared by D5.

⚠️ **`DKMBootstrap.E1E2CrossBridge` sits inside E1's closure** — a module named for the E1↔E2
relationship. That bears directly on the final open §D4 question and is measured at E2's retrofit,
where both sides are declarable.

---

## 3. Re-measured against existing machinery, NOT filed: the toolchain pin

E1's conclusion warrants the result with *"the formal verification chain (`lake build` clean,
v4.29.0, Mathlib commit `8850ed93`)"*, and the acknowledgments repeats it. The live pin is
**v4.32.0 / `81a5d257`**; `lakefile.toml`'s own comment records `8850ed93` as two bumps stale.

**Existing coverage, found by reading `validate.py --list` before measuring anything:**
`paper_toolchain_pin_drift` — *"Advisory (Class TP): paper-draft toolchain/Mathlib pins match
`lean-toolchain` + `lakefile.toml`."* Running it names **E1:449, E1:453, E1:454** — exactly the
three sites, at line granularity, with the live pin resolved.

**Nothing filed and nothing built.** The check exists, it is correct, and it classes the finding
advisory to be resolved at each bundle's Stage 13. Corpus-wide it reports **29 pin-drift sites and
5 capability-claim sites across 65 drafts** — the live figure; the older "32 sites" number in the
bump memory is superseded and is not quoted here.

*This is the "check whether a check already measures it" rule paying for itself: a hand measurement
would have produced a worse version of a number the machinery already reports better.*

---

## 4. The count macros are used CORRECTLY here — the third data point

E1's abstract and §1 write *"(`\substantivetheorems` substantive theorems / `\leanmodules` modules
/ `\axiomcount` axiom / `\sorrycount` sorry)"* — **project-scoped macros**, the same ones TODO-D9
flags in D1 and D5.

**Here the usage is right, and the sentence is why:** E1 says *"The Lean 4 verification of the
underlying chain … **is independent of platform parameters**"*. The claim is explicitly about the
whole project chain, not about E1's substrate, so a project-scoped macro is the correct instrument.

**Three data points now fix TODO-D9's real shape:**

| | instrument | verdict |
|---|---|---|
| D1, D5 | project-scoped macro for a **bundle** figure | ❌ wrong scope |
| L3 | **bundle-scoped derived** macro (`\bhThermoTotal`) for a bundle figure | ✅ the template |
| **E1** | project-scoped macro for a **project** claim | ✅ correct as written |

**The defect TODO-D9 tracks is scope mismatch, not macro use.** Recorded there.

*(`\axiomcount` currently resolves to **0** — the project carries no project-local axioms — so
E1's "0 axiom" is derived and true, if grammatically odd in the singular.)*

---

## 5. What E1 gets right

- **A scope demarcation shipped as a theorem, and framed generously toward the platform it
  excludes**: *"This is a positive demarcation, not a failure of the UPenn device — which performs
  admirably for its actual purpose of nonlinear cavity QED — but it pins which polariton physics
  the present paper can soundly claim to govern."* The exclusion is quantified (`Γ_LP/κ ≈ 24.86`
  against a `< 0.1` threshold, *"a factor of nearly 250"*) and kernel-verified.
- **The definitional encoding is disclosed at its point of use**, D4-style: the `T_H` binding is
  *"a `rfl`-discharge on the `Basic.hawkingTemp` definitional unfolding); the substantive
  universality content lives upstream."*
- **The idealization is named with its validity window**: the gain numbers *"assume the
  greybody-saturation limit `Γ(ω) ≡ 1`"*, said to be appropriate for `ω ≲ 0.3κ`, with the
  correction order given (`O(ω²/κ²)`).
- **The project's own quality standard is applied against the more impressive number**: *"The
  steep-horizon prediction should be treated as leading-order, not all-orders."*
- **The figure caption places E1's own baseline device in the *Borderline* tier**, not the
  Perturbative one — *"just above the Borderline–Perturbative boundary"* — and says the ultralong
  variant is what reaches Tier 1.
- **Inline provenance comments per numbered claim**, naming the `constants.py` /
  `provenance.py` symbol *and* the Lean theorem. The richest per-claim provenance in the corpus.
- **The two declined absorptions are declined in writing, with reasons and a redirect** — the W1a
  noise-floor content *"already incorporated … via the abstract phrase"*, the W1b Kerr–Schild
  content *"appropriate publication home is D1, not the E1 letter."* **The best-handled stub block
  measured** (TODO-D14 → ten bundles; three now handled correctly).
- **An AI-assistance disclosure that separates the layers** — prose AI-assisted and human-reviewed;
  proofs *"ultimately certified by the Lean 4 kernel … independently of any AI tool."*
- **A follow-up table retrofit is registered as owed rather than hidden**: *"would be required at
  PRL submission."*

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/E1/bundle_metadata.json` | `apex_theorems` added — 7 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 2 → 1 |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D9 restated as *scope mismatch* with the three-way table; TODO-D14 → ten |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V38 |

**Nothing reassigned, nothing filed, nothing built.** Gate: `validate.py --check
bundle_apex_resolves` — PASS, 611 apexes across 20 bundles.
