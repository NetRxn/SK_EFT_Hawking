# E2 apex retrofit — the last bundle, and the E1+E2 merge question answered at the substrate level

**Date:** 2026-08-07 · Twenty-first and final bundle retrofitted under ADR-010 §D5a.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/E2/paper_draft.tex`
(579 lines, every line, including the inline provenance block and the nested scope correction at
§6), `bundle_metadata.json`, `lean/SKEFTHawking/ChernBridge.lean` (to verify E2's own retraction
before repeating it), and the declaration lists of the six graphene modules plus
`DKMBootstrap/E1E2CrossBridge`.

---

## 1. What was declared

**6 apexes → 12 declarations across 6 modules, depth 1, zero truncations.**

**The smallest closure in the portfolio** — smaller than L1's 18. Depth 1: every apex rests only on
its own module's definitions.

| § | thread | apexes |
|---|---|---|
| §2 | the quasi-1D guarantee (lowest transverse channel `> 4ω_H`) | 1 |
| §2 | the acoustic-metric block-diagonalization | 2 |
| §3 | `T_eff > 0` for `D² < 6/π` | 1 |
| §4 | the closed-form noise PSD's algebraic identity | 1 |
| §1 | the `T_H` name-binding (disclosed as a `rfl`-discharge) | 1 |

**Excluded:** `DiracFluidWKB.toExactWKB` — E2 calls it *"the binding lemma"*, and it resolves as a
**`def`**, so it would fail `apexes_are_theorems` as well as the declaration rule.

---

## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean

| field | statement |
|---|---|
| **Audience** | Two named experimental groups (Dean, and Kim–Lucas for the transport side) plus the noise-spectroscopy community. Like E1, the paper has a section headed *Request to the Dean-Kim-Lucas teams*. |
| **Venue** | PRL \| PRR. Correct — a device-specific prediction with an integration-time estimate. |
| **The claim only this container can make** | **The one analog-Hawking platform whose predicted `T_H` sits inside an existing instrument's operating window, with the observable given as a closed-form current-noise PSD.** `T_H ≈ 2.4 K` — nine orders above atomic BEC, an order above polariton — and `ΔS_I(ω) = 2ħω σ_Q Γ(ω) n_H(ω)`, with cumulative SNR reaching unity in ~1 minute. No sibling makes a measurable-this-week claim. |
| **Substrate** | 6 modules, 12 declarations, depth 1: `DiracFluidMetric`, `DiracFluidWKB`, `GrapheneHawking`, `GrapheneNoiseFormula`, `AcousticMetric`, `Basic`. |
| **Honest size vs charter** | 579 lines against a Tier-4 letter — over, essentially identical to E1's 583. |
| **Boundary failure?** | **No.** `E2 ∩ D1 = 11` is D1's companion relationship (D1's abstract names E2); `E2 ∩ E1 = 5` is only the universal `T_H` binding. E2 needs no sibling's substrate. |

---

## 2. ✅ ADR-010 §D4 — the E1+E2 merge, measured. Evidence only; no recommendation.

The last open merge question, now measurable from both sides:

| measurement | value |
|---|---|
| `E1 ∩ E2` closure | **5 declarations**, entirely in `AcousticMetric` + `Basic` |
| what those 5 are | the platform-**independent** `T_H = ħκ/2πk_B` binding and its dependencies — the thing both drafts say is universal |
| apex overlap | **1** — `hawking_temp_from_surface_gravity`, i.e. exactly that binding |
| E1-only / E2-only declarations | **31 / 7** |
| E1-only modules | `PolaritonTier1`, `DKMBootstrap/{PolaritonF3Bound, HorizonTransportBootstrap, SKEFTSpecialization, Predicates, E1E2CrossBridge}` |
| E2-only modules | `DiracFluidMetric`, `DiracFluidWKB`, `GrapheneHawking`, `GrapheneNoiseFormula` |
| shared platform modules | **none** |

⚠️ **And the module named for the relationship argues against it.**
`DKMBootstrap.E1E2CrossBridge` — in E1's closure, never named by E2 — contains
`bec_kms_quality_approximate`, `polariton_kms_quality_effective_only`,
`graphene_kms_quality_strong`, and `platform_kms_qualities_pairwise_distinct`. **The one Lean module
built to relate the two platforms proves their KMS qualities are pairwise *distinct*.**

**Verdict — substrate level: REFUTED.** The two letters share only the universal temperature
binding; their platform substrates are disjoint at the module level; and the formal cross-bridge
establishes difference, not commonality. A merged bundle would be two disjoint substrates under one
cover.

**Verdict — editorial level: NOT DECIDED, and the closure is the wrong instrument.** Both are
~580-line Tier-4 letters with parallel structure (identical `T_H` paragraph, a *Falsifiable window*
section, a *Request to the … teams* section), addressed to **different experimental groups**. Whether
to publish one two-platform letter or two one-platform letters is a question about audience and
submission strategy, and no closure measurement can answer it. Recorded, not decided.

⚠️ **Context that belongs with the decision, not a recommendation:** **D1 already occupies the
one-paper-three-platforms position** — its abstract offers *"a unified, formally verified treatment
of analog Hawking radiation across three condensed-matter platforms"* and calls E1 and E2
*"companion experimental letters [that] carry the experimental-team-targeted implementations."* A
merged E1+E2 would sit between D1's unified treatment and the per-device letters that D1 says exist
to be per-device.

---

## 3. ⚠️ A cross-bundle inconsistency: E2 retracts a phrase E1 still uses

E2 §6 carries an italic scope correction:

> *"Earlier drafts called `c₁` **"the topological Chern coefficient of the graphene moiré
> band-structure"**. It is neither: `ChernBridge.lean:68` defines
> `categoricalChernExpansion c0 c1 := [c0, c1]`, a two-term Chebyshev expansion, and no graphene and
> no moiré superlattice appear anywhere in that module."*

**Verified before repeating it (C4).** `ChernBridge.lean:68` is exactly
`def categoricalChernExpansion (c0 c1 : ℝ) : ChebyshevExpansion := ⟨[c0, c1]⟩`. ✓

**And E2's correction of its own correction is also accurate.** It adds that an earlier version of
the retraction wrongly claimed no Brillouin zone appears — *"`ChernBridge.lean:14` frames the
crystalline limit as a Brillouin-zone Chern number reducing to a sum"*. The module docstring says
precisely that. ✓ **A nested self-correction where both layers check is the strongest honesty
artifact in the corpus.**

**But E1:410 still reads** *"AND the topological Chern coefficient `c₁` of the underlying
condensate vanishes"*, and continues *"the polariton platform … falls in the topologically-trivial
regime (`c₁ = 0` for the polariton fluid's effective Hamiltonian)."* Both letters carry the same
Phase-6w demarcation paragraph; **the 2026-08-01 D11 Stage-13 correction landed in E2 and not in
E1.** Filed as **TODO-D20**.

---

## 4. Also observed

- **`QuasiOneDReduction.lean` is named twice for the ≤1.8% bound; no theorem in it is named.** The
  module holds 11 theorems including `quasi1D_validity_bound`. TODO-D19 residue.
- **Four pin-drift sites** (`v4.29.0` / `8850ed93` in the conclusion and acknowledgments) — the
  registered `paper_toolchain_pin_drift` check already names **E2:484, 485, 488, 489**. Existing
  coverage; nothing filed, nothing built.
- ⚠️ **Not verified, and saying so per C4:** §2's *"`DiracFluidWKB.toExactWKB` … is checked in
  ~93% of the transferred Lean theorems."* I did not find a derivation for 93% and did not
  construct one — building a measurement for it would be new infrastructure under §6a. **Recorded
  as unverified, not as wrong.**
- **The `graphene Γ_H` reserved item is E2 §3**: `Γ_H = (η/s T)(κ/c_s)² ≈ 0.3 s⁻¹`,
  `δ_diss ≈ 10⁻¹³`. Noted, **not resolved** — it is a STOP-AND-ASK item.

---

## 5. What E2 gets right

- **The nested self-correction** of §3 above — a retraction that then narrows itself, with the file
  and line for each layer.
- **Its own headline theorem is disclosed as weaker than it looks**: `fdt_consistency`
  *"reduces to arithmetic on the closed-form expression (`unfold; ring` …); the Lean artifact
  certifies the algebraic identity of the closed form, **not the equivalence of the two
  derivations**."* The two-route agreement is the abstract's selling point, and the draft says the
  Lean does not prove it.
- **The cross-device modeling assumption is flagged three times** — abstract, §1, §3 — each time
  naming what was transferred and from where: *"a modeling assumption since the Dean nozzle device
  … is plausibly within the same universality class but is not itself the device measured in
  [Majumdar]."*
- **A more careful `κ` than the obvious one**: *"estimated from the deep-research-derived nozzle
  velocity profile rather than the order-of-magnitude identification `c_s/L ≈ 2.2×10¹² s⁻¹`."*
- **It corrects a cited paper's normalization rather than quoting it**: Falque et al.
  *"quote the un-normalised `ħκ/k_B ≈ 3 K`"* against the standard `T_H = ħκ/2πk_B`.
- **Prior credit is given before the contribution is claimed**: Geurs et al. *"already notes the
  de Laval–acoustic-black-hole analogy and an order-of-magnitude estimate `T_H ∼ 500 mK`; the
  detailed analog-Hawking spectrum … below are this Letter's theoretical development."*
- **A figure caption calls its own margin marginal**: `ω_H/Γ ≈ 1.6` is *"marginal but improving
  with ultra-clean samples."*
- **The framework's actual contribution is stated modestly**: with `δ_diss ~ 10⁻¹³`, *"the SK-EFT
  framework's value for graphene is therefore the systematic organization of corrections — and the
  formal verification — not a specific dissipative modification of `T_H`."*

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/E2/bundle_metadata.json` | `apex_theorems` added — 6 entries |
| `scripts/validation/checks/bundles_readiness.py` | **`UNDECLARED_APEX_CEILING` 1 → 0** |
| `docs/audits/2026-08-07-d4-merge-evidence/EVIDENCE.md` | the E1+E2 row completed — the last open merge question |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | **TODO-D20** (E1 still carries the phrase E2 retracts) |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V39 |

**All 21 bundles declare apexes.** Gate: `validate.py --check bundle_apex_resolves` — PASS,
617 apexes across 21 bundles, **0 undeclared**.
