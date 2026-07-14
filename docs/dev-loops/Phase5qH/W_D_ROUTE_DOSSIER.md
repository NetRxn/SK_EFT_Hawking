# W-D completeness-leg — route-selection dossier (input ledger + recommendation)

> **Status:** analysis-only deliverable (slot wt1, 2026-07-13). Gitignored notebook artifact — NOT committed.
> The lead makes the live-layer W-D route call from the executive summary + this ledger.
> **Scope of the decision:** which architecture discharges W-D completeness on the FAITHFUL carrier
> `pinPlusCharPairData prov : T2TangentialData` — the `charPairBrown : T2DataBordismGrp → ZMod 8` door
> already stands. Route candidates (roadmap §6): **KT §5 direct** vs **Smith-LES**.
> All on-main names below were verified live via grep/LSP against `lean/SKEFTHawking` — not trusted from docs.

---

## 0. The decision framing (what W-D actually has to prove, post-rebuild)

The faithful carrier is the **dim-4** `pinPlusCharPairData prov : T2TangentialData PUnit k I`
(`PinPlusCharPairData.lean:1063`), whose genuinely-computed invariant is
`charPairBrown : T2DataBordismGrp (pinPlusCharPairData prov) →+ ZMod 8` (`PinPlusCharPairData.lean:1094`)
— the `[∩w₁²]` characteristic-surface Brown map. **This is a mod-8 door, by design and honestly** (roadmap
§7: the GM surface package `(Σ,q)` computes the invariant mod 8 only; the `{0,8}` kernel is invisible to
`(Σ,q)` — the fake-ℝP⁴ 9-vs-1 fact). We have `charPairBrown_surjective` and `charPairBrown_rp4_ne_zero`
(`RP4CharPairWitness.lean:124,137`).

W-D's target is therefore the extension
```
0 → ℤ/2 → G → ℤ/8 → 0   (G := T2DataBordismGrp (pinPlusCharPairData prov)), non-split ⟹ G ≅ ℤ/16, ord[ℝP⁴]=16
```
with the surjection `G ↠ ℤ/8` = `charPairBrown` [DONE]. **W-D = the kernel analysis + the non-split bit.**
The two routes differ entirely in how they close `ker(charPairBrown) ≅ ℤ/2` and the non-split extension.

Crucial architectural consequence (drives everything below): on the **retired tied carrier** `grade16` was a
carried field, so `≃+ ZMod 16` and non-splitness were *free bookkeeping* — that is precisely leg-3 infidelity
(`nonhausdorff-bordism-collapse`, `genuine-gm-carrier-eight-torsion`). On the **rebuilt CharPair carrier the
ℤ/16 is NOT read off any carried grade** — the mod-8 door is all the `(Σ,q)` data can see, and the odd/16
content must be assembled at the extension level. The "index theory drops out" convenience recorded on the
tied carrier (SETTLED_FORKS `5qH-injectivity-routes` 07-06) was verified over the *tied* carrier and does
**not** transfer for free. This is the single biggest live uncertainty (§4, §5).

---

## 1. LEDGER — KT §5 direct route

Route: `0 → ℤ/2 → Ω₄^{Pin⁺} → ℤ/8 → 0` (`KT_LMS_Section5_completeness_proof_extracted.md`, Thm 5.2 /
Lemma 5.3 / §6). `ℤ/8` = `Ω₂^{Pin⁻}` (Brown/Gauss); kernel = image of `Ω₄^{Spin}`, `≤ ℤ/2` by Lemma 5.3
(÷32 signature); non-split via `ψ ∈ ℚ/32ℤ`, `ψ(ℝP⁴)=+2`. NO external stable ℤ/16 input — `card = 16 = 2·8`
assembled FROM BELOW.

| # | Required input | Class | Exact name / evidence |
|---|---|---|---|
| K1 | The `[∩w₁²]` surface map to `Ω₂^{Pin⁻}≅ℤ/8` (KT input iv) | **(a) ON MAIN** | `charPairBrown` `PinPlusCharPairData.lean:1094`; surjective `charPairBrown_surjective` + `charPairBrown_rp4_ne_zero` `RP4CharPairWitness.lean:124,137`; anti-collapse engine `brown_eq_of_taylorLeg_lagrangian` `:86` |
| K2 | ℝP⁴ IS the char surface source (equatorial ℝP²) + surjectivity chain | **(a) ON MAIN** | `hchar_pairing` `RP4CharSurfacePushforward.lean` / `RP4CharSurfaceSmithNat.lean`; `rp4SM_k` `RP4Manifold.lean:321`, `rp4SM` `RP4Witness.lean:33` |
| K3 | Kernel-null direction: `charPairBrown = 0 ⟹ spin-reducible` (Taylor A5/A6 bounding⟹q-vanishes) | **(b) RESTATEMENT-NEEDED** | `CharSurfaceMembrane.lean` / `taylorKernelVanishing_*` + `CharSurfaceBounding`/`CharSurfaceTrace`/`CharSurfaceCircle` exist but were authored against the old carrier; **template-mirror** onto the CharPair Bor |
| K4 | Spin-side instance of the CharPair pattern (empty-Σ) + inclusion `Ω₄^{Spin}→G` as the kernel | **(c) MISSING · template-mirror** | reuses `charPairEmptyStr`/`charPairSumStr` + the dim-4 `T2TangentialData` framework; a *specialization* (n=0) of W-A, not new dimension/geometry |
| K5 | `Ω₄^{Spin}≅ℤ` (KT input i), decomposed per Benedetti Ch.20 | **mixed (see K5a–K5d)** | `Omega4Spin_Z_formalization_route_20260706.md` |
| K5a | even-indefinite form `≅ p·E₈⊕q·H` + `σ=0 ⟹ n·H` lattice normal form | **(a) ON MAIN** | `exists_hyperbolic_congr` `HyperbolicNormalForm.lean:169`; `k3Form` (σ=−16) `SpinSigmaGenerator.lean:122`; Milnor–Husemoller lattice lemmas in-tree (reuses E1) |
| K5b | `σ : Ω₄^{SO}→ℤ` injective (σ=0 ⟹ bounds; Benedetti Thm 20.14, transversality) | **(c) MISSING · bounded-elementary** | Mathlib-absent but bounded; reuses E1's integral intersection form |
| K5c | handle-trading (Benedetti Lemma 20.17 / Prop 20.16) | **(c) MISSING · deep-new-geometry (1 lemma)** | the ONE piece with zero library support in ANY assistant; carryable as ONE tracked Prop w/ Benedetti 20.17 discharge plan |
| K5d | Rokhlin mod-16 (spin ⟹ 16∣σ) = Lemma 5.3 base | **(a/c) ON PLAN (E2)** | `hyp:rokhlin_sigma_mod_16`; Arf-FK bridge `GMRokhlinDischarge.lean`, `CharSurfaceRokhlinAssembly.lean`, `GMArfVanishing.lean`, `AlgebraicRokhlin.lean`, `RokhlinFromHM.lean` all present; residual = E2 htopo (mission's W-E) |
| K6 | Lemma 5.3 ÷32 (`32∣σ ⟹ Pin⁺-bounds`; Enriques/Habegger + Rokhlin-content) | **(c) MISSING · bounded-elementary** | E2-adjacent; the `⟸` uses "K3 generates Ω₄^{Spin}" (= K5, no Rokhlin-only shortcut — see fork 07-06b) |
| K7 | Non-split witness `8·[ℝP⁴] ≠ 0` (KT ψ∈ℚ/32ℤ, ψ(ℝP⁴)=2) | **(c) MISSING · deep-new OR standalone — THE uncertainty** | on the tied carrier this was free (carried grade); on CharPair the `{0,8}` distinction is invisible to `(Σ,q)` ⟹ needs ψ (index: μ+Atiyah–Singer α, deep-new) or a fresh structural argument. §4/§5. |

**KT deep-input residual (honest):** `{ Ω₄^{Spin}≅ℤ (K5b bounded-elementary + K5c one handle-trade lemma),
Rokhlin-content K5d/K6 (E2, in progress), non-split K7 }`. **No external stable ℤ/16.**

---

## 2. LEDGER — Smith-LES route

Route (`ABK_injectivity_routes_lemma_DAG_20260703.md` §4): the codim-2 Smith map gives
`0 → Ω₆^{Pin⁻}(≅ℤ/16) →^{(g),≅} Ω₄^{Pin⁺}(≅ℤ/16) → 0`, `ℝP⁶↦ℝP⁴`. The ℤ/16 is **transported**, never
generated from below; every published version consumes ONE external stable input.

| # | Required input | Class | Exact name / evidence |
|---|---|---|---|
| S1 | Codim-2 Smith map `g : Ω₆^{Pin⁻}→G` as a carrier homomorphism (zero-locus PD of w₁²) | **(c) MISSING · deep-new-geometry** | Smith App. A map (2); not in faithful form in-tree |
| S2 | Sphere-bundle construction `Z=Sph(A*σ)` (surjectivity leg) | **(c) MISSING · deep-new-geometry** | HKT Thm 4.1 proof; manifold-level model absent |
| S3 | Interval-bundle gluing `W=(X×[0,1])∪Z̃` (injectivity leg, twisted-structure bookkeeping) | **(c) MISSING · deep-new-geometry** | HKT Thm 4.1 / Fig. 3; the structure-bookkeeping "where errors live" |
| S4 | LES exactness of the three-term Smith sequence | **(c) MISSING · template-mirror once S1–S3 exist** | Smith Eq. (7.40) |
| S5 | **`smith_inflow_z16` : `Ω₆^{Pin⁻}≅ℤ/16`** (external stable input, ABP 1969, spectral) | **(b)+(c) RESTATEMENT-NEEDED + external-stable-input** | present ONLY over the vacated tied carrier: `PinPlusGMDataZ16.lean`, `PinPlusGMWitness.lean:210`, `PinPlusFaithfulnessCardBridge.lean`, `CommonOrigin.lean:215`. **Its faithful restatement requires a faithful dim-6 Ω₆^{Pin⁻} carrier** (§3). NO published elementary elimination. |
| S6 | Faithful dim-6 `Ω₆^{Pin⁻}` carrier (T2 + smooth + structure-tied — all 3 legs, at dim 6) | **(c) MISSING · deep-new-geometry (a second faithful carrier)** | none in-tree; the current Ω₆ appearances are tied-carrier / vacated |

**Smith deep-input residual:** `{ three geometric constructions S1–S3 (dim 4→6, deep-new),
a faithful dim-6 carrier S6 (deep-new — re-incurs all 3 faithfulness legs), plus the external spectral ℤ/16
S5 with no elementary discharge }`.

---

## 3. Spin-side assessment (the mission's critical leg — where the routes diverge structurally)

Both routes route their completeness through the Spin side. The shapes differ decisively:

- **KT §5 needs a dim-4 Spin instance = the empty-Σ SPECIALIZATION of the CharPair carrier already built.**
  A Spin 4-manifold has `w₁=w₂=0 ⟹ Σ` (dual to `w₂+w₁²`) is empty ⟹ the char-pair enhancement has `n=0`
  ⟹ `charPairBrown = 0` on the entire spin image — automatic and consistent (the spin classes ARE
  `ker(charPairBrown)`). The framework already carries `charPairEmptyStr`, `charPairSumStr`, `charPairUnitBor`.
  So the spin-side instance is **the same dim-4 `T2TangentialData` machine, specialized** — no new dimension,
  no new bundle constructions. The genuine added content is `Ω₄^{Spin}≅ℤ` (K5) + Lemma 5.3 (K6), both in the
  dim-4 / intersection-form wheelhouse that W-A/B/C + E1/E2 already occupy. The v4 gate no-gos are *satisfied
  by construction* here: the odd/16 bit is carried structurally (KT's w₁-dual `V`/ψ), NOT as an H¹ `comp`
  coordinate (`comp-twist-doubling-incompatible`), and the grade is enhancement-tied not free
  (`synthetic-grade-ker-bot-nogo`).

- **Smith-LES needs a dim-6 `Ω₆^{Pin⁻}` instance + the sphere/interval-bundle Smith machinery — a fresh
  faithful carrier at a new dimension.** The ℤ/16 lives in `Ω₆^{Pin⁻}` and is transported down; to be
  non-vacuous that dim-6 carrier must independently satisfy all three faithfulness legs (T2 + smooth +
  structure-tied). This is a *second* W-A-scale construction, largely disjoint from the dim-4 CharPair
  infrastructure, and it sits on top of an external spectral input that has no elementary substitute.

**Net spin-side verdict:** KT §5's spin-side is a *reuse-and-specialize* of the carrier the project just
built and hardened; Smith-LES's spin-side is a *new faithful carrier at dim 6* plus new geometric
constructions plus an unelimin­able external input. On the spin-side axis alone, KT §5 dominates.

---

## 4. Vacuity-attack surface (roadmap §3 — the MANDATORY zero-geometric-input attack on each terminal Prop)

The taylor-leg lesson: state the attack surface of each route's *terminal* completeness Prop, because any
`hbound`-class Prop is attacked with zero geometric input before it is consumed.

**KT §5 terminal Props:**
- `card ≤ 16` ⟺ `ker(charPairBrown) ≤ ℤ/2`. Attack = "can a degenerate/bookkeeping witness force `ker≤ℤ/2`
  without geometry?" The three known collapse exploits are **already fenced on the CharPair carrier**:
  non-Hausdorff spin witnesses are blocked per-datum (`membrane-level-nonhausdorff-collapse` fix — each
  manifold-typed field carries its own T2+compact+charted cert); the `÷32⟹bounds` content cannot reduce to
  algebra because `nogo_lattice_arf_not_sigma8` kernel-proves `σ/8 ≢ Arf mod 2` (the ÷16 is irreducibly
  geometric, NOT bookkeeping). **So the KT terminal `÷16/÷32` Prop's non-vacuity is partly PRE-PROTECTED by
  an existing kernel no-go.** This is a strong posture.
- Non-split `8·[ℝP⁴] ≠ 0`. Attack = "is `8·[ℝP⁴] = 0` forced trivially?" Since
  `charPairBrown(8·[ℝP⁴]) = 8·(gen ℤ/8) = 0`, `8·[ℝP⁴] ∈ ker` and the `(Σ,q)` data CANNOT see whether it is
  `0` or the order-2 class. **This is the one KT terminal Prop with a genuinely open attack surface** — it
  needs an invariant separating `{0,8}` (ψ / μ+α, or a structural `8·ℝP⁴=[Kummer]≠0` argument). See §5.

**Smith-LES terminal Prop:**
- `smith_inflow_z16 : Ω₆^{Pin⁻}≅ℤ/16`. Attack = "is a `ℤ/16` iso over a dim-6 bordism carrier
  self-dischargeable?" **YES, identically to the tied ℤ/16** — a T2-less / grade-carrying dim-6
  `Ω₆^{Pin⁻}` carrier collapses under the *same* `nonhausdorff-bordism-collapse` mechanism, and a carried
  grade makes the iso free bookkeeping. The current in-tree `smith_inflow_z16` is stated over exactly the
  vacated tied carrier — **it is already a vacuous statement today.** Making it non-vacuous re-incurs the
  entire three-leg faithfulness burden at dim 6 (S6). So Smith-LES's terminal Prop **reintroduces the full
  faithfulness-vacuity problem** the phase just paid to fix, one dimension up.

**Net vacuity verdict:** KT §5 concentrates its one open vacuity risk in a single, well-localized bit
(non-split, §5), with the bulk (`÷16/÷32`) pre-fenced by kernel no-gos on the hardened dim-4 carrier.
Smith-LES's terminal Prop is *currently vacuous* and its de-vacuum-ing is a second faithful-carrier program.

---

## 5. THE biggest uncertainty (both routes, but sharper for KT — name it explicitly)

**The non-split bit `8·[ℝP⁴] ≠ 0` on the faithful CharPair carrier.** On the retired tied carrier this was
free (grade16 carried). On the CharPair carrier the mod-8 door is blind to `{0,8}`, so the odd/16 content is
NOT supplied by `charPairBrown`. The SETTLED_FORKS record that "index theory drops out — surjective-onto-ℤ/16
is standalone via Gauss-sum + δ-cap" was verified over the *tied* carrier and does **not** automatically
transfer. Three ways it can resolve, in decreasing in-tree leverage:
1. a structural `8·[ℝP⁴] = [Kummer] ≠ 0 ∈ G` argument reusing the char-pair bordism relation + E2 Rokhlin
   (best case — bounded, reuses assets);
2. the KT `ψ ∈ ℚ/32ℤ` non-split witness (μ + Atiyah–Singer α) — genuinely index-theoretic, deep-new, NOT
   in faithful form in-tree (worst case for effort);
3. re-derivation of the tied carrier's Gauss-sum/δ-cap standalone argument on the CharPair carrier (needs
   fresh verification — plausibly the intended path, but unproven post-rebuild).

This bit is the most likely place W-D stalls **regardless of route** — KT localizes it to one 1-bit
extension fact; Smith-LES hides it inside `smith_inflow_z16` but only by paying for the external spectral
input + a dim-6 faithful carrier. A 1-bit localized risk is strictly preferable to a two-large-construction
relocation.

---

## 6. Effort-class bottom line

| | KT §5 direct | Smith-LES |
|---|---|---|
| dim-8 surface door (ℤ/8 quotient) | **ON MAIN** (`charPairBrown`) | ON MAIN (same door reusable) |
| spin-side instance | template-mirror of dim-4 W-A (empty-Σ) | **deep-new dim-6 faithful carrier (2nd 3-leg build)** |
| the ℤ/16 provenance | assembled FROM BELOW (2·8) | **transported from external spectral `Ω₆^{Pin⁻}`** |
| external stable input | **NONE** | **`smith_inflow_z16` (no elementary elimination; currently vacuous)** |
| deep geometric constructions | K5b σ-inject (bounded-elem) + K5c ONE handle-trade lemma | S1–S3 three constructions (all deep-new, dim 4→6) |
| Rokhlin leg | E2, on plan (shared, route-independent) | E2, on plan (shared) |
| terminal-Prop vacuity posture | ÷16/÷32 PRE-FENCED by kernel no-gos; 1 open bit (§5) | terminal Prop currently vacuous; de-vacuum = 2nd faithful carrier |
| in-tree convergence | high (charPairBrown, exists_hyperbolic_congr, k3Form, E2, 07-06 re-anchor) | low (dim-6 machine largely absent) |

KT §5's residual is **bounded-elementary + one handle-trade lemma + one localized non-split bit**, all on the
dim-4 carrier already built. Smith-LES's residual is **two large new constructions (dim-6 faithful carrier +
bundle machinery) + an unelimin­able external spectral input whose current statement is vacuous.**

---

## 7. RECOMMENDATION — **KT §5 direct**

Decisive factors (in order):

1. **Carrier reuse vs. a second faithful carrier.** KT §5's spin-side is the empty-Σ specialization of the
   dim-4 CharPair carrier W-A already built and hardened; Smith-LES requires a *fresh faithful dim-6
   `Ω₆^{Pin⁻}` carrier* re-incurring all three faithfulness legs plus new sphere/interval-bundle
   constructions. This is the single largest effort and risk asymmetry.

2. **No external stable ℤ/16.** KT assembles `card = 16 = 2·8` from below via `Ω₄^{Spin}≅ℤ`, which the
   Benedetti Ch.20 sizing shows is bounded-elementary and substrate-reusing (E1 lattice `exists_hyperbolic_congr`
   + `k3Form` on main; E2 Rokhlin on plan). Smith-LES's `smith_inflow_z16` has no published elementary
   elimination and — critically — its current in-tree statement is *vacated by `nonhausdorff-bordism-collapse`*;
   making it honest is itself a second faithful-carrier program.

3. **Stronger vacuity-attack posture.** KT's terminal `÷16/÷32` content is pre-protected by the existing
   `nogo_lattice_arf_not_sigma8` kernel no-go (the ÷16 cannot be bookkeeping) on the hardened CharPair
   carrier; its one open bit (non-split, §5) is well-localized. Smith-LES's terminal Prop re-opens the full
   faithfulness-vacuity problem at dim 6.

Corroborating: KT is the notebook's stated KT-lean posture, converges with the 07-06 keystone re-anchor and
every in-tree asset, and the route-equivalence fork (`5qH-injectivity-routes-...`) already proved the two are
apex-equivalent as *targets* — so choosing KT costs nothing in generality while buying the cheapest
substrate.

**Biggest uncertainty to flag to the lead:** the non-split bit `8·[ℝP⁴] ≠ 0` on the faithful carrier (§5).
The mod-8 `charPairBrown` door is blind to the `{0,8}` kernel, and the tied-carrier "index drops out" fact
does NOT transfer for free. Recommend that W-A/W-C already stage the structural `8·[ℝP⁴]=[Kummer]≠0`
argument (option 1) so W-D does not discover late that it needs the ψ/μ+α index invariant (option 2, the one
genuinely deep-new-geometry fallback). This bit — not the route choice — is the real critical node.

**Standing no-go compliance:** neither route re-attempts `lattice_arf_bridge_refuted` or
`dataBordism_two_torsion_of_revStr_trivial`; KT's ÷16 is honestly geometric (not a lattice Arf) and its grade
is enhancement-tied (not free). If W-D work starts reproducing either fork, STOP and report per ADR-007.
```
