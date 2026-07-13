# Phase 5q.H — Literature-grade unconditional `Ω₄^{Pin⁺} ≅ ℤ/16` (closing the two residual deltas)

> **▶ READ FIRST — the operational entry point is [`docs/dev-loops/Phase5qH/PHASE5QH_EXECUTION_MAP.md`](../dev-loops/Phase5qH/PHASE5QH_EXECUTION_MAP.md).** Start every session there: it carries the live 5-effort (E1–E5) build DAG, the verified-source index, the worktree pointers, the atlas both-fronts hook, and the parallelization plan. **This roadmap is the strategic tracker** (why the phase exists, route decisions, gate history); the execution map is *how* the build runs now. Present-state checkoffs ↓ (Status checklist).

**Status:** 🆕 OPENED 2026-07-03, immediately after Phase 5q.G closed at full strength (wave-3 merge
`036735e5`, trusted rebuild 9597 exit-0, validate 45/45 `validation_20260703T193710Z`, adversarial
review PASS 0-BLOCKER/0-MAJOR). Every claim in §2–§3 was **ground-truth-vetted against Lean source on
main at `1c455781`** (the 5q.G discipline: source/git/counts are evidence; notebook self-claims are not).

**Owner workstream:** public `SK_EFT_Hawking` Lean.
**→ §10 (2026-07-04): the Phase 1 / Phase 2 wave breakdown to unconditional discharge, from current main state.** Read §10 (+ its correction banners + crux note) for the execution path.

> **🟢 OPTION A — GO (operator, 2026-07-04): genuine unconditional discharge, full strength.** The A-vs-B decision is MADE: build the genuine L4 (`omega4PinPlusGM_equiv_zmod16`, genuine carrier, computed invariant, ZERO posits), NOT the disclosed-form L3 (retained only as stepping-stone/fallback). **The operational entry point is now `docs/dev-loops/Phase5qH/PHASE5QH_EXECUTION_MAP.md`** — it decomposes the build into **5 efforts (E1–E5), each with its own notebook**, indexes every personally-verified primary source, points the worktrees (wt1 holds usable relative-PD substrate; wt2/wt3 free), and gives the multi-agent parallelization plan. §10's P1.1/P1.2/P1.3/P2.1 waves map onto E2/E3/E4/E5 (E1 = the shared Substrate-G foundation §10 folds into Phase 1). **All external inputs are direct-primary-read verified** (Taylor `0802.0111`, Klug `2011.12418`, DDK⁺ `2405.04649`, HKT `1910.14039`, `2406.08237`, KT-LMS §5) — trace in `16Convergence_Reconciliation_Audit_2026-07-04.md §2`.
> **⚠ §0–§9 ARE SUPERSEDED where they conflict with §10 + `16Convergence_Reconciliation_Audit_2026-07-04.md`.** They are the *original 2026-07-03 phase-open plan* (H1–H8 gates, the "route α", the "two disclosed Props" and "Phase 1 in-tree / disclosed-form" framings). Three of those framings are now CORRECTED: (1) the "concentrated input is elementarily dischargeable (Matsumoto)" — WRONG (§9.3 conflated the divisibility base case with the non-elementary ℤ/16 completeness; see §9.3 banner). (2) "Phase 1 in-tree" — WRONG (it is a from-scratch geometric substrate build; see §10 Phase-1 banner). (3) "Phase 2 contingency" — WRONG (REQUIRED; see §10 crux note). Read §0–§9 as historical rationale, not current status.
**Tracker = this file.** Lab notebooks: **per-effort** under `docs/dev-loops/Phase5qH/E1…E5/` (entry point =
`PHASE5QH_EXECUTION_MAP.md`; the pre-Option-A disclosed-form notebook is archived at `Phase5qH/_archive/`).
Primary-source DR reports + the KT-LMS PDF live in `Lit-Search/Phase-5qH/` — read them directly, never via
summary. Negative register: `docs/dev-loops/SETTLED_FORKS.md` + the machine-fed atlas negative frontier
(`KERNEL_NOGO_REGISTRY` / `/skeft-qa:frontier`; ADR-007). Continuation of
[Phase 5q.G](Phase5qG_GenuineUnconditional_Roadmap.md).

---

## Status checklist (present state — last gated main @ `2f2da4e6`, validate 46/46 `validation_20260713T002620Z`, 2026-07-13)

> **⏱ FRESHNESS (2026-07-13 refresh):** the ✅/⚠ blocks below are re-synced to the live substrate. Main is now hundreds of commits past the 2026-07-04 `1e239b71` this section was first pinned to. **The single most important correction vs. the deep sections (§9.3/§10): the keystone is `Ω₄^{Spin}≅ℤ` GEOMETRIC (KT §5 from-below close), NOT the ABP spectral `smith_inflow_z16` — see the line-39 re-anchor banner, which SUPERSEDES §10's crux note where they conflict (§10 flagged inline).** Track by E-number; brick-by-brick live state = master `LAB_NOTEBOOK_INDEX.md` FRONTIER.

> **Naming (canonical):** work is tracked by **E1–E5** — the execution map's efforts (its *Naming* section holds the one E ↔ H ↔ P ↔ L cross-walk). **L1–L4** = result-strength diagnostic (not a work unit); **H1–H8 / P1.1…** = historical. Use E-numbers.

**✅ DONE — the disclosed-form L3 substrate + this phase's planning (the pre-E foundation):**
- [x] **Disclosed-form L3** on the synthetic **tied** carrier: `Ω₄^{Pin⁺}≅ℤ/16`, kernel-pure, modulo one Prop packaging G+S (`omega4PinPlusGMTied_equiv_zmod16_via_kt_of_grade0`). Bundles the Brown/ABK ℤ/16 algebra, ℝP⁴ surjectivity, and the injectivity route-unification to ONE completeness Prop (`smith_inflow_z16`).
- [x] **Reconciliation + Option-A GO + execution map + E1–E5 effort notebooks** (this phase's planning layer)
- [x] **All external inputs direct-primary-read verified** (Taylor/Klug/DDK⁺/HKT/`2406.08237`/KT-LMS §5 — reconciliation §2)
- [x] **ADR-007 kernel no-go ledger** — the negative frontier is machine-fed (supports the build; not a work effort)

**Carrier (unchanged):** the literal `DataBordismGrp(pinPlusGMData) ≃+ ZMod 16` target is **KERNEL-PROVEN IMPOSSIBLE** (`pinPlusGMData` is 8-torsion; no-go `genuine-gm-carrier-eight-torsion`); the genuine ℤ/16 lives on the **enriched (σ,F•F) / Smith-LES extension carrier**.

**✅ SURJECTIVITY / ℤ/16 detection (the σ÷16 leg) — DEMONSTRATED UNCONDITIONALLY:**
- [x] **E1 · integral-topology foundation — DONE.** Integral `(co)homology → cup → cap → Kronecker → intersection form → σ÷16`, functoriality (mod-2 AND ℤ), homotopy invariance (absolute + relative/pair), Euclidean acyclicity, pair-LES, subdivision/excision, cohomology MV, the local iso `H₄(M|x;ℤ)≅ℤ`, and the oriented fundamental class `[M]`/`intOrientation` — all MERGED, kernel-pure. The "community-scale wall" of building 4-manifold integral topology in Lean is discharged. Orientation is now a class-level device (`IntOrientationGlobalSection.IntGlobalGenerator`: any `E:H₄≃+ℤ` + two puncture-vanishings ⟹ `IntOrientationData M`).
- [x] **σ÷16 leg FIRES END-TO-END, ZERO BINDERS:** `sixteen_dvd_latticeSig_sphere4_unconditional` (S⁴) verified `{propext, Classical.choice, Quot.sound}` on main — the FIRST fully-unconditional Rokhlin-leg instance. Leg binders all discharged: `hcoreG`, orientation, `D` (spin), `kron` (absolute UCT, N4), `hv2`/N6.
- [x] **E2 Rokhlin algebra — COMPLETE + kernel-pure** (Brown metabolic, Gauss sums, surgery reduction = KT-LMS Lemma 3.7, GM null-bordant case); `TaylorKernelVanishing` (Taylor Thm 1.1) refactored to the EXACT split `⟺ KernelIsotropic ∧ KernelSpinVanishing` (membrane-free), quarantining the pin⁻ spin bit from the intersection form (makes `nogo_lattice_arf_not_sigma8` explicit). Remaining E2 = the general-M char-surface geometry (realizability Props `ClassesEmbedded`/`KernelCirclesBound`).
- [x] **E3 (extension-carrier ℤ/16) · E5 (finite Adams ℤ/16)** — landed; the finite side of the alt-route (`adamsAbutmentEquivZMod16`, col4 height) done.

**⬜ INJECTIVITY / completeness — reduced to ONE geometric node (re-anchored, see line-39 banner):**
- [x] **Route unified:** Thom / KT §5 / Smith-LES / cardinality-cap all PROVABLY collapse to one apex node (`hbound` grade-0-injectivity); reduction is canonical (`5qH-injectivity-routes-...`, kernel-checked). Do NOT route-shop.
- [ ] **The deep input — `Ω₄^{Spin}≅ℤ` (GEOMETRIC surgery, NOT the ABP spectral tower):** via KT §5's from-below sequence `0→ℤ/2→Ω₄^{Pin⁺}→ℤ/8→0` (`ℤ/8=Ω₂^{Pin⁻}` DONE in-tree). The σ-route door (`SpinSigmaRouteDoor`) is assembled at finest grain; open inputs = **Freeze A** (`RealizesSphereProducts`, Benedetti handle-trading — the one genuinely Mathlib-absent step) + **Freeze B** (`SphereProductBounds`, the DiskManifold campaign: gap-1 atlas+charts+ChartedSpace+smoothness DONE/finishing, **gap-2 J5 re-association still needed**) + **K3 witness** (abstract σ=−16) + `hfwd`/`h2g` + `hexact` (= the completeness key). Finest-grain wall: `σ=0` spin ⟹ `n·H` (Milnor–Husemoller, formalizable lattice algebra) ⟹ `n(S²×S²)` ⟹ 3-handle bound.
- [~] **`smith_inflow_z16` (ABP spectral / `Ω₆^{Pin⁻}`) — DEMOTED to a wired ALTERNATIVE** (harder), NOT the required keystone. It ranks atlas-#1 only because the Smith-LES transport is what's currently wired.

> **⚠ KEYSTONE RE-ANCHORED (2026-07-06 — supersedes the §9.3/§380 "required non-elementary ABP tower" framing for the completeness input).** Direct read of Kirby–Taylor LMS-151 §5 (pp.216–218) established the injective direction closes via the **GEOMETRIC exact sequence** `0→ℤ/2→Ω₄^{Pin⁺}→ℤ/8→0` (`card≤16 = 2×8` from below); the deep input is **`Ω₄^{Spin}≅ℤ`** (+ KT Lemma 5.3 `÷32`), NOT the spectral `smith_inflow_z16`/`Ω₆^{Pin⁻}` ABP tower (DEMOTED to a wired alternative). The index invariant (α/ψ) is OFF the critical path. Sized bounded/elementary via Benedetti arXiv:1907.10297 Ch.20. Full correction: `16Convergence_Reconciliation_Audit_2026-07-04.md §0-B`, `SETTLED_FORKS.md` (`5qH-injectivity-routes-...`), exec-map §0, deliverable `Lit-Search/Phase-5qH/Omega4Spin_Z_formalization_route_20260706.md`. The `smith_inflow_z16` node below remains a VALID (harder) alternative route; both bottom out at manifold topology, so the σ÷16 (W1) E1 work above is on the critical path either way.

**⛔ Option A is SETTLED (operator DIRECT ruling 2026-07-04) — full unconditional discharge is the ONLY path; B / disclosed-form is a RETIRED phantom, do NOT re-open or re-debate (the coach's build-ruling is authoritative; memory `feedback-coach-go-signal-authoritative`).**

> Per-effort status + the live brick-by-brick FRONTIER lives in `docs/dev-loops/Phase5qH/LAB_NOTEBOOK_INDEX.md` (master) + `E1_SubstrateG_Topology/LAB_NOTEBOOK_INDEX.md`.

## 0. Why 5q.H exists (read first)

5q.G delivered a **hypothesis-free ℤ/16 on the project's tied Pin⁺ carrier**:
`RP4Unconditional.rp4_dataBordismTied_equiv_zmod16` — kernel-pure, zero binders, fullness witnessed
by a genuine geometric manifold (ℝP⁴, whose `wuW2 = 0` and `w₁⁴ = 1` are now theorems computed
through the from-scratch Smith double-cover tower). The 16-convergence no longer routes through any
posited carrier, landmark binder, or spectral abutment.

What it is **not yet** is the literature's theorem. Two deltas remain (user directive 2026-07-03:
"bundle the remaining work to literature grade unconditionality"):

- **Δ1 — Faithfulness/injectivity.** The 5q.G result is an isomorphism of the **grade quotient**
  (`DataBordismGrp(tied) ⧸ ker(abkTiedGrade) ≃+ ZMod 16`). The literature's theorem is an
  isomorphism of the **bordism group itself**: the invariant is injective — `ABK = 0 ⟹
  Pin⁺-null-bordant`. In-substrate that means producing **genuine structured 5-bordisms**
  (`IsDataBordant` = `∃ b : Bordism (I.prod (𝓡∂ 1)) …, Nonempty (ξ.Bor b …)` — a real witness, not
  algebra; verified at `TangentialDataBordism.lean:80`).
- **Δ2 — The structure and the invariant are data-borne.** The tied/faithful carriers certify
  Pin⁺-*admissibility* (the Wu criterion `w₂ = 0`, genuine) but carry the ℤ/16 grade as **data**
  constrained by geometry only through its w₁⁴-parity (tied) or the hGM relation at the generator
  (faithful). Literature grade requires the invariant **computed from the structure**: the
  Guillou–Marin/ABK construction — a quadratic enhancement on a characteristic surface — or the
  η-invariant. (Bundle-level principal-Pin⁺(4)-bundle structures are the *fully* classical form; §5
  fixes the GM-structure formalization as this phase's target form, with the bundle form recorded as
  an explicit interface caveat, not silently claimed.)

**The phase's single sentence:** replace the carried grade by a computed Guillou–Marin invariant on
a characteristic-surface-structured carrier, prove it bordism-invariant and surjective (ℝP⁴), and
prove it injective by an explicit bordism-construction toolkit — landing
`Omega4PinPlusGM ≃+ ZMod 16` with both halves geometric.

---

## 1. The directive (read every bootstrap/compaction)

Finish **literature-grade unconditionality**: a bordism-group isomorphism
`DataBordismGrp (pinPlusGMData) ≃+ ZMod 16` where (i) the carrier's structure data is the
Guillou–Marin characteristic-surface package (not a carried ℤ/16 tag), (ii) the map is the
**computed** ABK/Brown invariant, (iii) surjectivity is the ℝP⁴ witness, and (iv) **injectivity is
proven** — grade-0 classes are exhibited as null-bordant via constructed 5-bordisms. Recast Ω₅ and
`CommonOrigin.sixteen_convergence_*` on this carrier; retire the tied carrier to stepping-stone
status.

**Continue-vs-stop rule (inherited verbatim from 5q.G §1, locked):** legitimate stops are ONLY a
kernel-checked no-go or a genuine user-only decision. "Absent from Mathlib / no foothold / needs
upstream infra / multi-week" are NOT stops — absence is the work. Kernel-purity non-negotiable:
axioms exactly `{propext, Classical.choice, Quot.sound}`; **no new project-local `axiom` without
explicit user sign-off**; no `sorry`/`native_decide`/`maxHeartbeats` in proof bodies. A
genuinely-hard geometric input is carried as ONE disclosed tracked `Prop` (registry + discharge
plan), never an axiom — and §4-H6 pre-authorizes exactly which Props those may be.

**Anti-spiral rules (inherited from 5q.G):** no frozen CURRENT-STATE naming engines; live state
recomputed from git + notebook FRONTIER; no-gos typed by strength; the ⛔ register is read before
any impossibility reasoning.

---

## 2. Precise statement of the gap (vetted 2026-07-03, main @ `1c455781`)

**What exists (5q.G bedrock — do not rebuild):**

| Asset | Where | Status |
|---|---|---|
| `subHomConnecting_openDuality` (PD engine) | `SingularConnSquareCloseNC*` | zero-sorry, kernel-pure |
| `poincareDual4Mid_of_closed` / `poincareDual4Lo_of_closed` | `SingularPD4Instances.lean:104,194` | THEOREMS for closed charted 4-manifolds |
| `wuW2_eq_zero_iff` (Pin⁺ criterion `w₂=0 ↔ v₂=v₁²`) | `PoincareDualityWuFormula.lean:163` | on genuine PD |
| ℝP⁴ cohomology ring ≤ deg 4 (`xpow`, spans, cup powers) | `RP4CohomologyLadder/RP4CupLadder` | kernel-pure |
| Smith double-cover tower (chain+cochain SES/LES, δS) | `RP4Transfer/RP4SmithLES/RP4SmithCochain` | kernel-pure |
| Signed ℤ/4 AW-Leibniz + Bockstein-derivation + `Sq1_on_H1` | `SingularBocksteinLeibniz`, `SingularBockstein` | kernel-pure, **degree-generic** |
| `v₁ = x`, `v₂ = x²`, `μ(x⁴) = 1`, `μ(Sq¹x³) = 1` | `RP4WuAssembly/RP4BocksteinAssembly` | kernel-pure |
| `rp4_hcert`, `rp4_htie`, `rp4_dataBordismTied_equiv_zmod16` | `RP4Unconditional.lean` | THE 5q.G capstone |
| Faithful side: `abkFaithfulGrade_surjective`, `faithfulGenerator_hGM`, `faithfulGenerator_order16` | `PinPlusFaithfulData.lean` | kernel-pure |
| Genuine bordism relation (`IsDataBordant` = real structured `Bordism`, cylinder + reversal ops) | `TangentialDataBordism.lean:75-170` | the quotient is honest |
| Brown/ℤ4-quadratic algebra (partial) | `SKEFTHawking.Brown.Z4Quadratic` namespace | **audit in H1-a** |
| η-route asset (DIII-BdG → ℤ/16) | `NbReDIIIToPinPlusZ16` | reference point only |

**What does NOT exist (the deltas' concrete surface):**

- No `ker(abkTiedGrade) = ⊥` and none is possible for the *free* grade — **kernel-checked no-go**
  `synthetic-grade-ker-bot-nogo` (ℝP⁴ is a grade-0 free-carrier witness with no unoriented
  null-bordism). ⛔ NEVER re-derive; the fix is a *different carrier* (GM), not a better proof.
- No characteristic-surface machinery (no embedded-surface data type, no H₁-of-a-surface
  computations beyond what the Smith tower gives for ℝPⁿ, no quadratic-enhancement-on-H₁ layer
  wired to geometry).
- No relative PD / PD-with-boundary (needed for bordism-invariance of a computed GM invariant).
- No bordism-construction toolkit (no explicit surgeries, handle moves, or connected sums as
  `Bordism` witnesses; only cylinders + reversal + disjoint-union exist).
- No bundle-level Pin⁺ structures (and §5 scopes them OUT of this phase's DONE — recorded caveat).

---

## 3. Route decision (settled at open; re-litigating = lateral motion)

Three classical routes to Δ1+Δ2 were weighed at phase-open:

- **(α) GM/characteristic-surface route (Kirby–Taylor).** Invariant = Brown invariant of a ℤ/4
  quadratic enhancement on H₁(Σ;ℤ/2) for a characteristic surface Σ ⊂ M; injectivity by
  surgery/normal-form bordism constructions. **CHOSEN.** Rationale: (i) maximal reuse — PD, Wu, the
  Smith tower, `faithfulGenerator_hGM`, and the Brown algebra all feed it; (ii) its hard geometry
  (explicit bordisms) is *constructive* — the same build-from-scratch style that succeeded for
  ℝP⁴/the M-ladder; (iii) it produces paper-consumable intermediate theorems at every gate.
- **(β) ABP/AHSS spectral route.** Requires Thom spectra + stable-homotopy machinery with no
  substrate foothold. ⛔ Recorded in the settled-fork register as the irreducible spectral input —
  **not the primary route; revisit only on substrate shift** (e.g. a Mathlib bordism/spectra
  landing; the bump-watchlist from the 2026-07-03 Mathlib survey applies).
- **(γ) η-invariant/index route.** Needs Dirac operators + APS — further from the substrate than
  (α) by a wide margin. Reference-only.

**Carrier decision:** a new `pinPlusGMData : TangentialData` whose `Mfd s` is the **GM package**
(characteristic-surface datum + enhancement; §4-H3), with `Bor` = restriction of a bordism-level GM
package. The tied carrier remains in-tree as the wave-1..3 stepping stone; comparison homs in H5
subsume its ℤ/16 into the new one.

---

## 4. The gate plan (H1 → H7)

> **⚠ HISTORICAL vocabulary.** The H-gates are the *original* work breakdown, now **retired** — current work is tracked by **E1–E5** (see the execution map's *Naming* section for the H → E cross-walk + the Status checklist for present state). Read §4 for gate *rationale*; never state current status with H-numbers (`H3 ≠ E3`).

> Brick-count reference-class only (the 5q.G M-ladder = ~30 bricks / 3 waves). NO calendar
> estimates (`feedback_ignore_pm_estimates`). Each gate closes with the full wave mechanics of §7.

### H1 — Recon + classical-mechanism pinning *(gate: the lemma DAG is written down and vetted)*

- **H1-a (substrate audit, in-repo):** exact contents of `Brown.Z4Quadratic` (what of the
  enhancement/Brown-invariant algebra already exists); exact statement of `faithfulGenerator_hGM`
  (what "hGM" already encodes); the `Bordism`/`TangentialData.Bor` API surface (what a structured
  bordism can carry); how dimension-specific the Smith tower is (S⁴/ℝP⁴-pinned — assess
  re-instantiation at n = 2 for ℝP² vs genericization; **pre-decision: re-instantiate**, the tower
  is ~10 files and only H₁(ℝP²) + the ℝP² fundamental class are needed).
- **H1-b (deep research, Tier-2 dispatch — ALREADY FILED):**
  `Lit-Search/Tasks/submitted/Phase5qH_KirbyTaylor_ABK_injectivity_blueprint.md` — the exact
  Kirby–Taylor mechanism: normalization of the enhancement (ℤ/4-valued q with
  q(x+y) = q(x) + q(y) + 2·(x·y)), the precise characteristic condition for Pin⁺ in dim 4, the ABK
  normalization making ℝP⁴ ↦ ±1 ∈ ℤ/16, and — critically — the **injectivity proof skeleton as a
  minimal lemma DAG** (which surgeries, which normal forms, which explicit null-bordisms), plus the
  bordism-invariance argument's exact shape (the dual 3-manifold in the 5-bordism). H2 (algebra)
  does not block on this; H3+ statement-shapes do.
- **DONE:** audit note in the notebook + the DR blueprint incorporated + the H3/H4/H6 statement
  shapes frozen in this file (§4 amended in place, logged).

### H2 — Brown/ABK algebra layer *(gate: the ℤ/16-valued Brown machinery is complete, in vacuo)*

Pure algebra over `ZMod 2`/`ZMod 4`/`ZMod 8`/`ZMod 16` — no topology:
- ℤ/4 quadratic enhancements on a finite ℤ/2-inner-product space; orthogonal sum; the Brown
  invariant (Gauss-sum or combinatorial definition per H1-b's normalization); additivity
  `β(q₁ ⊕ q₂) = β(q₁) + β(q₂)`; the values on the rank-1 forms; invariance under isometry.
- The ℤ/16 bookkeeping for the 4-dim story (per H1-b: the GM congruence's `2β(q) + Σ·Σ` shape).
- Extends/absorbs `Brown.Z4Quadratic` (never duplicate — the 5q.G lesson `f7ad88ce`: **search
  before build**, `lean_local_search` + grep the namespace first).
- **Aristotle-eligible:** self-contained, ≤12-term, 4.28-portable targets — batch per push-118
  policy when ≥3 qualify (user first/last call on submissions).
- **DONE:** the enhancement→ℤ/8(→ℤ/16) invariant with additivity + rank-1 values, kernel-pure.

### H3 — GM data layer *(gate: the GM carrier exists; ℝP⁴ carries a canonical GM structure)*

- `CharSurfDatum (M)`: a 2-dim `SingularManifold` Σ, a map `ι : C(Σ, M)`, and the
  **characteristic condition** stated cohomologically (the ι-pushforward class is PD-dual to the
  H1-b-pinned characteristic class — the substrate's PD + `w1` machinery states this without
  embeddedness; *embeddedness itself is data we do not demand* — the condition set is exactly what
  the GM congruence proof needs, frozen after H1-b).
- The enhancement field: `q : H₁(Σ;ℤ/2) → ZMod 4` with the H1-b compatibility conditions (its
  geometric grounding — normal-bundle framing counts — enters as the datum's coherence conditions,
  not as new differential topology).
- `pinPlusGMData : TangentialData` assembling (w₂-admissibility cert from 5q.G) + `CharSurfDatum` +
  `q`, with `Bor` = bordism-level restriction (mirroring the tied datum's architecture — reuse
  `PinPlusTiedData`'s k-generic patterns).
- **The ℝP⁴ witness:** ℝP² ⊂ ℝP⁴ constructed equivariantly (S² ↪ S⁴ equatorial, quotient — the
  `RP4PointSet` machinery re-instantiated at n = 2 per H1-a); H₁(ℝP²;ℤ/2) ≅ ℤ/2 via the n = 2
  Smith tower; the canonical `q` with `q(gen) = ±1` (normalization per H1-b); the characteristic
  condition discharged by the 5q.G Wu computations (`v₁ = x` etc.).
- **DONE:** `pinPlusGMData` compiles; `rp4GMStr : GM-structure on rp4SM` is a theorem-backed
  instance; the n = 2 tower lands H₁(ℝP²).

### H4 — the computed invariant + bordism invariance *(gate: `abkGM` is a genuine bordism hom)*

- `abkGM : StrMfd (pinPlusGMData) → ZMod 16` **computed** from the datum via H2 (the GM
  congruence form; on ℝP⁴ it evaluates by H3's witness — no carried tag anywhere).
- **Descent to `DataBordismGrp (pinPlusGMData)`** — the phase's second-hardest brick: a structured
  bordism `(W, GM-package)` forces `abkGM(M₀,s₀) = abkGM(M₁,s₁)`. Architecture (two-layer, per the
  tied precedent): (i) the `Bor` field of `pinPlusGMData` is *defined* to carry the
  bordism-level characteristic data restricting to both ends (invariance-by-structure — this is
  what makes descent provable); (ii) the honest geometric content — that this `Bor` is *inhabited*
  for the bordisms the theory needs (cylinders ✓ by construction, reversal ✓, the H6 constructions
  each built WITH their GM packages) — lands per-construction, never as a blanket axiom.
  ⚠ **Disclosure discipline:** if (ii) forces a named residual for some construction class, it is
  ONE tracked Prop with a discharge plan (§1); the capstone's statement must surface it until
  discharged.
- Additivity: `abkGM(M₀ ⊔ M₁) = abkGM(M₀) + abkGM(M₁)` (H2 additivity + the ⊔-machinery from the
  5q.G F-ladder patterns).
- **DONE:** `abkGMGrade : DataBordismGrp (pinPlusGMData) →+ ZMod 16`, kernel-pure, with the
  computed-not-carried property visible in its definition chain.

### H5 — surjectivity + comparison *(gate: the GM ℤ/16 is full; the tied capstone is subsumed)*

- `abkGMGrade` hits a generator: the ℝP⁴ GM witness evaluates to an odd class (H2 rank-1 value +
  H3 witness) → order 16 → surjective (the 5q.G `dataBordismTied_quotient_equiv_zmod16_of_odd`
  pattern, re-proven on the GM carrier).
- Comparison hom `pinPlusGMData → pinPlusTiedData` (forget the surface, keep the parity) +
  `abkGMGrade`-vs-`abkTiedGrade` compatibility → the 5q.G capstone becomes a corollary and the
  tied carrier is formally a stepping stone.
- **DONE:** `abkGMGrade` surjective; comparison square commutes; both kernel-pure.

### H6 — INJECTIVITY *(gate: `ker abkGMGrade = ⊥` — the summit)*

The literature's hard half, sequenced to stay unconditional as long as possible and to
quarantine the genuinely hard geometry into named, pre-authorized tracked Props:

- **H6-a (reduction architecture, unconditional):** the Kirby–Taylor reduction restated
  in-substrate per H1-b's DAG: `abkGM = 0 ⟹ null-bordant` **given** a finite toolkit of
  construction Props. Target shape: `theorem gm_injectivity (T : BordismToolkit) : ker abkGMGrade = ⊥`
  where `BordismToolkit` bundles the named inputs (expected, per H1-b to confirm/correct:
  `SurgeryOnCircles` — 5-dim surgery bordisms killing π₁-classes with GM packages;
  `CharSurfNormalForm` — enhancement-preserving surface moves; `NormalFormNullBordism` — the
  explicit null-bordisms of the residual normal-form list). The reduction itself is
  quotient/algebra work in the substrate's comfort zone.
- **H6-b (toolkit discharge, one wave per Prop):** each toolkit Prop discharged by an **explicit
  construction** in the `Bordism` framework — the same set-level + charted style that built
  `RP4PointSet` from nothing. Cylinders/reversal/⊔ exist; mapping-cylinder and
  boundary-connected-sum constructions are the expected first bricks; surgery traces
  (`D² × S¹`-for-`S¹ × D²` swaps realized as explicit charted 5-manifolds) the hardest. **Each
  discharge wave gets its own DR check-in against the H1-b blueprint before building.**
- **H6-c (assembly):** `ker abkGMGrade = ⊥` unconditional; if any toolkit Prop remains
  undischarged at a wave boundary, the capstone ships in disclosed form
  (`gm_injectivity_of_toolkit`) with the register entry — **never** a silent downgrade, never an
  axiom.
- ⛔ **Standing bans inside H6:** no ABP/AHSS re-route (fork §3-β); no re-derivation of the
  free-grade no-go; no "this needs real surgery theory, defer" hypothesis-descoping — the toolkit
  Props ARE the controlled form of that difficulty.
- **DONE:** `ker abkGMGrade = ⊥` kernel-pure (or the disclosed-toolkit form with every remaining
  Prop named in the capstone signature and the register).

### H7 — capstone + integration *(gate: the literature-grade statement + full wave mechanics)*

- **`omega4PinPlusGM_equiv_zmod16 : DataBordismGrp (pinPlusGMData) ≃+ ZMod 16`** — injective +
  surjective, invariant computed, no quotient-by-kernel, no carried grade.
- Ω₅ ≅ ℤ/16 recast on the GM carrier (the 5q.G Ω₅ pattern); `CommonOrigin.sixteen_convergence_*`
  retargeted; the tied/faithful forms retained as corollaries with docstrings marking their
  stepping-stone status.
- **Interface caveat, stated not hidden:** the carrier's structures are GM packages
  (characteristic-surface + enhancement data), the Kirby–Taylor-equivalent formulation — NOT
  principal-Pin⁺(4)-bundle structures. The bundle-level equivalence is recorded as the *sole*
  remaining delta to the fully classical statement (a possible 5q.I; not scoped here).
- Paper impact: bundles citing the 16-convergence (D7 anchor list; `PAPER_DRAFT_MAPPING`) get a
  freshness pass; `bundle_source_freshness` will flag — follow `LATE_PHASE6_ABSORPTION_PROTOCOL`
  branches if any bundle is already drafted against the tied form.
- **DONE (phase):** all of H1–H7 merged to local main; fresh adversarial review 0-BLOCKER/0-MAJOR;
  `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps` exit 0; `validate.py` N/N; counts +
  inventory + notebook INDEX synced; NOTHING pushed.

---

## 5. Scope fences (what 5q.H does NOT claim)

1. **No bundle-level Pin⁺ structures.** The GM package is the target form (§3, §4-H7 caveat).
2. **No spectra/Thom machinery.** Fork §3-β stands.
3. **No smooth-category upgrade.** The carrier stays at the substrate's charted/topological
   regularity (`k`-generic where the tied datum was; the smooth interface remains the standing
   project-wide caveat, unchanged by this phase).
4. **No new axioms, period** — the H6 toolkit Props are tracked hypotheses with discharge plans,
   surfaced in statements until discharged (§1 policy; `feedback_axiom_sign_off_policy`).

---

## 6. Venue, mechanics, and process (inherited 5q.G discipline)

- **Venue:** worktree slots (`wt2` default; `mcp__lean-lsp-wt2__*`), solo for the tightly-coupled
  chains (H2→H5 is one chain; H6-b Props may genuinely branch → ≤2 `lean-worker` fan-out per the
  slot-concurrency rule). Commit GREEN increments on the slot branch; merge to LOCAL main per wave
  with the full gate; **never push**.
- **Wave mechanics per gate:** fresh-context adversarial review (0-BLOCKER/0-MAJOR) → merge →
  trusted rebuild → validate N/N → counts/inventory/INDEX sync. Identical to 5q.G G6.
- **Preemptive-strengthening discipline** (CLAUDE.md checklist) before every theorem statement;
  the post-wave ruthless review stays mandatory.
- **Search-before-build** (the `f7ad88ce` lesson): `lean_local_search` + namespace grep before any
  new lemma; the Brown/GM/hGM assets especially.
- **Friction catalog:** the 5q.G laws carry over (native-spelling twins at high type-index;
  hidx-before-hval under dependent motives; sum-spelled degrees for `rw [coboundary_cup]`-class
  lemmas; whole-goal `show` over ₗ/plain seams; `nth_rewrite` for rep-mixing).
- **Aristotle:** H2 algebra is the prime candidate pool (self-contained, 4.28-portable); batch at
  ≥3 qualifying targets; user first & last call; safe partial-submission + verify-then-graft only.
- **DR checkpoints:** H1-b before H3 statement-freeze; a per-Prop check-in before each H6-b wave.

---

## 7. Risk register (top 5, with mitigations)

| # | Risk | Mitigation |
|---|---|---|
| 1 | H6 toolkit constructions (surgery traces as explicit charted 5-manifolds) are the phase's summit and may stall | Quarantined as named Props from day one (H6-a lands unconditional-given-toolkit); per-Prop DR blueprints; disclosed-form capstone as the honest intermediate state |
| 2 | The characteristic condition/enhancement coherence is mis-stated (formalization drifts from Kirby–Taylor) | H1-b DR blueprint BEFORE H3 statement-freeze; the ℝP⁴ witness is the live cross-check (its ABK must come out ±1 generator) |
| 3 | Bordism-invariance descent hides the content in an uninhabited `Bor` | §4-H4's two-layer discipline: inhabitation proven per-construction; any residual = ONE tracked Prop surfaced in the capstone |
| 4 | Duplicate/parallel machinery (Brown, hGM, ℝP² tower) | H1-a audit first; search-before-build; the ⊔/F-ladder patterns reused not re-proven |
| 5 | Re-deriving settled no-gos (free-grade ker=⊥; spectral route) | ⛔ register read-first rule; both are named in this file (§2, §3) |

---

## 8. Immediate next actions (the H1 wave, in order)

1. Scaffold `Lit-Search/Phase-5qH/` notebook (goal-arm does this; INDEX seeded from this §4).
2. H1-a audit: `Brown.Z4Quadratic` contents; `faithfulGenerator_hGM` exact statement; `Bordism`/
   `Bor` API; Smith-tower n = 2 re-instantiation surface. Log to the notebook; amend §4-H2/H3
   statement shapes here if the audit contradicts them.
3. H1-b: the DR task is filed at
   `Lit-Search/Tasks/submitted/Phase5qH_KirbyTaylor_ABK_injectivity_blueprint.md` — **user
   completes asynchronously**; H2 proceeds meanwhile (it does not block).
4. Open the H2 wave on wt2.

---

## 9. Deep-Research Log — 2026-07-03 Tier-1 returns (BINDING AMENDMENTS to §3/§4)

H1-b was fulfilled at **Tier 1** same-day (two research-scout reports, filed):
`Lit-Search/Phase-5qH/GM_structure_ABK_invariant_normalizations_20260703.md` (report A) and
`Lit-Search/Phase-5qH/ABK_injectivity_routes_lemma_DAG_20260703.md` (report B). Four findings are
**binding** on the gate plan; where they conflict with the §3/§4 first drafts, THIS section wins.

**9.1 — The GM surface package computes only the MOD-8 part (amends H3/H4).** The
characteristic-surface data (Σ ⊣ w₁², Pin⁻ on Σ, enhancement q, Brown β) determines the Pin⁺
ℤ/16 invariant only mod 8 (the ∩w₁² Smith map is "two layers"; the {0,8}-kernel is invisible to
(Σ,q) — fake-ℝP⁴: 9 vs 1). Any (β, Σ·Σ)-only closed formula is even-valued. ⇒ **H4's `abkGM`
is re-scoped as the computed MOD-8 invariant** (`abkGM8 : … →+ ZMod 8`, honest and fully
geometric), and the ℤ/16 lives at the **H6 architecture level** (9.3) — the odd bit is carried by
the extension position in the Smith LES, not by a surface formula. The H4 gate line becomes:
`abkGM8` computed + bordism-invariant + compatible with the tied grade mod 8.

**9.2 — Category fork surfaced (amends H7 + Scope fences).** Topological (C⁰) Pin⁺ bordism in
dim 4 is ℤ/2⊕ℤ/8 (KS + Arf; generators E8, ℝP⁴ — KT-LMS §9 via Torres). **ℤ/16 is a
smooth-category statement.** The 5q.G tied result (data-carrier, k-generic, witness at k = 0) is
untouched; but H6/H7's literature-grade injectivity theorem must be stated at smooth regularity:
the capstone is targeted at the `k = ∞` instantiation of the carrier, with the smooth-instance
upgrades of the witnesses (ℝP⁴'s quotient charts are smooth — an instance-work brick, added to
H3) and smooth bordism constructions in H6-b. The k-generic statements remain wherever they hold;
the C⁰ fork (ℤ/2⊕ℤ/8 + KS) is recorded as a non-goal corollary-target, not silently conflated.

**9.3 — Injectivity route v2: the SMITH-LES architecture (amends H6; supersedes the §4-H6
toolkit sketch).**
> **⚠ CORRECTION (2026-07-04, from `ABK_injectivity_routes_lemma_DAG_20260703.md` §4 read directly).** The paragraph below's claim that the concentrated input "is itself a proven theorem with a published ELEMENTARY, spectra-free proof (Matsumoto)" is an **ERROR — it conflates two distinct inputs.** (1) Rokhlin's `16∣σ` (the GM base case `2β=F·F−σ` at `F=∅`) IS elementary (Matsumoto/[FK]) = `hyp:rokhlin_sigma_mod_16` — but it is the mod-16 *detection* base case, NOT the completeness. (2) The Smith-LES *injectivity/completeness* consumes ONE external stable ℤ/16 input (`Ω₆^{Pin⁻}≅ℤ/16` [ABP 1969] / `Ω₄^{Spin}≅ℤ` / Stolz η) = `smith_inflow_z16`, of which the report states *"the ℤ/16 never comes from below … no published route eliminates this … none of the whitelisted sources offers an elementary substitute."* So the completeness is **required and non-elementary (the ABP tower)** — see §10 Phase 2. Read the paragraph below as identifying the *detection* base case only; the completeness input is `smith_inflow_z16`, not `hyp:rokhlin_sigma_mod_16`.

The KT-LMS §5 surgery proof's internals are not reconstructible from
whitelisted sources; the published route with the smallest constructive load is the Smith-LES
route (HKT Thm 4.1 + Smith-paper App. A), whose geometric inputs are exactly three, each with an
explicit manifold-level model: (i) zero-locus of a transverse section of a line bundle (the
w₁-dual, iterated for w₁²); (ii) the sphere-bundle construction (surjectivity leg); (iii) the
interval-bundle gluing over a null-bordism of the Smith image (injectivity leg). **The
`BordismToolkit` of §4-H6 is re-specified as exactly these three constructions** (+ the descent
two-out-of-three lemma). This converges with our substrate: we have just built a from-scratch
Smith tower, and the LES-with-explicit-section discipline is the same muscle.
**The one concentrated input — WITH ITS DISCHARGE GATE (H8):** every published route factors
through ONE Rokhlin-class theorem — Rokhlin's 16∣σ (the KT-GM base case), equivalently the
neighboring-column ℤ/16 (Ω₆^{Pin⁻} [ABP 1969] or Ω₅^{Spin×±1ℤ/4}), equivalently Stolz's
η-completeness. This is a statement about WHERE the work lives, NOT about dischargeability:
the input is itself a proven theorem with a published ELEMENTARY, spectra-free proof
(Matsumoto, "An elementary proof of Rochlin's signature theorem and its extension by Guillou
and Marin", in the same À la recherche volume as GM — quadratic-form + explicit-geometry
arguments squarely in this substrate's demonstrated range). During H2–H7 it is carried as ONE
tracked Prop, identified with the PRE-EXISTING atlas keystone `hyp:rokhlin_sigma_mod_16`
(no new debt is minted; the existing registered node is made precise and load-minimal).
**H8 (full-discharge gate, IN the phase's DONE):** discharge the Prop by whichever of two
convergent routes is shorter at H8-open — (a) the live Phase 5q.B spectra-free Rokhlin → 16∣σ
workstream (signature calculus already complete there; tracker `Phase5qB_*`), or (b) direct
formalization of the Matsumoto elementary proof (fetch with the §9.5 batch; blueprint it via a
Tier-1 scout at H8-open). The phase closes 100%-unconditional; the disclosed-Prop capstone is
only the intermediate state between H7 and H8.

**9.4 — Conventions locked (amends H2/H3 statement shapes).** β-sign: adopt the KT convention
(`2β(F) = F·F − σ(M) mod 16`); note GL/FK use the opposite sign. ℝP⁴'s two Pin⁺ structures = ±1
∈ ℤ/16, exchanged by twisting with the orientation line (P′ = P ⊗ ε). ℝP²'s two enhancements
send the generator to 1, 3 ∈ ℤ/4 (β = ±1 ∈ ℤ/8). Enhancement axiom: q(x+y) = q(x)+q(y)+2(x·y)
with 2· : ℤ/2 ↪ ℤ/4. The mod-8/mod-16 interface: the defect map (a,b) ↦ −a+2b on ℤ⊕ℤ/8.
Known documentation traps: the Smith-paper Fig. 3(g) pin±-label swap.

**9.5 — Tier-2 residue (user action requested).** The scouts could not fetch (egress whitelist):
KT-LMS 151 pp. 177–242 and KT-CMH 65 (1990) 434–447 — public mirrors exist (Kirby's Berkeley
page; Ranicki's Edinburgh archive), plus Brown 1972 / GM 1977–86 / ABP 1969 / Stolz 1988. Please
drop PDFs into `Lit-Search/Phase-5qH/primary-sources/`; the KT-LMS §5–§6 + §9 text is the one
gap that blocks verifying the [KT-restated] locators and reading Thm 6.11/Rem 6.15
(characteristic bordism) directly. H2 (Brown algebra) and H1-a proceed regardless.
**UPDATE 2026-07-04:** the KT-LMS 151 PDF is now in-corpus (`Lit-Search/Phase-5qH/KirbyTaylor_PinStructures_LMS151.pdf`); §5 pp. 216–219 read directly — Lemma 5.3, the exact sequence `0→ℤ/2→Ω₄^{Pin⁺}→ℤ/8→0`, and `ψ(ℝP⁴,ℝP³)=+2` confirmed verbatim. Matsumoto (À la recherche vol.) still to fetch per §9.5.

---

## 10. Phase 1 & Phase 2 — wave breakdown to unconditional discharge (2026-07-04, main @ `df10209b`)

> **⚠ HISTORICAL vocabulary.** The P-waves are **superseded by the E1–E5 efforts** (cross-walk: P1.1≡E2, P1.2≡E3, P1.3≡E4, P2.1≡E5; E1 = the shared Substrate-G foundation these waves assumed). Read §10 for the crux + substrate *rationale*; track work by **E-number** (execution map). "Phase 1/Phase 2" ≡ "Substrate G / Substrate S".

**Current state (main `df10209b`, source-verified):** the tied GM carrier (`pinPlusGMTiedData`) is built; `abkGMTied16` is the computed grade; surjectivity (`abkGMTied16_surjective`) + the ℝP⁴ odd generator are proven; the quotient `carrier ⧸ ker ≃+ ZMod 16` (`dataBordismGMTied_quotient_equiv_zmod16`) is unconditional and kernel-pure. Injectivity is **route-unified** — Thom / KT §5 / Smith-LES / cardinality-cap all provably reduce to ONE node (`spin_range_ge_of_grade0_inj`'s `hbound` = grade-0 completeness), with the KT §5 ⊆-half (`spin_range_le_ker_reduce`), the Spin map `s := n·g8`, and `hs` (`g8_zmultiples_ker`) discharged in-tree. So **H1–H5 + H6-a are effectively on main**; what remains is the injectivity toolkit (H6-b/c), the genuine-carrier upgrade (Δ2), and the single-Prop discharge (H8).

The unconditional close is two phases, and **BOTH are from-scratch, Mathlib-absent substrate builds** (only the assembling *algebra* is in-tree — see the §10 Phase-1 CORRECTION banner + `16Convergence_Reconciliation_Audit_2026-07-04.md`): **Phase 1 = Substrate G** (elementary char-surface/cobordism geometry — the `gm` congruence + the geometric Smith map/exactness), **Phase 2 = Substrate S** (the non-elementary external ℤ/16 input `Ω₆^{Pin⁻}≅ℤ/16`/`Ω₄^{Spin}≅ℤ`). **Phase 2 is REQUIRED, not a contingency** (crux note below). Neither is "the tractable in-tree part"; the disclosed-form L3 (synthetic carrier, modulo the one Prop packaging G+S) is what is already done.

> **⛔ SUPERSEDED (2026-07-06 re-anchor — see the line-39 KEYSTONE banner; this note is retained for its (a)/(b) content only).** The crux note below concludes that input **(c)** — an external non-elementary ℤ/16 (`smith_inflow_z16` / ABP `Ω₆^{Pin⁻}`) — is REQUIRED. **That conclusion is OVERTURNED.** A later direct read of KT-LMS §5 (pp.216–218) established the injective close runs `0→ℤ/2→Ω₄^{Pin⁺}→ℤ/8→0` from below, so the deep input is **(b) `Ω₄^{Spin}≅ℤ` (GEOMETRIC surgery)** alone — **(c) is DEMOTED to a wired alternative, not required.** The "(c) required / no elementary substitute" verdict was scout-sourced about the SPECTRAL computations and was never verified for the `Ω₄^{Spin}` surgery route (`SETTLED_FORKS 5qH-injectivity-routes` UPDATE 2026-07-06/06b; exec-map §0). Read the (a)/(b) reduction below as valid; ignore the "(c) required" conclusion.
>
**Crux (2026-07-04, from the primary planning source `ABK_injectivity_routes_lemma_DAG_20260703.md` §4, read directly) — (c)-conclusion SUPERSEDED per the banner above.** The divisibility-vs-completeness question is **settled, not open**: ABK-injective on `Ω₄^{Pin⁺}` reduces to **(a)** Smith-LES exactness [in-tree buildable], **(b)** `Ω₄^{Spin}≅ℤ`, and **(c)** ONE external stable ℤ/16 input (`Ω₆^{Pin⁻}≅ℤ/16` [ABP 1969], or `Ω₅^{Spin×ℤ/4}≅ℤ/16`, or Stolz η-completeness). The report states verbatim: *"the ℤ/16 never comes from below,"* *"no published route in scope eliminates this input,"* *"none of the whitelisted sources offers an elementary substitute."* So **the completeness input (b)+(c) is REQUIRED and non-elementary — it is the ABP spectral computation (`smith_inflow_z16` / Leg-D), and Phase 2 is therefore REQUIRED, not a contingency.** Rokhlin's `16∣σ` (elementary, Matsumoto/[FK], `hyp:rokhlin_sigma_mod_16`) is the SEPARATE GM base case (`2β=F·F−σ mod 16` at `F=∅`) — necessary for the mod-16 *detection*, NOT the completeness. **§9.3's claim that the concentrated input has a "published ELEMENTARY, spectra-free proof (Matsumoto)" is an error — it conflated the elementary divisibility with the non-elementary ℤ/16 completeness; see §9.3 correction banner.**

### Phase 1 — geometric derivation (reduce to the one required completeness input)

> **⚠ CORRECTION (2026-07-04, from the goal-loop turn-1 audit + Taylor `0802.0111`/Klug `2011.12418`, read in full — see `temporary/working-docs/16Convergence_Reconciliation_Audit_2026-07-04.md`).** "Phase 1 = **in-tree**" (below) is WRONG. Only the *algebra* is in-tree (`GMrelation`, `SpinCharSurfaceData` carrying `gm`, the abstract `pinPlus_zmod16_of_smith_les` transport, `col4`). **Phase 1's actual remaining content is a from-scratch, Mathlib-absent GEOMETRIC substrate build** — the char-surface topology for the `gm` congruence (Rokhlin) and the geometric Smith map + two-sided exactness (`smithDataHom` in-tree is only the grade-transport *shortcut*; the genuine geometric map is unbuilt; `pinPlusGMData` does not exist). Needs tubular neighborhoods, normal framings, handle/surgery traces, Novikov additivity, even fillings — none in Mathlib. Spectra-free (elementary per Taylor/Klug/Matsumoto), but **not** in-tree algebra. So Phase 1 is a from-scratch substrate build too — NOT the tractable part; the "Phase 1 in-tree / Phase 2 tower" split is false.

The algebra is in-tree; the geometry is a from-scratch build. Endpoint: the injective capstone in disclosed form, conditional on exactly the one required completeness input (Phase 2).

- **Wave P1.1 — Rokhlin `16∣σ` / GM base case (elementary; independent, startable now).**
  - *Build:* van der Blij `8∣σ` (have, `RokhlinHMDischarge`) + the FK congruence at `F=∅` (spin ⟹ `σ/8` even) — the geometric factor-of-2; reuses `GMArfVanishing` / Brown (algebra half in-tree). This is the GM formula base case (KT Thm 6.3, `F=∅`), NOT the completeness.
  - *Deliver:* `hyp:rokhlin_sigma_mod_16` discharged in-tree → `SmoothSpinManifold4.topo` retired → genuine `16∣σ`, kernel-pure.

- **Wave P1.2 — Smith-LES injectivity architecture (H6-b/c).**
  - The three geometric constructions (report §3) as explicit `Bordism` witnesses on the carrier: (i) transverse line-bundle zero-locus (`w₁`-dual, iterated for `w₁²`); (ii) sphere-bundle (surjectivity leg); (iii) interval-bundle gluing over a Smith-image null-bordism (injectivity leg); + the descent two-out-of-three; + LES exactness (a).
  - *Deliver:* `ker abkGMGrade = ⊥` reduced to **exactly the one required completeness input (b)+(c)** — i.e. `omega4PinPlusGM_equiv_zmod16_of_smith_inflow`, kernel-pure, with `smith_inflow_z16` the single named Prop in the signature.

- **Wave P1.3 — genuine-carrier + smooth-instance upgrade (Δ2; §9.1/§9.2).**
  - `abkGM8` computed on the fully geometric GM carrier; smooth-instance (`k=∞`) witnesses; the tied carrier → stepping-stone.

**Phase 1 endpoint:** the injective capstone on the genuine GM carrier, kernel-pure, **conditional on the single required Prop `smith_inflow_z16`** (`Ω₆^{Pin⁻}≅ℤ/16` / `Ω₄^{Spin}≅ℤ`). Disclosed form — the honest intermediate; NOT yet unconditional.

### Phase 2 — the required completeness input (ABP / Leg-D / Phase 5q.D)

**Required, not conditional** (crux above). Discharge the external stable ℤ/16 input `smith_inflow_z16` (`Ω₆^{Pin⁻}≅ℤ/16`, ABP 1969, or the `Ω₄^{Spin}≅ℤ` / `Ω₅^{Spin×ℤ/4}≅ℤ/16` equivalent).

- **Wave P2.1 — the ABP spectral computation.**
  - The Phase 5q.D shelf-ready Adams/ABP plan on the built `Ext_{A(1)}` E₂ core (§2/§4 there): `Σ⁻¹MTPin⁺ ≃ MSpin∧MTO₁` (Freed–Hopkins), ABP splitting (7-connected in `t−s<8`), Adams collapse → the ℤ/16 abutment. No elementary substitute exists (report §2/§4).
  - **This is the substrate-shift frontier** — the coupled Mathlib/PhysLib pin-set bump (ADR-003 Decision #7 watchlist + `feedback-mathlib-physlib-bump-coupled-authorization`) is the genuine lever: a coherent pin-set shipping spin-bordism + a low-degree computation collapses this node; else build in-tree per 5q.D.
  - **Circularity guard:** ABP's low-degree input is Rokhlin-entangled (`spin_bordism_iso_Z.circularity_note`); the ABP computation must route through the Adams SS, never cite Rokhlin as its own proof.
  - *Deliver:* `smith_inflow_z16` discharged → Phase 1's disclosed capstone becomes `omega4PinPlusGM_equiv_zmod16`, 100% unconditional.
