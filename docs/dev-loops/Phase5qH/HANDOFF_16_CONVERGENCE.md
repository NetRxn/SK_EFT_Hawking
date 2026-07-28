# Phase 5q.H — The 16-Convergence: Overview & Handoff

**Written:** 2026-07-15. **Fully re-verified and rewritten 2026-07-27** (lead, directly in the
Lean — every claim below was read out of the tree, not carried forward from a prior revision).

**Ground state (refreshed 2026-07-28, SOLO — after the K3-ledger collapse / GM-ceiling / lattice
round):** main `1b935fab`. `lake build` → **exit 0, 10,348 jobs**; library-wide **24,967 theorems,
0 axioms, 0 sorry**. `nogo_substrate_integrity` **PASSED** at **41** kernel-encoded no-go forks
(was 38, +3 this round: two GM entries + the FK mod-2 membrane ceiling), verified against a **fresh**
extraction (`lake build ExtractDeps` + `update_counts.py`, never a hash delete). Counts drift again
after each commit — run `/skeft-qa:sync` before the next gate run. Full `validate.py` N/N last run
`20260728T033834Z` at **47/48**; the single failure (`proxy_body_audit`, an `Iff.rfl` tautology) was
fixed by BUILDING the substantive statement (`ae4f28b1`), not by registering it as debt, and that
check now passes standalone.
⛔ `rm -rf .lake/build` remains BANNED until after 16-convergence (operator; ~40 min, it is DONE-gate
(3), not an interim to-do).

⚠ **READ [Part 2.δ′](#part-2δ--state-delta-2026-07-28-solo--supersedes-2δ-read-first) FIRST.** It
supersedes 2.δ and **corrects a false claim carried in it** (the `StableNegRank16`
"elementary, not genus theory" characterization). Precedence: **INDEX FRONTIER > 2.δ′ > 2.δ > §2.1
onward.**

**This document:** part 1 is the big picture for anyone catching up cold; part 2 is the remaining
work in dependency order; part 3 is the binding architectural law set. The always-authoritative
*live* resume map is the **FRONTIER block** in [LAB_NOTEBOOK_INDEX.md](LAB_NOTEBOOK_INDEX.md) — if
this document and the INDEX disagree, **the INDEX wins**. Objective / constraints / gates /
verified-source index live in the durable roadmap
[`docs/roadmaps/Phase5qH_LiteratureGradeUnconditional_Roadmap.md`](../../roadmaps/Phase5qH_LiteratureGradeUnconditional_Roadmap.md).

---

## Part 1 — The big picture

### The goal

Formalize in Lean 4, fully **unconditionally**, the classical Kirby–Taylor result

> **Ω₄^{Pin⁺} ≅ ℤ/16**,

on a **faithful** carrier — a genuine bordism-of-manifolds substrate (T2 carrier, smooth `k ≥ 1`
data, structure-extension bordism relation with the Brown/ABK invariant *computed*, not posited) —
with the isomorphism injective and surjective, zero posits, kernel axiom set exactly
`{propext, Classical.choice, Quot.sound}`, no project-local `axiom` / `sorry` / `native_decide` /
`maxHeartbeats`, and every completeness Prop passed through a vacuity-attack gate *before* anything
consumes it.

### Why the carrier was the hard part

The original carrier collapsed in the 2026-07-13 **T2-collapse finding**: the old `DataBordismGrp`
was non-faithful — a degenerate (non-Hausdorff) "bordism" could relate anything to anything, making
the ℤ/16 statement vacuously satisfiable. Arm 3 rebuilt the substrate as a *gated* carrier; arm 4
drove it to its final form and decomposed the remaining mathematics into a gated leaf row. That
work is done and its lessons are kernel-encoded.

### The architecture (four interlocking pieces)

1. **The carrier** — `pinPlusCharPairData` over `CharPairBorRealizedTethered`
   (`PinPlusCharPairCarrier.lean`, `PinPlusCharPairBorTethered.lean`). The bordism relation is
   *realized and tethered*: every membrane comes with a closed embedding `ιW` into the bordism
   manifold `W` plus pointwise glue data — gate round 6 proved anything weaker lets a free membrane
   fake the relation. All 8 carrier ops run through a σ-threaded per-op provider
   (`CharPairWProviderPerOp`), which is **unconditional**. Gate round 7 passed this carrier.

2. **Surjectivity — DONE, unconditionally, in the SMOOTH category.**
   `charPairBrown_surjective_smooth` and `rp4_ne_zero_smooth`
   (`PinPlusKTAssemblyResiduals.lean` §R.1) off the real-analytic ℝP⁴ witness. No hypotheses.

3. **Injectivity / order 16 — the W-D decomposition**, following Kirby–Taylor §5. The minimal
   consumption unit is the gated triple `{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}` (rounds
   8–10 proved every 2-subset admits a degenerate model — it is triple-or-nothing). The assembly of
   record `kt_equiv_zmod16_of_two_leaves` (`PinPlusKTLeafGate.lean:463`) is **proven**.

4. **The provider + surgery foundation.** The cylinder `[W,∂W]` ladder is complete and the provider
   inhabits unconditionally. The surgery foundation supplies KRS's deep binder: a genuine
   rank-lowering tethered surgery-trace bordism.

### Status in one paragraph

**The theorem is proven as a sharp conditional; the phase is row-emptying plus one regularity
lift.** Waves **W-A** (faithful carrier), **W-B** (smooth surjectivity — unconditional at `k = ⊤`)
and **W-C** (computed invariant) are closed. **W-D**'s assembly is proven and its hypothesis row *is*
the remaining mathematics.

⚠ **W-E is NOT closed** (an earlier revision said "closed" — retracted). Every assembly variant ships
a `rokhlin_sixteen_…` twin, including at `k = ⊤`, so W-E fires *automatically the moment the row
empties* — but it inherits the row's hypotheses and is therefore exactly as conditional as W-D today.
**W-F** (the `k = ∞` capstone + Ω₅ recast) is untouched and is a genuinely new re-basing arc.

Since the 2026-07-27 rewrite the **entire S²×D³ / Freeze-B geometric coboundary lane closed** —
`hBbord` is no longer a lane — and that lane is now `k`-generic (§2.1). What remains is listed
atom-by-atom in part 2.

---

## Part 2.δ′ — STATE DELTA (2026-07-28, SOLO) — SUPERSEDES 2.δ; READ FIRST

⚠ **Freshness.** Current as of `1b935fab` (main; build 10,348 jobs; 24,967 theorems, **0 axioms,
0 sorry**). Precedence: **INDEX FRONTIER > this block > Part 2.δ > §2.1 onward.** Everything below
2.δ is accurate about *architecture* and stale about *status*.

⚠ **Mode: SOLO** (operator directive 2026-07-28 — orchestration was costing efficiency). No workers
in flight; all three slots idle at main. The delegation-policy block in the INDEX still applies if
fan-out resumes.

### ⛔ CORRECTION TO 2.δ — do not re-inherit its `StableNegRank16` characterization

2.δ says `StableNegRank16` "reduces to Wall's characteristic-vector transitivity ALONE — one open
leaf, **elementary (reflections only), not genus theory**." **That last clause is FALSE and was
inherited from a worker report without checking.** Compute the inertia: rank 18 with `σ = −16` gives
`(sigPos, sigNeg) = (1, 17)` — the Lorentzian `II_{1,17}`, which is *exactly* where Eichler's
criterion fails and where every published proof needs the spinor genus. This is kernel-checked as
`inertia_of_rank18_sig_neg16`.

That is why the brick was **restated at rank 20** as `StableNegRank16Two`, whose inertia is `(2,18)`
— `min ≥ 2`, so `2U` splits and Eichler applies. The rank-20 form is exactly as useful downstream.
(This error is the origin of PRE_DECISIONS item 5, "never inherit an estimate **or a
characterization**".)

### The row: `{hKRS, row, hA, hB, hcol, KTNonSplit}` — 6 binders

2.δ's row shape is stale: **`hker` dropped out** of the row entirely, and `{hcyc, h2}` collapsed
through `hΦg` to `KTNonSplit`. The row's five *fields* factor into exactly two deep lanes:
**`hdvd`** (Rokhlin — the atlas KEYSTONE, gating 11) and **`g`/`hrank`/`hk3`** (the K3 generator).

### ⭐ K3 LANE — the Gram congruence is GONE; ledger is `StableNegRank16Two` + ONE geometric datum

- `f5fcf065` routed the Gram obligation through the **lattice classification**. Keystone: Sylvester's
  law of inertia needs only an **ℝ**-invertible change of coordinates, so `latticeSig` transports
  from a merely **finite-index sublattice**. Hence 22 classes with Gram `⟨−2⟩¹⁶ ⊕ 3H` pin `σ = −16`
  on any rank-22 basis datum — a table of cup products; **no basis, no Kummer half-sums, no PD, no
  gluing-signature machinery**.
- `16c6e7e4` **merged `hpd` into `hfam`** (cap–cup adjunction turns 253 cup products into 253
  Kronecker pairings; the same family's cap-duals supply integral PD by spanning).
- `8bc19ac3` **DELETED `heven`** — stated as an *iff*, so it cannot relocate the obligation. The
  whole SpinWu / `w₂(K3) = 0` sub-lane is **retired**.
- ⛔ Anti-circularity fence still binding: `kummerK3_pdInput_of_gram` takes the Gram as hypothesis
  and is unusable on the route that produces it (`SETTLED_FORKS: k3-gram-must-not-use-pdInput-of-gram`).
  The live route is `nonempty_intPD_of_capSpan`, whose hypothesis list is
  `{Free/Finite ℤ H₂, Finite ℤ H², Projective ℤ (boundaries 1)}` + an equiv + a cap-spanning family —
  **no Gram, no `IntCongr`, no `k3Form`** (lead-verified in the Lean).
- ⛔ **LEDGER CORRECTION, and it goes the harder way:** the banked `3H` Gram
  (`KummerT4GramCross.interMatrix_t4_intCongr_torusFourForm`) lives on **T⁴ itself** — not descended
  to `Q = T⁴°/τ`, not on the weld, and an `IntCongr` rather than an equality. "3H is already banked"
  was FALSE as stated.
- **Open here:** the T⁴°→Q→weld descent of the 6 torus classes; `E_c · E_d = −2δ_{cd}` (ambient
  cap-dual data — the `−2` is the normal bundle's Euler number, invisible to `H₂(E;ℤ) ≅ ℤ`); and
  `StableNegRank16Two` (below).

### ⭐ ROKHLIN LANE (`hdvd`, the KEYSTONE) — the ceiling is now KNOWN, three no-gos machine-enforced

The wire *from* a general-σ Guillou–Marin relation *to* `16 ∣ σ` is **built**
(`sixteen_dvd_sig_of_gm_realization`); the sole gap is `hgm` at general σ. Every in-tree producer
proves only the null case. Three `KERNEL_NOGO_REGISTRY` entries now bound the design space:

1. `gm-triple-level-layer-is-decided-by-sigma-alone` — **this one corrects an earlier entry of mine.**
   I had recorded the empty-surface route as circular *because* its hypothesis is biconditional with
   `16 ∣ σ` at spin. `triple_layer_forcing` proves that criterion is **unsatisfiable**: every
   predicate on the invariant triple `(σ, F·F, 2β)` that follows from GM and suffices for Rokhlin at
   spin has exactly that property — **the true Guillou–Marin theorem included**. The correct test is
   **intensional**: what DATA the hypothesis is a predicate on. The practical ban stands (that datum
   *is* σ-arithmetic); only the justification changed. See the amendment at the head of the
   SETTLED_FORKS entry `gm-empty-surface-specialization-is-circular`.
2. `gm-pin-torsor-free-shadow-weaker-than-van-der-blij` — σ = 8 satisfies `8 ∣ σ` **and** the full
   torsor-invariant GM shadow, yet `¬(16 ∣ 8)`. The pin⁻-**free** content of `[FK]` has **zero**
   marginal content over the lattice bound already owned; the geometry must enter through `w`.
3. `fk-mod2-membrane-index-cannot-reach-nonorientable-stratum` — any `μ` satisfying the `[Q2]`
   refinement identity forces `B(v,v) = 0` (put `x = y = v`; `2μ(v) = 0` in `ZMod 2`), so a mod-2
   index reaches the **orientable stratum and kernel-checkably only that one**; refuted at
   `stdQuadratic 1`, the ℝP² half of the `(ℝP⁴,ℝP²)` generator. **Not fixable by more membrane
   work** — the obstruction is the polarization identity. Reaching the nonorientable stratum needs
   the GM **ℤ/4-resolution** index.
   ✅ **RESOLVED 2026-07-28 (`3e15199c`).** The split is now PINNED from the primary source, read
   directly by the lead: **Klug arXiv:2011.12418v3 §6 p. 18** (following Matsumoto / Guillou–Marin).
   ⚠ The earlier version of this line said **§2** — that was wrong; §2 is the *orientable* mod-2 case
   and Klug states the orientability assumption there explicitly. The split is
   **`e_F(x) = n(D) + 2(D·F) + 2 d(C)  (mod 4)`**, coefficients `1,2,2`, with the half-integrality in
   `n(D)` — the framing, counting right-handed **half**-twists — and **not** in a doubled `D·F`, so
   the shape this fence warned against guessing was indeed the wrong one. Two cross-checks against
   the source came back clean: Klug's `e(x+y) = e x + e y + 2(x·y)` **is** in-tree
   `Brown.Z4Quadratic.refine'`, and Klug Theorem 5 `σ = F·F + 2β(F) (mod 16)` **is** in-tree
   `GuillouMarinBridge.GMrelation` — the algebra layer needed no correction.
   Built: `GMZ4MembraneIndex.lean` (`Z4MembraneData`, `index_refine` **derives** the identity from
   the three additivity laws; `two_mul_q_self`/`q_self_reduce` give the sharp escape — the mod-2
   index term dies under polarization and forces `B v v = 0`, the ℤ/4 term survives as `2·q v` and
   what is forced is the *congruence* `q v ≡ B v v (mod 2)`; `orientable_framing_forces_alternating`
   shows a whole-twist framing re-imposes the obstruction, so the half-twists are load-bearing).
   Corpus: `Lit-Search/Phase-5qH/Klug-GuillouMarin-Z4-membrane-index-coefficient-split.md`.

Positive substrate that DID land: the three FK summands are built as genuine **constructions**
(`MembraneIndex.lean`), including the framing obstruction as a loop **degree** with additivity
proved — no `ZMod`-valued field, so the P5 repackaging trap is avoided. The pin⁻ enhancement torsor
is proved **simply transitive** (`shift_simply_transitive`, `nat_card_pin_enhancements = 2^rk H₁`);
both `CharSurfaceFKVacuity` §3 and the ceiling module had *assumed* this without proving it.

⚠ Carried, not acted on: `CharSurface.Membrane` hard-codes `𝓡∂ 2`, for which no in-tree inhabitant
is exhibitable (the project's disk asset is the **product** model). Verified it has no load-bearing
consumer outside its own file → a do-not-build-on-this note, not an active defect.

### ✅ LATTICE LANE — **CLOSED** (`80536c5d`) — `PlaneReductionDescent.lean`

`UnitCancellation` → `StableNegRank16Two` → the K3 Gram. wt1 reduced `UnitCancellation` to ONE
geometry-free statement, **`PlaneReduction`**; the safeguard is lead-verified (`planeStep_lift`
*proves* each arithmetic move is realised by an actual isometry, so the reduction target is not
hand-transcribed folklore). Built since:

- the move algebra + six closers (`65fc0d83`) — specialising one transvection parameter to `0`
  collapses the moves to clean elementary operations;
- **`planeReduction_of_axis`** (`c6d19bd7`) — the whole 4-parameter statement reduces to its
  `β = 0` axis;
- the two axis moves + **`planeReduction_axis_round`** (`456d532f`, `1404193f`) — one axis visit
  strictly drops `gcd(γ,δ)`;
- **the conserved quantity** (`f847b2d4`) — `N := αβ + γδ` is invariant under **all four** moves
  (it is half the norm of `w'`'s `U ⊕ U₁` component, so isometry-invariance forces it). Endpoint
  constraint: reaching `(0,0,γ',δ')` forces `γ'δ' = N`;
- **`descent_round`** + **`descent_to_axis`** (`21d4b23a`, `1b935fab`) — the descent side complete,
  with the gcd bound. The key observation: the `β`-reducing step leaves one plane-2 coordinate
  *completely alone*, so the post-round gcd **divides** it.

- **the REFUTATION of the divisibility strengthening** (`23c03116`) — the tempting
  `gcd(γ₂,δ₂) ∣ gcd(γ₁,δ₁)` between axis visits is **FALSE** (7 violations in 600 hard states;
  smallest `(5,0,24,30) ↦ [6,4]`, `4 ∤ 6`). The measure is an inequality, so the induction must
  carry a *bound*, not a divisibility chain. The "post-round gcd **divides** the untouched
  coordinate" reading above was the thing this refuted — kept for provenance, superseded.
- **`axisReturnBound` + the close** (`80536c5d`) — `PlaneReduction`, `UnitCancellation` and
  **`StableNegRank16Two` are now unconditional theorems** (`*_holds`), kernel-pure.

**The join's idea** (the whole obstacle, recorded because the shape of the fix is not the shape the
problem suggested): §5's descent bounds the returning axis gcd by `|β|`; §6's axis induction needs it
bounded by the *incoming* plane-2 coordinates; `m₃` rewrites `γ,δ` mod `β`, so no carried invariant
survives a round. The resolution is that **no carry is needed** — ONE round already drops `|β|` below
`B = max(|γ|,|δ|)` (in the `m₂` branch `β' = β % (γ%β)`, so `|β'| < γ%β ≤ γ ≤ B`; mirror in `m₁`),
after which §5's own bound suffices verbatim. The two-sided Euclid on `(gcd(α,β), gcd(γ,δ))` that the
open note called for was never needed and was not built.

**Downstream, same commit:** `KummerK3E1Unconditional.lean` drops `hstable` from every Kummer
consumer — `hk3_holds`, `kummerK3_hk3_holds`, and the four E1-atom entry points. The welded Kummer
K3's E1 residual ledger is now **ONE geometric datum** (`hgeo`), the lattice half being gone.

### Method note worth keeping
The axis measure was **tested before being formalised**, and the first test was worthless: a random
sweep showed 239 clean trials but every gcd sequence had length ≤ 2 — random tuples essentially never
reach the hard case. Constructing the hard case directly (400 axis states with `e ∤ α`) is what
actually validated it. Same pattern earlier: a brute-force `PlaneReduction` search "failed" on 19
tuples purely because the multiplier radius was 6 and `(6,10,15,0)` needs `q = 10`.

### The row (SUPERSEDED — kept for provenance): `{hKRS, row, hA, hcol, hker, hΦg}` + slot pin

| atom | movement this session |
|---|---|
| **`row`** (via `row.hg`) | **`orientInput` DISCHARGED**, and **Milnor–Husemoller II.4.3 is now UNCONDITIONAL** (`oddRank34Diagonalizable` is a bare theorem; use `odd_indefinite_intCongr_unconditional` downstream). **`StableNegRank16` now reduces to WALL'S CHARACTERISTIC-VECTOR TRANSITIVITY ALONE** — one open leaf, elementary (reflections only), not genus theory. Earlier: `nonempty_intOrientation_kummerK3_uncond` + `nontrivial_h4K3`, both binder-free, kernel-pure. K3 E1 triple now rests on **`hk3` alone** → which reduces to **`StableNegRank16`** → now gated on exactly TWO elementary inputs, **neither genus theory**: `OddRank34Diagonalizable` (ranks 3–4 only) and Wall's characteristic-vector transitivity. Milnor–Husemoller II.4.3 is BUILT (`odd_indefinite_unit_peel` unconditional; rank 2 constructive). |
| **`hA`** | **RE-SCOPED and BUILT.** The old Freeze-A atoms are **kernel-proven satisfiable with ZERO geometry** (registry `freeze-a-atoms-satisfiable-with-zero-geometry`) — `HandleTradeCobordism` is met by the unit cylinder. Replacement `BordantToSplitLocus` on a **faithful** presentation, where `rank q = m` is DERIVED from additivity rather than declared. Refutable by a nonzero `σ = 0` class; the old atom was unrefutable. |
| **`hker`** | Route fixed and typed. `gluesT2_iff_singleWitness` (registry): the single-witness extraction is **EQUIVALENT** to gluing — no shortcut exists. `refl`/`symm` unconditional ⟹ gluing is the SOLE missing equivalence law. **`SeamGlueChart` INHABITED** for mapping cylinders + empty seam; the transport engine means **only the `chart` field is hard**. Arc B needs **TWO** new `TangentialData` fields (not one) — visible already at the empty seam — both breaking changes, **unauthorized**. |
| **`hcol`** | Refined, **NOT** discharged (`RankZeroCollapseSupply` is an interface). Everything there is `k = 0`. B2 wall kernel-encoded: on a Wu-witness carrier no char-pair structure has empty surface, so the terminal move must change the carrier. |

### Two lane-level facts worth not relearning
- **`orientInput` is retired as a GATE, not settled as a PROPOSITION.** The 2-saturation statement is
  neither proved nor disproved; nothing consumes it.
- **The surgery trace is OUTSIDE `SeamGlueChart`'s domain** (welds along a proper subset, not a whole
  boundary component) — not blocked by a field. → `surgery-trace-is-not-a-seamglue-composition`.

### Binding disciplines added this session (tracked in `../PRE_DECISIONS.md`)
**Pre-dispatch target diligence** (vacuity-attack the target / carrier-not-model / survey alternatives
/ never inherit an estimate) · **"Mathlib lacks X" is COST, never CLOSURE** · **never grep for
`native_decide`/`sorry`/`axiom`** — use `#print axioms` + `lean_verify`.

### Non-goal work now sharing capacity (goal stays TOP priority)
`6E*` graphene/detector series authorized: roadmaps 6EA–6EE landed, bundle **D12** authorized, 6EA
Stage 2 frozen. ⚠ Build defect corrected there that applies repo-wide: **the root `SKEFTHawking.lean`
has no `globs`, so a module not imported there is NOT built by `lake build` at all** — every wave must
add its own root import.

## Part 2 — The remaining work, in dependency order

### 2.0 Environment checklist at resume (before any Lean work)

- If the machine rebooted since the last `sysctl`: re-apply `sudo sysctl -w kern.maxvnodes=786432`
  (reverts on reboot; the default 263k ceiling causes machine-wide ENFILE under parallel Lean).
- Run the CLAUDE.md session-start lean-lsp trim (kill off-repo `lean-lsp-mcp` servers).
- **3 worktree slots authorized** (`wt1/wt2/wt3`, operator-confirmed). `ulimit -n 65536`,
  `LEAN_NUM_THREADS=4`; serialize cold header imports; no lead full-library `lake build` while all
  three lanes are hot. Lake 5.0.0 has no `-j` flag.
- Workers **commit after their first green brick** and every ~3 after (committed work survives an
  agent death; uncommitted triage does not).
- The wt3 stash `stash@{0}` is old pre-5q.G material, deliberately preserved — do not pop or drop.

### 2.1 The two headline statements — and the gap between them

| | statement | carrier | row |
|---|---|---|---|
| **Refined (C⁰)** | `kt_equiv_zmod16_of_residuals_freezeAtoms_sphereDiskPinned` (`PinPlusKTSphereProdP23Close`) | `residualProv = residualProvK 0` | 7 atoms + one slot pin |
| **Smooth (k=⊤), coarse row** | `kt_equiv_zmod16_of_residuals_smooth` (`PinPlusKTAssemblyResiduals:166`) | `residualProvK ⊤` | the COARSE 8 atoms |
| Smooth (k=⊤), §7 | `kt_equiv_zmod16_smooth_sphereDiskPinned` + W-E twin `rokhlin_sixteen_smooth_sphereDiskPinned` (`PinPlusKTSphereProdP23Close` §7) | `residualProvK ⊤` | 8 binders — same COUNT as the coarse row, but `hB`→`hs2s2` (row-realization pin) and `H`→`KernelReducesToSpin` are both WEAKER |
| **⭐ Smooth (k=⊤), SHARPEST** | `kt_equiv_zmod16_smooth_phig_sphereDiskPinned` + W-E twin `rokhlin_sixteen_smooth_phig_sphereDiskPinned` (`PinPlusKTSphereProdP23Close` §8, `d1c9de12`) | `residualProvK ⊤` | **7** binders `{hKRS, row, hA, hcol, hker, hΦg}` + slot pin `hs2s2` — `{hcyc, h2}` collapsed to the single generator-image atom `hΦg` |

**The 8 → 7 shrink is kernel-checked, not asserted.** `kt_equiv_zmod16_of_residuals_ofKRS` (and the §7
sphere-disk form) are now *derived from* their §8 seven-binder counterparts by calling
`spinForgetPhi_g_eq_ktKernelRep_of_cyclic` — that call IS the arrow `{hcyc, h2} ⟹ hΦg`. Statements of
the pre-existing theorems are unchanged; only their proofs factor through the weaker-input form.
⚠ No converse is claimed anywhere: `hΦg` is *a* weaker input, not proven *strictly* weaker.
The k-generic backbone is `PinPlusKTAssemblyResiduals.kt_equiv_zmod16_of_residuals_ofKRS_phig`.

**The goal requires the smooth one.** Roadmap §2 leg 2 is a hard constraint: at `k = 0` the honest
group is topological Pin⁺ bordism `≅ ℤ/2 ⊕ ℤ/8`, the wrong group; the `IsManifold` binder at `k = 0`
is *free* (`PinPlusRegularityFence.isManifoldZero_free`).

**Regularity status (updated 2026-07-27 — the audit ran and the first tranche landed).** Kernel fork
`k0-to-k1-transport-refuted` forbids lifting: a smooth-category result must be **re-declared**
`k`-generically, never transported.

* ✅ **DONE (`c495abaf`, `ae0178e7`) — the S²×D³ coboundary lane is now `k`-generic.** The audit
  confirmed the substrate (`CharPairBorRealizedTethered`, `CharPairStrBundled`, `WAdmPinned`,
  `spinEmptyData`, `sphereProdCoboundaryBordism k`, `sphereDiskSmoothData k`) was **already**
  `k`-generic; the C⁰ pin was 7 declarations across 4 files plus one section-scoped `variable`, and
  **no proof body touched `k`**. Re-declared in place, so every `k = 0` call site still works by
  inference; `rfl` conservativity certificate landed. `hB : SphereProductBounds` is now *produced*
  from that geometry at every `k` rather than assumed.
* ⬜ **REMAINING — the `freezeAtoms` family** (`PinPlusKTFreezeDischarge`, `…_ofCoboundary`,
  `…_sphereDiskPinned`) still consumes `residualProv` (= `residualProvK 0`). Same shape of work.
  ⚠ Do **not** mass-edit its ~297 `residualProv` references: the k-generic backbone
  `kt_equiv_zmod16_of_residuals_ofKRS` already exists, so build on that instead (that is how
  `kt_equiv_zmod16_smooth_sphereDiskPinned` was obtained).
* ⚙ **Friction law (bought here):** when generalizing a parameter, grep the enclosing `section`'s
  `variable` line FIRST. A stale section binder presents as `(deterministic) timeout at isDefEq`, and
  `maxHeartbeats` is both banned and useless against it.

The one genuinely C⁰-tied input is a **smooth handle attachment for the surgery trace**
(`SurgeryFoundation.SmoothSurgeryChartDatum.ofC0` sets `k := 0`;
`SingularSurgeryChartsConcrete.ambientTraceBordism_concrete` builds the boundary embedding's
"smoothness" as continuity). It is on the KRS lane's critical path regardless.

### 2.2 The row — every remaining atom

Grouped by independent program. Nothing here is blocked on anything else in the table except where
stated, so all of it is fan-out-able.

**A · `H` — the KRS leaf.** ⚠ **STATUS 2026-07-27: BOTH obligations are now seam-local, and the
row alone is NOT a sound consumption target.**
* `hbd` → `qGen_boundary_mem_iff_forall_seamCore` (`…CollarPairSeamLocal.lean:275`), an `↔`.
* `hdetAB` → `hdetAB_iff_forall_seamCore` (`…CollarPairSeamDetect.lean:198`), an `↔`. `∂W` leaves
  the statement entirely; both obligations are indexed by `seamCore ⊆ ↥S` and nothing else.
  Entry point: `CollarPairCoreRow.ofSeamCoreLocal` (:236), strictly sharper than `ofSeamLocal`.
* ⛔ **THE VACUITY ATTACK NOW COMPLETES ON THE WHOLE ROW.**
  `nonempty_collarPairCoreRow_of_seamCore_empty` (`…SeamDetect.lean:283`): at `seamCore = ∅` the
  **entire two-obligation row is inhabited with ZERO geometric input**. Earlier rounds freed one
  obligation each; this frees both. So `CollarPairCoreRow.toHasClass` would fire on a row containing
  no geometry. **`hseamHit` as a side condition is therefore a PROVED NECESSITY, not advice** — any
  consumption of `H` must carry it. (No claim is made that `seamCore = ∅` is geometrically
  realizable; this is a scope/soundness fact about the interface.)
* ⛔ **STRUCTURAL NO-GO (kernel-checked, registry-eligible): both one-sided congruence routes are
  dead.** The engine layer advertises exactly one route (`SeamCollarChainDatum`: `qGen = p + e`,
  discard `e`, detect with `p`). At a core seam point: `cylPush_notMem_compl_seamPoint` (:342) — the
  pushed cylinder prism is supported at every seam point, so never the away-error `e`;
  `collarChain_ne_cylPush` (:424) — nor the collar chain `p`; `collarChain_ne_diskPush` (:449) — nor
  can the disk piece be `p`. ⟹ **the collar chain of any congruence-route discharge must be a
  genuinely THIRD chain.** Encode in `KERNEL_NOGO_REGISTRY` (Inv #17) — backings exist.
* New reusable engine: `crossChain_notMem_subspaceChains_compl_top` (:52) — the prism over a
  fundamental cycle is supported at every TOP-FACE point (companion to
  `fundCycle_notMem_subspaceChains_compl`).
* Remaining: produce `z`, `cHa` whose glued 5-chain has nonzero local class at every core seam
  point. `diskBoundary_notMem_compl_seamParam_of_hbd` (:512) sharpens the forcing to POINTWISE —
  `∂cHa` hits *every* core parameter — so the adapted-cycle residual is a **simultaneous**
  cancellation over the whole core. Honest next route (wt3's read, not started): the local
  Mayer–Vietoris at a seam point, which needs the local-homology bridge the project routes around.

*(Historical: the #212 collar-pair repair reduced this to exactly two obligations on
`CollarPairCoreRow`: **`hbd`** and **`hdetAB`**,
at the canonical `cHa := diskDetectChain` (`hcHa`/`hdetHa` fall to the banked
`diskDetectChain_hc`/`_hdet`). The chain to `hasClass` is complete
(`CollarPairCoreRow.toHasClass`, `PinPlusTraceCapstoneCollarPairMatch.lean:609`). **Do not build the
shared-`cCore` co-adaptation** — it is off-path (SETTLED_FORKS). Do not re-attempt `cSeam`
construction against the open-support transfer shape (fork
`seam-transfer-open-support-uninhabitable`).)*

**B · `row` — the σ-presentation.** Two genuinely separate contents hide here:

- **B1 · `hdvd : ∀ x, 16 ∣ R.sig x` — Rokhlin's theorem. This is the atlas KEYSTONE**
  (`hyp:rokhlin_sigma_mod_16`, gating impact 11 — the highest in the graph). Every in-tree producer
  is conditional: `CharSurfaceRokhlinAssembly.rokhlin_of_bounded_charSurface` needs the [FK]/GM
  congruence for the specific `M` plus the CharSurface tower's leaves
  (`KernelClassesEmbedded`, `KernelCirclesBound`, `MembraneSpinKill`, `KernelLagrangianForB`).
  Its irreducible factor is `2 ∣ σ/8`; `lattice_arf_bridge_refuted` proves it is **not** reachable
  from Arf — Rokhlin mod 16 is irreducibly geometric. Primary route: Matsumoto's elementary proof
  (blueprint `Lit-Search/Phase-5qH/Rokhlin_16_sigma_elementary_blueprint_20260703.md`; the
  À la recherche volume is an outstanding fetch).

  **SUPPLIER INVENTORY — lead-verified 2026-07-27 by grepping every `GMrelation` occurrence.**
  The wire *from* GM-at-general-σ *to* `16 ∣ σ` is **BUILT**
  (`sixteen_dvd_sig_of_gm_realization` :109 → `topo_of_bounded_charSurface` :125). What is missing is
  **exactly `hgm : GMrelation σ 0 C.Q` at general σ**: every in-tree producer proves only
  `GMrelation 0 0 C.Q`, the null-bordant/metabolic leg (`CharSurfaceMembrane` :343,
  `CharSurfaceBounding` :123, `CharSurfaceNormalShadow` :210/233/245, `CharSurfaceRealization` :199),
  each off a `Bounding` datum where `σ = 0` holds trivially. The tethered carrier does **not** supply
  it either — `CharPairStrBundled` has surf/emb/surfClass/basis/hpolar/hchar ties but **no field
  relating σ to the Brown invariant**. ⛔ And the empty-surface specialization is **CIRCULAR** (at
  `F = ∅`, `GMrelation σ 0 Q` degenerates to `16 ∣ σ` itself) — see SETTLED_FORKS
  `gm-empty-surface-specialization-is-circular`.
- **B2 · the K3 generator** (`g`, `hrank`, `hk3`). The Kummer program — far along. `KummerK3`
  exists as a genuine 16-fold welded carrier, is **smooth** (`isManifold_R4_kummerK3'`, any `k`),
  and **`kummerK3_b2_target_unconditional` (H₂(K3;ℤ) ≅ ℤ²²) is landed with no hypotheses**
  (`KummerChart1NbhdAcyclicInt.lean:893`).

  **⭐ STATE 2026-07-27 (late): the E1 residual ledger is down to ONE obligation.**
  `KummerK3E1FromGram.nonempty_kummerK3E1Atoms_of_gram` (:61) — all three of the original
  `KummerK3E1Residuals` (`KummerK3E1Package.lean:184`) are gone: `h1Free` is unconditional
  (`KummerK3SeamWindingParity.free_h1K3_uncond`, `H₁(K3;ℤ) = 0`), `orientInput` is **retired as a
  gate** (`KummerK3SeamTransport.nonempty_intOrientation_kummerK3_uncond` produces the `orient` field
  unconditionally by the degree-4 seam-kernel route — note it is retired, *not proved*), and
  `pdInput` is contained in the Gram. What remains is exactly the **K3 Gram congruence**
  `∀ o, ∃ C hC, IntCongr (reindex (interMatrix [K3]_o C)) k3Form`, then the K9 spin/`StrMfd`
  packaging.

  **The Gram converges on the K8b lattice lane.** `hk3_of_stable16_two`
  (`UnitBlockCancellation.lean:403`) delivers `IntCongr M k3Form` from `StableNegRank16Two` plus
  `IsEvenUnimodular M` and `latticeSig M = -16` on the rank-22 form. So B2's residual factors as
  (i) even-unimodularity — genuine integral PD on the welded carrier, ⛔ **NOT** via
  `kummerK3_pdInput_of_gram`, which takes the Gram as hypothesis (SETTLED_FORKS
  `k3-gram-must-not-use-pdInput-of-gram`); (ii) `σ(K3) = −16`; and (iii) `StableNegRank16Two`, whose
  sole residual is Eichler STEP 1.

  **State of the triple after the 2026-07-27 three-slot fan-out (`6a2cf2e2` + `1143d9fa`):**
  * `orientInput` — **still open; the whole degree-3 window around it is now pinned.**
    (State after the 2026-07-27 wt2 round, `KummerK3H3SeamWindow.lean`.)
    **THE residual, lossless (`↔`):** `kummerK3H3TwoTorsionFree_iff_qSeamCoord3_two_saturated`
    (:196) — `im qSeamCoord3` is 2-saturated in `H₃(Q;ℤ)`, where
    `qSeamCoord3 : (EIndex → ℤ) →ₗ[ℤ] H₃(Q;ℤ)` (:184). No `H₃(K3)`, no product summand, no abstract
    MV map: **sixteen boundary-ℝP³ classes in `H₃(Q;ℤ)`.** Its strongest form is *exactly*
    `H₃(K3;ℤ) = 0` (`qSeamCoord3_surjective_iff_h3K3_eq_zero`, :234 — vacuity attack run: it fails,
    the criterion is equivalent to an open computation, not discharge-for-free).
    Unconditional now (§4b): `H₄(qThick)⊕H₄(eImage) →Σ₄ H₄(K3) →∂₄ ℤ¹⁶ →qSeamCoord3 H₃(Q) ↠ H₃(K3) → 0`
    with `Σ₄` injective, so `ker qSeamCoord3 = im ∂₄` is pinned too. **The only uncomputed objects
    left in the degree-3 window are `H₃(Q;ℤ)` and `H₄(K3;ℤ)`.** New reusable brick: `projH_transferH`
    (:351), `p̄ ∘ t = 2`, dual to the existing `transferH_projH`.
    ⚠⚠ **CORRECTION to the 2026-07-27 (earlier) revision of this document, which said
    `thickA_H3_twoTorsionFree` gives "H₃(T⁴°;ℤ) 2-torsion-free at the punctured-torus level". That
    was IMPRECISE — lead-verified in the tree:** `thickA = (⋃ halfBall c)ᶜ`
    (`KummerPunctureBalls.lean:244`, HALF-radius balls) whereas
    `puncturedTorus = excisedBallsᶜ` (`KummerPuncturedTorus.lean:432`, FULL `excisionRadius` balls).
    They are complements of balls of **different radii**, hence different carriers, and
    `thickA_H3_twoTorsionFree` is NOT a statement about `PTtop`. So there are **TWO** gaps to the
    Q side, not one: `thickA → PTtop`, then `PTtop → Q`, and then the weld MV.
    ⚠ `T⁴° → Q` is still **not** a free transport (free ℤ/2 quotients *create* 2-torsion in general:
    H₁(S³)=0 but H₁(ℝP³)=ℤ/2). The only unconditional covering bridge is
    `two_smul_mem_range_mapInt_qmkC` (:382): `2·Hₙ₊₁(Q;ℤ) ⊆ im p_*`. Nothing claims descent. #309.

    **STATE 2026-07-27 (late) — reduced to TWO inputs, both named on banked maps.**
    `KummerQuotientTransferSequence.lean` landed the identification the previous round could only
    *name*: `qHmlEquivA n : Hₙ(Q;ℤ) ≅ Hₙ(A;ℤ)` with `inclAH ∘ qHmlEquivA = transferH` — the Smith
    norm subcomplex `A = N·C(T⁴°)` of the FREE double cover **is** the chain model for `Q`. Plus the
    full transfer exact sequence (`exact_deltaQ_transferH`, `exact_transferH_diffH`,
    `exact_inclAH_diffH`) and `deltaIII_four_bijective` / `deltaQ_three_injective`.
    ⟹ **`transferH_three_injective_iff_h5Q_eq_zero` (:297)** — given `h4PT : H₄(T⁴°;ℤ)=0` and
    `h5PT : H₅(T⁴°;ℤ)=0`, `transferH 3` is injective **iff `H₅(Q;ℤ) = 0`**. Composed with
    `KummerQuotientH3Descent.twoTorsionFree_iff_transferH_three_injective`, `orientInput` reduces to:
    **(1) three top-degree vanishings — `H₄(T⁴°)`, `H₅(T⁴°)`, `H₅(Q)` — and (2) even descent
    (`im p_* ⊆ 2·im qSeamCoord3`).** The wiring past both is already built and unconditional:
    `transferH_three_injective_of_top_vanishing` (:223), `twoTorsionFree_of_top_vanishing` (:230),
    `h3K3_eq_zero_of_top_vanishing_of_evenDescent` (:238),
    `nonempty_intOrientation_of_top_vanishing_of_evenDescent` (:247).
    ⚙ (1) is a *dimension* fact — `T⁴°` is an OPEN 4-manifold, `Q` its free quotient — and the
    project has run the analogous argument once already: `KummerRP3HomologyTop.lean` (`H₄(ℝP³) =
    H₅(ℝP³) = 0`, via `hml_s3_high` on the cover + the `trA`/`rHmlEquivAHml` Smith transport, with
    `KummerRP3GoodCoverTelescope` behind it). ⚠ "True by dimension" is a heuristic — the ℝP³ case
    needed a real good-cover/telescope argument; budget for that.
    ⚠ The Smith **transport** pattern (`trA`/`rHmlEquivAHml`) is NOT the fenced degree-3 Smith
    **walk** — different mechanism, and it is fine to use.
  * `h1Free` — ✅ **CLOSED, UNCONDITIONALLY** (2026-07-27, `KummerK3SeamWindingParity.lean`).
    `free_h1K3_uncond` (:577) : `Module.Free ℤ (Homology KummerK3top 1)` — **no hypotheses**
    (lead-verified: the signature carries no binders, `#print axioms` =
    `{propext, Classical.choice, Quot.sound}`). Also `h1K3_eq_zero_uncond` (:572),
    `qLatticeInSeamSpan` (:568), `seamClass_injective` (:564), `seamWindingOdd` (:561),
    `seamWindParityInjective` (:544) — all hypothesis-free.
    **The computation that did it:** `seamWind_odd_iff` (:518) —
    `¬ 2 ∣ seamWind c i ↔ coordC i c.1 = negOne`, i.e. **`seamWind c` IS the half-period bit
    vector**. An `↔`, so vacuity is structurally excluded (a `c`-constant substitute has uniform
    parity and fails it outright). Sharper than planned: `pull_tauC_wPT` (:183) gets the involution
    pullback at **cochain** level (`τ*(wPT i) = −wPT i − δ(aPT i)`), which upgrades "the winding
    parity is lift-independent" to the exact formula
    `windowJ[γ_c − γ_c' + v − τ_#v] i = seamWind c i − seamWind c' i + 2⟨wPT i, v⟩` — so the
    connecting path `δ` provably never has to be constructed.
    ⚙ Basepoint artifact worth knowing: at `basePt = (1,0)`, coordinate `0` gets the odd bit from
    winding `−1`/branch `0` and coordinates `≠ 0` from winding `0`/branch `1`. Both odd; the
    asymmetry is basepoint-dependent, the total is not.
    ⟹ **`KummerK3E1Residuals` is now a TWO-field obligation** — `orientInput` + `pdInput`.
    `kummerK3E1Residuals_of_orient_pd` (:605) and `nonempty_kummerK3E1Atoms_of_orient_pd` (:613)
    deliver the whole `orient`/`B`/`pd`/`rank22` atom quadruple from those two.
    *(Superseded route record, kept for provenance: the 2026-07-27 earlier round
    `KummerK3H1SeamLattice.lean` reduced the residual to `SeamWindingOdd`; that chain is what the
    closure fires through.)*
    **THE residual:** `SeamWindingOdd` (:322) — for `c ≠ c'` and ANY lift `y` of
    `seamClass c − seamClass c'`, some coordinate of the four puncture-window winding functionals
    `windowJ y` (:144) is odd. Choice-independent by `windowJ_sub_even_of_mapInt_qmkC_eq` (:296), so
    the `∀ y` is not a strengthening. Non-vacuous: refuted outright by any collapse of two seam
    classes, and the hypothesis is inhabited (`seam_diff_mem_range_qmk` proves a lift exists).
    Key new bricks: **`mapInt_qmkC_eq_zero_iff` (:276) — `ker p_* = 2·H₁(T⁴°;ℤ)` EXACTLY**;
    `tauStar_eq_neg` (:93) — `τ_* = −1` on `H₁(T⁴°;ℤ)`; `exact_inclBH_projH` (:265) — SES-III middle
    exactness, which the tree lacked; `qLatticeInSeamSpan_of_seamClass_injective` (:219) — the
    pigeonhole (16 distinct differences inside a set of size ≤ 2⁴).
    ⚙ **The scary part of the old discharge plan is provably unnecessary:** the connecting path `δ`
    drops out mod 2, so no explicit path in `T⁴°` need ever be constructed.
    ⚠ Honest scope: `Function.Injective seamClass` is proved SUFFICIENT for `QLatticeInSeamSpan`,
    not equivalent; the converse would need surjectivity of the puncture window
    `H₁(T⁴°;ℤ) → H₁(T⁴;ℤ)`, which is not in tree.
    ⚠ **Vacuity note (lead, still binding):** `QLatticeInSeamSpan` is **equivalent** to
    `seamSpan = ⊤` — a faithful re-expression in four explicit generators, **not** a strictly weaker
    hypothesis. Do not present it as a smaller assumption than the spanning fact.
    The geometry (independently lead-derived, then matched by the module): the seam at the fixed
    point of half-period `v` is `t_{2v}·σ`, so seam differences realize every class of `ℤ⁴/2ℤ⁴`.
    The 16 seams share deck-parity 1 — which is all `qDeck` sees — so **do not** conclude from the
    common parity that their images coincide; if they did, the cokernel would be `(ℤ/2)⁴ ≠ 0` and
    `π₁(K3) = 1` would fail. That contradiction is a useful wrong-turn detector.
  * `pdInput` — ✅ **COLLAPSED: it is NOT an independent residual.** (2026-07-27,
    `IntPoincareDualityDetCriterion.lean` + `KummerK3PoincareDuality.lean`.)
    **Lead-verified by reading the structure:** `IntPoincareDuality fc`
    (`IntersectionFormUnimodularInt.lean:89`) has exactly TWO fields — `toDualEquiv` and
    `toDualEquiv_apply` — so it asserts precisely that the *curried* form
    `interFormInt fc : H²(M;ℤ) →ₗ Dual ℤ (H²(M;ℤ))` is an iso; and
    `interMatrix_eq_toMatrix_interFormInt` (:85, **consumes no PD datum**) says the Gram IS that
    map's matrix. Hence `nonempty_intPoincareDuality_iff_isUnit_det` (:119):
    **`Nonempty (IntPoincareDuality fc) ↔ IsUnit (interMatrix fc B).det`** on any carrier holding an
    `IntH2Basis`. Since `IntCongr` and `Matrix.reindex` preserve determinants and `k3Form` is
    unimodular, **`intPoincareDualityOfIntCongr` (:134) derives PD from the `hk3` congruence the K10
    Gram span already has to prove.** At K3: `kummerK3_pdInput_of_gram`,
    `kummerK3E1Residuals_of_orient_gram`, `nonempty_kummerK3E1Atoms_of_orient_gram`.
    Also: `k3RealizingElement_of_gram` — the `pd` disclosure inside
    `PinPlusKTSpinSigmaStock.K3RealizingElement` is **redundant**; that structure already carries
    `hk3`. Non-vacuity anchor: `sphereProdIntPoincareDuality` discharges the datum **unconditionally
    at S²×S²** (`b₂ = 2`, hyperbolic) — a non-degenerate carrier where the disclosed PD is derived.
    ⚙ Unblocked by `h1Free`: `kummerK3H1Free` (instance) makes the whole H² side unconditional —
    `kummerK3CohomTwoEquivInt_uncond` (`H²(K3;ℤ) ≅ ℤ²²`), Free/Finite instances,
    `kummerK3BoundariesOneProjective`.
    ⚠ **Substrate-strength note (lead-confirmed, worth carrying):** the `IntPoincareDuality`
    docstring calls it "the community-scale integral-PD core" and says it is "equivalently the cap
    map `·⌢[M]` is an iso". The structure as defined is **exactly Gram unimodularity**; the cap-iso
    reading additionally needs the `H₂ ≅ Dual H²` identification. Those coincide when `H₂` is free
    f.g. (true for K3), so this is not a defect — but the datum is narrower than the docstring reads.
  ⚠ `KummerK7H1Window.h1K3_surjective_from_Q` gives H₁(K3) only as a surjective image of a free
  module — that does **not** give freeness.
  ⚠ State the Gram as `IntCongr … k3Form`, never a literal matrix equality on a chosen basis
  (SETTLED_FORKS, general rule); the 16 exceptional + 6 descended classes span a proper index-2⁸
  sublattice, so a "tabulate the 16+6 block" plan fails on determinant grounds.

**C · `hCob` + `hBase`** — the two Benedetti E1 surgery primitives. SETTLED
(`freeze-atoms-not-composable-from-sigma-trace`): they do **not** compose from the landed Σ-trace —
orthogonal axes (enhancement-rank vs b₂). They need a direct E1 surgery foundation
(Benedetti Ch. 20 handle trades); `HandleTradeSplit`/`HyperbolicPeel` statement layers exist.
Treat `{row, hCob, hBase, hΦg}` as ONE Benedetti cluster, not separate black boxes.

**D · `hcolD`** — the rank-0 → empty-Σ **membrane kill**. Proven a different construction from the
rank-lowering trace (which stops AT rank 0, `ambientSurgeryDatum_pos_rank`). Landed: B0 Wu-sector
split, the B1 interface (`PinPlusKTRankZeroBounding.lean`), B4 (`TauMembraneWeldDatum.ofRankZero`).
Remaining: B5/B6 thin assembly, then the two deep fronts — **B1-inhabitation** (WuNullCarrier ⟹
embedded bounding Q) and **B2** (`TerminalCharacteristicExtensionDatum`).
⚠ The one-sphere/3-handle collapse is UNSOUND without a framing theorem (SETTLED_FORKS); the
winning construction is the global KT characteristic-bordism route.

**E · `hker`** — `KerPhiSubDoubles`, the **w₁-dual spin submanifold**. ⛔ **BOTH previously-named
routes are now KERNEL-REFUTED (2026-07-27). An earlier revision of this document named
`KTSharpnessSupply` via `kerPhiSubDoubles_of_row_of_supplyGeo` as "its true route" — that claim is
RETRACTED.**

* **Fork 32 `hker-opener-supplyGeo-is-non-reducing`** (backing
  `PinPlusKTHkerAmbPinGate.nonempty_ktSharpnessSupplyGeo_iff_hfwd`): the consumed supply is
  **equivalent** to the `hfwd` conclusion, so `kerPhiSubDoubles_of_row_of_supplyGeo` — true as a
  theorem — reduces nothing. **Never dispatch "inhabit `KTSharpnessSupplyGeo`" at any depth.**
* **Fork 31 `hker-ambient-pin-does-not-restore-geometry`** (backings
  `nonempty_dualSpinFromW_iff_thirtytwo_dvd`, `dualSpinFamily_iff_pointwise_thirtytwo_dvd`,
  `isClosedEmbedding_empty`): the natural repair — pinning `amb` to the genuine tethered `b.W` per
  round-12 spec 1 — buys **nothing**; the conclusion-equivalence holds at every Hausdorff ambient and
  at an arbitrary ambient *family*.

**ROOT CAUSE (structural, deeper than the round-12 `amb` note):** `SmoothSpinManifold4`
(`SpinRokhlinInterface.lean:62`) is **pure lattice data** (`rank`/`form`/`even_unimod`/`topo`) with
**no underlying space**. So in `DualSpinFromW` the topological half (`Vspace`/`ιV`/`hclosed`) and the
arithmetic half (`Vspin`/`hdouble`) are **disconnected by construction** — the empty submanifold
closed-embeds into any T2 `W` while `spinOfSigMul16` supplies the lattice.

**⟹ THE ONLY REMAINING ROUTE:** a **NEW interface that carries the submanifold and DERIVES its
intersection lattice** (the `SpinSigmaAtomPkg` pattern — fundamental class + `H²` basis + Poincaré
duality on an actual manifold), **plus the `w₁`-duality tie**; then the smooth transversality
(Mathlib-absent). Nothing built over `SmoothSpinManifold4` + a bare embedded `Vspace` can work —
that is kernel-checked, not opinion. Also **not** the σ/Novikov tower, which is kernel-settled
ORPHANED (`sigma-tower-ORPHANED-not-on-16-convergence-critical-path`; do not revive it).

**STATUS 2026-07-27 (lead, `c1142672`) — half of that route is BUILT.**
`PinPlusKTDualSpinDerived.DualSpinDerivedFromW` is the derived-lattice interface: `Vspace` now carries
the full closed-4-manifold instance block (`T2` / `CompactSpace` / `Nonempty` / `ChartedSpace
(EuclideanSpace ℝ (Fin 4))`), and `rank` / `form` are **computed** as `interMatrix` of `V`'s own `H²`
basis against its own fundamental class, not supplied. Kernel-checked consequences:

* `abs_sig_le_two_mul_rank` : `|σ(M)| ≤ 2·b₂(V)` (Sylvester). No statement of this shape exists for
  `DualSpinFromW`, whose `Vspin.rank` is free.
* `derived_excludes_fork31_witness_class` : at `σ = 32m`, `m ≠ 0`, the refuted interface **is**
  inhabited (banked) while **no** derived datum has a trivial-`H²` carrier — the exact witness class
  behind fork 31 is excluded.
* `rank_ge_sixteen_at_sig_neg_thirtytwo` : at the forced kernel element `2[g]` (`σ = −32`), a derived
  datum needs `b₂(V) ≥ 16` — K3-strength, `norm_num`-backed.
* `toDualSpinFromW` : total forward compatibility, so every existing consumer is unchanged.

⚠ **This does NOT discharge `hker`, and the module says so.** The remaining half is the **`w₁`-duality
tie**: the only `V`–`W` relation is still `hclosed : IsClosedEmbedding ιV`, which constrains `V`
inside `W` but does not say *which class* `V` represents — so a putative inhabiter could in principle
supply a free-floating spin 4-manifold of signature `σ(M)/2` and never use `W`'s geometry. **That
sketch is a prose ROUTE CAUTION, not a kernel-checked no-go** — proving it needs a realization
construction (a closed 4-manifold with an `IntPoincareDuality` datum of every signature in `16ℤ`)
this project does not have, so per Invariant #17 it stays out of `KERNEL_NOGO_REGISTRY`. Do not cite
it as settled. **The next brick is the `w₁`-duality field, stated as an actual cohomological identity
on `W` (`[V]` PD to `w₁(W)`) — never as a bare `Prop`**, which would reintroduce exactly the free
field the derived interface was built to eliminate. In-tree substrate: the relative Lefschetz–Wu /
`[W,∂W]` tower already used by the capstone lane. ⚠ Scoping note (lead, assessed against the tree
2026-07-27): the honest form needs a class `τ_V ∈ H¹(W;ℤ/2)` **realized from `ιV`** (Thom class of
`V`'s normal bundle), then `τ_V = w₁(W)`. The Wu-class pattern (`PoincareDualityWu.wuClass2` /
`wuClass1` / `wuClassW1` — characterize the class as the PD-representative of a functional via
`pairing_bijective`, defining relation as a theorem) is the right *statement* template and is
genuinely non-vacuous; the *realization* of `τ_V` is not in tree. This is a multi-brick arc — scope
an opener before dispatching. Alternatives assessed and rejected as heavier: "`W ∖ V` orientable"
(5-manifold orientability), mod-2 intersection number with loops (transversality).

**⟹ ROOT CONSOLIDATION (lead, 2026-07-27): the `amb` pin, the single-witness extraction, and the
`w₁` tie all sit downstream of ONE absent thing — bordism GLUING.** This is not a new discovery; it
is already written at `PinPlusKTDualSpinSubmanifold.lean:38–48` and is recorded here so the three
residuals stop being tracked as independent. From `hx : spinForgetPhi prov x = 0` one can only reach
`EqvGen (IsT2DataBordant) …` (`Quot.exact` on `Quot (IsT2DataBordant)`, `T2TangentialBordism.lean:69`);
collapsing that to a single `IsT2DataBordant` needs **transitivity of the bordism relation**, which is
**ABSENT BY DESIGN** (`BordismGroup.lean` §4: "`Quot (IsBordant)` — no transitivity/gluing needed").
There is no `Equivalence (IsT2DataBordant ξ)` in tree (verified by search: zero refl/symm/trans
lemmas). Consequences, in order:
* no gluing ⟹ no single-witness extraction ⟹ `amb` **must** be carried as a field ⟹ item (1) is not
  a wiring fix but a request for the gluing theorem;
* with `amb` free, `V` cannot be a function of `W`, which is also what makes the `w₁` tie load-bearing.
**Open strategic call for a future turn** (not decided here): whether to invest in
`Equivalence (IsT2DataBordant ξ)` — refl = cylinder, symm = reversal, **trans = collar-gluing** —
which would unblock the `amb` pin and the extraction together. The project does hold relevant
machinery (`SmoothWeld`, the collar stack, `addBorRealized`/`negBorRealized`), so this is *not*
obviously infeasible; but transitivity is the hard leg and it was deliberately designed around.
⚠ Do NOT record "gluing is impossible" — nothing kernel-checked says that; it says only that the
current construction avoids needing it.

**F · `hΦg`** — `spinForgetPhi[g] = k₀`. Not independent: derived from `hker` + `hcyc` + `h2` once
`row` exists (`spinForgetPhi_g_eq_ktKernelRep_of_cyclic`). `hcyc`/`h2` were shown non-independent —
h2 outright-discharge IS the ÷32 conclusion (circular), and the ℤ/8 quotient does not force
`2·k₀ = 0`.

**G · `hs2s2`** — `(row.R.s2s2).1 = sphereProdSM4 0`, a slot pin, not geometry. Falls out when the
row is built concretely.

### 2.3 Convergence, after the row

- **W-E** fires automatically — every assembly variant carries its `rokhlin_sixteen_…` twin.
- **W-F**: the `k = ∞` capstone statement + the Ω₅ / `CommonOrigin.sixteen_convergence_*` recast is
  a genuinely new re-basing arc (verified: the 5q.G capstones live on separate carriers — this is
  not wiring).
- **Closure gates**: `rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps` clean →
  `validate.py` N/N → a fresh-context `skeft-qa:adversarial-reviewer` with zero BLOCKER findings →
  `/skeft-qa:sync` + counts → notebook + memory close-out. **Never push.**
- **Gate discipline stands**: any NEW completeness / bounding Prop gets a vacuity-attack round
  before its discharge is consumed; the binding specs live in the `PinPlusResidualGate.lean`
  (round 12) and `PinPlusRoundThirteenGate.lean` (round 13) headers; consume the assembly ONLY
  through the audited variant chain.

---

## Part 3 — Binding architectural laws (do not relearn these)

Violating any of these reproduces a known multi-hour wall.

- **Folded-def / abstract-D discipline:** never unfold concrete cylinder boundary sets inside
  detection equations (the whnf wall class — 2M-heartbeat loops). Keep `D` abstract; state detection
  via the folded definitions.
- **The implicit-`TopCat` `isDefEq` wall:** calls taking `{X : TopCat}` implicitly (`homProjInt`,
  `homIncl`, `connectingInt`, `ambIncl`, `excisionEquivInt`, `seamHomologyEquivInt`,
  `Homology.mapInt_ambIncl`, the `exact_*` family) MUST be written `(X := …)`. Unpinned they unfold
  the `RelHomologyInt` instances into a 200k-heartbeat `isDefEq` wall. Diagnostic: *"(deterministic)
  timeout at isDefEq"* on a one-line `LinearMap.comp` def. This is an ELABORATION wall — the
  "heartbeat ⟹ decompose" rule does not apply and `maxHeartbeats` is the wrong fix (and banned).
- **Carrier-metavar traps:** never type-ascribe TopCat coercions; use explicit `(X := …)`/`(N := …)`;
  composed `ChartedSpace.comp` instances need an explicit `letI`.
- **The three-opacity-state split** for quotient-coercion walls (the `αU ≠ 0` mechanism): route
  through `relCycleToHom`, keep `crossChain` opaque, characterize `boundaryExtract` once via
  chainIncl-injectivity.
- **Sealed-wrapper spelling** (`bdW`/`cylBdW`) — use the sealed names, never re-derive.
- **σ-threading:** provider fields take `CharPairStrBundled` (bare-`s` fields are uninhabitable).
- **Root-aggregator registration:** every merge must verify new modules are imported in
  `lean/SKEFTHawking.lean` (this defect has recurred repeatedly; a job-count jump on registration is
  the tell).
- **Gram targets** are stated as `IntCongr … <form>`, never a literal matrix equality on a chosen
  basis — the extra content is basis normalization, not geometry, and is generically unreachable
  whenever a basis vector comes from a choice.
- **`lean_local_search` returning one hit is NOT a reference check** — it does not surface namespaced
  members. Use `lean_references` or read the module. A direction-shifting claim ("dead", "orphaned",
  "nothing consumes X") must be traced in code, never grep-and-concluded.
- **Proof-mechanics laws** (bought expensively): predicate sets (`{‖v‖=1}`) never
  `ModelWithCorners.boundary`; `.choose`-hide concrete points; package acyclicity/connecting
  arguments abstract in `X` and instantiate late; extract heavy structure data to NAMED defs
  (iota-projection never whnf's a tactic-proof field); an unresolved identifier / missing `open`
  masquerades as a whnf timeout — check name resolution FIRST; `lean_multi_attempt` is NOT a reliable
  heartbeat signal (trust `lake build`); raw `Submodule.Quotient.mk` statements are `rfl` — bridge
  with `show`/`rfl`, never `rw`; `lean_verify` rejects non-ASCII decl names and lexically flags the
  word "opaque" even in prose; the authoritative axiom check is a fresh `lake env lean`
  `#print axioms`.
- **Never re-enter a registry fork** — 32 kernel-encoded forks / 77 aliases in `KERNEL_NOGO_REGISTRY` + 40
  `SETTLED_FORKS.md` prose entries, surfaced by `/skeft-qa:frontier` (negative frontier). Name the
  relevant forks in every worker brief; a fresh worker is the highest-risk re-deriver.

---

## Part 4 — Where the ground truth lives

| What | Where |
|---|---|
| Live resume map (authoritative) | the FRONTIER block in [LAB_NOTEBOOK_INDEX.md](LAB_NOTEBOOK_INDEX.md) |
| Objective, constraints, verdicts, gates, sources | [the durable roadmap](../../roadmaps/Phase5qH_LiteratureGradeUnconditional_Roadmap.md) |
| Per-brick history | [LAB_NOTEBOOK.md](LAB_NOTEBOOK.md) + `LAB_NOTEBOOK_W*.md` shards |
| Machine truth of open / settled nodes | the atlas — `/skeft-qa:frontier`, both fronts |
| Kernel-checked impossibilities | `KERNEL_NOGO_REGISTRY` (`src/core/constants.py`) → `lean/SKEFTHawking/KernelNoGos.lean`; prose in `docs/dev-loops/SETTLED_FORKS.md` |
| Gate-round records | `PinPlusCharPairFlipGate/TetherGate`, `PinPlusKTSectorGate`, `PinPlusKTStepGate`, `PinPlusKTLeafGate`, `PinPlusResidualGate`, `PinPlusRoundThirteenGate` |
| The assembly of record | `kt_equiv_zmod16_of_two_leaves` (`PinPlusKTLeafGate.lean:463`) |
| Cross-session memory | `project_5qH_nonhausdorff_substrate_bug.md` |
