# Phase 5q.E: the "16 convergence" — what a genuine common-origin proof would require

## Technical Roadmap — June 2026 (top-row EXECUTED 2026-06-14; bottom-row DEFERRED, trigger-gated)

*Created 2026-06-13. Governed by [ADR-003](../adrs/ADR-003-rokhlin-leg-discharge-and-deferred-topological-frontiers.md)
(same deferred-frontier framework as Leg C-geometric / Leg D). Status framing:
[`docs/SIXTEEN_CONVERGENCE_STATUS.md`](../SIXTEEN_CONVERGENCE_STATUS.md).*

**STATUS (2026-06-14): the buildable TOP-ROW shards are DONE, and the common-origin capstone is built
CONDITIONALLY (W5).** Phase 5q.E waves W1–W4 shipped every genuine, kernel-pure *algebraic shadow* of the four
facets; **W5 `CommonOrigin.lean` then assembled the actual common-origin theorem** (`sixteen_convergence_common_origin`)
— the four 16s as images of ONE genuine Pin⁺ bordism ℤ₁₆ under explicit maps, with Rokhlin and Kitaev reading it
identically pointwise — **conditional on the disclosed `SmithInflow` tracked input** (the Smith hom's ℤ₁₆-level
content; inhabited, NOT an axiom). See [§Landed algebraic shards](#landed-algebraic-shards-phase-5qe-waves--the-top-row-buildable-now-content).
**What remains DEFERRED** is now narrower: the *geometric* `Ω₅^{Spin-ℤ₄}` bordism group + geometric Smith map +
Dai–Freed functor (to discharge `SmithInflow` into an *unconditional* unification) — Mathlib-absent landmarks
(verified 2026-06-14, [§Mathlib status](#mathlib-status--verified-2026-06-14-semantic-search-not-grep)). The
convergence is now a **conditional genuine unification**, no longer a bare enumeration. The rest of this doc records
the remaining geometric plan **recorded, not re-derived**.*

---

## What this would prove (and what it would not)

**Goal.** Replace the current *enumeration* (`sixteen_convergence_full` — "the numeral 16 appears in four
contexts") with a kernel-verified **common-origin** statement: that the four 16s are images of **one ℤ₁₆
bordism invariant** under explicit maps. Concretely, the honest target is the **anomaly-inflow chain**:

> SM 16-fermion content (Spin(10) spinor) → its Dai–Freed global anomaly ∈ `Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆` →
> (Smith homomorphism) → the Pin⁺/spin-4-manifold ℤ₁₆ that Rokhlin and the Kitaev 16-fold way both read.

If proved, this would establish — within the project's emergent-substrate thesis — that **the SM matter content
is a topological selection rule of the emergent vacuum** (anomaly inflow from a ℤ₁₆-SPT substrate forces the
boundary fermion count), not a tunable input. This is the SymTFT picture made rigorous.

**What it would NOT establish (honest, load-bearing — keep in any paper):** a shared bordism invariant
**constrains, it does not derive**. It does not single out the SM (many theories share ℤ₁₆), says nothing about
gauge couplings/masses/mixings, and is a *classification* statement, not a dynamical mechanism. The value is
entirely in the **explicit maps**; absent them, "all the same 16" is coincidence-spotting (cf. the Arf-bridge
and Ext⁴=16 no-gos, `SIXTEEN_CONVERGENCE_STATUS.md` §4).

---

## What it would require (decomposition — all but the first are Mathlib-ABSENT)

| Brick | Needed for | In-repo today? |
|---|---|---|
| SM 16 = Spin(10) spinor; 16-fermion anomaly arithmetic | facet 1 ↔ 2 (algebraic half) | ✅ **W2 realized** (2026-06-14) — `Spin10Sixteen.lean`: branching `16→10⊕5̄⊕1` at dimension/assignment level + hypercharge & B−L Cartan consistency; plus `total_components_with_nu_R`, `z16_anomaly_*`. The spinor *module* + GEM bordism class remain cited-not-proved (bottom-row). |
| **Spin / Pin⁺ / Spin-ℤ₄ bordism groups** `Ω₄^{Pin⁺}≅ℤ₁₆`, `Ω₅^{Spin-ℤ₄}≅ℤ₁₆` as *computed* groups | facets 2,3,4 share one ℤ₁₆ | ⚠️ **skeleton only** — Phase 6r `PinBordism`/`PinPlusBordism4` ship `Omega4PinPlusBordism ≃+ ZMod 16` as a *substrate Quotient*; the genuine geometric bordism group is a tracked Prop (`IsKirbyTaylorPinPlusBordism`), Mathlib-absent |
| **Dai–Freed anomaly = bordism invariant** (anomaly-in-d = invertible-term-in-d+1) | facet 2 as a bordism class | ❌ absent — needs the η-invariant/APS + invertible-TQFT formalism (Phase 6o `APSEta` is a *substrate* η, not the Dai–Freed functor) |
| **The Smith homomorphism** `Ω_*^{Spin-ℤ₄} → Ω_{*−1}^{Pin⁺}` (the map tying SM-anomaly ℤ₁₆ to the Pin⁺ ℤ₁₆) | the actual identification facet 2 ↔ 3/4 | ❌ absent — never formalized in any prover |
| **KO-theory / ABS** doubling (Bott 8 → 16 via real/quaternionic spinor structure) | the *origin* of "8×2 = 16" | ❌ absent (the same KO/Adams stack as ADR-003 Leg D) |
| Rokhlin geometric factor (`Arf=0` on a characteristic surface) | facet 3 as bordism, not lattice | ❌ deferred — ADR-003 Phase-2 / Leg C-geometric (the lattice Arf route is a **no-go**, `RokhlinArfNoGo.lean`) |

So the load-bearing capstones — computed Pin⁺/Spin-ℤ₄ bordism groups, the Dai–Freed functor, and the Smith
homomorphism — are **bottom-row, tier-2** (no formalization blueprint in any proof assistant), the **same
frontier** ADR-003 already defers for Leg C/D. This is a "build a Mathlib landmark," not a days-task.

---

## Landed algebraic shards (Phase 5q.E waves — the top-row, buildable-now content)

These are the genuine, kernel-pure, falsifiable shards that advance the *enumeration →
explicit-finite-maps* gradient WITHOUT the absent capstones. They are the algebraic shadows;
each is honest that a shared ℤ₁₆ **constrains, does not derive**, and flags its wall.

| Wave | Module | What landed (genuine, non-vacuous) | Wall it stops at |
|---|---|---|---|
| **W1** (2026-06-13) | `KitaevSixteenFold.lean` | The Kitaev facet's ℤ₁₆ as an **explicit faithful central-charge character**: `c₋(ν)=ν/2`; `kitaevCentralCharge_faithful` (16 charges pairwise-distinct mod 8 ⇔ ν=μ — *the* 16-fold statement); `kitaev_eight_bosonic_phases` (index-8 bosonic sub-sector, the "8 doubled to 16" shadow); `sm_realizes_trivial_kitaev_class` (SM 16 Weyl→c=8→class 0 via `total_components_with_nu_R`); `rokhlin_forces_bosonic_boundary` (honest **conditional** Rokhlin→bosonic inflow). Supersedes the vacuous `Z16Classification` placeholders. | the index relation `c₋=σ/2` and the bulk-boundary map are *hypotheses*, not proved — the genuine identification needs the Smith homomorphism + computed bordism groups (bottom-row). |
| **W2** (2026-06-13/14) | `Spin10Sixteen.lean` | The facet-1↔facet-2 algebraic half: the Spin(10) Weyl-spinor branching `16 → 10 ⊕ 5̄ ⊕ 1` realized at dimension/assignment level. `su5dim` grounds `10,5,1` as even-exterior-power dims `C(5,2),C(5,4),C(5,0)`; `weyl_spinor_as_even_exterior` (`C(5,0)+C(5,2)+C(5,4)=2⁴`); Georgi–Glashow `su5Multiplet` is a verified partition (`su5_partition_exhaustive`); `su5_branching_{ten,fivebar,one}` (components/multiplet = irrep dim, falsified by any wrong assignment); `spinor16_decomposition` via `total_components_with_nu_R`. **(2026-06-14) embedding-consistency added**: `hypercharge_traceless_{ten,fivebar,total}` — `Σ Y·components = 0` per multiplet and over the full 16 (the traceless-generator condition = GUT charge quantization), grounded in the real `hyperchargeY` data; **+ B−L Cartan** (`c980f4bf`): `bMinusL_traceless_total` (=0 over the 16 ⇒ Spin(10) generator) and `bMinusL_su5_ten_trace` (=2 over the SU(5) `10` ⇒ NOT an SU(5) generator), identifying B−L as the SO(10)\SU(5) `U(1)` whose ℤ₄ remnant `X=5(B−L)−4Y` carries the ℤ₁₆ anomaly — the explicit facet-1↔facet-2 link. | constructing the Spin(10) spinor *module* / `SU(5) ⊂ Spin(10)` / the branching as a rep-theory theorem (CliffordAlgebra/spinGroup) is Mathlib-absent (generational). |
| **W3** (2026-06-13) | `SixteenConvergenceExplicit.lean` | The honest capstone (explicit maps, NOT unification): `sm_trivial_among_sixteen_distinct` (**constrains-not-derives** — SM is the trivial one of 16 *genuinely distinct* phases, via Kitaev faithfulness); `sm_count_trivializes_z16` (explicit facet-1→facet-4 composition: Spin(10) branching sum =16 is the integer whose Kitaev class is 0). | the bordism identification (Smith homomorphism + computed `Ω₄^{Pin⁺}/Ω₅^{Spin-ℤ₄}≅ℤ₁₆`) that would make "all the same 16" literal is Mathlib-absent. |
| **W4** (2026-06-14) | `AnomalyPhaseCharacter.lean` | The explicit **finite map**: the anomaly phase `e^{2πiν/16} ∈ μ₁₆` as a faithful character `ℤ₁₆ → μ₁₆`. NEW headline `anomalyPhase_eq_central_charge_phase` (anomaly phase `= e^{2πi·c₋/8}`, Vafa form at label level, backed by a `kitaevCentralCharge` call); `anomalyPhase_add` (homomorphism), `anomalyPhase_faithful` (16 distinct phases, μ₁₆-codomain form of W1 faithfulness), `sm_anomalyPhase_trivial` (SM at identity). | the **deep** Gauss-sum `p₊ = D·e^{2πic₋/8}` link to a concrete MTC is **native_decide-purity-blocked** — the repo's Ising `p₊=2ζ₁₆` (`WRTComputation.ising_gauss_sum_is_2zeta`) would give the ν=1 realization, but it carries `Lean.ofReduceBool`. A kernel-pure `QCyc16` Gauss-sum computation would unlock it. |
| **W5** (2026-06-14) | `CommonOrigin.lean` | **The actual common-origin capstone (E.5), CONDITIONAL.** The four 16s as images of ONE genuine ℤ₁₆ — the Pin⁺ bordism group `Omega4PinPlusBordism` (real `Quotient`, `≃+ ZMod 16`, `[RP⁴]` order *exactly* 16) — under explicit maps. `rokhlin_reads_kitaev` (**pointwise** `signatureMod16 ∘ smith ∘ kitaevClass = id` ⇒ Kitaev labels = Rokhlin signature classes, the SAME ℤ₁₆); `kitaev_generator_is_bordism_generator` (ν=1 ↦ `[RP⁴]`, non-vacuous heart); `sm_anomaly_trivial_in_bordism` + `rokhlin_k3_trivial` (SM/smooth-spin at the trivial class); `sm_spin10_count_trivial_in_bordism` (**facet-1** routed in — the Spin(10) `su5dim` count → anomaly → bordism, the chain from its start); `sixteen_convergence_common_origin` bundles all four facets. Conditional on the disclosed **`SmithInflow`** tracked hypothesis (the Smith hom's ℤ₁₆-level content; **inhabited** by `substrateSmithInflow`; **canonical/unique** by `smithInflow_smith_unique` ⇒ choice-free; NOT an axiom). Supersedes the bare `sixteen_convergence_full` enumeration. Still **constrains-not-derives**. Fresh-context adversarial review (fake-unification focus): PASS, "the legitimate opposite of the Arf-bridge failure mode." | the **geometric** Smith homomorphism + the `Ω₅^{Spin-ℤ₄}` bordism group + the Dai–Freed functor are Mathlib-absent — carried as the disclosed `SmithInflow` input (its ℤ₁₆ **iso-ness** cited-true, GEM 2018 / Wang 2024; the generator pin `1↦[RP⁴]` a canonical normalization convention). ⚠️ `SmithInflow` registry entry in `HYPOTHESIS_REGISTRY` is DEFERRED (concurrency: `constants.py` held by the parallel 6A agent); disclosed here + in the module meanwhile. |

Brick (iv) (SM-anomaly → SymTFT inflow) was assessed **already-covered**: `SymTFT/IsSMMatterTopologicalBoundary.lean`
ships `z16_class=16·N_f`, `sm_3gen_via_symtft`, the η-invariant vanishing, and the topological-boundary
witness. Adding more would be renaming; the modular ℤ/24 sector is correctly kept DISTINCT from the
Kitaev/anomaly ℤ/16 (no false bridge). The bottom-row brick table above (Spin/Pin⁺/Spin-ℤ₄ bordism
groups, Dai–Freed functor, Smith homomorphism, ABS/KO doubling, geometric Rokhlin Arf) is unchanged:
those remain Mathlib-absent walls.

---

## LOE + posture (per ADR-003 velocity rows)

- **Algebraic shards** (the Kitaev faithful character, the Spin(10) branching + Cartan consistency, the μ₁₆
  anomaly-phase character, the constrains-not-derives capstone): top-row — **DONE 2026-06-14** (W1–W4, §Landed
  shards). These are the *facets* with explicit maps, no longer a bare enumeration.
- **The connective tissue** (bordism groups as computed, Dai–Freed, Smith homomorphism, ABS doubling): bottom-row,
  Mathlib-absent, generational. This is where "all the same 16" actually lives, and it is exactly the remaining gap.

**Posture: top-row EXECUTED; bottom-row DEFER, trigger-gated** (identical to ADR-003 Leg C/D). The convergence is
now carried as a *formal enumeration with explicit per-facet maps* (W1–W4) + a *cited* literature connection for
the unification (GEM 2018; Wang 2024 Smith-homomorphism / string-bordism ℤ₂₄). Do **not** open the **bottom-row
capstones** absent the trigger.

## Mathlib status — verified 2026-06-14 (semantic search, not grep)

Confirming the walls are genuine and ordering them by approachability:
- **`Ω₄^{Pin⁺}`/`Ω₅^{Spin-ℤ₄}` computed bordism groups — ABSENT.** `leansearch "cobordism group … Z/16"` and
  `local_search "Bordism"` return only homotopy groups, `IsManifold`, and the project's own
  `SymTFT.BordismVanishes` predicate. No bordism *ring/group*. (Deepest wall; shared with ADR-003 Leg D.)
- **Smith homomorphism — ABSENT.** `loogle "Smith homomorphism"` → no results. Never formalized in any prover.
- **Dai–Freed anomaly functor — ABSENT** (η/APS substrate only; no invertible-TQFT functor).
- **`spinGroup` / `pinGroup` — PRESENT** (`Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup`, as Clifford-algebra
  groups, NOT bordism). ⟹ the **Spin(10) spinor-module** route (W2's wall) is the *most approachable* capstone:
  the Clifford/spin substrate exists, so constructing the irreducible 16 as a `spinGroup`-module and proving the
  `SU(5) ⊂ Spin(10)` branching as rep theory is "hard but has a foothold," unlike the bordism groups which have none.
- **An `Ω₅^{Spin-ℤ₄}` *substrate* (à la `Omega4PinPlusBordism`) is NOT cleanly buildable** — checked from first
  principles 2026-06-14 while trying to discharge `SmithInflow`. The Pin⁺ substrate is genuine because its invariant
  `signature : ℤ` is **ℤ-valued** with a `16 ∣ Δσ` quotient relation; the Ω₅ Dai–Freed invariant is **intrinsically
  ℤ₁₆** (η/16 mod 1) with no natural ℤ-lift, so a `Quotient`-by-equality substrate collapses to `ZMod 16` relabeled
  (**vacuous**). The `APSEta.wittenYonekuraToZ16` η-map is also a placeholder (`:= 0`). So the Ω₅ side of the chain
  is *genuinely* gated on the η-invariant / Dai–Freed geometry — it is NOT a thin-wrapper away. This is why W5's
  common origin carries the Ω₅↔Pin⁺ identification as the disclosed `SmithInflow` rather than two substrates.

## Re-trigger conditions

Activate this phase when **any** of:
1. **Mathlib/community ships computed spin-flavored bordism groups** (`Ω_*^{Spin}`, `Ω_*^{Pin⁺}`, Thom-spectrum
   homotopy) — watch `loogle "Spectrum"`, `loogle "Thom"`, `leanfinder "spin bordism group"`, and the `gh`
   master-tree `Geometry/Manifold/Bordism*` (Rothgang's `SingularManifold` brick already landed — see ADR-003).
   This is the **shared** trigger with ADR-003 Leg D.
2. **A publication demands the literal common-origin result** (e.g. a "topological selection rule for SM matter"
   claim that the project wants kernel-backed rather than cited).
3. **The project deliberately funds the bordism/KO stack** as a foundational Mathlib ambition (then Leg C/D and
   this phase share the substrate and should be sequenced together).

On trigger, the wave plan is: (E.1) computed `Ω₄^{Pin⁺}/Ω₅^{Spin-ℤ₄} ≅ ℤ₁₆` as genuine bordism groups (discharge
the Phase-6r tracked Prop); (E.2) the Dai–Freed anomaly functor + the SM anomaly as a class in it; (E.3) the
Smith homomorphism tying (E.2) to (E.1); (E.4) the Rokhlin/Kitaev readings of the same ℤ₁₆; (E.5) replace
`sixteen_convergence_full` with the common-origin theorem + retire the "enumeration-only" caveat. Each capstone is
trigger-individually gated; partial completion still strengthens the *enumeration → cited-connection → one-map*
gradient honestly.

**Status update (2026-06-14): E.4 + E.5 DONE conditionally; E.1 (Pin⁺ half) already present.** `W5
CommonOrigin.lean` ships the **conditional** common-origin theorem (`sixteen_convergence_common_origin`): the
four facets are images of ONE genuine Pin⁺ bordism ℤ₁₆ (`Omega4PinPlusBordism`, E.1 Pin⁺ half from Phase 6r)
under explicit maps, with Rokhlin and Kitaev reading it identically pointwise (E.4). E.5 is realized **modulo the
disclosed `SmithInflow` tracked input** (the E.2 Dai–Freed inflow + E.3 Smith hom at the ℤ₁₆ level; geometric
construction = the still-deferred bottom-row landmarks). The remaining *unconditional* work is exactly building
the geometric `Ω₅^{Spin-ℤ₄}` bordism group + the geometric Smith map + Dai–Freed functor to discharge `SmithInflow`
— the same Mathlib-landmark frontier. So the convergence is now a **conditional genuine unification**, not a bare
enumeration; only its geometric *inputs* remain trigger-gated.

---

## Honest endpoint

Even fully built, the result is: *"the SM matter content is the ℤ₁₆-anomaly boundary of the emergent vacuum, and
that ℤ₁₆ is the invariant Rokhlin and Kitaev read."* A **classification/consistency** statement — strong and
worth it, but it constrains rather than derives, and must never be stated as "we proved the SM" or "all four 16s
are the same" without the explicit maps in hand.

---

*Phase 5q.E roadmap. Created 2026-06-13. Governed by ADR-003. Status companion: `docs/SIXTEEN_CONVERGENCE_STATUS.md`.*
