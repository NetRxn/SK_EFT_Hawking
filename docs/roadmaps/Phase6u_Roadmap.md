# Phase 6u: Generic-Alphabet Solovay–Kitaev Substrate

## Technical Roadmap — May 2026

*Prepared 2026-05-23 PM, following Phase 6t close (Path A Option C kernel-verified quantitative SK length bound for Fibonacci anyons; commits `5eaa861` + `0ec1522`).*

**Trigger condition:** Phase 6t shipped a kernel-verified quantitative Solovay–Kitaev length bound (`solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight`) for the **specific** Fibonacci-anyon braid representation `ρ_Fib_SU2 : BraidGroup 3 → Matrix (Fin 2) (Fin 2) ℂ`. The Lie-algebraic substrate underneath (BCH cubic bound, V_n unitarity √2 factor, Y_h Lipschitz π/2 tightening, super-quadratic recursion engine, level-to-error map `skLevel_polylog`, length closed-form `skLength`) is **representation-agnostic at the SU(2) level** but is currently bolted to Fibonacci-specific generators (σ_Fib_1, σ_Fib_2), Fibonacci-specific closure (H_Fib), and Fibonacci-specific ε₀-net (`fibonacciEpsilonNet`).

Phase 6u parametrizes the substrate over the generating alphabet so that additional alphabets (Clifford+T, trapped-ion Mølmer–Sørensen, Clifford+CCZ, higher SU(2)_k Read–Rezayi anyons) can be instantiated on the same Lie-algebraic core without re-deriving the BCH / Y_h / recursion-engine layers.

**Headline goal:** ship a `SolovayKitaevGenericSU2` substrate that takes any generating set `G : Finset SU(2)` with proven closure-density and an ε₀-net witness, and produces the bundled-strict quantitative compilation theorem **mechanically**. Instantiate the parametric substrate at Clifford+T as the canonical second example to validate the refactor.

**Predecessor:** Phase 6t Path A Option C (`docs/roadmaps/Phase6t_Roadmap.md`). Phase 6u is **strictly substrate-side**: a Mathlib-upstream-PR-quality public substrate for generic-alphabet quantitative Solovay–Kitaev compilation. Vendor-specific tuning, cert formats, and engagement scoping are out of scope for this roadmap.

**Project rule applied:** No new project-local axioms (Pipeline Invariant #15 RESPECTED). No `maxHeartbeats` overrides in proof bodies (Invariant #10). Tracked-Prop posture for any closure-density hypothesis that requires alphabet-specific algebraic-number-theoretic argument beyond Mathlib4 v4.29.1 — explicit user sign-off gate per Invariant #15.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY PHASE 6u WAVE WORK:**
>
> 1. **Mandatory project bootstrap** per workspace `CLAUDE.md` Mandatory References list.
> 2. **Read `Phase6t_Roadmap.md` end-to-end** — Phase 6u's parametrization treats Phase 6t's Fibonacci ship as the canonical first instance; the wave structure mirrors Phase 6t Wave 1 through Wave 8.
> 3. **Read this roadmap end-to-end** before any wave-level claim.
> 4. **Critical substrate — read source directly:**
>    - **Dawson–Nielsen 2006** (`arXiv:quant-ph/0505030`) — exponent `c = log 5 / log(3/2) ≈ 3.9694` and the super-quadratic recursion.
>    - **Kliuchnikov–Maslov–Mosca 2013** (`arXiv:1206.5236`) — exact synthesis over Clifford+T (the substrate that gridcert's Ross-Selinger compilation builds on; relevant for Phase 6u Wave 2's closure-density witness).
>    - **Boykin–Mor–Pulver–Roychowdhury–Vatan 1999** (`arXiv:quant-ph/9906054`) — the canonical proof that ⟨H, T⟩ closure is dense in SU(2) modulo global phase.
>    - **Phase 6t landscape scan** at `Lit-Search/Phase-6t/Phase 6t Solovay-Kitaev Formal-Verification Landscape Scan.md` — confirms no prior kernel-verified quantitative SK formalization across Lean/Coq/Agda/Isabelle/HOL4/Metamath/Rocq.
> 5. **Do not delegate Lean theorem proving to subagents.** MCP loop default; Aristotle is fallback.
> 6. **No PM / time estimates anywhere** — by user direction.
> 7. **Pivot rule:** if a Wave's closure-density witness for a target alphabet requires a tracked Prop (e.g., a non-cyclotomic-eigenvalue argument that cannot be discharged constructively in Mathlib4 v4.29.1), YIELD for user sign-off per Pipeline Invariant #15. Do NOT ship a project-local axiom.

---

## Wave catalog — Shape D (Linear substrate refactor + 4 alphabet instantiations)

Six primary substrate waves, plus four alphabet-instantiation tracks. The substrate waves (W1-W6) generalize Phase 6t's Fibonacci-specific modules; the alphabet tracks (T-S, T-A1, T-A2, T-B) instantiate the generic substrate at one alphabet each.

**Status legend:**
- ✅ **SHIPPED** — Lean / numerical deliverables committed and kernel-verified.
- 🟡 **IN-PROGRESS** — partial deliverables shipped.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft only.
- ⏳ **NOT STARTED**.

| Wave | Codename | Status | Bundle absorption |
|---|---|---|---|
| **Wave 1** | Parametrize `H_Fib` → `H_of_G : Subgroup ↥SU(2)` over a generic `GeneratingSet` (W, ρ_hom, gens) | ✅ SHIPPED 2026-05-25 | D4 §9.6 |
| **Wave 2** | Abstract closure-dense witness `ClosureDenseWitness gs` + `H_of_G_eq_top_of_witness` + `IsDenseInSU2_gs` + Fibonacci instance | ✅ SHIPPED 2026-05-25 | D4 §9.6 |
| **Wave 3** | Generic ε₀-net `epsilonNet_findNearest gs h_dense U ε₀` via existential extraction + correctness lemma + Fibonacci validation | ✅ SHIPPED 2026-05-25 | D4 §9.6 |
| **Wave 4a** | Generic recursion engine `skApproxC_generic gs baseFinder` + `dnStepFG_su2` (alphabet-agnostic) + Fibonacci-instance discharge via Phase 6t bridge | ✅ SHIPPED 2026-05-25 | D4 §9.7 |
| **Wave 4b** | Generic discharge of `SkApproxCSuperQuadraticBound_generic K_compose gs baseFinder` — alphabet-agnostic super-quadratic bound (~800-1000 LoC port of Phase 6t Path A Option C) | 🟡 IN-PROGRESS (Wave 4a Fibonacci bridge unconditional; substantive generic discharge tracked) | D4 §9.7 |
| **Wave 5** | Generic length bound at `skLevel_polylog ε` — alphabet-independent re-export of existing `skLength_at_skLevel_polylog_le` | ✅ SHIPPED 2026-05-25 | D4 §9.7 |
| **Wave 6** | Generic bundled-strict headline `solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight` + Fibonacci unconditional validation | ✅ SHIPPED 2026-05-25 | D4 §9.7 |
| **Track T-S (Tier S)** | Instantiate at Clifford+T (`G = {H, T, S}` ⊂ SU(2), dense closure per Boykin et al. 1999): T-S.1 generating set + T-S.2 closure-density witness + T-S.3 ε₀-net + T-S.4 calibration + T-S.5 headline | ⏳ NOT STARTED (depends on Wave 4b) | D4 §9.8 |
| **Track T-A1 (Tier A)** | Instantiate at trapped-ion native gate set (Mølmer-Sørensen MS(θ) discretized at some grid + arbitrary 1Q rotations) | ⏳ NOT STARTED | (was "likely Phase 6v"; **Phase 6v scope finalized 2026-05-25 does NOT include this track** — re-slot to Phase 6x or later) |
| **Track T-A2 (Tier A)** | Instantiate at Clifford+CCZ for 3-qubit primitives (target group SU(8) not SU(2); substantial substrate extension) | ⏳ NOT STARTED | **RE-SLOT NEEDED 2026-05-25:** Phase 6w now claimed for Tindall/Sels + Aalto material per strategy synthesis D-8. Re-slot to Phase 6x or later. |
| **Track T-B (Tier B)** | Instantiate at Read-Rezayi SU(2)_k for k ∈ {5, 7} (next universal anyons beyond Fibonacci) | ⏳ NOT STARTED | **RE-SLOT NEEDED 2026-05-25:** Phase 6w now claimed for Tindall/Sels + Aalto material per strategy synthesis D-8. Re-slot to Phase 6x or later. |

**Wave dependencies:**
- W1 → W2 → W3 must be sequential (each depends on the predicate framework from the previous).
- W4 → W5 → W6 must follow W1-W3 (the recursion engine + length bound + headline consume the parametrized closure + net).
- Track instantiations T-S / T-A1 / T-A2 / T-B can run **in parallel** after W6 lands — each alphabet's instantiation is structurally independent and can be sequenced based on substrate-readiness priority.
- Phase 6t Fibonacci is **retro-fit as the W1-W6 reference instance**: after Phase 6u substrate ships, the existing `fibonacci_density_F21_unconditional` + `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight` should become specializations of the generic theorems. This is a refactor-only validation step (no new theorems; verifies the parametrization didn't break the Fibonacci specialization).

---

## Wave-by-wave detail

### Wave 1 — Generic generating-set framework

**Goal:** ship `lean/SKEFTHawking/FKLW/GenericSU2GeneratingSet.lean` defining the abstract framework for an SU(2) generating set with a parametric closure.

**Key declarations:**
```lean
structure GeneratingSet : Type where
  G : Finset ↥(specialUnitaryGroup (Fin 2) ℂ)
  G_nonempty : G.Nonempty
  G_symmetric : ∀ g ∈ G, g⁻¹ ∈ G  -- inverse-closed (optional; some alphabets are inverse-closed by construction)

def H_of_G (gs : GeneratingSet) : Subgroup ↥(specialUnitaryGroup (Fin 2) ℂ) :=
  topologicalClosure (Subgroup.closure gs.G : Subgroup _)
```

**Substrate-level lemmas:**
- `H_of_G_closed (gs)` : `IsClosed (H_of_G gs : Set _)`
- `H_of_G_inv_mem (gs) (h : ↥(H_of_G gs))` : `h⁻¹ ∈ H_of_G gs`
- `H_of_G_specialize_Fib` : `H_of_G ⟨{σ_Fib_1_SU, σ_Fib_2_SU}, _, _⟩ = H_Fib` (validates the refactor against Phase 6t's `H_Fib`)

**Mathlib4 substrate dependencies:** `Subgroup.closure`, `topologicalClosure`, `IsClosed_iff_topologicalClosure_le` — all present in Mathlib4 v4.29.1. Expected to be a thin refactor of existing `H_Fib`-specific machinery.

**Risk:** LOW. This is mostly renames + abstraction over an existing predicate. The Phase 6t `H_Fib_*` lemma corpus transfers near-mechanically.

**Estimated LoC:** ~200-400.

---

### Wave 2 — Abstract closure-dense witness

**Goal:** ship `lean/SKEFTHawking/FKLW/GenericClosureDenseWitness.lean` defining the predicate
```lean
def IsDenseInSU2 (gs : GeneratingSet) : Prop :=
  ∀ (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ), 0 < ε →
    ∃ h ∈ H_of_G gs, ‖(h : Matrix _ _ ℂ) - (U : Matrix _ _ ℂ)‖ < ε
```
plus the canonical instantiator `IsDenseInSU2.of_v4_witness` that consumes a Phase 6t v4-style explicit-X₁-X₂ witness and produces the density conclusion.

**Key declarations:**
```lean
structure ClosureDenseWitness (gs : GeneratingSet) : Type where
  X₁ : Matrix (Fin 2) (Fin 2) ℂ
  X₂ : Matrix (Fin 2) (Fin 2) ℂ
  hX₁_mem : X₁ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)
  hX₂_mem : X₂ ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin 2)
  hX₁_flow : ∀ t : ℝ, ∃ M ∈ H_of_G gs, M.val = SU2MatrixExp.expAmbient ((t:ℂ) • X₁)
  hX₂_flow : ∀ t : ℝ, ∃ M ∈ H_of_G gs, M.val = SU2MatrixExp.expAmbient ((t:ℂ) • X₂)
  hLI : ∀ a b : ℝ, (a:ℂ) • X₁ + (b:ℂ) • X₂ = 0 → a = 0 ∧ b = 0

theorem IsDenseInSU2.of_v4_witness (gs : GeneratingSet)
    (w : ClosureDenseWitness gs) : IsDenseInSU2 gs := by
  -- Compose CartanFinalStep_SU2_v4_holds with the witness; conclude H_of_G gs = ⊤;
  -- then density follows from Aharonov-Arad bridge.
  sorry
```

**Substrate-level transitions:**
- Existing `CartanFinalStep_SU2_v4_holds` (from `SU2BCHBracketClosure.lean` Phase 5 Step 13) is alphabet-agnostic — it takes ANY closed subgroup with two ℝ-LI traceless skew-Hermitian flow lines and concludes the subgroup equals ⊤. **This is the key transfer point.**
- The Aharonov-Arad bridge (`AharonovAradBridgeIteration.lean`) takes any representation `ρ` abstractly — also alphabet-agnostic.
- Wave 2's main work: factor the existing `H_Fib_v4_witness_unconditional` into a `ClosureDenseWitness {σ_Fib_1_SU, σ_Fib_2_SU}` value, and prove the `of_v4_witness` instantiator using the existing Cartan + AA bridge composition.

**Risk:** LOW-MEDIUM. The transfer is clean; the only structural concern is whether `H_Fib_v4_witness_unconditional`'s Bolzano-Weierstrass extraction (which gave `‖X₁‖ = 1`) is recoverable as a `ClosureDenseWitness` value. Expected: yes, with cosmetic refactoring.

**Estimated LoC:** ~200-400.

---

### Wave 3 — Generic ε₀-net structure

**Goal:** ship `lean/SKEFTHawking/FKLW/GenericEpsilonNet.lean` defining the abstract finite-net structure.

**Key declarations:**
```lean
structure SU2EpsilonNet (gs : GeneratingSet) (ε₀ : ℝ) : Type where
  ε₀_pos : 0 < ε₀
  net : Finset (FreeMonoid gs.G)  -- finite set of words over the generating alphabet
  net_nonempty : net.Nonempty
  net_covers : ∀ (U : ↥(specialUnitaryGroup (Fin 2) ℂ)),
    ∃ w ∈ net, ‖(evaluateWord w : Matrix _ _ ℂ) - (U : Matrix _ _ ℂ)‖ ≤ 2 * ε₀

noncomputable def findNearest (gs : GeneratingSet) (ε₀ : ℝ)
    (net : SU2EpsilonNet gs ε₀) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    FreeMonoid gs.G := ...  -- argmin over net.net

theorem findNearest_approx_opNorm (gs ε₀ net U) :
    ‖(evaluateWord (findNearest gs ε₀ net U) : Matrix _ _ ℂ) - (U : Matrix _ _ ℂ)‖ ≤ 2 * ε₀
```

**Coverage-verification interface:** Wave 3 defines the predicate `net_covers` but does NOT discharge it abstractly. Discharge happens per-alphabet (Track T-S, T-A1, etc.) using one of three strategies:
1. **Computational** — brute-force enumerate words up to length L0, port the `Finset` literal to Lean, verify coverage at a Haar-grid of test points via `decide` or `native_decide`. Mechanical but slow at large L0.
2. **Symbolic** — leverage an algebraic-number-theoretic structure on the alphabet (e.g., Z[ω][1/√2] for Clifford+T per Ross-Selinger; algebraic-number-theoretic structure on σ_Fib generators for Fibonacci). More elegant but harder to formalize.
3. **Hybrid** — short-word net (length ≤ 5) symbolic + extension via SK iteration to ε₀.

**Risk:** MEDIUM. The abstract structure is straightforward; per-alphabet coverage verification is the load-bearing engineering cost (deferred to track instantiations).

**Estimated LoC (substrate only):** ~250-500.

---

### Wave 4 — Generic recursion engine

**Goal:** ship `lean/SKEFTHawking/FKLW/GenericSolovayKitaevRecursion.lean` containing the parametrized super-quadratic recursion.

**Key declarations:**
```lean
noncomputable def skApproxC_generic (gs : GeneratingSet) (ε₀ : ℝ)
    (net : SU2EpsilonNet gs ε₀) :
    ℕ → ↥(specialUnitaryGroup (Fin 2) ℂ) → FreeMonoid gs.G
  | 0, U => findNearest gs ε₀ net U
  | (n + 1), U =>
    let V_n := skApproxC_generic gs ε₀ net n U
    let V_n_SU2 := evaluateWord V_n
    let Δ := V_n_SU2⁻¹ * U
    let H := ((-Complex.I) : ℂ) • Y_h Δ.val
    -- Compute F, G ∈ 𝔰𝔲(2) with [F, G] = -H (balanced-commutator factorization)
    let (F, G) := dnStepFG_generic Δ
    let A_F := expIsu2 F
    let A_G := expIsu2 G
    V_n * (skApproxC_generic gs ε₀ net n A_F *
           skApproxC_generic gs ε₀ net n A_G *
           (skApproxC_generic gs ε₀ net n A_F)⁻¹ *
           (skApproxC_generic gs ε₀ net n A_G)⁻¹)
```

**Substrate-level lemmas:**
- `SkApproxCSuperQuadraticBound_generic K gs ε₀ net` : `Prop` (parametrized predicate)
- `SkApproxCSuperQuadraticBound_generic_holds_of_calibration` : for K = K_compose = 1024 and ε₀ = 1/(8·K²), the predicate holds.

**Important transfer note:** the existing Phase 6t Path A Option C discharge of `SkApproxCSuperQuadraticBound K_compose` (~981 LoC in `SolovayKitaevPathA.lean`) uses:
- `‖Δ.val - 1‖ ≤ √2 · ε_n` (V_n unitarity bound; generic SU(2), no Fibonacci)
- Cubic bound via `dnStepFG_gC_minus_Delta_norm_le_cubic` (generic for SU(2) operator-norm composition)
- K_compose = 1024 calibration with margin ~236 (depends on the proof's K_proof ≈ 788 ≤ K_compose)

**The discharge proof should transfer verbatim** modulo Fibonacci-specific naming (`V_n_braid : FibonacciBraidWord` → `V_n_word : FreeMonoid gs.G`). The Wave 4 audit is to walk the ~981 LoC and verify no σ_Fib-specific lemma slipped in. Expected pass; minor naming refactor.

**Risk:** LOW-MEDIUM. The recursion engine itself is generic; the audit is mechanical.

**Estimated LoC:** ~500-800 (mostly refactor; some new generic-alphabet wiring).

---

### Wave 5 — Generic length bound + level selector

**Goal:** ship `lean/SKEFTHawking/FKLW/GenericSolovayKitaevLengthBound.lean` containing the parametrized closed-form length recurrence.

**Key declarations:**
```lean
noncomputable def skLength_generic (gs : GeneratingSet) (baseCase decompCost : ℝ) (n : ℕ) : ℝ :=
  baseCase * (5 : ℝ) ^ n + decompCost * ((5 : ℝ) ^ n - 1) / 4

noncomputable def skLevel_polylog_generic (gs : GeneratingSet) (K : ℝ) (ε : ℝ) : ℕ := ...
  -- ceil(log(log(1/(K²·ε))/log 4) / log(3/2)), same as Fibonacci

theorem skLength_at_skLevel_polylog_le_generic (gs K ε₀ ε baseCase decompCost) :
    ε ≤ ε₀ → skLength_generic gs baseCase decompCost (skLevel_polylog_generic gs K ε) ≤
      lengthConst * (Real.log (1 / ε)) ^ (Real.log 5 / Real.log (3 / 2))
```

**Per-alphabet parameters:**
- `baseCase` = max word length in the alphabet's ε₀-net (Phase 6t Fibonacci: 100; Clifford+T: probably 30-50 per Ross-Selinger L0 calibration)
- `decompCost` = per-level balanced-commutator cost (Phase 6t Fibonacci: 100; Clifford+T: similar order)

**Risk:** LOW. The length-recurrence math is alphabet-agnostic.

**Estimated LoC:** ~100-200 (mostly parametrized refactor of Phase 6t Wave 5).

---

### Wave 6 — Generic bundled-strict headline

**Goal:** ship `lean/SKEFTHawking/FKLW/GenericSolovayKitaevQuantitative.lean` with the parametric headline theorem.

**Key declaration:**
```lean
theorem solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight
    (gs : GeneratingSet)
    (witness : ClosureDenseWitness gs)
    (ε₀ : ℝ) (h_ε₀ : ε₀ = 1 / (8 * K_compose ^ 2))
    (net : SU2EpsilonNet gs ε₀)
    (h_calibration : SkApproxCSuperQuadraticBound_generic K_compose gs ε₀ net)
    (ρ : FreeMonoid gs.G →* ↥(specialUnitaryGroup (Fin 2) ℂ))
    (h_ρ_eval : ∀ w, (ρ w : Matrix _ _ ℂ) = evaluateWord w)
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖(ρ (solovayKitaev_compile_strict_constructive_generic gs ε₀ net U ε) :
        Matrix _ _ ℂ) - (U : Matrix _ _ ℂ)‖ ≤ ε ∧
    skLength_generic gs net.baseCase net.decompCost
        (skLevel_polylog_generic gs K_compose ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent
```

The parametric headline takes (a) the alphabet `gs`, (b) the closure-density witness, (c) the calibrated ε₀, (d) the ε₀-net, (e) the calibration discharge, (f) a representation `ρ` — and produces the simultaneous error + length bound.

**Phase 6t Fibonacci re-derivation (validation step):**
```lean
example : solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight =
    solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight
      fibonacciGeneratingSet
      fibonacciClosureDenseWitness
      ε₀ rfl
      fibonacciEpsilonNet
      fibonacciSkApproxCSuperQuadraticBound_holds
      ρ_Fib_SU2
      ρ_Fib_SU2_evaluateWord := by
  -- Should be defeq or a thin proof.
  sorry
```

**Risk:** LOW. Composition of W1-W5 deliverables.

**Estimated LoC:** ~150-300.

---

## Track instantiations

### Track T-S — Clifford+T over arbitrary SU(2)

**Goal:** instantiate the generic substrate at `G = {H, T, S}` ⊂ SU(2) and produce a customer-shippable quantitative compilation theorem for arbitrary SU(2) targets using the Clifford+T gate set.

**Concrete decomposition:**

**T-S.1 — Generating set + group structure** (~100-200 LoC). Define `H : SU(2) = (1/√2)[[1, 1], [1, -1]]`, `T = diag(1, e^{iπ/4})`, `S = diag(1, i) = T²` (or include S = T² as derived). Build `cliffordTGeneratingSet : GeneratingSet`. Note that S is in `⟨H, T⟩` (S = T²), so the minimal generating set is `{H, T}` with S as a derived element. The 24-element Clifford group is `⟨H, S⟩` (or `⟨H, T²⟩`); adding T gives universal.

**T-S.2 — Closure-dense witness** (~300-600 LoC). Prove the `ClosureDenseWitness cliffordTGeneratingSet` value. This is the **Wave 2 hard step** per the productization walk-through:
- Strategy: construct X₁ ∈ 𝔰𝔲(2) such that `∀ t : ℝ, exp(t·X₁) ∈ closure(⟨H, T⟩ : Set _)`.
- The witness candidate: `T·T·T = diag(1, e^{i·3π/4})` — but this is a discrete element, not a 1-parameter subgroup. The 1-parameter subgroup arises from a Bolzano-Weierstrass extraction analogous to Phase 6t's H_Fib_v4_witness, but the accumulation-point argument requires the *non-cyclotomic* nature of `e^{iπ/4}`'s relationship to the Clifford group's roots of unity.
- Alternative strategy: use the **rotation-by-irrational-angle** argument explicitly — `(T·H)^n` for varying n hits a dense set on the great circle perpendicular to the T-rotation axis. Combine with H's reflection to get the second LI direction.
- Risk: MEDIUM. The closure-density of Clifford+T is well-known (Boykin et al. 1999), but lifting to a `ClosureDenseWitness`-shaped proof in Lean is non-trivial.

**T-S.3 — ε₀-net** (~250-500 LoC). Construct `cliffordTEpsilonNet : SU2EpsilonNet cliffordTGeneratingSet (1/8388608)`.
- Strategy options (per Wave 3 discussion):
  - **Computational**: brute-force enumerate Clifford+T words up to length L0 (likely L0 ~30-40 per Dawson-Nielsen 2006 §3 base-case analysis). At L0=30, the net has ~10⁶-10⁷ words (after deduplication). Coverage verification at a Haar grid is expensive.
  - **Symbolic via Ross-Selinger**: leverage the `Z[ω][1/√2]` algebraic structure. Clifford+T words are in 1-1 correspondence with certain `M ∈ U(2; Z[ω][1/√2])` with a denominator-controlling exponent; coverage at ε₀ can be argued via a counting argument on the discriminant. Public-substrate-quality formalization.
  - **Hybrid**: short-word net (length ≤ 5; ~10³ Clifford+T words) symbolic + SK iteration extension.
- Risk: HIGH. This is the load-bearing engineering cost — same as Phase 6t Wave 3 was for Fibonacci (~400 LoC, multi-session).

**T-S.4 — Calibration discharge** (~50-200 LoC). Walk the Phase 6t Path A Option C `SkApproxCSuperQuadraticBound_holds` discharge and verify it transfers to `cliffordTGeneratingSet`. The K_compose = 1024 calibration should hold (the proof bounds are SU(2)-generic) but may need bump if Clifford+T's geometry forces different K_stab1 / K_cubic. Document any retune.

**T-S.5 — Headline + ρ representation** (~150-300 LoC). Define `ρ_CliffordT : FreeMonoid {H, T, S} →* ↥SU(2)` (the obvious word-evaluation map). Compose Wave 6 generic headline. Resulting theorem:
```lean
theorem solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖(ρ_CliffordT (compile_cliffordT U ε) : Matrix _ _ ℂ) -
        (U : Matrix _ _ ℂ)‖ ≤ ε ∧
    cliffordT_length (level_polylog ε) ≤
      skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent
```

**Aggregate Track T-S effort:** ~850-1,800 Lean LoC.

---

### Track T-A1 — Trapped-ion Mølmer-Sørensen + arbitrary 1Q rotation

**Goal:** instantiate the substrate at the Quantinuum / IonQ native gate set (MS(θ) + 1Q rotations parametrized by angle).

**Key distinction:** trapped-ion alphabets are **continuous-parameter** — MS(θ) is one gate per angle θ ∈ [0, 2π), and arbitrary 1Q rotations are parametrized by Euler angles. The standard SK framework assumes a **finite** generating set; pre-processing is required.

**Decomposition:**

**T-A1.1 — Discretization layer** (~200-400 LoC). Define a finite subset `MS_grid ⊂ {MS(θ) : θ ∈ rational multiples of π/N for some grid N}` plus a finite 1Q rotation grid. Prove that the discretized alphabet has closure dense in SU(2) (or in the relevant 2-qubit subspace — trapped-ion MS is intrinsically 2-qubit).

**T-A1.2 — Target group choice** (decision). MS(θ) is 2-qubit (acts on SU(4) for 2 ions). The Phase 6u substrate is currently SU(2)-targeted. Options:
- (a) Restrict to single-qubit compilations (use only the 1Q rotation part of the trapped-ion alphabet, ignore MS): trivial substrate reuse but not commercially useful.
- (b) Extend Phase 6u substrate to SU(4): substantial Lie-algebra work (𝔰𝔲(4) is dim 15 not 3; v4 IFT 3-direction discharge becomes 15-direction).
- (c) Decompose target SU(4) compilation into a sequence of 2-qubit subspaces: needs `KAK decomposition` / `cosine-sine decomposition` infrastructure. This is a Mathlib-PR-quality lift (the underlying math — block-ZXZ + cosine-sine landscape — is public-domain; the substrate would need to be built out in Mathlib4).

**Risk:** HIGH for option (b); MEDIUM for option (c) (the underlying math is public-domain but the Mathlib4 substrate is currently absent).

**Aggregate Track T-A1 effort:** ~1,200-2,500 LoC (substantial; likely Phase 6v).

---

### Track T-A2 — Clifford+CCZ for 3-qubit primitives

**Goal:** instantiate at `G = {H ⊗ I ⊗ I, I ⊗ H ⊗ I, I ⊗ I ⊗ H, CCZ}` (Clifford+CCZ universal gate set on 3 qubits, target group SU(8)).

**Key challenge:** target group is SU(8), not SU(2). Substantial Phase 6u substrate extension required:
- 𝔰𝔲(8) is dim 63 (not 3). The v4 IFT 3-direction discharge becomes a **63-direction discharge**. Phase 6u Wave 1-2 substrate needs generalization beyond SU(2).
- BCH cubic bound for SU(d) general d: Mathlib-PR-quality but currently absent. Phase 6u substrate would need to ship this.
- Y_h Lipschitz pullback for SU(d): generalizes from π/2 (SU(2) Bloch) to a d-dependent constant. Needs new derivation.

**Risk:** HIGH. Phase 6w / Phase 6x scope, not Phase 6u.

**Aggregate Track T-A2 effort:** ~2,000-4,000 LoC (largest of the four tracks).

---

### Track T-B — Read-Rezayi SU(2)_k

**Goal:** instantiate at SU(2)_k for k ∈ {5, 7} — the next universal Read-Rezayi anyon levels beyond Fibonacci (k=3).

**Key advantage:** highest substrate reuse of all the tracks (~80-90%). The Phase 6t Fibonacci-specific machinery transfers near-mechanically with new σ_k generators replacing σ_Fib generators. Target group remains SU(2).

**Decomposition:**

**T-B.1 — New generators** (~50-100 LoC per k). Define `σ_k_1, σ_k_2 ∈ SU(2)` for the SU(2)_k braid representation. The 2-strand representation of B_n at SU(2)_k generates a subgroup of SU(2) with explicit closure structure (Jones-Wenzl projectors, F-symbols).

**T-B.2 — Closure-dense witness** (~150-300 LoC per k). Replicate the Phase 6t Cartan v4 witness with σ_k generators. The non-cyclotomic trace argument may differ per k (Fibonacci used `(3-√5)/2`); for SU(2)_5 the analogous trace is a root of a different irreducible polynomial.

**T-B.3 — ε₀-net + recursion + headline** (~200-400 LoC per k). Direct refactor of Phase 6t Waves 3-6 with the new alphabet.

**Risk:** LOW per k (high substrate reuse). Multiple k values can be shipped in sequence.

**Aggregate Track T-B effort:** ~400-800 LoC per k value. SU(2)_5 alone: ~500 LoC.

---

## Cross-cutting work

### Mathlib upstream PR candidates

Phase 6u surfaces several Mathlib-PR-quality lemmas that should be upstream-contributed (Phase 6s Track 2 community-citizenship framing):

1. **Generic BCH order-2 cubic bound** for any matrix Lie algebra: `‖exp(A)·exp(B)·exp(-A)·exp(-B) - exp([A,B])‖ ≤ K_BCH · (‖A‖³ + ‖B‖³)` for explicit K_BCH. Currently shipped SU(2)-specific in `SU2BCHBracketClosure.lean`; the proof is generic.
2. **Generic density-from-Cartan-v4-witness lemma**: any closed subgroup of a compact connected matrix Lie group containing two ℝ-LI 1-parameter subgroups equals the whole group (modulo Cartan's classification, which is the hard upstream PR).
3. **`HasStrictFDerivAt.toOpenPartialHomeomorph` 3-direction-product strict differentiability**: shipped as `threeDirProduct_hasStrictFDerivAt_zero` in Phase 5 Step 13; the technique is generic.

### Adversarial-review checkpoints

Per `BUNDLE_LIFT_PROCEDURE.md` Stage 13 hard gate:

- **CP1 — after Wave 6**: fresh-context `claims-reviewer` agent on the generic substrate (W1-W6) + the Fibonacci re-derivation validation step.
- **CP2 — after Track T-S**: fresh-context `claims-reviewer` agent on the Clifford+T instantiation + the customer-facing headline.
- **CP3 — after each subsequent track**: per-track Stage 13 review on the instantiation deliverables.

### Pipeline Invariants

- **#10 (no `maxHeartbeats`)**: RESPECTED throughout. The Phase 6t valid-branch composition lesson (`valid_branch_K_chain_le_K_compose_numeric` helper extraction) applies to Phase 6u — if any wave's main theorem hits the heartbeat budget, decompose via top-level numerical helpers.
- **#15 (no new axioms without user sign-off)**: RESPECTED. Pivot rule explicit: if any track's closure-density witness requires algebraic-number-theoretic work beyond Mathlib4 v4.29.1, YIELD for user sign-off.

---

## Sessions log

### Session 1 — 2026-05-25 (Phase 6u kickoff)

Goal: ship Waves 1-6 substrate scaffolding + lay groundwork for Wave 4b
substantive generic discharge.

**Waves 1, 2, 3, 4a, 5, 6 SHIPPED (5 new modules, ~1,200 LoC, zero new
axioms, kernel-only):**

  * `lean/SKEFTHawking/FKLW/GenericSU2GeneratingSet.lean` (Wave 1):
    `structure GeneratingSet` carrying `(W, ρ_hom, gens, gens_generate)`;
    `H_of_G gs := gs.ρ_hom.range.topologicalClosure`; Fibonacci instance
    `fibonacciGeneratingSet` with `H_of_G_specialize_Fib : H_of_G ... = H_Fib`
    by reflexivity.

  * `lean/SKEFTHawking/FKLW/GenericClosureDenseWitness.lean` (Wave 2):
    `structure ClosureDenseWitness gs` carrying two ℝ-LI traceless
    skew-Hermitian flow-line tangents; `H_of_G_eq_top_of_witness` composes
    `CartanFinalStep_SU2_v4_holds` (Phase 5 Step 13, alphabet-agnostic)
    to dispatch any witness into `H_of_G gs = ⊤`; `IsDenseInSU2_gs gs`
    generic density predicate; `isDenseInSU2_gs_of_eq_top` gives the
    `H_of_G = ⊤ ⟹ density` chain (via `Subgroup.topologicalClosure_coe`
    + continuous push-forward via `Subtype.val`); `fibonacciClosureDenseWitness`
    extracts from `H_Fib_v4_witness_unconditional` (Prop → Type via
    `Nonempty.some` + Classical.choice).

  * `lean/SKEFTHawking/FKLW/GenericEpsilonNet.lean` (Wave 3):
    `epsilonNet_findNearest gs h_dense U ε₀ hε₀_pos : gs.W` via
    Classical.choose on `IsDenseInSU2_gs`; correctness lemma
    `epsilonNet_findNearest_approx_opNorm`; convenience composition
    `epsilonNet_findNearest_of_witness` straight from a
    `ClosureDenseWitness`; Fibonacci validation.

  * `lean/SKEFTHawking/FKLW/GenericSolovayKitaevRecursion.lean` (Wave 4a):
    `dnStepFG_su2 V_n U` (alphabet-agnostic version of Phase 6t's
    `dnStepFG`, with `dnStepFG_su2_eq_dnStepFG` validating refl-equivalence
    at Fibonacci); `skApproxC_generic gs baseFinder` parametric SK
    recursion; `SkApproxCSuperQuadraticBound_generic K gs baseFinder`
    predicate; `BaseFinder_approximates_within` predicate;
    `fibonacciBaseFinder`; `skApproxC_generic_fibonacci_eq` reduction
    lemma (by structural rfl after induction); `SkApproxCSuperQuadraticBound_generic_fibonacci`
    UNCONDITIONAL Fibonacci-instance discharge by composing the reduction
    with Phase 6t's `SkApproxCSuperQuadraticBound_holds`;
    `solovayKitaev_compile_strict_constructive_generic` wrapper at
    `skLevel_polylog ε`.

  * `lean/SKEFTHawking/FKLW/GenericSolovayKitaevLengthBound.lean` (Wave 5):
    re-export of the already-alphabet-agnostic
    `skLength_at_skLevel_polylog_le` with `GeneratingSet`-aware naming.

  * `lean/SKEFTHawking/FKLW/GenericSolovayKitaevQuantitative.lean` (Wave 6):
    GENERIC bundled-strict headline
    `solovayKitaev_dawson_nielsen_quantitative_generic_strict_constructive_tight`
    (conditional on `SkApproxCSuperQuadraticBound_generic K_compose gs baseFinder`);
    Fibonacci-instance specialization
    `solovayKitaev_dawson_nielsen_quantitative_fibonacci_strict_constructive_tight_via_generic`
    UNCONDITIONAL via the Wave 4a Fibonacci bridge — recovers Phase 6t's
    canonical strict headline through the generic substrate.

**Key design decisions (Session 1):**

  1. **`GeneratingSet` carries the word type `W : Type` (a Group) plus
     a representation homomorphism `ρ_hom : W →* SU(2)`** — instead of
     the roadmap's original `Finset ↥SU(2)` shape. Rationale: Fibonacci
     uses `W = BraidGroup 3` and Clifford+T uses (e.g.) `W = FreeGroup
     (Fin 3)`. Both fit naturally; the `Finset ↥SU(2)` shape would lose
     the BraidGroup typing for Fibonacci. The explicit generator field
     `gens : Finset W` with `gens_generate` keeps the ε₀-net's word-
     enumeration interface viable.

  2. **`H_of_G` defined via `ρ_hom.range.topologicalClosure`** — by
     definition this matches `H_Fib` for Fibonacci, giving
     `H_of_G_specialize_Fib` by reflexivity (no rewriting). This is
     critical for `dnStepFG_su2_eq_dnStepFG` and
     `skApproxC_generic_fibonacci_eq` to close by rfl/induction-rfl
     respectively.

  3. **Wave 4 split into 4a (definitions + Fibonacci bridge) and 4b
     (substantive generic discharge)** — Wave 4a ships in this session
     and provides an UNCONDITIONAL Fibonacci-instance headline (validates
     the abstraction). Wave 4b is the ~800-1000 LoC substantive port of
     Phase 6t Path A Option C's `SkApproxCSuperQuadraticBound_holds`
     adapted to arbitrary `GeneratingSet` + `baseFinder` satisfying
     `BaseFinder_approximates_within` (i.e., the base-case ε₀-approx
     property). Wave 4b is the prerequisite for Track T-S Clifford+T
     to land with UNCONDITIONAL discharge.

**Open work for next session(s):**

  * **Wave 4b substantive discharge** (highest priority). Port the
    `SkApproxCSuperQuadraticBound_holds` proof (`SolovayKitaevPathA.lean`
    §7.8, ~981 LoC) to a generic `SkApproxCSuperQuadraticBound_generic_holds`
    parametric over `gs` + a base-finder satisfying the ε₀-approx property.
    All substrate lemmas (cubic, stability, V_n unitarity, etc.) are
    already alphabet-agnostic; the port is mostly substitution
    `ρ_Fib_SU2 ↦ gs.ρ_hom` + `FibonacciBraidWord ↦ gs.W` + recursive-call
    renames. Should close Wave 4b without re-deriving SU(2)-geometric
    substrate.

  * **Track T-S substantive ship** (after Wave 4b). T-S.1 (generating
    set) is small. T-S.2 (closure-density witness from Boykin-Mor-Pulver-
    Roychowdhury-Vatan 1999) is the LOAD-BEARING substantive piece
    (~500-800 LoC). T-S.3 (ε₀-net via Ross-Selinger ℤ[ω][1/√2] or
    computational enumeration) is ~250-500 LoC. T-S.4 + T-S.5 are
    thin wrappers given Wave 4b done.

  * **CP1 + CP2 adversarial reviews** + **strengthening pass** after
    Wave 4b + Track T-S land.

**Build state (end of Session 1, after Waves 1-6 ship):**

  - `lake build SKEFTHawking.FKLW.GenericSolovayKitaevQuantitative` clean
    (8285 jobs).
  - Zero new project-local axioms.
  - Zero sorries introduced.
  - Standard-kernel-only headlines (`{propext, Classical.choice, Quot.sound}`).

**Publication-strategy impact (Session 1):**

  - **D4 bundle §9.6-§9.8 absorption**: Wave 1-6 substrate provides the
    *generic* alphabet-independent quantitative Solovay-Kitaev result.
    When D4's late absorption protocol runs, §9.6 (Fibonacci closure-
    density), §9.7 (Fibonacci quantitative SK), and §9.8 (alphabet
    survey) all gain the generic substrate as their PRIMARY exposition
    target — Fibonacci becomes the canonical first instance, with
    Clifford+T (Track T-S, pending Wave 4b) as the canonical second
    instance demonstrating the abstraction's utility. No content changes
    needed for D4 §9.1-§9.5 (Fibonacci-specific deep results stand);
    §9.6 onward should reference the generic substrate as the
    canonical-presentation target. Add a note to `docs/PAPER_DRAFT_MAPPING.md`
    once Wave 4b + Track T-S close.

---

## Cross-references

- **Phase 6t roadmap** (`docs/roadmaps/Phase6t_Roadmap.md`) — Fibonacci-specific predecessor; W1-W6 of Phase 6u abstract its Wave 1-6.
- **Phase 6t close memo** (`docs/PHASE6T_QUANTITATIVE_SK_COMPLETE.md`) — canonical narrative + numbers (K_proof ≤ 788, margin ~236, K_compose = 1024).
- **Lit-Search Phase 6t landscape scan** (`Lit-Search/Phase-6t/...`) — confirms no prior kernel-verified quantitative SK formalization.
- **BCH bracket closure substrate** (`lean/SKEFTHawking/FKLW/SU2BCHBracketClosure.lean`) — Phase 5 Step 13 + Phase 6t reuse base.
- **Aharonov-Arad bridge** (`lean/SKEFTHawking/FKLW/AharonovAradBridgeIteration.lean`) — abstract density framework, already alphabet-agnostic.
- **Bundle Readiness Heatmap** (`docs/BUNDLE_READINESS_HEATMAP.md`) — for tracking D4 §9.6-9.8 absorption status as waves ship.
