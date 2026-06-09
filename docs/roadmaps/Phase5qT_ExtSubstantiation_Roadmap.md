# Phase 5q.T: Ext Substantiation — grounding the A(1) Ext computation in Mathlib's real `Ext`

## Technical Roadmap — June 2026

*Prepared 2026-06-03. Follows Phase 5q (resolution + Ext dimensions) and Phase 5r (change-of-rings H2 placeholder). Strengthens the **algebraic core** of the generation-constraint chain. PUBLIC repo. No new axioms; no new `sorry`; the goal is to **upgrade thin/proxy theorems into substantive ones**, not to add scaffolding.*

---

## Why this wave exists

A focused re-read of the generation-constraint Lean chain (2026-06-03) found that the
**algebraic core is genuinely machine-checked at the level of the F₂ chain complex**
([A1Resolution.lean](../../lean/SKEFTHawking/A1Resolution.lean): `dᵢ·dᵢ₊₁ = 0`, kernel
cardinalities, RREF rank certificates — all real), but the **bridge from those matrices to
the actual `Ext` functor is a proxy**:

- [A1Ext.lean](../../lean/SKEFTHawking/A1Ext.lean) `ext_dim_n : (Fintype.card (Fin (8·rₙ)))/8 = rₙ` is
  arithmetic (`24/8 = 3 by decide`), not a statement about `Ext^n_{A(1)}(F₂, F₂)`.
- [ChangeOfRings.lean](../../lean/SKEFTHawking/ChangeOfRings.lean) `h2_discharged : True := trivial`
  and `hom_tensor_adjunction_dim : rank = rank := rfl` are placeholders, not the Hom-tensor adjunction.

**Why this slipped QA:** `ext_dim_n` is *not* type `True` (so `update_counts.py` doesn't count it as a
placeholder) and its body is `decide` not `rfl`/`trivial` (so `build_graph.py`'s `PlaceholderMarker`
detector doesn't flag it). It is a substantive-*looking* theorem whose content is weaker than its name.
This wave removes that class of proxy from the generation chain and adds a detector so it can't recur.

**Scope boundary.** This wave addresses the **algebraic** layer only (Ext over A(1), change-of-rings).
The three genuinely-topological hypotheses (H1 ko-cohomology, H3 Adams-SS collapse, H4 ABP splitting)
are out of scope here — they are handled by Phase 5q.B (spectra-free route) or a future faithful
ko/Adams/ABP build, and the A/B decision between those is tracked in
`docs/assessments/GenerationConstraint_RouteA_vs_B_ImpactAssessment.md`.

---

## Entry-state ground truth (verified 2026-06-03)

| Asset | Real state | Implication for this wave |
|---|---|---|
| `A1Ring.lean` | **Not** a `Ring` instance. `L0..L7 : Matrix (Fin 8) (Fin 8) F2` = left-regular-rep matrices of the 8 basis elements; mul facts by `decide`. | Need a genuine `Ring`/`Algebra (ZMod 2)` instance (Wave T2). |
| `A1Resolution.lean` | Real: explicit `dᵢ`, `dᵢ·dᵢ₊₁=0`, ker-cards (d₁–d₃), RREF certs (d₄,d₅). A(1)-linearity asserted in comments, **not** proven against the ring. | Reuse matrices; prove A(1)-linearity once the ring exists. |
| `A1Ext.lean` | `ext_dim_n` are `cols/8` arithmetic proxies. Minimality (`dₙ_minimal`) is real. | Replace proxies with cohomology-of-dual-complex finrank (Wave T1), then real `Ext` (Wave T3). |
| `ChangeOfRings.lean` | `h2_discharged : True`. | Prove genuine change-of-rings (Wave T4). |
| Mathlib (pin v4.29.1) | Has `CategoryTheory/Abelian/Ext.lean` (`Ext R C n`, `ProjectiveResolution.isoExt`), `ModuleCat/ChangeOfRings.lean` (`extendRestrictScalarsAdj` — **CommRing only**, `:877`; the general-ring adjunction is `restrictCoextendScalarsAdj` `restrictScalars ⊣ coextendScalars`, `[Ring R] [Ring S]`, `:640`; `restrictScalars` itself is general-ring, `:85`), `RingTheory/TensorProduct/Free.lean`. All homology `noncomputable`. | Real `Ext` reachable; change-of-rings needs the **noncommutative** adjunction (A(1) is noncommutative) — use `restrictCoextendScalarsAdj`, NOT the CommRing `extendRestrictScalarsAdj`. |

---

## Waves

### Wave T1 — Cohomology-of-the-dual-complex substantiation (no categorical Ext yet) [COMPLETE 2026-06-03]

**Goal.** Replace the `ext_dim_n := cols/8` proxies with honest statements: the cohomology of the
`Hom_{A(1)}(P•, F₂)`-dualized complex has F₂-dimension `rₙ`, grounded in the **vanishing of the dual
coboundary maps** (the real content of "minimal ⟹ Ext = Hom"), not arithmetic.

**Math.** For a free module `Pₙ` of rank `rₙ`, `Hom_{A(1)}(Pₙ, F₂) ≅ F₂^{rₙ}`. The dual coboundary
`δⁿ : F₂^{rₙ} → F₂^{rₙ₊₁}` is the matrix `Δₙ(i,j) = ε(dₙ₊₁ block(i,j))`, where `ε` is the augmentation
(coefficient of the unit basis element `e₀`). In the F₂-expanded encoding, `ε(block(i,j)) = dₙ₊₁(8i, 8j)`,
and **minimality** (`dₙ₊₁` rows `8i` are zero) gives `Δₙ = 0`. Hence `Hⁿ = ker δⁿ / im δⁿ⁻¹ = F₂^{rₙ}`.

**Deliverable.** `lean/SKEFTHawking/A1ExtSubstantive.lean`:
- `dualCoboundary n : Matrix (Fin rₙ₊₁) (Fin rₙ) F2` (augmentation-extracted from `dₙ₊₁`).
- `dualCoboundary_eq_zero n` — `Δₙ = 0`, proven from the existing minimality theorems. **Substantive.**
- `ext_cohomology_finrank n : Module.finrank F2 (Hⁿ) = rₙ` where `Hⁿ` is the genuine `ker/im` quotient
  (fallback if quotient finrank is fiddly: ship `dualCoboundary_eq_zero` + `Module.finrank F2 (Fin rₙ → F2) = rₙ`
  + a combined corollary, with the docstring spelling out `Ext^n = ker/im = whole space`).
- Re-export / deprecate the `A1Ext.ext_dim_n` proxies with docstrings pointing here.

**Status: COMPLETE 2026-06-03** (`lean/SKEFTHawking/A1ExtSubstantive.lean`, added to root `SKEFTHawking.lean`).
Delivered the *full* quotient-finrank version (not the fallback):
- `delta0..delta4` — dual coboundaries augmentation-extracted from `d1..d5`.
- `delta0_eq_zero .. delta4_eq_zero` (+ `all_dual_coboundaries_vanish`) — **substantive**, proven by
  kernel-pure `decide` (NO `native_decide`).
- `ker_deltaN_top` (cocycles = ⊤), `range_deltaN_bot` (coboundaries = ⊥) as genuine `LinearMap` facts.
- `ext0_dim_substantive .. ext5_dim_substantive` (+ master `ext_dims_substantive`) — `Module.finrank F2` of
  the **cokernel of the incoming coboundary over the full cochain group** `(Fin rₙ → F2) ⧸ range δⁿ⁻¹`
  = 1,2,2,2,3,4. This equals Hⁿ = ker δⁿ / im δⁿ⁻¹ *because* the outgoing coboundary vanishes
  (`ker_deltaN_top`), so cocycles = ⊤. Honest replacements for `A1Ext.ext_dim_0..5 : cols/8`.
- `ext4_homology_dim_substantive` — the **literal subquotient** `ker δ⁴ ⧸ im δ³` (im δ³ viewed inside
  ker δ⁴ via `comap subtype`), finrank = 3. This is the unimpeachable "dim Ext⁴ = 3" that does not rely on
  the cocycle-restriction being elided (added 2026-06-03 after adversarial review flagged the coker-vs-Hⁿ
  statement gap; proof avoids the heavy `↥⊤ ⧸ ⊥` carrier by collapsing the ⊥-quotient before rewriting
  ker → ⊤, so NO `maxHeartbeats` bump needed).

Verification: `lean_diagnostic_messages` clean (no errors/warnings); `lake env lean` file-gate OK; axioms
on `ext_dims_substantive` = `{propext, Classical.choice, Quot.sound}` only (kernel-pure, no proxy axiom).
Remaining at checkpoint: full `lake build` project gate + `update_counts.py`/Inventory sync + Wave T5 detector.

### Wave T2 — A(1) as a genuine `Ring` / `Algebra (ZMod 2)` instance

**Goal.** Promote A(1) from "8 left-rep matrices" to a real algebra object Mathlib's `Ext` can consume.
**Approach.** Define `A1 := Fin 8 → ZMod 2` (newtype to dodge the `Pi` mul diamond) in the **Milnor basis
`e₀..e₇`**, with multiplication read off the existing `A1Ring.L·` left-regular-representation matrices
(`L_a · e_b` columns give the genuine sum-valued products, e.g. `Sq(1)·e₂ = e₃+e₄`). `Ring`/`Algebra (ZMod 2) A1`
axioms by `decide`; augmentation `A1 →ₐ[ZMod 2] ZMod 2` (project onto `e₀`). Prove the rep
`A1 →ₐ Matrix (Fin 8) (Fin 8) F2` (sending `eᵢ ↦ Lᵢ`) is a faithful algebra hom — this is what ties Wave T2
to the existing `L·` matrices and to `A1Resolution`'s differentials. Source the multiplication from the `L·`
matrices, **not** from `SteenrodA1.a1_mul`: the latter is in the admissible/Adem basis and returns
`Option A1Basis` (a single basis element), so it cannot represent the sum-valued products the `L·`
(Milnor-basis) matrices encode; the `L·` matrices are the correct, sum-capable source.
**Risk.** Low-medium (typeclass diamond; mitigated by newtype, proven pattern in repo).

### Wave T3 — Real `Ext^n_{A(1)}(F₂, F₂)` via `ProjectiveResolution.isoExt`

**Goal.** Build `ProjectiveResolution` of `F₂` over `A1` from the resolution matrices and prove
`Module.finrank (ZMod 2) ((Ext _ _ n).obj (op F₂)).obj F₂) = rₙ` using `ProjectiveResolution.isoExt`.
**Sub-tasks.** (a) `ModuleCat A1` wrappers for `Pₙ` (free) and the differentials as `A1`-linear maps;
(b) free ⟹ projective; (c) the five `ProjectiveResolution` fields incl. `quasiIso` (exactness — port the
ker-card / RREF rank facts into the homology vanishing of the augmented complex); (d) a small
computable-rank-over-F₂ helper to turn matrix ranks into `finrank`; (e) `isoExt` +
minimality ⟹ dimension. **Risk.** Medium — `noncomputable` homology API wrangling; the certified complex is
already in hand.

### Wave T4 — Genuine change-of-rings (discharge H2 for real)

**Goal.** Replace `h2_discharged : True` with a proof of `Ext^n_A(A ⊗_{A(1)} F₂, F₂) ≅ Ext^n_{A(1)}(F₂, F₂)`
(Shapiro / Hom-tensor adjunction). **Wrinkle.** Mathlib's `extendRestrictScalarsAdj` is `CommRing`-only;
A(1) and the full Steenrod algebra A are **noncommutative**, so use the general-ring adjunction
`restrictCoextendScalarsAdj` (`restrictScalars ⊣ coextendScalars`, `[Ring R] [Ring S]`, in Mathlib's
`ModuleCat/ChangeOfRings.lean`) — **not** the `CommRing`-only `extendRestrictScalarsAdj` — and lift to `Ext`
via dimension-shifting / derived-functor naturality. For the chain only the **dimension equality** at each `n`
is needed, which is lighter than the full natural iso. **Risk.** Medium-high (Mathlib lacks Shapiro; may need
upstreamable lemmas). **Decision gate:** if full generality balloons, ship the dimension-equality form and
leave the natural-iso as tracked follow-up — but **not** as a `True` placeholder; as an explicit
`Ext`-dimension theorem about the concrete A//A(1) module.

### Wave T5 — Guard rail + pipeline integration

- **Detector:** extend `build_graph.py` `_PLACEHOLDER_BODY_PATTERNS` (or a new `ProxyMarker`) to flag
  `decide`/`norm_num` bodies whose **statement is a closed arithmetic identity** (`a/b = c`, `a+b = c`)
  on a theorem whose **name/docstring claims a structural quantity** (`*_dim`, `*Ext*`, `rank`, `finrank`).
  This is the gap that let `ext_dim_n` through. Add a `validate.py` check.
- Update `A1Ext.lean` / `ChangeOfRings.lean` docstrings; sync Inventory, counts, README.
- Update the target **bundles** — **D2** (`papers/D2/`, the deep paper whose Ext section carries this) and
  the **L2** PRL splash (`papers/L2/`) — to cite the substantive theorems, not the proxies. (The
  `papers/paper10_*` per-wave draft is internal source material, not a deliverable.)
- Update `HYPOTHESIS_REGISTRY` H2 entry: `placeholder → discharged` only when Wave T4 ships real content.

### Wave T6 — (OPTIONAL) full Steenrod algebra A + the `A//A(1)` module structure [governed by ADR-003]

**Goal.** Extend the genuine A(1) ring (Wave T2) to the **full Steenrod algebra A**, and state/prove the
**`A//A(1)` module structure** — the *algebraic* content of hypothesis **H1** (`H*(ko;𝔽₂) ≅ A//A(1)` as an
A-module). This is the **tractable, top-row, spectra-free adjacent** of Leg D (the Adams/ABP frontier): it
strengthens the Ext-as-E₂-page *corroboration* narrative **without** building any stable homotopy.

**Scope boundary (critical).** T6 delivers only the *algebraic* `A//A(1)` structure. It does **NOT** discharge
H1/H3/H4 as *topological* facts — that requires the ko spectrum / Adams SS / ABP (Leg D), which is a
deferred bottom-row frontier per [ADR-003](../adrs/ADR-003-rokhlin-leg-discharge-and-deferred-topological-frontiers.md)
and `Phase5qD`. T6 must not imply the topological realization is proven.

**Trigger.** Pursue **only if** the Ext-as-E₂ corroboration narrative is judged worth the cost (it is *not* on
any critical path; `16 ∣ σ` is already unconditional via Phase 5q.B). Otherwise leave planned.

**Risk.** Low–medium (Adem-relation bookkeeping by `decide`; same newtype/diamond pattern as T2, larger basis).

---

## Status and sequence

| Wave | Scope | Status | Risk |
|------|-------|--------|------|
| T1 | Dual-complex cohomology substantiation | **COMPLETE 2026-06-03** | — |
| T2 | A(1) genuine Ring/Algebra instance | Planned | Low-medium |
| T3 | Real `Ext` via `isoExt` | Planned | Medium |
| T4 | Genuine change-of-rings (H2) | Planned | Medium-high |
| T5 | Proxy detector + integration | Planned | Low |
| T6 | (OPTIONAL) full Steenrod A + `A//A(1)` structure | Planned — narrative-gated (ADR-003) | Low-medium |

**Recommended sequence:** the T5 proxy detector can land immediately (independent, low-risk, and it guards the
whole class of issue T1 addressed). T2 is the prerequisite for T3 (real `Ext` needs the genuine ring). T4
(change-of-rings) depends on T3's `Ext` being real. T6 (optional) extends T2's ring and is narrative-gated —
pursue only if the Ext-as-E₂ corroboration story is wanted. T1–T6 are all **top-row** (finite F₂ algebra +
standard homological algebra Mathlib supports abstractly) and **not** gated on the Mathlib community — unlike
the *topological* discharge of H1/H3/H4 (Leg D), which is deferred and trigger-gated in `Phase5qD` per ADR-003.

**Execution prompts:** ready-to-run `/goal` prompts for T2–T5 (split into two parts) live in
[Phase5qT_goal_prompt.md](Phase5qT_goal_prompt.md).

## What success looks like

`dim Ext^n_{A(1)}(F₂, F₂) = rₙ` is a theorem about **Mathlib's `Ext` functor** (not `cols/8`); change-of-rings
is a real proof (not `True`); a detector prevents arithmetic-proxy theorems from masquerading as structural
results. The headline "first machine-checked Ext computation over a Steenrod subalgebra" becomes literally
true at the level of the derived functor. The **topological** hypotheses remain explicitly open (Phase 5q.B).

*Phase 5q.T roadmap. Created 2026-06-03. Follows [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
