# Kummer K4–K10 design pass (lead, 2026-07-20) — ROUTE B adopted

**Status: BINDING for K4–K10 dispatches** (supersedes the K4–K6 route as stated in the
`KummerK3Base.lean` dossier docstring; K0–K3, K7–K10 numbering retained). Companion to the
11-brick dossier; execution authority for the quotient/resolution leg. Verified-in-code
anchors are cited inline — re-verify with LSP at dispatch time.

## The architectural decision

**K4-as-stated (a singular orbifold carrier "smooth away from 16 cone points") is ELIMINATED.**
Mathlib has no orbifold/singular-space type and the dossier's candidate carrier would be a new
project-local type with heavy downstream cost. Route B never forms the singular quotient:

> Excise first, quotient free, weld bundles.
> `K3 := (T⁴° / τ) ∪_{16 × ℝP³} 16 × E`, where `T⁴°` = T⁴ minus 16 open τ-invariant balls
> (τ acts FREELY there), the quotient is an honest smooth manifold-with-boundary, and
> `E` = the concrete Euler−2 disk bundle over S². Every object is a genuine smooth
> manifold-(with-boundary); the singular space never exists.

This is also the classical cut-and-paste Kummer construction (verdict doc
`Lit-Search/Phase-5qH/K3_generator_realization_verdict_20260717.md`: "elementary smooth
cut-and-paste, reuses the surgery/atlas machinery").

**Verified design facts (2026-07-20, code-read):**
1. `K3RealizingElement` (`PinPlusKTSpinSigmaStock.lean:261`) fields = {g (T2, Nonempty), pkg
   (orient/B/pd), hfc, hB, hrank : rank = 22, hk3 : IntCongr(reindexed interMatrix, k3Form)}.
   **NO π₁ / simple-connectivity field ⟹ the K6 van Kampen sub-wall is OFF the critical path.**
2. `hk3` is an `IntCongr` certificate, and classification substrate partially exists:
   `HyperbolicNormalForm.lean` (imports `EvenUnimodularHyperbolic`) has the σ=0 even-unimodular
   → hyperbolic normal form (`:99–:102`) + `IntCongr.isEvenUnimodular` transport (`:71`).
3. `pkg_realizes_even_unimod` (`PinPlusKTSpinSigmaStock.lean:~247`) already discharges the
   even-unimodular obligation from `orient` + `pd` via
   `isEvenUnimodular_of_orientation_pd_emptySigma` — K8's "even" and "unimodular" conjuncts
   come from the package, NOT from Gram entries.

## The brick sequence (Route B)

| Brick | Content | Banked machinery | Genuinely new |
|---|---|---|---|
| **K2** (unchanged) | τ(w) = w⁻¹ on Circle⁴, smooth involution | `Circle` LieGroup inverse smooth, `ContMDiff.prod_map` | τ as `𝓡 4`-self-map smoothness |
| **K3** (unchanged) | Fix(τ) = {±1}⁴, exactly 16 points | `Circle` membership; `Fintype (Fin 2)⁴` | `{z : Circle ∣ z⁻¹ = z} = {1, −1}` |
| **K4′** | The punctured torus `T⁴°`: 16 τ-invariant open balls excised (centered charts at fixed points where τ = −id in-chart); **τ free on T⁴°**; ∂T⁴° = 16 × S³ | the surgery-foundation excision/chart stack (#125–#136); K0's charted `TorusFour` | the τ-equivariant centered chart + freeness |
| **K5′** | The free quotient `Q := T⁴°/τ`, smooth mfd-with-boundary; **∂Q = 16 × ℝP³** | **the ℝP⁴ = S⁴/±1 hand-chart template** (#44 `RP4Manifold`/rp4SM — the same free-ℤ/2-quotient construction one dimension up); quotient topology | the boundary-ℝP³ chart identification |
| **K6′a** | The concrete 𝒪(−2) disk bundle `E`: TWO charts `D² × D²`, clutching `(z,w) ↦ (z⁻¹, z²·w)`; ∂E ≅ L(2,1) = ℝP³; the zero-section (−2)-sphere | `ChartsConcrete`/chartB/chartHa two-chart pattern (#132–#135); `PinPlusTraceDiskSphereCycle` | the explicit clutching transition smoothness + the ∂ ≅ ℝP³ diffeo |
| **K6′b** | The 16-fold boundary weld `K3 := Q ∪ 16×E`; closed smooth 4-manifold. **No van Kampen** (fact 1) | `SmoothWeld → IsManifold` (#128), seam collar + boundary identification (#136), disjointness from K3-brick's finite fixed set | iterating the weld 16× (bookkeeping only — same mechanism each time) |
| **K7** | b₂ = 22: MV over the 16 welds; rank 6 (τ-invariant image of H₂(T⁴) = ℤ⁶, banked K1-a) + rank 16 (exceptional zero-sections) | relative MV/LES + excision-bridge machinery (#141, #154, the capstone MV stack); `KummerHomologyT4Full` | the invariant-subspace + weld-MV rank accounting |
| **K8a** | even (pkg, fact 3) + unimodular (pd) + **σ = −16 via Novikov additivity**: σ(K3) = σ(Q) + 16·σ(E), σ(E) = −1 (single (−2)-class), σ(Q) = 0 | σ-additivity (#164 `intFundClassSum` arc), Thom σ bordism-invariance (#169 hbord), `interMatrix`/`latticeSig` | the weld-additivity instantiation + σ(Q) = 0 |
| **K8b** | **ROUTE (i) ADJUDICATED (codex xhigh, 2026-07-20, det-argument + inventory VETTED — `scratchpad/codex_K8b_adjudication.md`): the scoped classification hybrid.** ⚠ Route (ii) naïve base-change is ARITHMETICALLY IMPOSSIBLE (naïve Gram `U(2)³⊕⟨−2⟩¹⁶` has \|det\| = 2²²; k3Form unimodular; det(PᵀGP) = det(P)²·det(G) can never be ±1) — the honest (ii) needs the index-2¹¹ saturated basis (Kummer lattice 2⁵ + six mixed glue classes 2⁶; Bryan–Pietromonaco L4.10, Garbagnati P3.3) = ~85% new geometry. Route (i) plan: reuse the REAL in-tree engine (`exists_hyperbolic_congr` σ=0 ⟹ H-blocks; `IntCongr.hyp_block`; splits) generalized to indefinite residual signature → split H³ off rank-22/σ=−16 → **THE hard interior brick = `stable_neg_rank16` (H ⊕ D ≅ H ⊕ 2(−E₈) for neg-def even unimodular rank-16 D — the ONE-hyperbolic stabilization; NOTE definite rank-16 uniqueness is FALSE (E₈² vs D₁₆⁺), stabilization essential)** → re-block to k3Form. 7–10 bricks, ~1,600–2,900 lines; high-risk components = the odd-indefinite/char-vector reduction (600–1,100) + the stable absorption (350–650). **Fable-or-codex-class for the interior brick.** Doc-drift fixed: SpinRokhlinInterface.lean STATUS corrected (the E₈-sum existence was overstated). | `exists_hyperbolic_congr` + IntCongr engine + 8∣σ divisibility + HM isotropy | the indefinite-residual split generalization + `stable_neg_rank16` |
| **K9** (unchanged) | spin + `StrMfd` packaging on `𝓡 4` (even form ⟹ w₂ = 0 via the banked Wu machinery) | stock StrMfd templates (S⁴/sphereProdSM/rp4SM); the `𝔼¹⁴ ≃ₗᵢ 𝔼⁴` re-chart | the K3-instance packaging |
| **K10** (unchanged) | `SpinSigmaAtomPkg` + `K3RealizingElement` assembly | `sphere4IntOrientation`/`sphere4IntPoincareDuality` templates; `K3RealizingElement.presentationRow` (auto-fires the row) | the `IntOrientation.redCompat` mod-2 comparison at K3 |

**Dropped from the critical path:** the singular-quotient carrier (K4-as-stated), van Kampen /
π₁ (K6 sub-wall — fact 1), and the "disclosed-atom" posture for K1/K7/K8 (operator Option A:
build UNCONDITIONALLY; K1's 3H Gram = the EZ keystone, Fable in flight).

## Dependency structure + dispatch plan

```
K2 ─→ K3 ─→ K4′ ─→ K5′ ─┐
                          ├─→ K6′b ─→ K7 ─→ K8a ─┐
        K6′a (INDEPENDENT)┘                       ├─→ K9 ─→ K10
        K1-b EZ (Fable, in flight) ──→ K8 3H part┘
        K8b (algebra, independent of all geometry once K8a's numerics are fixed)
```

- **Wave K-I (2 parallel workers when slots free):** {K2 + K3 + K4′} (one block — the
  τ/fixed-point/excision chain) ∥ {K6′a} (fully independent concrete bundle).
- **Wave K-II:** K5′ (needs K4′; ℝP⁴-template worker).
- **Wave K-III:** K6′b (the weld; forward the `chartW6` local-instance friction law).
- **Wave K-IV:** K7 ∥ K8b-scoping; then K8a; then K9/K10.
- K8b route decision: at Wave-K-IV open, run a short in-tree scoping (what exactly
  `EvenUnimodularHyperbolic` provides) + optionally a research-scout on formalized
  even-unimodular classifications; then choose (i) vs (ii). If (i): Fable.

## Risks / open questions (tracked, not blocking Wave K-I)

1. **σ(Q) = 0** (K8a): believed classical (the quotient's form is the invariant 3H rescaled —
   σ = 0 regardless); needs an in-tree proof route — likely via the K7 MV basis directly
   rather than an abstract argument. Revisit at Wave K-IV with K7's basis in hand.
2. **The ∂E ≅ ℝP³ identification** (K6′a) must match K5′'s boundary chart PRESENTATION of ℝP³
   (antipodal-quotient of S³) — fix ONE presentation (the S³/±1 quotient charts) in BOTH bricks
   from the start; this is the seam-mismatch failure mode the 5qF collar work hit.
3. **Rank-6 invariant image** (K7): τ acts as −1 on H₁(T⁴) = ℤ⁴ hence as +1 on H₂ = Λ²(ℤ⁴) —
   the FULL ℤ⁶ is invariant. The rank-6 contribution is the image in the quotient-resolution,
   not a proper invariant subspace. Phrase K7 accordingly (image classes, not fixed sublattice).
