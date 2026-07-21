# codex_strength_audit_20260721

> **Codex dossier — the run's FINAL DELIVERABLE only.** Harvested 2026-07-21 by `scripts/codex_dossier.py`.
> The raw transcript (1,300,531 bytes) is ephemeral and is deliberately NOT in the repo: reading it
> would overflow the orchestrator and defeat the point of using a second provider.
> Source: `codex_strength_audit_20260721.md`.

**Question asked:** (record it in CODEX_INDEX.md)

## Run metadata

```
workdir: /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean
model: gpt-5.6-sol
provider: openai
approval: on-request
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019f8499-e2d3-7482-9908-a835c9d33108
```

## Deliverable

# Adversarial strength audit

Audit baseline: HEAD `3315bbf5c2e2e5a0a8c136fb3df924581b88261d`. Read-only throughout; no files generated or edited. The pre-existing worktree change in `SKEFTHawking/KernelNoGos.lean` remained untouched. I inspected source and existing `.olean` artifacts rather than running a write-producing rebuild.

## BLOCKER

### 1. “Separability” does not satisfy the project’s separability predicate

[ElectricComonoid.lean:36](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SymTFT/ElectricComonoid.lean:36) works over an arbitrary `CommRing k`. The headliner proves only

`electricComul ≫ electricMul = 𝟙 + 𝟙`

at [ElectricComonoid.lean:228](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SymTFT/ElectricComonoid.lean:228) and [ElectricComonoid.lean:239](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SymTFT/ElectricComonoid.lean:239). But the project’s strengthened definition requires `Δ ≫ μ = 𝟙` exactly at [FrobeniusAlgebra.lean:144](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SymTFT/FrobeniusAlgebra.lean:144). No theorem constructs `IsSeparableAlgebra (unitPlusElectricObj k)`. In characteristic two, the proved composite is zero, not the identity.

The two Frobenius laws themselves are genuine four-corner calculations, not vacuous. The weakness is specifically the “separability/S2 apex complete” claim.

**Repair:** under an explicit invertibility hypothesis for `2 : k`, construct the normalized comonoid with `Δ' = ½Δ` and correspondingly normalized counit, reprove its comonoid/Frobenius laws, and land actual `IsFrobeniusAlgebra` and `IsSeparableAlgebra` declarations. Retain the existing theorem as the unnormalized FP-dimension computation.

### 2. The welded Kummer carrier still has no bridge into the row-side K3 element

The K7 work is carrier-faithful: `KummerK3` really is the quotient of `FreeQuotient ⊕ (EIndex × ResE)` along the pinned RP³ seams at [KummerWeld.lean:184](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerWeld.lean:184), and `kummerK3_b2_window` targets its actual singular `H₂` at [KummerPuncturedMV.lean:467](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerPuncturedMV.lean:467).

But `K3RealizingElement` still starts from an unrelated, freely supplied `StrMfd`, orientation, basis, Poincaré duality package, and intersection-form congruence at [PinPlusKTSpinSigmaStock.lean:253](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTSpinSigmaStock.lean:253). The repository explicitly leaves its K9/K10 packaging open at [KummerK3Base.lean:105](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerK3Base.lean:105). There is no declaration connecting `KummerWeld.KummerK3` to `K3RealizingElement`, `hCob`, `hBase`, or the σ = −16 row.

The window is strong enough to exclude hidden rank six: its injective `ℤ⁶ × ℤ¹⁶ → H₂(K3)` forces a rank-22 free subgroup, and the doubled-class condition prevents additional rational rank. It does **not** prove the full target `H₂(K3) ≃ ℤ²²`, eliminate possible 2-primary extension/torsion, or calculate the intersection form.

**Repair:** construct the `𝓡 4` manifold and spin carrier on the welded quotient, an integral orientation and explicit rank-22 basis, prove torsion-freeness/extension closure, calculate the Gram matrix—including Q-side/exceptional cross terms—and package that same carrier into `SpinSigmaAtomPkg` and `K3RealizingElement`.

## MAJOR

### 3. B0 and B1 are disconnected; `toLeaves` is an interface wrapper, not a cap construction

B0 advertises `WuNullCarrier` as the branch input to B1 at [PinPlusKTWuSectorSplit.lean:21](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTWuSectorSplit.lean:21), but B1 does not import B0 and contains no theorem constructing a bounding datum from it. B1 acknowledges that inhabitation is open at [PinPlusKTRankZeroBounding.lean:33](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTRankZeroBounding.lean:33).

The hard conclusions are supplied as fields:

- the exact-boundary bounding manifold at [PinPlusKTRankZeroBounding.lean:89](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTRankZeroBounding.lean:89);
- the handle presentation, weld, presentation homeomorphism, and endpoint glue equality at [PinPlusKTRankZeroBounding.lean:143](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTRankZeroBounding.lean:143).

`toLeaves` merely repackages those supplied fields at [PinPlusKTRankZeroBounding.lean:186](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTRankZeroBounding.lean:186). It does have exactly the `TraceMembraneLeaves (capstoneB …) σ τ` type expected as the `ml` input of `traceTethered_of_leaves` at [PinPlusTraceMembranePresented.lean:147](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceMembranePresented.lean:147); there is no type-transport gap. It remains uncalled, and the independent `TraceWAdmLeaves` input is still required.

**Repair:** build an actual `WuNullCarrier → RankZeroSurfaceBoundingDatum` construction, construct the anchored handle/weld data, then provide a theorem composing `toLeaves` with the corresponding `TraceWAdmLeaves` into the row-side tethered consumer.

### 4. B1’s advertised pin content is consumer-dead and rank-zero trivial

`pinCompat` is described as irreducible, load-bearing Pin⁻ content at [PinPlusKTRankZeroBounding.lean:97](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTRankZeroBounding.lean:97), but `toLeaves` does not use it. The only theorem consuming it, `membraneSpinKill`, simply projects the hypothesis through an existing implication at [PinPlusKTRankZeroBounding.lean:202](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTRankZeroBounding.lean:202), and that theorem has no downstream use.

Moreover, the admitted `toLeaves` path assumes `[IsEmpty (Fin τ.n)]`. The membrane’s substantive `hq` and `hlagK` fields are discharged with `Subsingleton.elim` at [PinPlusCharPairEmptySourceRealization.lean:525](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairEmptySourceRealization.lean:525), and the same zero-vector argument makes `KernelSpinVanishing` content-free. Nothing downstream needs nonzero-rank information.

There is a second dormant semantic risk: `pinCharSurfaceOfBundled` chooses the Kronecker-dual H₁ coordinates at [PinPlusKTRankZeroBounding.lean:65](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusKTRankZeroBounding.lean:65), whereas `τ.hpolar` ties `q.B` to cup products in the original H¹ coordinates at [PinPlusCharPairData.lean:1447](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairData.lean:1447). No two-dimensional Poincaré-duality theorem proves these are the same identification. Rank zero masks the mismatch; nonzero reuse would not.

**Repair:** build the surface PD bridge and define/prove `H1Iso` via `basis ∘ PD⁻¹`, including an equality between `Bounding.kernelL` and `ker boundingBInc`. Then carry an actual Pin⁻ extension/restriction datum through `TraceMembraneLeaves` so its spin consequence is used by the tethered consumer.

### 5. The B2 Stokes block is substantive but stranded before the promised cross value

The +140-line block contains real cup/Stokes, seam restriction, and chain-cancellation arguments at [SphereProdStokesPeel.lean:63](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProdStokesPeel.lean:63) and [SphereProdStokesPeel.lean:171](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProdStokesPeel.lean:171). It is not vacuous. But the module itself says the polar-cover geometry and final pairing are still open at [SphereProdStokesPeel.lean:22](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProdStokesPeel.lean:22), and none of its declarations feeds the actual `hcross` parameter required at [SphereProdGramPinReduce.lean:66](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SphereProdGramPinReduce.lean:66).

**Repair:** instantiate the generic two-leg theorem on the concrete S² polar cover, identify the seam class via the MV boundary map, execute the torus right-peel, prove `hcross = 1`, and feed that theorem directly to the Gram-pin consumer.

## MINOR

### 6. The resolution-boundary partial is honest, but only 16/36 transition pairs are done

`contDiffOn_reshapeConj` is a genuine composition proof at [KummerResolutionPieceBoundary.lean:1713](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerResolutionPieceBoundary.lean:1713). The eight cross-side cases are vacuous for a valid reason—the restricted sources are disjoint—and the equator is assigned to the annulus charts at [KummerResolutionPieceBoundary.lean:2059](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerResolutionPieceBoundary.lean:2059).

The final `IsManifold ResE` and smooth boundary equivalence do not exist: four annulus–annulus and sixteen annulus↔base pairs remain open at [KummerResolutionPieceBoundary.lean:2188](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerResolutionPieceBoundary.lean:2188).

**Repair:** finish those twenty transitions, dispatch the full atlas through `isManifold_of_contDiffOn`, and prove the smooth `∂E ≃ RP3` upgrade consumed by the eventual smooth welded-K3 packaging.

### 7. Several endpoint declarations are umbrella-only or otherwise stranded

The umbrella registers them, but no committed module imports/uses their headliners:

- `ElectricComonoid` — [SKEFTHawking.lean:320](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking.lean:320)
- `PinPlusKTWuSectorSplit`, `PinPlusKTRankZeroBounding` — [SKEFTHawking.lean:4592](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking.lean:4592)
- `KummerResolutionPieceBoundary` — [SKEFTHawking.lean:4687](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking.lean:4687)
- `KummerRP3TransferHomology` — [SKEFTHawking.lean:4705](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking.lean:4705)
- `KummerPuncturedMV` — [SKEFTHawking.lean:4720](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking.lean:4720)
- `SphereProdStokesPeel` — [SKEFTHawking.lean:4724](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking.lean:4724)

Specific stranded declarations include `rankZero_brown_preserved`, `Hmap_congr`, `projHomRP3_transferHml`, `qH2EquivInt`, and the final `kummerK3_b2_window`.

`KummerK7SeamCoverNoGo` is umbrella-only in committed HEAD. The existing dirty worktree adds its intended `KernelNoGos` registration, but that registration is not part of the audited merged baseline.

## Confirmed strong / no finding

- **B0:** `pushedSurfClass_eq_zero_iff_wuNull` performs genuine work in both directions; the reverse uses Kronecker faithfulness, not packaging.
- **Rank-zero specialization:** `hq` and `hlagK` really are content-free at rank zero, and the current consumer never needs nonzero-rank content.
- **RP³:** `RP3E` is a fresh Euclidean presentation, but [KummerRP3HomologyUnconditional.lean:124](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerRP3HomologyUnconditional.lean:124) supplies an explicit homeomorphism to the pinned `RP3`. `rp3H3EquivInt_unconditional` is transported through the good-cover and Smith engines, not a chosen-carrier shell.
- **Q:** `Qtop` is definitionally `TopCat.of FreeQuotient` at [KummerQuotientCovering.lean:26](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerQuotientCovering.lean:26), the same quotient used by the weld. `qH2EquivInt` is an actual Smith/MV computation.
- **K7:** `exceptionalEmbed` lands directly in `Homology KummerK3top 2`, and its injectivity proof uses the actual MV sum at [KummerK7MVAssembly.lean:430](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerK7MVAssembly.lean:430).
- **No-go:** `k7SeamCoverHyp_false` negates the opener’s exact fully qualified hypothesis, not a reconstructed strawman; compare [KummerK7Opener.lean:125](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerK7Opener.lean:125) with [KummerK7SeamCoverNoGo.lean:358](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KummerK7SeamCoverNoGo.lean:358).
- **Suspicious proof patterns:** the inspected `rfl` proofs are quotient-lift evaluation or functoriality lemmas; `Hmap_comp` first takes a quotient representative. The only material `Subsingleton.elim` use is the honest empty-index collapse. No scoped declaration contains a live `sorry`, local axiom, `native_decide`, or `True := trivial` body.

## Carrier-connectivity table

| Headliner | Actual consumer | Carrier-faithful? |
|---|---|---|
| Electric Frobenius laws | **STRANDED**, terminal S2 output | Y for Frobenius; N for claimed separability |
| B0 Wu-sector split | **STRANDED** | Y |
| `ofRankZero` / `ofRankZeroTauMembrane` | `RankZeroSurfaceWeldAnchor.toLeaves` | Y |
| `RankZeroSurfaceWeldAnchor.toLeaves` | **STRANDED**; type-compatible with `traceTethered_of_leaves` | Needs B0→B1 construction and WAdm bridge |
| RP³ top/unconditional table | K7 `interH3EquivInt`, `interH4_eq_zero` | Y |
| RP³ transfer relation | **STRANDED** | Y |
| `KummerWeldFiberFlow` | K7 thickened MV and seam no-go | Y |
| K7 MV / `exceptionalEmbed` | Q-side solve and K3 window | Y, actual welded K3 |
| `k7SeamCoverHyp_false` | Committed: **STRANDED**; dirty tree adds registry alias | Y, exact opener hypothesis |
| Q covering/transfer/Smith/T⁴-cycle engine | `qH2EquivOfWindow`, puncture finale | Y |
| `punctureH2EquivFin6` | `qH2EquivInt`, K3 window | Y |
| `qH2EquivInt` | **STRANDED** as a named declaration | Y |
| `kummerK3_b2_window` | **STRANDED** from `K3RealizingElement` and row assembly | Y internally; needs carrier-to-row bridge |
| Sphere-product Stokes peel | **STRANDED** before `hcross` | Needs concrete S²×S² bridge |
| Resolution 16-pair block | **STRANDED**, partial atlas | Y for `ResE`; final smooth structure absent |

## Verdict

The RP³→K7→Q→puncture computation is structurally sound and carrier-faithful: its principal equivalences and injectivity results are real computations on the intended quotient and welded spaces. The recent arc as a whole is not yet structurally closed: B0/B1 and B2 remain interface/partial endpoints, and the Kummer homology result never reaches the row-side K3 object. The single highest-risk weakness is the missing bridge from the actual welded `KummerK3` carrier to `K3RealizingElement`; until its smooth/spin/orientation/basis/intersection-form package is built, the largest completed arc cannot support the σ = −16, `hCob`, or `hBase` consumers.
