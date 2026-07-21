# codex_hcolD_B1_design

> **Promoted from session scratchpad 2026-07-21.** The raw ~1-2 MB codex
> transcript was session-scoped and would have been lost on cleanup; this is the run's
> **final deliverable** plus its run metadata. Source transcript: `codex_hcolD_B1_design.md` in the
> session scratchpad (ephemeral). Cited by `LAB_NOTEBOOK_INDEX.md`.

## Run metadata

```
workdir: /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean
model: gpt-5.6-sol
provider: openai
approval: on-request
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019f837a-f345-75b2-a21b-a7733d256675
```

## Deliverable

# Design dossier: `RankZeroSurfaceBoundingDatum`

## Recommendation

Use **(c): split B1 into a free geometric core B1a and capstone-specific weld plumbing B1b**.

The crucial implementation rule is: B1b must reuse B1a’s carrier type literally as `QC`. Then `(capstoneEmptySourceReal …).Q` reduces definitionally to that same type, and its chart is B1a’s chart without transport. This follows the landed `#163` pattern, where [`capstoneHW`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneMembraneWeld.lean:81) is `Homeomorph.refl _` because the carriers coincide definitionally.

Option (a), with independently retyped free and welded carriers, would create unnecessary obligations for charts, smoothness, exact boundary, homology bases, and glue conjugation. Option (b) would bury the mathematical “Σ bounds” statement inside B2’s long capstone telescope and make it difficult to reuse or audit.

## A. Proposed structures

First add a lossless adapter from the bundled characteristic pair to the existing Pin⁻ surface shadow:

```lean
noncomputable def pinCharSurfaceOfBundled
    {t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)}
    (τ : CharPairStrBundled (𝓡 4) t) :
    CharSurface.PinCharSurface t.M 0 where
  -- [IN-TREE: τ.surf, τ.emb, τ.embSmooth]
  F :=
    { M := τ.surf.M
      f := τ.emb
      hf := τ.embSmooth.continuous }

  -- [IN-TREE: τ.embInj]
  emb := τ.embInj

  -- [IN-TREE: τ.n, τ.q]
  ι := Fin τ.n
  Q := τ.q

  -- [IN-TREE: homologyBasisOfCohomologyBasis τ.basis]
  H1Iso :=
    SingularKroneckerBasisBridge.homologyBasisOfCohomologyBasis τ.basis
```

This is important: the Pin⁻ shadow is not a freshly chosen quadratic enhancement. It is literally `τ.q`, placed on the genuine `H₁(τ.surf; ℤ/2)` coordinates derived from `τ.basis` using [`homologyBasisOfCohomologyBasis`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularKroneckerBasisBridge.lean:135).

### B1a: free geometric core

```lean
structure RankZeroSurfaceBoundingDatum
    {t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)}
    (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty (Fin τ.n)] where

  /-- B0's null-side normal form.

  Store the pushed-class equation rather than `WuNullCarrier` so the datum
  remains usable in the empty-carrier branch, where `WuNullCarrier` cannot
  be formed without `[Nonempty t.M]`.
  -/
  -- [IN-TREE: pushedSurfClass, pushedSurfClass_eq_zero_iff_wuNull]
  wuNullClass :
    PinPlusKTWuSectorSplit.pushedSurfClass τ = 0

  /-- A compact smooth 3-manifold whose entire boundary is the given Σ. -/
  -- [IN-TREE: PinCharSurface.Bounding]
  -- [NEW-GEOMETRIC: construct Q and a smooth injection
  --   τ.surf.M → Q with range exactly ∂Q]
  bound :
    (pinCharSurfaceOfBundled τ).Bounding ((𝓡 2).prod (𝓡∂ 1))

  /-- The Hausdorff certificate B4 requires. -/
  -- [IN-TREE: T2Space]
  -- [NEW-GEOMETRIC: prove for the constructed Q]
  QT2 : T2Space bound.V

  /-- The boundary Pin⁻ spin bit extends over classes killed in Q. -/
  -- [IN-TREE: KernelSpinVanishing,
  --   membraneSpinKill_of_kernelSpinVanishing]
  -- [NEW-GEOMETRIC: prove from the Pin⁻ bounding construction;
  --   rank zero may discharge its current algebraic shadow]
  pinCompat : bound.KernelSpinVanishing

  /-- Coordinate dimension for H₁(Q; ℤ/2). -/
  -- [IN-TREE: the `mid` input of capstoneEmptySourceReal]
  -- [NEW-GEOMETRIC: obtain from a finite handle/CW presentation of Q]
  mid : ℕ

  /-- The interior basis required by the tied membrane realization. -/
  -- [IN-TREE: Homology, GeoRealizationTied.eQ]
  -- [NEW-GEOMETRIC: construct from finite-dimensional H₁(Q; ℤ/2)]
  eQ :
    Homology (TopCat.of bound.V) 1 ≃ₗ[ZMod 2]
      (Fin mid → ZMod 2)
```

The exact-boundary package is already frozen by [`PinCharSurface.Bounding`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/CharSurfaceBounding.lean:67). It supplies:

- `ChartedSpace` and `IsManifold` for the correct three-dimensional corners model;
- `CompactSpace`;
- a smooth injective boundary map;
- `Set.range e = ((𝓡 2).prod (𝓡∂ 1)).boundary V`.

Derived B4 views should be definitions, not additional fields:

```lean
namespace RankZeroSurfaceBoundingDatum

def QC (B : RankZeroSurfaceBoundingDatum τ) : TopCat :=
  TopCat.of B.bound.V

def QCompact (B : RankZeroSurfaceBoundingDatum τ) :
    CompactSpace (B.QC : Type) :=
  B.bound.compactV

def ιY (B : RankZeroSurfaceBoundingDatum τ) :
    C((τ.surf.M : Type), (B.QC : Type)) :=
  ⟨B.bound.e, B.bound.he_smooth.continuous⟩

theorem hιY (B : RankZeroSurfaceBoundingDatum τ) :
    letI := B.QT2
    IsClosedEmbedding B.ιY := by
  letI := B.QT2
  exact B.bound.he_smooth.continuous.isClosedEmbedding B.bound.he_inj

noncomputable def chartQ
    {s : SingularManifold.{0} PUnit.{1} 0 (𝓡 4)}
    (σ : CharPairStrBundled (𝓡 4) s)
    [IsEmpty σ.surf.M]
    (B : RankZeroSurfaceBoundingDatum τ) :
    letI := B.QT2
    letI := B.QCompact
    ChartedSpace MembraneModel
      ↑(capstoneEmptySourceReal σ τ B.QC B.ιY B.hιY B.mid B.eQ).Q := by
  change ChartedSpace MembraneModel B.bound.V
  exact B.bound.chartV

end RankZeroSurfaceBoundingDatum
```

The final `change` should succeed because:

1. `capstoneEmptySourceReal` sets `Q := QC` definitionally; and
2. `MembraneModel` is definitionally the model space of `(𝓡 2).prod (𝓡∂ 1)`.

### B1b: capstone anchor

```lean
structure RankZeroSurfaceWeldAnchor
    (s t : SingularManifold.{0} PUnit.{1} 0 (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S)
    (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam :
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion
        ⊆ cd.seamNbhd)
    (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)
    (σ : CharPairStrBundled (𝓡 4) s)
    (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)] [IsEmpty (Fin τ.n)]
    (B : RankZeroSurfaceBoundingDatum τ) where

  -- [IN-TREE: HandleAttachment]
  -- [NEW-GEOMETRIC: present B.bound.V by the membrane handle attachment]
  HAQ : HandleAttachment.{0, 0}

  -- [IN-TREE: HandleAttachment.Weld]
  -- [NEW-GEOMETRIC: weld the presented Q into the fixed KT capstone]
  weld :
    HandleAttachment.Weld HAQ
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj)

  -- [IN-TREE: exact B4 `hQ` type]
  -- [NEW-GEOMETRIC: presentation homeomorphism; no carrier retyping]
  hQ :
    letI := B.QT2
    letI := B.QCompact
    ((capstoneEmptySourceReal
        σ τ B.QC B.ιY B.hιY B.mid B.eQ).Q : Type) ≃ₜ HAQ.carrier

  -- [IN-TREE: exact B4 `glueτ` equation]
  -- [NEW-GEOMETRIC: prove the target boundary factorization]
  glueτ :
    letI := B.QT2
    letI := B.QCompact
    ∀ x : ↑(sub
        (capstoneEmptySourceReal
          σ τ B.QC B.ιY B.hιY B.mid B.eQ).Uᶜ),
      weld.carrierMap
          (hQ
            ((capstoneEmptySourceReal
                σ τ B.QC B.ιY B.hιY B.mid B.eQ).ι
              (subInclCM
                (capstoneEmptySourceReal
                  σ τ B.QC B.ιY B.hιY B.mid B.eQ).Uᶜ x)))
        =
      (capstoneB s t S hS φ hφ hφinj cd hseam d).e
        (Sum.inr
          (τ.emb
            ((capstoneEmptySourceReal
                σ τ B.QC B.ιY B.hιY B.mid B.eQ).homτ x)))
```

Do not add `chartQ` to B1b. It is derived from B1a, so storing it again would permit incoherent duplicate atlas choices.

## B. Composition into B4

The wrapper is direct:

```lean
noncomputable def RankZeroSurfaceWeldAnchor.toLeaves
    (B : RankZeroSurfaceBoundingDatum τ)
    (A : RankZeroSurfaceWeldAnchor
      s t S hS φ hφ hφinj cd hseam d σ τ B) :
    TraceMembraneLeaves
      (capstoneB s t S hS φ hφ hφinj cd hseam d) σ τ :=
  letI := B.QT2
  letI := B.QCompact
  TraceMembraneLeaves.ofRankZeroTauMembrane
    s t S hS φ hφ hφinj cd hseam d σ τ
    B.QC B.QT2 B.QCompact
    B.ιY B.hιY B.mid B.eQ
    A.HAQ A.weld A.hQ A.glueτ
    (B.chartQ σ)
```

Field flow:

| B4 input | Source |
|---|---|
| `QC` | `TopCat.of B.bound.V` |
| `QT2` | `B.QT2` |
| `QCompact` | `B.bound.compactV` |
| `ιY` | `B.bound.e` with `he_smooth.continuous` |
| `hιY` | compact-to-Hausdorff `Continuous.isClosedEmbedding` |
| `mid`, `eQ` | B1a |
| `HAQ`, `weld`, `hQ`, `glueτ` | B1b |
| `chartQ` | definitional reduction to `B.bound.chartV` |
| `hq`, `hlagK` | discharged by [`ofRankZero`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairEmptySourceRealization.lean:525) |

No transport lemma is required beyond named `change`-based API locks such as `chartQ` and `hιY`.

If distinct free and welded carrier types were allowed, new machinery would be needed for at least:

- `PinCharSurface.Bounding.transport`;
- smooth/diffeomorphic, not merely homeomorphic, transport of `IsManifold`;
- naturality of `ModelWithCorners.boundary`;
- conjugation of the exact boundary embedding;
- `H₁` basis transport through a homeomorphism-induced equivalence;
- `hQ` and `glueτ` conjugation.

The existing `chartedSpaceOfHomeomorph` only creates a plain charted-space structure; it does not transfer the full bounding package. That makes option (a) structurally inferior.

After `toLeaves`, the existing route is:

```text
toLeaves
→ traceTethered_of_leaves
→ symmBorTethered, when the collapse direction must be reversed
→ staged T2 bordism equality
→ SectorIsGeometric
→ kt_equiv_zmod16_of_residuals_sector
```

The relevant endpoints are [`traceTethered_of_leaves`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceMembranePresented.lean:147) and [`symmBorTethered`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairBorTethered.lean:233).

## C. Pin compatibility

The recommended exact field is:

```lean
pinCompat : B.bound.KernelSpinVanishing
```

Its assertion is:

```lean
∀ l ∈ B.bound.kernelL,
  (pinCharSurfaceOfBundled τ).Q.toZ2 l = 0
```

Thus every boundary class killed in `H₁(Q; ℤ/2)` has bounding induced spin bit. The in-tree theorem `membraneSpinKill_of_kernelSpinVanishing` then yields [`MembraneSpinKill`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/CharSurfaceMembrane.lean:293), the repository’s explicitly named Pin⁻ atom on detection-coherent framed circles.

The ambient tie is preserved because:

- the surface map is exactly `τ.emb`;
- the enhancement is exactly `τ.q`;
- its `H₁` coordinates are derived from `τ.basis`, not independently chosen;
- `τ.hpolar` and `τ.hchar` remain the ambient characteristic-surface ties.

`τ.cert : PinPlusCertK` must not be reused as the pin-compatibility field. It is a Wu/`w₂` admissibility certificate on the four-dimensional carrier, not a Pin⁻ structure on either `Σ` or `Q`.

There is no project type representing an actual Pin⁻ principal structure and its restriction to the boundary. Consequently, this is the strongest honest in-tree formulation. At rank zero its algebraic shadow may self-discharge; it must not be advertised as a construction of a literal principal Pin⁻ bundle. If literal restriction equality is later required, that is new substrate and a separate Fable-tier front.

## D. Anti-vacuity

The load-bearing field is `bound`, specifically the conjunction of:

```lean
IsManifold ((𝓡 2).prod (𝓡∂ 1)) 0 bound.V
CompactSpace bound.V
Function.Injective bound.e
Set.range bound.e =
  ((𝓡 2).prod (𝓡∂ 1)).boundary bound.V
```

This blocks the principal fakes:

- **Point `Q`:** cannot carry the required local three-dimensional half-space manifold structure for a nonempty surface boundary.
- **Reuse `Q := Σ`:** excluded by the three-dimensional chart and `IsManifold` fields. The existing tether-gate analysis explains why the [`MembraneModel` chart is substantive](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairTetherGate.lean:72).
- **`Σ × [0,1]`:** its boundary contains two surface ends. Mapping only one end cannot satisfy the exact range-equals-boundary equation.
- **Unrelated abstract cap:** B1b’s `weld`, `hQ`, and pointwise `glueτ` force the same `Q` into the actual capstone carrier and anchor its boundary to the actual τ-end.

No field classifies `Σ` as a union of spheres. No normal Euler or framing-zero hypothesis appears. This respects the settled warning that rank zero plus `hchar` does not force normal Euler zero; the one-sphere/3-handle shortcut remains unavailable without extra framing data ([settled fork](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/dev-loops/SETTLED_FORKS.md:404)).

## E. Risks and sizing

| Risk | Assessment and tier |
|---|---|
| `WuNullCarrier` only gives homological nullity, not an embedded smooth bounding 3-manifold | **High, Fable.** This is the mathematical heart of B1. Do not replace it with a classification-by-spheres assertion. |
| Constructing `bound.V`, its atlas, and exact boundary equality | **High, Fable**, unless B2 supplies an explicit handle-built model whose atlas can reuse the disk/Kummer precedents. |
| Literal Pin⁻ extension is absent from the substrate | **High, Fable** if genuinely required. The current `KernelSpinVanishing`/`MembraneSpinKill` shadow is **Opus** at rank zero. |
| `mid`/`eQ` | **Medium.** Opus when a finite handle/CW presentation supplies finite-dimensional `H₁`; otherwise a missing general finiteness result can promote it to Fable. |
| `HAQ`, `weld`, `hQ`, `glueτ` | **High, Fable geometric construction.** These are B1b/B2 interface obligations, not transport bookkeeping. |
| Adapter, `QC`/`ιY` views, closed-embedding proof, chart reduction, B4 wrapper | **Low, Opus.** Mostly  definitional and existing lemmas. |
| Definitional equality becoming fragile after refactors | **Low–medium, Opus.** Protect it with named `change`-based lemmas and small compilation tests. |
| Empty carrier cannot instantiate `WuNullCarrier` | **Low, Opus.** Store `pushedSurfClass τ = 0`; split `IsEmpty`/`Nonempty` only when invoking B0’s iff theorem. |

Estimated interface size:

- adapter and B1a: 35–50 LOC;
- derived B4 views: 25–40 LOC;
- B1b exact telescope: 45–65 LOC;
- composition and smoke tests: 25–40 LOC.

Total: approximately **130–195 LOC**, excluding the actual geometric inhabitants. Those inhabitants are the dominant work and may be several hundred lines per explicit handle model.

This was a read-only inspection; no files were changed and no Lean build was run.


tokens used
382,782
# Design dossier: `RankZeroSurfaceBoundingDatum`

## Recommendation

Use **(c): split B1 into a free geometric core B1a and capstone-specific weld plumbing B1b**.

The crucial implementation rule is: B1b must reuse B1a’s carrier type literally as `QC`. Then `(capstoneEmptySourceReal …).Q` reduces definitionally to that same type, and its chart is B1a’s chart without transport. This follows the landed `#163` pattern, where [`capstoneHW`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneMembraneWeld.lean:81) is `Homeomorph.refl _` because the carriers coincide definitionally.

Option (a), with independently retyped free and welded carriers, would create unnecessary obligations for charts, smoothness, exact boundary, homology bases, and glue conjugation. Option (b) would bury the mathematical “Σ bounds” statement inside B2’s long capstone telescope and make it difficult to reuse or audit.

## A. Proposed structures

First add a lossless adapter from the bundled characteristic pair to the existing Pin⁻ surface shadow:

```lean
noncomputable def pinCharSurfaceOfBundled
    {t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)}
    (τ : CharPairStrBundled (𝓡 4) t) :
    CharSurface.PinCharSurface t.M 0 where
  -- [IN-TREE: τ.surf, τ.emb, τ.embSmooth]
  F :=
    { M := τ.surf.M
      f := τ.emb
      hf := τ.embSmooth.continuous }

  -- [IN-TREE: τ.embInj]
  emb := τ.embInj

  -- [IN-TREE: τ.n, τ.q]
  ι := Fin τ.n
  Q := τ.q

  -- [IN-TREE: homologyBasisOfCohomologyBasis τ.basis]
  H1Iso :=
    SingularKroneckerBasisBridge.homologyBasisOfCohomologyBasis τ.basis
```

This is important: the Pin⁻ shadow is not a freshly chosen quadratic enhancement. It is literally `τ.q`, placed on the genuine `H₁(τ.surf; ℤ/2)` coordinates derived from `τ.basis` using [`homologyBasisOfCohomologyBasis`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularKroneckerBasisBridge.lean:135).

### B1a: free geometric core

```lean
structure RankZeroSurfaceBoundingDatum
    {t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)}
    (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty (Fin τ.n)] where

  /-- B0's null-side normal form.

  Store the pushed-class equation rather than `WuNullCarrier` so the datum
  remains usable in the empty-carrier branch, where `WuNullCarrier` cannot
  be formed without `[Nonempty t.M]`.
  -/
  -- [IN-TREE: pushedSurfClass, pushedSurfClass_eq_zero_iff_wuNull]
  wuNullClass :
    PinPlusKTWuSectorSplit.pushedSurfClass τ = 0

  /-- A compact smooth 3-manifold whose entire boundary is the given Σ. -/
  -- [IN-TREE: PinCharSurface.Bounding]
  -- [NEW-GEOMETRIC: construct Q and a smooth injection
  --   τ.surf.M → Q with range exactly ∂Q]
  bound :
    (pinCharSurfaceOfBundled τ).Bounding ((𝓡 2).prod (𝓡∂ 1))

  /-- The Hausdorff certificate B4 requires. -/
  -- [IN-TREE: T2Space]
  -- [NEW-GEOMETRIC: prove for the constructed Q]
  QT2 : T2Space bound.V

  /-- The boundary Pin⁻ spin bit extends over classes killed in Q. -/
  -- [IN-TREE: KernelSpinVanishing,
  --   membraneSpinKill_of_kernelSpinVanishing]
  -- [NEW-GEOMETRIC: prove from the Pin⁻ bounding construction;
  --   rank zero may discharge its current algebraic shadow]
  pinCompat : bound.KernelSpinVanishing

  /-- Coordinate dimension for H₁(Q; ℤ/2). -/
  -- [IN-TREE: the `mid` input of capstoneEmptySourceReal]
  -- [NEW-GEOMETRIC: obtain from a finite handle/CW presentation of Q]
  mid : ℕ

  /-- The interior basis required by the tied membrane realization. -/
  -- [IN-TREE: Homology, GeoRealizationTied.eQ]
  -- [NEW-GEOMETRIC: construct from finite-dimensional H₁(Q; ℤ/2)]
  eQ :
    Homology (TopCat.of bound.V) 1 ≃ₗ[ZMod 2]
      (Fin mid → ZMod 2)
```

The exact-boundary package is already frozen by [`PinCharSurface.Bounding`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/CharSurfaceBounding.lean:67). It supplies:

- `ChartedSpace` and `IsManifold` for the correct three-dimensional corners model;
- `CompactSpace`;
- a smooth injective boundary map;
- `Set.range e = ((𝓡 2).prod (𝓡∂ 1)).boundary V`.

Derived B4 views should be definitions, not additional fields:

```lean
namespace RankZeroSurfaceBoundingDatum

def QC (B : RankZeroSurfaceBoundingDatum τ) : TopCat :=
  TopCat.of B.bound.V

def QCompact (B : RankZeroSurfaceBoundingDatum τ) :
    CompactSpace (B.QC : Type) :=
  B.bound.compactV

def ιY (B : RankZeroSurfaceBoundingDatum τ) :
    C((τ.surf.M : Type), (B.QC : Type)) :=
  ⟨B.bound.e, B.bound.he_smooth.continuous⟩

theorem hιY (B : RankZeroSurfaceBoundingDatum τ) :
    letI := B.QT2
    IsClosedEmbedding B.ιY := by
  letI := B.QT2
  exact B.bound.he_smooth.continuous.isClosedEmbedding B.bound.he_inj

noncomputable def chartQ
    {s : SingularManifold.{0} PUnit.{1} 0 (𝓡 4)}
    (σ : CharPairStrBundled (𝓡 4) s)
    [IsEmpty σ.surf.M]
    (B : RankZeroSurfaceBoundingDatum τ) :
    letI := B.QT2
    letI := B.QCompact
    ChartedSpace MembraneModel
      ↑(capstoneEmptySourceReal σ τ B.QC B.ιY B.hιY B.mid B.eQ).Q := by
  change ChartedSpace MembraneModel B.bound.V
  exact B.bound.chartV

end RankZeroSurfaceBoundingDatum
```

The final `change` should succeed because:

1. `capstoneEmptySourceReal` sets `Q := QC` definitionally; and
2. `MembraneModel` is definitionally the model space of `(𝓡 2).prod (𝓡∂ 1)`.

### B1b: capstone anchor

```lean
structure RankZeroSurfaceWeldAnchor
    (s t : SingularManifold.{0} PUnit.{1} 0 (𝓡 4)) [T2Space s.M]
    (S : Set D5) (hS : IsClosed S)
    (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
    (hseam :
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion
        ⊆ cd.seamNbhd)
    (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)
    (σ : CharPairStrBundled (𝓡 4) s)
    (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)] [IsEmpty (Fin τ.n)]
    (B : RankZeroSurfaceBoundingDatum τ) where

  -- [IN-TREE: HandleAttachment]
  -- [NEW-GEOMETRIC: present B.bound.V by the membrane handle attachment]
  HAQ : HandleAttachment.{0, 0}

  -- [IN-TREE: HandleAttachment.Weld]
  -- [NEW-GEOMETRIC: weld the presented Q into the fixed KT capstone]
  weld :
    HandleAttachment.Weld HAQ
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj)

  -- [IN-TREE: exact B4 `hQ` type]
  -- [NEW-GEOMETRIC: presentation homeomorphism; no carrier retyping]
  hQ :
    letI := B.QT2
    letI := B.QCompact
    ((capstoneEmptySourceReal
        σ τ B.QC B.ιY B.hιY B.mid B.eQ).Q : Type) ≃ₜ HAQ.carrier

  -- [IN-TREE: exact B4 `glueτ` equation]
  -- [NEW-GEOMETRIC: prove the target boundary factorization]
  glueτ :
    letI := B.QT2
    letI := B.QCompact
    ∀ x : ↑(sub
        (capstoneEmptySourceReal
          σ τ B.QC B.ιY B.hιY B.mid B.eQ).Uᶜ),
      weld.carrierMap
          (hQ
            ((capstoneEmptySourceReal
                σ τ B.QC B.ιY B.hιY B.mid B.eQ).ι
              (subInclCM
                (capstoneEmptySourceReal
                  σ τ B.QC B.ιY B.hιY B.mid B.eQ).Uᶜ x)))
        =
      (capstoneB s t S hS φ hφ hφinj cd hseam d).e
        (Sum.inr
          (τ.emb
            ((capstoneEmptySourceReal
                σ τ B.QC B.ιY B.hιY B.mid B.eQ).homτ x)))
```

Do not add `chartQ` to B1b. It is derived from B1a, so storing it again would permit incoherent duplicate atlas choices.

## B. Composition into B4

The wrapper is direct:

```lean
noncomputable def RankZeroSurfaceWeldAnchor.toLeaves
    (B : RankZeroSurfaceBoundingDatum τ)
    (A : RankZeroSurfaceWeldAnchor
      s t S hS φ hφ hφinj cd hseam d σ τ B) :
    TraceMembraneLeaves
      (capstoneB s t S hS φ hφ hφinj cd hseam d) σ τ :=
  letI := B.QT2
  letI := B.QCompact
  TraceMembraneLeaves.ofRankZeroTauMembrane
    s t S hS φ hφ hφinj cd hseam d σ τ
    B.QC B.QT2 B.QCompact
    B.ιY B.hιY B.mid B.eQ
    A.HAQ A.weld A.hQ A.glueτ
    (B.chartQ σ)
```

Field flow:

| B4 input | Source |
|---|---|
| `QC` | `TopCat.of B.bound.V` |
| `QT2` | `B.QT2` |
| `QCompact` | `B.bound.compactV` |
| `ιY` | `B.bound.e` with `he_smooth.continuous` |
| `hιY` | compact-to-Hausdorff `Continuous.isClosedEmbedding` |
| `mid`, `eQ` | B1a |
| `HAQ`, `weld`, `hQ`, `glueτ` | B1b |
| `chartQ` | definitional reduction to `B.bound.chartV` |
| `hq`, `hlagK` | discharged by [`ofRankZero`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairEmptySourceRealization.lean:525) |

No transport lemma is required beyond named `change`-based API locks such as `chartQ` and `hιY`.

If distinct free and welded carrier types were allowed, new machinery would be needed for at least:

- `PinCharSurface.Bounding.transport`;
- smooth/diffeomorphic, not merely homeomorphic, transport of `IsManifold`;
- naturality of `ModelWithCorners.boundary`;
- conjugation of the exact boundary embedding;
- `H₁` basis transport through a homeomorphism-induced equivalence;
- `hQ` and `glueτ` conjugation.

The existing `chartedSpaceOfHomeomorph` only creates a plain charted-space structure; it does not transfer the full bounding package. That makes option (a) structurally inferior.

After `toLeaves`, the existing route is:

```text
toLeaves
→ traceTethered_of_leaves
→ symmBorTethered, when the collapse direction must be reversed
→ staged T2 bordism equality
→ SectorIsGeometric
→ kt_equiv_zmod16_of_residuals_sector
```

The relevant endpoints are [`traceTethered_of_leaves`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceMembranePresented.lean:147) and [`symmBorTethered`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairBorTethered.lean:233).

## C. Pin compatibility

The recommended exact field is:

```lean
pinCompat : B.bound.KernelSpinVanishing
```

Its assertion is:

```lean
∀ l ∈ B.bound.kernelL,
  (pinCharSurfaceOfBundled τ).Q.toZ2 l = 0
```

Thus every boundary class killed in `H₁(Q; ℤ/2)` has bounding induced spin bit. The in-tree theorem `membraneSpinKill_of_kernelSpinVanishing` then yields [`MembraneSpinKill`](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/CharSurfaceMembrane.lean:293), the repository’s explicitly named Pin⁻ atom on detection-coherent framed circles.

The ambient tie is preserved because:

- the surface map is exactly `τ.emb`;
- the enhancement is exactly `τ.q`;
- its `H₁` coordinates are derived from `τ.basis`, not independently chosen;
- `τ.hpolar` and `τ.hchar` remain the ambient characteristic-surface ties.

`τ.cert : PinPlusCertK` must not be reused as the pin-compatibility field. It is a Wu/`w₂` admissibility certificate on the four-dimensional carrier, not a Pin⁻ structure on either `Σ` or `Q`.

There is no project type representing an actual Pin⁻ principal structure and its restriction to the boundary. Consequently, this is the strongest honest in-tree formulation. At rank zero its algebraic shadow may self-discharge; it must not be advertised as a construction of a literal principal Pin⁻ bundle. If literal restriction equality is later required, that is new substrate and a separate Fable-tier front.

## D. Anti-vacuity

The load-bearing field is `bound`, specifically the conjunction of:

```lean
IsManifold ((𝓡 2).prod (𝓡∂ 1)) 0 bound.V
CompactSpace bound.V
Function.Injective bound.e
Set.range bound.e =
  ((𝓡 2).prod (𝓡∂ 1)).boundary bound.V
```

This blocks the principal fakes:

- **Point `Q`:** cannot carry the required local three-dimensional half-space manifold structure for a nonempty surface boundary.
- **Reuse `Q := Σ`:** excluded by the three-dimensional chart and `IsManifold` fields. The existing tether-gate analysis explains why the [`MembraneModel` chart is substantive](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusCharPairTetherGate.lean:72).
- **`Σ × [0,1]`:** its boundary contains two surface ends. Mapping only one end cannot satisfy the exact range-equals-boundary equation.
- **Unrelated abstract cap:** B1b’s `weld`, `hQ`, and pointwise `glueτ` force the same `Q` into the actual capstone carrier and anchor its boundary to the actual τ-end.

No field classifies `Σ` as a union of spheres. No normal Euler or framing-zero hypothesis appears. This respects the settled warning that rank zero plus `hchar` does not force normal Euler zero; the one-sphere/3-handle shortcut remains unavailable without extra framing data ([settled fork](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/dev-loops/SETTLED_FORKS.md:404)).

## E. Risks and sizing

| Risk | Assessment and tier |
|---|---|
| `WuNullCarrier` only gives homological nullity, not an embedded smooth bounding 3-manifold | **High, Fable.** This is the mathematical heart of B1. Do not replace it with a classification-by-spheres assertion. |
| Constructing `bound.V`, its atlas, and exact boundary equality | **High, Fable**, unless B2 supplies an explicit handle-built model whose atlas can reuse the disk/Kummer precedents. |
| Literal Pin⁻ extension is absent from the substrate | **High, Fable** if genuinely required. The current `KernelSpinVanishing`/`MembraneSpinKill` shadow is **Opus** at rank zero. |
| `mid`/`eQ` | **Medium.** Opus when a finite handle/CW presentation supplies finite-dimensional `H₁`; otherwise a missing general finiteness result can promote it to Fable. |
| `HAQ`, `weld`, `hQ`, `glueτ` | **High, Fable geometric construction.** These are B1b/B2 interface obligations, not transport bookkeeping. |
| Adapter, `QC`/`ιY` views, closed-embedding proof, chart reduction, B4 wrapper | **Low, Opus.** Mostly  definitional and existing lemmas. |
| Definitional equality becoming fragile after refactors | **Low–medium, Opus.** Protect it with named `change`-based lemmas and small compilation tests. |
| Empty carrier cannot instantiate `WuNullCarrier` | **Low, Opus.** Store `pushedSurfClass τ = 0`; split `IsEmpty`/`Nonempty` only when invoking B0’s iff theorem. |

Estimated interface size:

- adapter and B1a: 35–50 LOC;
- derived B4 views: 25–40 LOC;
- B1b exact telescope: 45–65 LOC;
- composition and smoke tests: 25–40 LOC.

Total: approximately **130–195 LOC**, excluding the actual geometric inhabitants. Those inhabitants are the dominant work and may be several hundred lines per explicit handle model.

This was a read-only inspection; no files were changed and no Lean build was run.
