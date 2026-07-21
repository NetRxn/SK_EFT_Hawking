# codex_212_gate

> **Promoted from session scratchpad 2026-07-21.** The raw ~1-2 MB codex
> transcript was session-scoped and would have been lost on cleanup; this is the run's
> **final deliverable** plus its run metadata. Source transcript: `codex_212_gate.md` in the
> session scratchpad (ephemeral). Cited by `LAB_NOTEBOOK_INDEX.md`.

## Run metadata

```
workdir: /Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research
model: gpt-5.6-sol
provider: openai
approval: on-request
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019f8208-80eb-7923-a169-05e1087583a2
```

## Deliverable

# Round-13 SHAPE GATE — task #212

## Verdict: **FAIL — keep the repair frozen**

The proposed `CapstoneSeamCollarPair` is presently fakeable, and the intended existing consumer is type-level incompatible with the repair:

1. `K := ∅`, `wAtt := 0`, and `wOut := z@⊤` give a trivial collar-pair split. The compactness, interior-subset, support, split, and homology-correction obligations all collapse to standard empty/zero/`μ := 0` discharges.
2. The corrector can be supplied independently of that fake split. Thus the collar half adds no geometry over the corrector half.
3. `hasClass_ofTransferCorrector` cannot consume the repaired shape: it still requires the dead `T : CapstoneSeamTransfer` and calls `hbd_ofTransfer T`. See [PinPlusTraceCapstoneSeamTransfer.lean:459](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneSeamTransfer.lean:459) and [line 498](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneSeamTransfer.lean:498).

This is exactly the kind of conclusion-fakeable carrier rejected by round 13.

## 1. Field-by-field attack

Let `A := Set.range φ`, `Top := Set.univ ×ˢ {⊤}`, and `f := z@⊤`.

| Candidate field | Kind | Vacuous/fake discharge | Required guard |
|---|---|---|---|
| `K : Set HA.B` | **DATA** | Choose `∅`, or later an unrelated singleton. | Must be linked to the actual fundamental top-face chain. |
| `hKcompact : IsCompact K` | Prop | `K := ∅`; also true for junk finite sets. | Necessary for the open complement, but carries no core content. |
| `hKint : K ⊆ interior A` | Prop | `Set.empty_subset _`. | Combine with a nontrivial core-hit condition. |
| `K.Nonempty` | Prop, insufficient | An unrelated singleton inside `interior A`. | Do not use this as the anti-fake. |
| `μ : ℕ` | **DATA** | `μ := 0`. | Fine as data, provided the resulting split is nontrivial. |
| `wAtt`, `wOut` | **DATA** | `wAtt := 0`, `wOut := f`. | Require `f` genuinely to meet `K`. |
| `hwAtt : wAtt ∈ C(interior A)` | Prop | `Submodule.zero_mem`. | Derived support is fine, but cannot certify attachment. |
| `hwOut : wOut ∈ C(Top \ K)` | Prop | With `K=∅`, this is just support in `Top`. | Add `hcoreHit : f ∉ C(Top \ K)`. |
| `hsplit : Sd^[μ] f = wAtt + wOut` | Prop | At `μ=0`, `f = 0 + f`. | With `hcoreHit`, it forces `wAtt ≠ 0`. |
| subdivision homology correction | Prop | At `μ=0`, both sides reduce by characteristic two and zero prism. | Prefer deriving it from the existing engine, not storing it independently. |
| `p` | **DATA** | Correct: the corrector must be an inspectable chain, not hidden inside `∃ p`. | Must be constructed from the collar-pair data, not merely bundled beside it. |
| `hpS : ∂p ∈ C(∂W)` | Prop | Individually, `p := 0`. | Consumed jointly with the other corrector facts. |
| `heS : ∂(glued-p) ∈ C(∂W)` | Prop | Individually, `p := glued`. | Must be explicit in the repaired API. |
| `hagree : glued-p ∈ C((CA∩CB)ᶜ)` | Prop | `p := glued`, making the mismatch zero. | Honest only jointly with `hpS`, `heS`, and `hp_det`. |
| `hp_det` | universal Prop | Empty quantifier if `(CA ∩ CB) \ ∂W = ∅`; `p=0` then escapes. | Genuine attachment must produce an overlap point or directly force `p ≠ 0`. |
| `hasClass` | **must not be a field** | It simply assumes the desired downstream atom. | Derive it from the controlled corrector datum. |

The decisive fake is therefore schematic:

```lean
def fakeCollarExtension
    (R : CapstoneSeamCorrectorT ...) :
    CapstoneSeamCollarPair ... where
  K := ∅
  hKcompact := isCompact_empty
  hKint := Set.empty_subset _
  μ := 0
  wAtt := 0
  wOut := topFace R.z
  hwAtt := Submodule.zero_mem _
  hwOut := topFace_supported_in_top
  hsplit := by simp
  -- copy p/hpS/heS/hagree/hp_det from R
```

So, absent a shared-data construction tie, the collar-pair fields add zero statement strength over a standalone corrector. This mirrors round 13’s zero-collar attack at [PinPlusRoundThirteenGate.lean:291](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusRoundThirteenGate.lean:291).

The minimum nontrivial split guard is:

```lean
hcoreHit :
  topFace z ∉ subspaceChains (Top \ K) 4
```

Together with `hsplit` and `hwOut`, that excludes both `K=∅` and `wAtt=0`. But it still does **not** connect the split to `p`. A named construction such as

```lean
p := collarPairCorrector cd K μ wAtt wOut ...
```

must exist as **DATA**. Taking an arbitrary `p` plus a Prop asserting “it came from the pair” merely moves the fake to that Prop.

## 2. `CollarSplitDatum` does not derive `K`

No. The new machinery operates on a different collar and a different object called `A`.

`CollarSplitDatum` contains only:

```lean
mid : weldedInterval
cyl_side : ...
handle_side : ...
```

It separates `range fromCyl` and `range fromHandle` inside `cd.seamNbhd`; see [KTCompletenessCollarSplit.lean:151](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessCollarSplit.lean:151). Its `cd.A` is an arbitrary **type** underlying the welded-collar model, not the attaching-image set `Set.range φ` in the cylinder end. `SeamCollarDatum` makes that distinction explicit at [SingularSurgerySeamCollar.lean:107](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgerySeamCollar.lean:107).

Consequently it supplies none of:

- a subset of `HA.B`;
- compactness or a compact exhaustion;
- a map identifying `cd.A` with `Set.range φ`;
- a spatial inward collar of the boundary of `Set.range φ`;
- a theorem producing `K ⊆ interior (Set.range φ)`.

The new `coverA` is also unrelated to the repair’s `A`: it is `range fromCyl ∪ seamNbhd`, as defined at [KTCompletenessMVCover.lean:92](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessMVCover.lean:92).

Deriving `K` would require an additional attaching-base collar/compact-exhaustion datum connecting `Set.range φ` to the collar base. That is at least as much new geometry as supplying `K` directly, so it does not reduce the fake surface.

## 3. Corrector versus collar slide

There are two different answers.

### Literal API: incompatible

The existing `hasClass_ofTransferCorrector` requires the killed `CapstoneSeamTransfer` and derives `heS` through `hbd_ofTransfer`. A repaired collar-pair deliberately cannot construct that `T`. Therefore it cannot use this theorem.

The replacement must use the four-fact generic interface:

```lean
SeamCollarChainDatum.ofCorrector hpS heS hagree hp_det
```

at [SingularRelativeCoverMVSeamCorrector.lean:64](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularRelativeCoverMVSeamCorrector.lean:64), with `heS` supplied explicitly.

### Geometry: compatible, but no bridge exists yet

There is no inherent conflict on the same `cd`. `CollarSplitDatum` proves that the actual seam is the `mid` slice and the slide fixes it pointwise; see [KTCompletenessCollarSplit.lean:191](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessCollarSplit.lean:191) and [line 306](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessCollarSplit.lean:306). A seam-detecting corrector can therefore coexist with the slide.

But the merged toolkit proves continuous deformation retractions and homology finiteness. It does not construct a 5-chain `p`, nor prove that pushing a chain through the slide preserves the exact `hpS`, `heS`, `hagree`, and local-detection shapes. Homotopy equivalence alone is insufficient for those exact chain-support statements; prism corrections must be exposed explicitly.

Thus: **no conflict, but no discharge**.

## 4. Sharp replacement boundary

The sharp consumed object should omit `K` and the split entirely. Those belong to a producer theorem. The consumer should be a controlled-cylinder corrector:

```lean
structure CapstoneSeamCorrectorT where
  z : cycles (TopCat.of s.M) 4

  hz :
    SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) 4 z

  p : SingularChain (TopCat.of HA.carrier) 5

  hpS :
    chainBoundary (TopCat.of HA.carrier) 4 p
      ∈ subspaceChains BdW 4

  heS :
    chainBoundary (TopCat.of HA.carrier) 4
      (pushCyl (capstoneCylChainT s S hS φ hφ hφinj z)
        + pushHandle diskDetectChain - p)
      ∈ subspaceChains BdW 4

  hagree :
    pushCyl (capstoneCylChainT s S hS φ hφ hφinj z)
        + pushHandle diskDetectChain - p
      ∈ subspaceChains
          (Set.range HA.fromCyl ∩ Set.range HA.fromHandle)ᶜ 5

  hp_det :
    ∀ x, x ∉ BdW →
      x ∈ Set.range HA.fromCyl →
      x ∈ Set.range HA.fromHandle →
      relClassOf ({x}ᶜ) 3 p (...) ≠ 0

  nonzero_of_genuine :
    topFace z ∉ subspaceChains
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc 0 1))) \ Set.range φ) 4 →
    p ≠ 0
```

`hasClass` is then derived through `SeamCollarChainDatum.ofCorrector`, using the controlled `capstoneCylChainT z`; it is not stored.

The collar-pair work should have the producer signature:

```lean
def correctorT_of_collarPair
    (pair : CollarPairBuild ...) :
    CapstoneSeamCorrectorT ...
```

where `CollarPairBuild` contains the inspectable construction data `K`, subdivision count, split chains, and the actual collar-prism/MV-partition construction. Its output must prove `nonzero_of_genuine`; compare the old shared-chain anti-fake at [PinPlusTraceSeamChainConstruct.lean:159](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceSeamChainConstruct.lean:159).

Until that producer exists, the exact settled-fork warning remains controlling: the collar-pair was only a proposed engine-compatible split, and the corrector was required separately ([SETTLED_FORKS.md:357](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/dev-loops/SETTLED_FORKS.md:357)).

## Frozen round-13 specification

1. Do not add `CapstoneSeamCollarPair` as a consumed supply field.
2. Do not route through `CapstoneSeamTransfer`, `hbd_ofTransfer`, or `hasClass_ofTransferCorrector`.
3. `K`, split chains, subdivision counts, collar maps, and `p` must be data.
4. Require `hcoreHit`; compactness plus `K ⊆ interior A` is vacuous.
5. Construct the same `p` from the split—no independent corrector packet.
6. Supply `heS` explicitly.
7. Prove that genuine attachment forces `p ≠ 0`.
8. Export only the controlled corrector datum; derive `hasClass`, whose current downstream locations are direct fields at [PinPlusTraceCapstoneInhabit.lean:307](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneInhabit.lean:307), [PinPlusTraceCapstoneSupplyMV.lean:110](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneSupplyMV.lean:110), and [PinPlusTraceCapstoneMembraneWeld.lean:257](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneMembraneWeld.lean:257).

Read-only gate: no files changed and no build run. Current worktree remains `main` ahead of `origin/main` with the existing untracked `H_GEOMETRIC_LEG_DESIGN.md`.


tokens used
428,651
# Round-13 SHAPE GATE — task #212

## Verdict: **FAIL — keep the repair frozen**

The proposed `CapstoneSeamCollarPair` is presently fakeable, and the intended existing consumer is type-level incompatible with the repair:

1. `K := ∅`, `wAtt := 0`, and `wOut := z@⊤` give a trivial collar-pair split. The compactness, interior-subset, support, split, and homology-correction obligations all collapse to standard empty/zero/`μ := 0` discharges.
2. The corrector can be supplied independently of that fake split. Thus the collar half adds no geometry over the corrector half.
3. `hasClass_ofTransferCorrector` cannot consume the repaired shape: it still requires the dead `T : CapstoneSeamTransfer` and calls `hbd_ofTransfer T`. See [PinPlusTraceCapstoneSeamTransfer.lean:459](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneSeamTransfer.lean:459) and [line 498](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneSeamTransfer.lean:498).

This is exactly the kind of conclusion-fakeable carrier rejected by round 13.

## 1. Field-by-field attack

Let `A := Set.range φ`, `Top := Set.univ ×ˢ {⊤}`, and `f := z@⊤`.

| Candidate field | Kind | Vacuous/fake discharge | Required guard |
|---|---|---|---|
| `K : Set HA.B` | **DATA** | Choose `∅`, or later an unrelated singleton. | Must be linked to the actual fundamental top-face chain. |
| `hKcompact : IsCompact K` | Prop | `K := ∅`; also true for junk finite sets. | Necessary for the open complement, but carries no core content. |
| `hKint : K ⊆ interior A` | Prop | `Set.empty_subset _`. | Combine with a nontrivial core-hit condition. |
| `K.Nonempty` | Prop, insufficient | An unrelated singleton inside `interior A`. | Do not use this as the anti-fake. |
| `μ : ℕ` | **DATA** | `μ := 0`. | Fine as data, provided the resulting split is nontrivial. |
| `wAtt`, `wOut` | **DATA** | `wAtt := 0`, `wOut := f`. | Require `f` genuinely to meet `K`. |
| `hwAtt : wAtt ∈ C(interior A)` | Prop | `Submodule.zero_mem`. | Derived support is fine, but cannot certify attachment. |
| `hwOut : wOut ∈ C(Top \ K)` | Prop | With `K=∅`, this is just support in `Top`. | Add `hcoreHit : f ∉ C(Top \ K)`. |
| `hsplit : Sd^[μ] f = wAtt + wOut` | Prop | At `μ=0`, `f = 0 + f`. | With `hcoreHit`, it forces `wAtt ≠ 0`. |
| subdivision homology correction | Prop | At `μ=0`, both sides reduce by characteristic two and zero prism. | Prefer deriving it from the existing engine, not storing it independently. |
| `p` | **DATA** | Correct: the corrector must be an inspectable chain, not hidden inside `∃ p`. | Must be constructed from the collar-pair data, not merely bundled beside it. |
| `hpS : ∂p ∈ C(∂W)` | Prop | Individually, `p := 0`. | Consumed jointly with the other corrector facts. |
| `heS : ∂(glued-p) ∈ C(∂W)` | Prop | Individually, `p := glued`. | Must be explicit in the repaired API. |
| `hagree : glued-p ∈ C((CA∩CB)ᶜ)` | Prop | `p := glued`, making the mismatch zero. | Honest only jointly with `hpS`, `heS`, and `hp_det`. |
| `hp_det` | universal Prop | Empty quantifier if `(CA ∩ CB) \ ∂W = ∅`; `p=0` then escapes. | Genuine attachment must produce an overlap point or directly force `p ≠ 0`. |
| `hasClass` | **must not be a field** | It simply assumes the desired downstream atom. | Derive it from the controlled corrector datum. |

The decisive fake is therefore schematic:

```lean
def fakeCollarExtension
    (R : CapstoneSeamCorrectorT ...) :
    CapstoneSeamCollarPair ... where
  K := ∅
  hKcompact := isCompact_empty
  hKint := Set.empty_subset _
  μ := 0
  wAtt := 0
  wOut := topFace R.z
  hwAtt := Submodule.zero_mem _
  hwOut := topFace_supported_in_top
  hsplit := by simp
  -- copy p/hpS/heS/hagree/hp_det from R
```

So, absent a shared-data construction tie, the collar-pair fields add zero statement strength over a standalone corrector. This mirrors round 13’s zero-collar attack at [PinPlusRoundThirteenGate.lean:291](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusRoundThirteenGate.lean:291).

The minimum nontrivial split guard is:

```lean
hcoreHit :
  topFace z ∉ subspaceChains (Top \ K) 4
```

Together with `hsplit` and `hwOut`, that excludes both `K=∅` and `wAtt=0`. But it still does **not** connect the split to `p`. A named construction such as

```lean
p := collarPairCorrector cd K μ wAtt wOut ...
```

must exist as **DATA**. Taking an arbitrary `p` plus a Prop asserting “it came from the pair” merely moves the fake to that Prop.

## 2. `CollarSplitDatum` does not derive `K`

No. The new machinery operates on a different collar and a different object called `A`.

`CollarSplitDatum` contains only:

```lean
mid : weldedInterval
cyl_side : ...
handle_side : ...
```

It separates `range fromCyl` and `range fromHandle` inside `cd.seamNbhd`; see [KTCompletenessCollarSplit.lean:151](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessCollarSplit.lean:151). Its `cd.A` is an arbitrary **type** underlying the welded-collar model, not the attaching-image set `Set.range φ` in the cylinder end. `SeamCollarDatum` makes that distinction explicit at [SingularSurgerySeamCollar.lean:107](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularSurgerySeamCollar.lean:107).

Consequently it supplies none of:

- a subset of `HA.B`;
- compactness or a compact exhaustion;
- a map identifying `cd.A` with `Set.range φ`;
- a spatial inward collar of the boundary of `Set.range φ`;
- a theorem producing `K ⊆ interior (Set.range φ)`.

The new `coverA` is also unrelated to the repair’s `A`: it is `range fromCyl ∪ seamNbhd`, as defined at [KTCompletenessMVCover.lean:92](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessMVCover.lean:92).

Deriving `K` would require an additional attaching-base collar/compact-exhaustion datum connecting `Set.range φ` to the collar base. That is at least as much new geometry as supplying `K` directly, so it does not reduce the fake surface.

## 3. Corrector versus collar slide

There are two different answers.

### Literal API: incompatible

The existing `hasClass_ofTransferCorrector` requires the killed `CapstoneSeamTransfer` and derives `heS` through `hbd_ofTransfer`. A repaired collar-pair deliberately cannot construct that `T`. Therefore it cannot use this theorem.

The replacement must use the four-fact generic interface:

```lean
SeamCollarChainDatum.ofCorrector hpS heS hagree hp_det
```

at [SingularRelativeCoverMVSeamCorrector.lean:64](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/SingularRelativeCoverMVSeamCorrector.lean:64), with `heS` supplied explicitly.

### Geometry: compatible, but no bridge exists yet

There is no inherent conflict on the same `cd`. `CollarSplitDatum` proves that the actual seam is the `mid` slice and the slide fixes it pointwise; see [KTCompletenessCollarSplit.lean:191](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessCollarSplit.lean:191) and [line 306](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/KTCompletenessCollarSplit.lean:306). A seam-detecting corrector can therefore coexist with the slide.

But the merged toolkit proves continuous deformation retractions and homology finiteness. It does not construct a 5-chain `p`, nor prove that pushing a chain through the slide preserves the exact `hpS`, `heS`, `hagree`, and local-detection shapes. Homotopy equivalence alone is insufficient for those exact chain-support statements; prism corrections must be exposed explicitly.

Thus: **no conflict, but no discharge**.

## 4. Sharp replacement boundary

The sharp consumed object should omit `K` and the split entirely. Those belong to a producer theorem. The consumer should be a controlled-cylinder corrector:

```lean
structure CapstoneSeamCorrectorT where
  z : cycles (TopCat.of s.M) 4

  hz :
    SingularFundamentalClass.fundamentalClass (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) 4 z

  p : SingularChain (TopCat.of HA.carrier) 5

  hpS :
    chainBoundary (TopCat.of HA.carrier) 4 p
      ∈ subspaceChains BdW 4

  heS :
    chainBoundary (TopCat.of HA.carrier) 4
      (pushCyl (capstoneCylChainT s S hS φ hφ hφinj z)
        + pushHandle diskDetectChain - p)
      ∈ subspaceChains BdW 4

  hagree :
    pushCyl (capstoneCylChainT s S hS φ hφ hφinj z)
        + pushHandle diskDetectChain - p
      ∈ subspaceChains
          (Set.range HA.fromCyl ∩ Set.range HA.fromHandle)ᶜ 5

  hp_det :
    ∀ x, x ∉ BdW →
      x ∈ Set.range HA.fromCyl →
      x ∈ Set.range HA.fromHandle →
      relClassOf ({x}ᶜ) 3 p (...) ≠ 0

  nonzero_of_genuine :
    topFace z ∉ subspaceChains
      ((Set.univ ×ˢ ({⊤} : Set (Set.Icc 0 1))) \ Set.range φ) 4 →
    p ≠ 0
```

`hasClass` is then derived through `SeamCollarChainDatum.ofCorrector`, using the controlled `capstoneCylChainT z`; it is not stored.

The collar-pair work should have the producer signature:

```lean
def correctorT_of_collarPair
    (pair : CollarPairBuild ...) :
    CapstoneSeamCorrectorT ...
```

where `CollarPairBuild` contains the inspectable construction data `K`, subdivision count, split chains, and the actual collar-prism/MV-partition construction. Its output must prove `nonzero_of_genuine`; compare the old shared-chain anti-fake at [PinPlusTraceSeamChainConstruct.lean:159](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceSeamChainConstruct.lean:159).

Until that producer exists, the exact settled-fork warning remains controlling: the collar-pair was only a proposed engine-compatible split, and the corrector was required separately ([SETTLED_FORKS.md:357](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/dev-loops/SETTLED_FORKS.md:357)).

## Frozen round-13 specification

1. Do not add `CapstoneSeamCollarPair` as a consumed supply field.
2. Do not route through `CapstoneSeamTransfer`, `hbd_ofTransfer`, or `hasClass_ofTransferCorrector`.
3. `K`, split chains, subdivision counts, collar maps, and `p` must be data.
4. Require `hcoreHit`; compactness plus `K ⊆ interior A` is vacuous.
5. Construct the same `p` from the split—no independent corrector packet.
6. Supply `heS` explicitly.
7. Prove that genuine attachment forces `p ≠ 0`.
8. Export only the controlled corrector datum; derive `hasClass`, whose current downstream locations are direct fields at [PinPlusTraceCapstoneInhabit.lean:307](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneInhabit.lean:307), [PinPlusTraceCapstoneSupplyMV.lean:110](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneSupplyMV.lean:110), and [PinPlusTraceCapstoneMembraneWeld.lean:257](/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/PinPlusTraceCapstoneMembraneWeld.lean:257).

Read-only gate: no files changed and no build run. Current worktree remains `main` ahead of `origin/main` with the existing untracked `H_GEOMETRIC_LEG_DESIGN.md`.
