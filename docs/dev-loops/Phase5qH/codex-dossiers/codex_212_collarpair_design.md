# codex_212_collarpair_design

> **Codex dossier — the run's FINAL DELIVERABLE only.** Harvested 2026-07-21 by `scripts/codex_dossier.py`.
> The raw transcript (951,905 bytes) is ephemeral and is deliberately NOT in the repo: reading it
> would overflow the orchestrator and defeat the point of using a second provider.
> Source: `codex_212_collarpair_design.md`.

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
session id: 019f836f-e245-7103-8eeb-45de1c4e3896
```

## Deliverable

The honest design is a three-layer input: genuine collar geometry, a shared controlled boundary core, and an inspectable relative MV partition. It must not contain `p`, any of `hpS/heS/hagree/hp_det`, or `toHasClass`.

There is no unconditional in-tree inhabitant today. In particular, canonical `diskDetectChain` has no existing theorem co-adapting its chosen chain representative to the attaching collar.

## A. Proposed `CollarPairBuild`

Use helper definitions for:

```lean
HA       := ktHandleAttachment s.M D5 S hS φ hφ hφinj
W        := TopCat.of HA.carrier
B        := TopCat.of HA.B
Ha       := TopCat.of HA.Ha
Bd       := ((𝓡 4).prod (𝓡∂ 1)).boundary
              (capstoneB s t S hS φ hφ hφinj cd hseam d).W
Ovl      := Set.range HA.fromCyl ∩ Set.range HA.fromHandle
topFace  := Set.univ ×ˢ ({⊤} : Set (Set.Icc (0 : ℝ) 1))
Ssph     := PinPlusTraceDiskSphereCycle.Ssph

q₀ z :=
  closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding 5
      (capstoneCylChainT s S hS φ hφ hφinj z)
  +
  closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding 5
      diskDetectChain
```

`κC` and `κH` denote the attaching-set inclusions into the top-face and sphere subtypes, defined using `hφtop` and `hS_sphere`. `seamPoint a := HA.fromHandle (a : D5)`, and `Sbd := seamPoint ⁻¹' Bd`.

The proposed Lean shape is:

```lean
structure CollarPairBuild where
  /- Fundamental representative. -/

  z : cycles (TopCat.of s.M) 4
  -- [IN-TREE: Submodule.Quotient.mk_surjective, Homology.mk]

  hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass
        (m := 2) (M := s.M)
      = Homology.mk (TopCat.of s.M) 4 z
  -- [IN-TREE: Submodule.Quotient.mk_surjective]

  /- Honest attachment/collar geometry missing from the present parameter row. -/

  hφtop : ∀ a, ((φ a).2 : ℝ) = 1
  -- [NEW: Supply this from the actual surgery attaching embedding. It is the hypothesis used by
  -- SingularSurgeryBoundaryFloor.cylBot_not_mem_range_phi.]

  hS_sphere : S ⊆ PinPlusTraceDiskSphereCycle.Ssph
  -- [NEW: Supply the construction theorem that the handle attaching region lies in ∂D⁵.]

  csd : KTCompletenessCollarSplit.CollarSplitDatum HA cd
  -- [NEW: Construct the lower/upper side equalities from the concrete welded-collar chart;
  -- seam_collar_coord_eq_mid is then available.]

  seamBase : ↥S ≃ₜ cd.A
  -- [NEW: Identify the abstract base cd.A with the actual attaching set, not merely an unrelated
  -- four-manifold.]

  seamBase_mid :
    ∀ a, cd.hHomeo (seamPointInCollar hseam a) = (seamBase a, csd.mid)
  -- [NEW: Verify directly from the concrete quotient collar; this ties seamBase and csd to φ/S.]

  /- The shrunk closed core K ⊂ int(A), on both sides. -/

  K : Set ↥S
  -- [NEW: Choose a compact shrink of the portion of the attaching region met by the selected
  -- fundamental representative.]

  hKcompact : IsCompact K
  -- [NEW: Obtain from the compact-shrink/tube construction inside the relative interiors.]

  hKcyl : κC '' K ⊆ interior (Set.range κC)
  -- [NEW: This is the cylinder-side K ⊂ int(A) condition, in the top-face subtype topology.]

  hKha : κH '' K ⊆ interior (Set.range κH)
  -- [NEW: This is the handle-side mirror inside the sphere subtype.]

  hKoffBd : K ⊆ Sbdᶜ
  -- [NEW: The compact core is chosen away from the boundary of the finished trace.]

  /- Shared four-dimensional seam core. -/

  cCore : SingularChain (TopCat.of ↥S) 4
  -- [NEW: Construct by co-adapting the top-face cycle with zS :=
  -- boundaryExtract diskDetectChain over the collar pair.]

  hcCoreBd :
    chainBoundary (TopCat.of ↥S) 3 cCore
      ∈ subspaceChains (X := TopCat.of ↥S) Sbd 3
  -- [NEW: Its only boundary is the boundary of the attaching region; discharge from the
  -- relative collar fundamental-chain construction.]

  hcCoreDet :
    ∀ a, a ∉ Sbd →
      relClassOf (X := TopCat.of ↥S) ({a}ᶜ) 2 cCore
        (subspaceChains_mono
          (Set.subset_compl_singleton_iff.mpr ‹a ∉ Sbd›) 3 hcCoreBd) ≠ 0
  -- [NEW: Prove by relative excision from the fundamental top/sphere cycles, using
  -- zSclass_eq_sphGen and the cylinder fundamental-class pin hz.]

  hcoreHit :
    mapChain (slice (graphHom (TopCat.of s.M)) 1) 4
        (z : SingularChain (TopCat.of s.M) 4)
      ∉ subspaceChains (X := B) (topFace \ Set.range φ) 4 →
    cCore ∉ subspaceChains (X := TopCat.of ↥S) Kᶜ 4
  -- [NEW: The K-collar split must show that a core supported off K would force the whole top
  -- face off range φ; use mem_subspaceChains_of_mapChain_mem and hφinj.]

  /- Controlled cylinder/handle boundary splits. -/

  μC : ℕ
  -- [IN-TREE: exists_subtype_boundary_split_of_relCycle_inf supplies the raw count]

  μH : ℕ
  -- [IN-TREE: diskDetectChain_subtype_boundary_split_inf supplies the raw count]

  outC : SingularChain B 4
  -- [IN-TREE: exists_iterate_cover_split_amb_inf supplies the top-face remainder]

  outH : SingularChain Ha 4
  -- [IN-TREE: diskDetectChain_subtype_boundary_split_inf supplies the sphere remainder]

  hctrlC :
    chainBoundary B 4 (ctrlC z μC)
      = mapChain (seamLegCyl s S φ hφ) 4 cCore
          + outC + ctrlBottom z μC
  -- [NEW: Co-adapt the cylinder split to the shared cCore. ctrlC is the subdivided
  -- capstoneCylChainT and ctrlBottom its subdivided bottom face.]

  hctrlH :
    chainBoundary Ha 4 (ctrlH μH)
      = mapChain (seamLegHa s S hS φ hφ hφinj) 4 cCore + outH
  -- [NEW: Co-adapt the canonical disk boundary split to exactly the same cCore; ctrlH is the
  -- subdivided diskDetectChain.]

  houtC :
    outC ∈ subspaceChains (X := B) (topFace \ κC '' K) 4
  -- [IN-TREE: exists_iterate_cover_split_amb_inf with U₁ := int(A), U₂ := topFace \ K]

  houtH :
    outH ∈ subspaceChains (X := Ha) (Ssph \ κH '' K) 4
  -- [IN-TREE: diskDetectChain_subtype_boundary_split_inf with the K-complement cover]

  bdOut : SingularChain (sub (X := W) Bd) 4
  -- [NEW: The explicit boundary-subtype chain left after the two collar-annulus remainders
  -- are welded.]

  houtPair :
    closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding 4 outC
      + closedEmbeddingChain HA.isClosedEmbedding_fromHandle.isEmbedding 4 outH
      + closedEmbeddingChain HA.isClosedEmbedding_fromCyl.isEmbedding 4
          (ctrlBottom z μC)
      = chainIncl Bd 4 bdOut
  -- [NEW: Build by matching the two A \ K annulus pieces through the welded collar; the
  -- genuinely free top/sphere pieces land in Bd via SurgeredEndDatum.]

  /- Relative homology bridge back to the frozen, unsubdivided q₀. -/

  bridge : SingularChain W 6
  -- [NEW: Sum the two iterated subdivision prisms and the collar prism correcting their
  -- boundary-homotopy terms.]

  bridgeBd : SingularChain (sub (X := W) Bd) 5
  -- [NEW: Collect the bottom, free-face, and collar-annulus errors that already lie in Bd.]

  hbridge :
    qCtrl z μC μH
      = q₀ z
          + chainBoundary W 5 bridge
          + chainIncl Bd 5 bridgeBd
  -- [NEW: Prove from iterHomotopy_chainHomotopy, hctrlC/hctrlH, houtPair, and
  -- closedEmbeddingChain_mapChain_glue_eq.]

  /- Inspectable ambient relative-MV partition. -/

  μW : ℕ
  -- [IN-TREE: exists_cover_split_homologous over seamNbhd and Ovlᶜ]

  near away : SingularChain W 5
  -- [IN-TREE: exists_cover_split_homologous supplies the raw cover-fine pieces]

  hpartition :
    ((⇑(singularSd W 5))^[μW]) (qCtrl z μC μH) = near + away
  -- [IN-TREE: exists_cover_split_homologous]

  nearCollar : SingularChain (sub (X := W) cd.seamNbhd) 5
  -- [IN-TREE: mem_subspaceChains_iff_exists_mapChain_ambIncl]

  hnearCollar : mapChain (ambIncl cd.seamNbhd) 5 nearCollar = near
  -- [IN-TREE: mem_subspaceChains_iff_exists_mapChain_ambIncl]

  awayOff : SingularChain (sub (X := W) Ovlᶜ) 5
  -- [IN-TREE: mem_subspaceChains_iff_exists_mapChain_ambIncl]

  hawayOff : chainIncl Ovlᶜ 5 awayOff = away
  -- [IN-TREE: mapChain_ambIncl, mem_subspaceChains_iff_exists_mapChain_ambIncl]

  nearBd awayBd : SingularChain (sub (X := W) Bd) 4
  -- [NEW: These are the two explicit relative-boundary witnesses produced by the
  -- collar-relative MV refinement.]

  hnearBd : chainBoundary W 4 near = chainIncl Bd 4 nearBd
  -- [NEW: Correct the raw near boundary across the collar intersection, rather than assuming
  -- a generic cover split is a relative split.]

  hawayBd : chainBoundary W 4 away = chainIncl Bd 4 awayBd
  -- [NEW: The same overlap correction makes the away piece a relative cycle.]

  /- Local product comparison that supplies detection. -/

  modelHomotopy : SingularChain W 6
  -- [NEW: Construct from the prism comparing near with the explicit welded-collar product
  -- chain collarCorePrism csd seamBase cCore.]

  modelOff : SingularChain (sub (X := W) Ovlᶜ) 5
  -- [NEW: Collect the part of that comparison lying away from the actual overlap.]

  hnearModel :
    near
      = collarCorePrism cd csd seamBase cCore
          + chainBoundary W 5 modelHomotopy
          + chainIncl Ovlᶜ 5 modelOff
  -- [NEW: Prove simplex-by-simplex from the collar-relative MV construction; this is the
  -- tether that prevents near from being an arbitrary supplied corrector.]
```

`collarCorePrism` should be a definition, not a field: map `cCore` through `seamBase`, apply `prismOp` across two canonical levels bracketing `csd.mid`, then map back through `cd.hHomeo.symm` and include `cd.seamNbhd` into `W`.

## B. Producer proof skeleton

Define:

```lean
qC := qCtrl R.z R.μC R.μH
Dq := iterHomotopy W 5 R.μW qC
Db := iterHomotopy W 4 R.μW (chainBoundary W 4 qC)

corr6  := R.bridge + Dq
corrBd := chainIncl Bd 5 R.bridgeBd + Db

p := R.near + chainBoundary W 5 corr6 + corrBd
```

From `hctrlC`, `hctrlH`, and `closedEmbeddingChain_mapChain_glue_eq`, the two pushed copies of `cCore` cancel over `ZMod 2`. `houtPair` then gives:

```lean
chainBoundary W 4 qC = chainIncl Bd 4 R.bdOut
```

Hence `Db` is `Bd`-supported by `SingularExcision.iterHomotopy_mem_subspaceChains`.

The subdivision identity `iterHomotopy_chainHomotopy`, together with `hbridge` and `hpartition`, gives the key equation:

```lean
q₀ R.z = p + R.away
```

equivalently, in the consumer’s notation, `q₀ R.z - p = R.away`.

Field mapping:

| Target field | Construction |
|---|---|
| `z` | `R.z` |
| `hz` | `R.hz` |
| `p` | The definition above; never a `CollarPairBuild` field |
| `hpS` | Rewrite `∂p`; use `R.hnearBd`, `chainBoundary_chainBoundary_apply`, support of `corrBd`, `chainBoundary_mem_subspaceChains`, and `SingularExcision.iterHomotopy_mem_subspaceChains` |
| `heS` | Rewrite `q₀ - p = away`; use `R.hawayBd` |
| `hagree` | Rewrite the same equation; use `R.hawayOff`, `mapChain_ambIncl`/`chainIncl` membership |
| `hp_det` | First prove the new `collarCorePrism_hdet` from `hcCoreDet`, `seamBase_mid`, `seam_collar_coord_eq_mid`, and local product/excision. Transfer through `hnearModel`, then through the boundary-plus-`Bd` correction defining `p`, using `SingularRelClassHomologous.relClassOf_eq_of_homologous` |
| `nonzero_of_genuine` | The premise and `hcoreHit` imply `K.Nonempty`, since every chain lies in `C(univ)` (`mem_subspaceChains_univ`). Choose `a ∈ K`; `hKoffBd` gives an off-boundary overlap point, `hp_det` gives a nonzero local class there, and `p = 0` contradicts it |

After constructing the result, `CapstoneSeamCorrectorT.seamDatum` and `CapstoneSeamCorrectorT.toHasClass` remain exactly as currently written. The producer must not invoke `hbd_ofTransfer` or `hasClass_ofTransferCorrector`.

## C. Anti-fake audit

The forcing field is `hcoreHit`.

Under the consumer’s genuine-attachment premise:

- `K = ∅` is impossible: then `Kᶜ = univ`, and `cCore ∈ C(univ)` automatically.
- `cCore = 0` is impossible: zero belongs to every support submodule.
- `near = 0` cannot pass `hnearModel` plus `hcCoreDet`; the intended `collarCorePrism_hdet` makes its local class nonzero.
- An independently supplied `p` is impossible because `p` is a definition from `near`, `bridge`, and the subdivision homotopy.
- Independently supplied final facts are impossible because none of `hpS/heS/hagree/hp_det/nonzero_of_genuine` is a build field.

`hcoreHit` alone is not sufficient; its tether is the chain:

```text
cCore
  → hctrlC/hctrlH
  → hbridge and hnearModel
  → computed p
```

That is precisely what the failed shape lacked. `CollarSplitDatum` alone still does not help: its `cd.A` is abstract, so `seamBase` and `seamBase_mid` are necessary to bind it to `S` and `φ`.

The design also respects the #210 fence: `outC` and `outH` are supported off the smaller `K`, so their annular parts may overlap in `A \ K`. It never reinstates the impossible “attached chain in closed `A`, remainder in `Aᶜ`” split.

## D. Risk register

1. **Canonical `diskDetectChain` bridge — highest risk.**  
   `diskDetectChain_subtype_boundary_split_freeSphere` controls a subdivision, not the frozen chain itself. Decompose `hbridge` into cylinder subdivision, disk subdivision, and a separate collar-annulus bridge; use `zS`, `chainIncl_boundaryExtract`, `zSclass_eq_sphGen`, and `homologyWitness_of_relClass_eq` for the disk component.

2. **Exact shared `cCore` and `houtPair`.**  
   Independent cover splits do not produce the same attached chain. If exact sharing is too rigid, use two visible cores `cCoreC/cCoreH` plus an explicit collar 5-chain whose boundary is their pushed difference modulo a `Bd`-chain; derive the comparison core rather than returning to the dead exact-support transfer.

3. **Relative MV partition with detection.**  
   Generic `exists_cover_split_homologous` does not prove `hnearBd` or `hawayBd`. A fallback helper structure should expose the raw split, an overlap correction chain, the two boundary-subtype witnesses, and `hnearModel`; then prove a reusable `exists_collar_relative_partition` theorem.

An upstream stop condition should be explicit: without proofs of `hφtop` and `hS_sphere`, the claimed producer cannot be total over the current arbitrary `S, φ` parameter row.

## E. Sizing

| Component | Estimate | Tier |
|---|---:|---|
| Helper notation, `qCtrl`, correction algebra, support transport | 100–180 LOC | Fable |
| Raw subdivision/cover wrappers | 150–250 LOC | Fable |
| `seamBase`, mid-slice tie, `K` shrink geometry | 250–450 LOC | Opus |
| Shared `cCore`, `houtPair`, canonical-chain `hbridge` | 450–800 LOC | Opus, hardest |
| Relative MV refinement and `hnearModel` | 350–650 LOC | Opus |
| `collarCorePrism_hdet` and final producer wiring | 180–320 LOC | Mixed: detection Opus, wiring Fable |

Expected total: roughly **1,480–2,650 LOC**. Only the final producer shell is safely Fable-tier; describing the entire remaining target that way would understate the canonical-disk and relative-collar geometry.

Read-only audit only: no files were changed, and no build was run because this turn introduced no Lean source to compile.
