/-
# Phase 5q.H (W-A arm 4) — the terminal `hcls`, reduced to LOCAL-CROSS injectivity

The final wiring of route B. The frozen exposure
`PoincareLefschetzRelFundClassCylinderCrossRestrict.restrictBd_cylFundClassCandidate` says the
candidate's restriction at an interior point `x = (σ,t)` is `[prismOp graphHom z]` rel `{x}ᶜ`
(`z` a cycle rep of `[M]`). `PoincareLefschetzRelFundClassCylinderCrossLocal.crossHloc` is the
well-defined local cross `H_{m'+2}(M, M∖σ) → H_{m'+3}(M×I, (M×I)∖x)`, `[c] ↦ [prismOp graphHom c]`.
Here we prove the **naturality square** identifying the candidate's restriction with `crossHloc`
applied to `M`'s local fundamental class `[M]|_σ`, then reduce the terminal `hne` (hence `hcls`) to
the **injectivity of `crossHloc` at every interior point** — the honest interior local-Künneth
nonvanishing, isolated as a single well-defined-map property.

## What this banks

* **§1 — interior-point slice/puncture facts** (`h1`/`h0`/`hpunc` from `x ∉ ∂W`): endpoint slices
  land in `{x}ᶜ` (`t ≠ 0,1`) and `{σ}ᶜ` prisms land in `{x}ᶜ` (`a ≠ σ ⟹ (a,s) ≠ (σ,t)`).
* **§2 — `M`'s local fundamental class** `mLocalClass σ = [M]|_σ ∈ H_{m'+2}(M, M∖σ)` and its
  nonvanishing (`SingularFundamentalClass.fundamentalClass_restricts`).
* **§3 — the naturality square** `restrictBd candidate = crossHloc ([M]|_σ)` (both `[prismOp z]`
  rel `{x}ᶜ`, chain-level), hence `hne` at `x` ⟺ `crossHloc (m'+1)` injective (source and target
  both `ℤ/2` local homologies), and — quantified over interior points — the terminal `hcls`.

The residual crux is the **injectivity of `crossHloc`** at every interior point (equivalently
`[prismOp graphHom z] ≠ 0`): the interior local-Künneth, a separate deep arc (a chart-excision
product computation or a chain-level retraction of the local cross). Named, not faked.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocal
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossRestrict
import SKEFTHawking.SingularFundamentalClassExist
import SKEFTHawking.SingularLocalDuality
import SKEFTHawking.SingularBaseCaseD0

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossRestrict
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocal
open SKEFTHawking.SingularFundamentalClass

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalReduce

noncomputable section

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-! ## §1. Interior-point slice/puncture facts -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- At an interior point `x ∉ ∂W`, the interval coordinate `x.2` is neither endpoint `⊥`, `⊤`. -/
theorem interior_snd_ne (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)) :
    x.2 ≠ ⊥ ∧ x.2 ≠ ⊤ := by
  rw [cyl_boundary_eq] at hx
  simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or] at hx
  exact hx

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The endpoint slice `M × {1}` lands in `{x}ᶜ`** at an interior point (`x.2 ≠ ⊤`). -/
theorem interior_slice_one (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)) :
    Set.MapsTo (slice (graphHom (TopCat.of M)) 1) (Set.univ : Set ↑(TopCat.of M))
      ({x}ᶜ : Set ↑(cyl (TopCat.of M))) := by
  intro a _
  rw [Set.mem_compl_iff, Set.mem_singleton_iff, slice_graphHom]
  intro h
  refine (interior_snd_ne x hx).2 ?_
  have hs : x.2 = (1 : unitInterval) := (congrArg Prod.snd h).symm
  rw [hs]; exact Subtype.ext rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The endpoint slice `M × {0}` lands in `{x}ᶜ`** at an interior point (`x.2 ≠ ⊥`). -/
theorem interior_slice_zero (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)) :
    Set.MapsTo (slice (graphHom (TopCat.of M)) 0) (Set.univ : Set ↑(TopCat.of M))
      ({x}ᶜ : Set ↑(cyl (TopCat.of M))) := by
  intro a _
  rw [Set.mem_compl_iff, Set.mem_singleton_iff, slice_graphHom]
  intro h
  refine (interior_snd_ne x hx).1 ?_
  have hs : x.2 = (0 : unitInterval) := (congrArg Prod.snd h).symm
  rw [hs]; exact Subtype.ext rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The `{σ}ᶜ` prism engine at `x`**: `a ≠ σ ⟹ (a,s) ≠ (σ,t) = x` — the puncture containment the
local cross needs (`graphHom` prisms of `{σ}ᶜ`-chains land in `{x}ᶜ`). -/
theorem interior_punc (x : ↑(TopCat.of (cylW M))) :
    ∀ a ∈ ({x.1}ᶜ : Set ↑(TopCat.of M)), ∀ s : unitInterval,
      graphHom (TopCat.of M) (a, s) ∈ ({x}ᶜ : Set ↑(cyl (TopCat.of M))) := by
  intro a ha s
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  exact ha (Set.mem_singleton_iff.mpr (congrArg Prod.fst h))

/-! ## §2. `M`'s local fundamental class `[M]|_σ` and its nonvanishing -/

/-- **The local fundamental relative cycle** `[z]` rel `{σ}ᶜ` — a cycle rep `z` of `[M]`, viewed as a
relative cycle of `(M, M∖σ)` (its boundary `∂z = 0` is trivially a `{σ}ᶜ`-chain). -/
noncomputable def mLocalRelCycle (x : ↑(TopCat.of (cylW M)))
    (z : cycles (TopCat.of M) (m' + 2)) :
    relCycles ({x.1}ᶜ : Set ↑(TopCat.of M)) (m' + 2) :=
  ⟨RelativeChain.mk ({x.1}ᶜ : Set ↑(TopCat.of M)) (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2)),
    SKEFTHawking.SingularLocalDuality.relMk_mem_relCycles ({x.1}ᶜ : Set ↑(TopCat.of M))
      (z : SingularChain (TopCat.of M) (m' + 2))
      (by rw [LinearMap.mem_ker.mp z.2]; exact Submodule.zero_mem _)⟩

/-- **`M`'s local fundamental class** `[M]|_σ ∈ H_{m'+2}(M, M∖σ)` at `σ = x.1`, as the class of the
fundamental cycle rep rel `{σ}ᶜ`. Equal to `restrictHomologyToPoint σ [M]` (`mLocalClass_eq`). -/
noncomputable def mLocalClass (x : ↑(TopCat.of (cylW M))) (z : cycles (TopCat.of M) (m' + 2)) :
    RelativeHomology ({x.1}ᶜ : Set ↑(TopCat.of M)) (m' + 2) :=
  RelativeHomology.mk ({x.1}ᶜ : Set ↑(TopCat.of M)) (m' + 2) (mLocalRelCycle x z)

/-- **`mLocalClass` is `restrictHomologyToPoint σ [M]`** (`restrictHomologyToSet_mk` at `K = {σ}`,
using `[M] = [z]`). The bridge to the fundamental-class nonvanishing. -/
theorem mLocalClass_eq (x : ↑(TopCat.of (cylW M))) (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    mLocalClass x z = SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
      (X := TopCat.of M) x.1 (m' + 2)
        (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)) := by
  rw [hz]
  refine (SKEFTHawking.SingularBaseCaseD0.restrictHomologyToSet_mk
    (X := TopCat.of M) (K := ({x.1} : Set ↑(TopCat.of M)))
    (z : SingularChain (TopCat.of M) (m' + 2)) z.2
    (by rw [LinearMap.mem_ker.mp z.2]; exact Submodule.zero_mem _)).symm.trans ?_
  rfl

/-- **`[M]|_σ ≠ 0`**: `M`'s local fundamental class is nonzero (it restricts to the local generator
`(manifoldLocalIso σ).symm 1 ≠ 0`, `SingularFundamentalClass.fundamentalClass_restricts`). -/
theorem mLocalClass_ne_zero (x : ↑(TopCat.of (cylW M))) (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    mLocalClass x z ≠ 0 := by
  rw [mLocalClass_eq x z hz,
    SKEFTHawking.SingularFundamentalClass.fundamentalClass_restricts (m := m') (M := M) x.1]
  intro h
  exact one_ne_zero
    ((SKEFTHawking.SingularChartBridge.manifoldLocalIso (m := m') x.1).symm.map_eq_zero_iff.mp h)

/-! ## §3. The naturality square and the reduction of `hcls` to local-cross injectivity -/

/-- **The naturality square** `restrictBd candidate = crossHloc ([M]|_σ)`: the candidate's restriction
at the interior point `x = (σ,t)` is the local cross of `M`'s local fundamental class. Both are
`[prismOp graphHom z]` rel `{x}ᶜ` at the chain level (frozen `restrictBd_cylFundClassCandidate` +
`crossHloc_mk`, the underlying prism chain matched after stripping the identity pushforward). -/
theorem restrictBd_candidate_eq_crossHloc
    (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M))
    (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    restrictBd (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) hx (m' + 1 + 2)
        (cylFundClassCandidate (M := M) (m' := m'))
      = crossHloc (M := TopCat.of M) (interior_slice_one x hx) (interior_slice_zero x hx)
          (interior_punc x) (m' + 1) (mLocalClass x z) := by
  rw [restrictBd_cylFundClassCandidate x hx z hz, mLocalClass, crossHloc_mk]
  refine congrArg (RelativeHomology.mk ({x}ᶜ : Set ↑(cyl (TopCat.of M))) (m' + 1 + 2))
    (Subtype.ext ?_)
  rw [relCyclesMap_coe]
  show relMapChain (ContinuousMap.id ↑(TopCat.of (cylW M))) _ (m' + 1 + 2)
      (RelativeChain.mk ((cylModel m').boundary (cylW M)) (m' + 1 + 2)
        (crossChain (m' + 2) (z : SingularChain (TopCat.of M) (m' + 2))))
    = crossRelChainLM (interior_punc x) (m' + 1)
        (RelativeChain.mk ({x.1}ᶜ : Set ↑(TopCat.of M)) (m' + 2)
          (z : SingularChain (TopCat.of M) (m' + 2)))
  rw [relMapChain_mk, SKEFTHawking.SingularFunctoriality.mapChain_id, crossRelChainLM_mk]
  rfl

/-- **The candidate's restriction is nonzero at `x`, given local-cross injectivity there.** With
`crossHloc` injective at the interior point `x`, `restrictBd candidate = crossHloc ([M]|_σ) ≠ 0`
(since `[M]|_σ ≠ 0` and injective maps send nonzero to nonzero). -/
theorem restrictBd_candidate_ne_zero_of_crossHloc_injective
    (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M))
    (hinj : Function.Injective (crossHloc (M := TopCat.of M) (interior_slice_one x hx)
      (interior_slice_zero x hx) (interior_punc x) (m' + 1))) :
    restrictBd (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) hx (m' + 1 + 2)
      (cylFundClassCandidate (M := M) (m' := m')) ≠ 0 := by
  obtain ⟨z, hz0⟩ := Submodule.Quotient.mk_surjective _
    (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M))
  have hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z := hz0.symm
  rw [restrictBd_candidate_eq_crossHloc x hx z hz]
  intro hcross
  exact mLocalClass_ne_zero x z hz (hinj (by rw [hcross, map_zero]))

/-- **The concrete cylinder `HasRelFundClass`, reduced to local-cross injectivity.** If the local cross
`crossHloc` is injective at every interior point (the interior local-Künneth nonvanishing, isolated as
a well-defined-map property), the terminal `hcls` hole of the concrete cylinder datum is discharged. -/
theorem hasRelFundClass_cylGen_of_crossHloc_injective [T1Space (cylW M)]
    (hinj : ∀ (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)),
      Function.Injective (crossHloc (M := TopCat.of M) (interior_slice_one x hx)
        (interior_slice_zero x hx) (interior_punc x) (m' + 1))) :
    HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
      (cylGen (M := M) (m' := m')) :=
  hasRelFundClass_of_candidate_ne_zero
    (fun x hx => restrictBd_candidate_ne_zero_of_crossHloc_injective x hx (hinj x hx))

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalReduce
