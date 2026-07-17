/-
# Phase 5q.H close-out — THE SEAM SPLIT ENGINE: the #189 cover-split repackaged into the
# subtype-pushforward shape the capstone seam datum consumes.

The capstone seam datum `CapstoneSeamTransferSeam` (`PinPlusTraceCapstoneSeamTransferSupply`) demands
its attached faces in the EXACT shape `mapChain (ambIncl U) cSeam` — a pushforward from the subtype
`↥U` (its two legs `seamLegCyl`/`seamLegHa` are the subtype inclusions) — plus a remainder supported
in the complementary cover set, exhibited as HOMOLOGOUS to the original chain (so detection transfers
via `relClassOf_eq_of_homologous`, #189). The subdivision-to-cover engine
(`exists_cover_split_homologous`, #189) delivers the split with the attached part only as
`fU ∈ subspaceChains U` — a chain SUPPORTED in `U`, not visibly a subtype pushforward. This module
closes that last gap:

* `mem_subspaceChains_iff_exists_mapChain_ambIncl` — the "supported ⟹ subtype-pushforward" bridge:
  `c ∈ subspaceChains U ↔ ∃ cU, mapChain (ambIncl U) cU = c` (from `subspaceChains = range chainIncl`
  and `mapChain_ambIncl : mapChain (ambIncl U) = chainIncl U`).
* `exists_subtype_cover_split_homologous` / `_cycle` — the #189 engine in the consumed shape: for an
  open cover `{U, V}` and a chain `f` supported in `U ∪ V`, a subdivision count `μ`, a subtype chain
  `cU : SingularChain (sub U)`, and a remainder `fV ∈ subspaceChains V` with
  `Sdᵘ f = mapChain (ambIncl U) cU + fV`, homologous to `f` (general / cycle correction). The exact
  `hsplit`/`hsplitHa` shape (pushforward-from-subtype + complementary remainder).

**The residual (honest, NOT here).** The concrete disk-side instantiation over `{nbhd S, nbhd(S⁴ ∖ S)}`
fights the OPEN-cover hypothesis: the surgery region `S ⊆ D⁵` is CLOSED, so the engine yields the
attached part over an open nbhd `U ⊇ S`, not over `S` itself; pushing `↥U`-content down to `↥S` (the
collar retraction) and the co-adaptation of the SHARED seam chain across the two attaching legs
(`hsplit`/`hsplitHa` demanding the same `cSeam` through `φ` and `incl`) remain the genuine geometric
atoms. This module supplies the engine; the concrete tie is the separate final brick.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project
axiom, no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularSubdivisionToCover
import SKEFTHawking.SingularRelClassHomologous

namespace SKEFTHawking.PinPlusTraceCapstoneSeamSplit

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularSubdivision
open SKEFTHawking.SingularSubdivisionToCover

noncomputable section

variable {X : TopCat}

/-- **The "supported ⟹ subtype-pushforward" bridge.** A chain `c` is supported in `U`
(`c ∈ subspaceChains U`) iff it is the pushforward `mapChain (ambIncl U) cU` of a chain `cU` on the
subtype `↥U`. Immediate from `subspaceChains U = range (chainIncl U)` and the chainIncl–mapChain
bridge `mapChain_ambIncl : mapChain (ambIncl U) = chainIncl U`. This turns the subdivision engine's
raw `fU ∈ subspaceChains U` into the exact subtype-pushforward shape the seam datum needs. -/
theorem mem_subspaceChains_iff_exists_mapChain_ambIncl (U : Set ↑X) (n : ℕ)
    (c : SingularChain X n) :
    c ∈ subspaceChains U n ↔ ∃ cU : SingularChain (sub U) n, mapChain (ambIncl U) n cU = c := by
  rw [subspaceChains, ← mapChain_ambIncl]
  exact LinearMap.mem_range

/-- **The subdivision-to-cover engine, subtype-pushforward form.** For a chain `f` supported in the
union `U ∪ V` of a two-set open cover, there is a subdivision count `μ`, a subtype chain
`cU : SingularChain (sub U)` and a remainder `fV ∈ subspaceChains V` with
`Sdᵘ f = mapChain (ambIncl U) cU + fV`, and `fU ∪ fV = Sdᵘ f` homologous to `f` via the subdivision
prism correction `f + (mapChain (ambIncl U) cU + fV) = ∂(Dᵤ f) + Dᵤ(∂f)`. Repackages
`exists_cover_split_homologous` (#189) with the attached part exposed as a pushforward from `↥U` — the
exact `hsplit`/`hsplitHa` shape (pushforward-from-subtype + complementary remainder). -/
theorem exists_subtype_cover_split_homologous [T2Space ↑X] {U V : Set ↑X} (hU : IsOpen U)
    (hV : IsOpen V) {n : ℕ} (f : SingularChain X (n + 1)) (hf : f ∈ subspaceChains (U ∪ V) (n + 1)) :
    ∃ (μ : ℕ) (cU : SingularChain (sub U) (n + 1)) (fV : SingularChain X (n + 1)),
      fV ∈ subspaceChains V (n + 1)
      ∧ (⇑(singularSd X (n + 1)))^[μ] f = mapChain (ambIncl U) (n + 1) cU + fV
      ∧ f + (mapChain (ambIncl U) (n + 1) cU + fV)
        = chainBoundary X (n + 1) (iterHomotopy X (n + 1) μ f)
          + iterHomotopy X n μ (chainBoundary X n f) := by
  obtain ⟨μ, fU, fV, hfU, hfV, hsplit, hhom⟩ := exists_cover_split_homologous hU hV f hf
  obtain ⟨cU, hcU⟩ := hfU
  have hmap : mapChain (ambIncl U) (n + 1) cU = fU := by rw [mapChain_ambIncl]; exact hcU
  refine ⟨μ, cU, fV, hfV, ?_, ?_⟩
  · rw [hsplit, hmap]
  · rw [hmap]; exact hhom

/-- **The subdivision-to-cover engine for a cycle, subtype-pushforward form.** When `f` is a cycle
(`∂f = 0`) the boundary correction collapses to a pure boundary `∂(Dᵤ f)`, so the split
`mapChain (ambIncl U) cU + fV` is genuinely HOMOLOGOUS to `f`. The form the seam cycles (`z@⊤`, `∂cHa`
— both cycles) ride on, exposing the attached part as a pushforward from `↥U`. -/
theorem exists_subtype_cover_split_homologous_cycle [T2Space ↑X] {U V : Set ↑X} (hU : IsOpen U)
    (hV : IsOpen V) {n : ℕ} (f : SingularChain X (n + 1)) (hf : f ∈ subspaceChains (U ∪ V) (n + 1))
    (hcyc : chainBoundary X n f = 0) :
    ∃ (μ : ℕ) (cU : SingularChain (sub U) (n + 1)) (fV : SingularChain X (n + 1)),
      fV ∈ subspaceChains V (n + 1)
      ∧ (⇑(singularSd X (n + 1)))^[μ] f = mapChain (ambIncl U) (n + 1) cU + fV
      ∧ f + (mapChain (ambIncl U) (n + 1) cU + fV)
        = chainBoundary X (n + 1) (iterHomotopy X (n + 1) μ f) := by
  obtain ⟨μ, fU, fV, hfU, hfV, hsplit, hhom⟩ := exists_cover_split_homologous_cycle hU hV f hf hcyc
  obtain ⟨cU, hcU⟩ := hfU
  have hmap : mapChain (ambIncl U) (n + 1) cU = fU := by rw [mapChain_ambIncl]; exact hcU
  refine ⟨μ, cU, fV, hfV, ?_, ?_⟩
  · rw [hsplit, hmap]
  · rw [hmap]; exact hhom

end

end SKEFTHawking.PinPlusTraceCapstoneSeamSplit
