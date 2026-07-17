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
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularMayerVietorisLES
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelClassHomologous
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

/-! ## §2. Detection transfer across barycentric subdivision (the controlled rep inherits detection).

The subdivided rep `Sdᵘ c` of a relative-cycle chain `c` (`∂c ∈ subspaceChains W`) satisfies
`∂(Sdᵘ c) = Sdᵘ(∂c)` — so its boundary splits exactly whenever `∂c`'s cover-split does — and it is
homologous to `c` with the homotopy correction `Dᵤ(∂c)` supported in `W ⊆ {y}ᶜ`. Hence the interior
detection `relClassOf {y}ᶜ` transfers verbatim from `c` to `Sdᵘ c` (`relClassOf_eq_of_homologous`,
#189). This is the exact tool step 2 uses: the controlled (subdivided) disk rep inherits
`diskDetectChain_hdet`. -/

/-- **`∂(Sdᵘ c)` lands in the same subspace as `∂c`.** `Sd` is a chain map (`∂Sdᵘ = Sdᵘ∂`) and
iterated `Sd` preserves supports (`singularSd_iterate_mem_subspaceChains`). -/
theorem chainBoundary_singularSd_iterate_mem {W : Set ↑X} (m : ℕ) (c : SingularChain X (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains W (m + 1)) (μ : ℕ) :
    chainBoundary X (m + 1) ((⇑(singularSd X (m + 2)))^[μ] c) ∈ subspaceChains W (m + 1) := by
  rw [singularSd_iterate_chainBoundary]
  exact SingularExcision.singularSd_iterate_mem_subspaceChains hc μ

/-- **Detection transfers across subdivision.** For a relative-cycle chain `c` (`∂c` supported in `W`)
and an interior point `y ∉ W`, the subdivided rep `Sdᵘ c` has the same `({y}ᶜ)`-relative class as `c`:
`relClassOf {y}ᶜ (Sdᵘ c) = relClassOf {y}ᶜ c`. So `Sdᵘ c` detects the local generator at `y` exactly
when `c` does. Via `relClassOf_eq_of_homologous` on the char-2 homotopy identity
`Sdᵘ c = c + ∂(Dᵤ c) + Dᵤ(∂c)`, with the correction `Dᵤ(∂c)` supported in `W ⊆ {y}ᶜ`. -/
theorem relClassOf_singularSd_iterate_eq {W : Set ↑X} (m : ℕ) (c : SingularChain X (m + 2))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains W (m + 1)) (μ : ℕ) (y : ↑X) (hy : y ∉ W) :
    relClassOf ({y}ᶜ) m ((⇑(singularSd X (m + 2)))^[μ] c)
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m + 1)
          (chainBoundary_singularSd_iterate_mem m c hc μ))
      = relClassOf ({y}ᶜ) m c
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m + 1) hc) := by
  have hhom := iterHomotopy_chainHomotopy X μ (m + 1) c
  have hcongr : (⇑(singularSd X (m + 2)))^[μ] c
      = c + chainBoundary X (m + 2) (iterHomotopy X (m + 2) μ c)
        + iterHomotopy X (m + 1) μ (chainBoundary X (m + 1) c) := by
    have h : c + (⇑(singularSd X (m + 2)))^[μ] c
        = chainBoundary X (m + 2) (iterHomotopy X (m + 2) μ c)
          + iterHomotopy X (m + 1) μ (chainBoundary X (m + 1) c) := hhom.symm
    rw [add_assoc, ← h, ← add_assoc, ZModModule.add_self, zero_add]
  have he : iterHomotopy X (m + 1) μ (chainBoundary X (m + 1) c) ∈ subspaceChains W (m + 2) :=
    SingularExcision.iterHomotopy_mem_subspaceChains hc μ
  exact relClassOf_eq_of_homologous (Set.subset_compl_singleton_iff.mpr hy) m hcongr he
    (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m + 1)
      (chainBoundary_singularSd_iterate_mem m c hc μ))
    (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m + 1) hc)

/-! ## §3. The disk-side split producer — the controlled rep's boundary splits exactly. -/

/-- **The controlled rep's boundary splits into a subtype-pushforward + complementary remainder,
staying boundary-supported.** For a relative-cycle chain `c` (`∂c` supported in `W`, `W ⊆ U ∪ V` an
open cover), there is a subdivision count `μ` such that the controlled rep `Sdᵘ c` has
`∂(Sdᵘ c) = mapChain (ambIncl U) cU + vOut` — the attached part `mapChain (ambIncl U) cU` a
pushforward from `↥U`, the remainder `vOut ∈ subspaceChains V` — while `∂(Sdᵘ c)` remains supported in
`W`. Because `∂(Sdᵘ c) = Sdᵘ(∂c)` (chain map) and `∂c` is a cycle, the split is the exact
`hsplitHa`/`hsplit` shape for the controlled rep; combined with `relClassOf_singularSd_iterate_eq`
(§2), `Sdᵘ c` also inherits `c`'s interior detection. The disk-side seam split, reduced to the open
cover `{U, V}` of the boundary-support set `W`. -/
theorem exists_subtype_boundary_split_of_relCycle [T2Space ↑X] {U V W : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V) (hWUV : W ⊆ U ∪ V) {m : ℕ} (c : SingularChain X (m + 2))
    (hbd : chainBoundary X (m + 1) c ∈ subspaceChains W (m + 1)) :
    ∃ (μ : ℕ) (cU : SingularChain (sub U) (m + 1)) (vOut : SingularChain X (m + 1)),
      vOut ∈ subspaceChains V (m + 1)
      ∧ chainBoundary X (m + 1) ((⇑(singularSd X (m + 2)))^[μ] c)
          = mapChain (ambIncl U) (m + 1) cU + vOut
      ∧ chainBoundary X (m + 1) ((⇑(singularSd X (m + 2)))^[μ] c) ∈ subspaceChains W (m + 1) := by
  have hcyc : chainBoundary X m (chainBoundary X (m + 1) c) = 0 :=
    chainBoundary_chainBoundary_apply X m c
  obtain ⟨μ, cU, vOut, hvOut, hsplit, _⟩ :=
    exists_subtype_cover_split_homologous_cycle hU hV (chainBoundary X (m + 1) c)
      (subspaceChains_mono hWUV (m + 1) hbd) hcyc
  refine ⟨μ, cU, vOut, hvOut, ?_, chainBoundary_singularSd_iterate_mem m c hbd μ⟩
  rw [singularSd_iterate_chainBoundary]
  exact hsplit

end

end SKEFTHawking.PinPlusTraceCapstoneSeamSplit
