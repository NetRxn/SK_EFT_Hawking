import Mathlib
import SKEFTHawking.SingularConnSquareMatch
import SKEFTHawking.SingularConnSquareLHS
import SKEFTHawking.SingularConnSquareLHSCover
import SKEFTHawking.SingularConnSquareCloseFinal
import SKEFTHawking.SingularConnSquareRHSPairing
import SKEFTHawking.SingularCapSubKDuality
import SKEFTHawking.SingularOpenDualityCycle
import SKEFTHawking.SingularHcrossClose
import SKEFTHawking.SingularCoverPartitionExist
import SKEFTHawking.SingularConnSquareLHSExplicit
import SKEFTHawking.SingularAbsCohomConnGeom
import SKEFTHawking.SingularConnSquareLHSRealize
import SKEFTHawking.SingularRelCohomSetCongrMk
import SKEFTHawking.SingularConnSquareMatchCross
import SKEFTHawking.SingularConnSquareHLHSBridge
import SKEFTHawking.SingularConnSquarePartitionRelate
import SKEFTHawking.SingularRcapCoverAgree
import SKEFTHawking.SingularMvDeltaPartition
import SKEFTHawking.SingularConnSquareCloseChainMap

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-NC) — non-circular connecting-square closure (WIP)

Closes the per-`K` Poincaré-duality connecting square `subHomConnecting (legW K g) = openDuality (legδ K g)`
by reducing it (via `SingularConnSquareMatch.subHomConnecting_openDuality_of_match`, which discharges all
leg/colimit machinery through Kronecker non-degeneracy) to the single relative-Kronecker **MATCH M**
`hmatch`, then closing `hmatch` via the **cup-form PAIRING route** (route B, 2026-06-22): both legs reduce
to `⟨grep ∪ a', z₀⟩` on the single shared `z₀` via `SingularConnSquareRHSPairing.pair_fund_eq_pair_z0`
(a cocycle `c = grep ∪ a'` vanishing on `C(Kᶜ)` pairs identically against `fund` and `z₀` when they are
rel-homologous). The hmem/excision gap is cap-form/class-altitude only; the pairing form sidesteps it
(`relKroneckerH_relMvDelta_pairing` is unconditional).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularCohomologySnake
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularConnSquareMatch
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularConnSquareLHS

namespace SKEFTHawking.SingularConnSquareCloseNC

variable {X : TopCat} [T2Space ↑X]

/-- **Seam-telescope (whnf-free, explicit seam variables).** With the two seam homeos as EXPLICIT `C(·,·)`
variables (NOT the anonymous `{toFun, continuous_toFun}` structs of the concrete `hmatch` goal, which whnf-wall
the `kronecker_mapChain` `rw` — the documented HLHSBridge obstacle), the double `pullbackCochainMap` on the
cochain telescopes onto the chain as the double `mapChain`. Applied to `SingularConnSquareCloseChainMap`'s
`hmatch` to move the seam transport off `a'rep` (Lean instantiates the variables to the concrete seam structs). -/
theorem kronecker_double_pullback {Y Z W : TopCat} (φseam : C(↑Y, ↑Z)) (φsub : C(↑W, ↑Y)) (n : ℕ)
    (a : SingularCochain Z n) (c : SingularChain W n) :
    kronecker (SingularKroneckerFunctoriality.pullbackCochainMap φsub n
        (SingularKroneckerFunctoriality.pullbackCochainMap φseam n a)) c
      = kronecker a (SingularFunctoriality.mapChain φseam n (SingularFunctoriality.mapChain φsub n c)) := by
  rw [← SingularKroneckerFunctoriality.kronecker_mapChain,
    ← SingularKroneckerFunctoriality.kronecker_mapChain]

/-- **Pullback of a relative cochain vanishes.** A cochain `a` that vanishes on the subspace chains
`subspaceChains S` (i.e. `a ∈ relCochains S`) pulls back to `0` along `sub S ↪ X`: on a basis `sub S`-simplex
`τ`, `pullbackCochain S a τ = a (simplexIncl S τ) = ⟨a, chainIncl S (single τ 1)⟩ = 0`. This is the
`legSplitUᶜ`-part-vanishing engine for the seam-term cover-partition: in `exists_cap_cover_partition` the
`A`-part `cap (pullbackCochain A (cochainSplit A ω)) u` dies because `cochainSplit A ω ∈ relCochains A`. -/
theorem pullbackCochain_relCochains_eq_zero {M₀ : TopCat} {S : Set ↑M₀} (k : ℕ)
    (a : SingularCochain M₀ k) (ha : a ∈ relCochains S k) :
    SingularCapChainIncl.pullbackCochain S k a = 0 := by
  funext τ
  rw [SingularCapChainIncl.pullbackCochain_apply]
  have h0 := ha _ (LinearMap.mem_range_self (chainIncl S k) (Finsupp.single τ 1))
  rwa [chainIncl_single, kronecker_single, one_mul] at h0

/-- **Cap cover-localization to the `B`-part** (chain-altitude; the cap analogue of LHSCover's
`cup_cover_pairing_sd`). For a cover `{A, B}`, a cochain `g` that vanishes on `A` (`g ∈ relCochains A`),
and an `(A∪B)`-supported chain `z`, some subdivision `Sdᵐz` cover-splits and the `A`-part of the cap
`cap g (Sdᵐz)` dies (`pullbackCochain A g = 0`), localizing the whole cap onto the `B`-part. This is the
seam-localization engine: with `g = cochainSplit (legSplitUᶜ) ω'`, `A = legSplitUᶜ`, `B = legSplitVᶜ`, the
seam-term cap onto `∂F ∈ subspaceChains(legSplitUᶜ ∪ legSplitVᶜ)` reads off as the pure `legSplitVᶜ`-part. -/
theorem cap_cover_localize_to_B {M : TopCat} {k l : ℕ} (A B : Set ↑M) (hA : IsOpen A) (hB : IsOpen B)
    (g : SingularCochain M k) (hg : g ∈ relCochains A k) (z : SingularChain M (k + l))
    (hz : z ∈ subspaceChains (A ∪ B) (k + l)) :
    ∃ (m : ℕ) (w : SingularChain (sub B) (k + l)),
      cap g ((⇑(SingularSubdivision.singularSd M (k + l)))^[m] z)
        = chainIncl B l (cap (SingularCapChainIncl.pullbackCochain B k g) w) := by
  obtain ⟨m, u, w, _, hcap⟩ :=
    SingularConnSquareRHSScaffold.exists_cap_cover_partition A B hA hB g z hz
  refine ⟨m, w, ?_⟩
  rw [hcap]
  have hA0 : (cap (SingularCapChainIncl.pullbackCochain A k g)) u = 0 := by
    rw [pullbackCochain_relCochains_eq_zero k g hg, ← capₗ_apply, map_zero, LinearMap.zero_apply]
  rw [hA0, map_zero, zero_add]

/-- **chainIncl-injection of the seam-term cap** (whnf-free glue). The sub-space cap of a pulled-back
cochain against a sub-space boundary `chainIncl`-injects to the *ambient* cap of the original cochain
against the ambient boundary: `chainIncl (cap (pullbackCochain S φ) (∂c)) = cap φ (∂(chainIncl c))`, via
`cap_chainIncl` (cap–chainIncl naturality) + `chainIncl_chainBoundary` (chainIncl is a chain map). This is
the bridge that lifts the concrete seam-term into the ambient `X` where `cap_cover_localize_to_B` applies
(the `{M, S}` binders keep it whnf-free over the concrete `realize F`). -/
theorem cap_pullback_chainBoundary_chainIncl {M : TopCat} {S : Set ↑M} {k m : ℕ}
    (φ : SingularCochain M k) (c : SingularChain (sub S) (k + m + 1)) :
    chainIncl S m (cap (SingularCapChainIncl.pullbackCochain S k φ) (chainBoundary (sub S) (k + m) c))
      = cap φ (chainBoundary M (k + m) (chainIncl S (k + m + 1) c)) := by
  rw [← SingularCapChainIncl.cap_chainIncl, chainIncl_chainBoundary]

/-- **Cap subdivision-invariance with the δφ-coupling made explicit** (chain-altitude). For a cycle `z`
(`∂z = 0`), `cap φ z` equals `cap φ (Sdʲz)` up to a boundary `∂(cap φ Dⱼz)` PLUS the non-cocycle correction
`cap (δφ)(Dⱼz)` (since `φ` need not be a cocycle), where `Dⱼz = iterHomotopy` is the subdivision chain
homotopy. From `add_singularSd_iterate_eq_boundary` (`z + Sdʲz = ∂Dⱼz`, type-ascribed to the `k+(m+1)` degree
so it matches `cap_leibniz`'s output) + `cap_leibniz`. The `δφ`-term folds the seam-term subdivision into the
χ-term (the two facts are coupled); the boundary term absorbs into the bounding chain `W`. -/
theorem cap_singularSd_iterate {M : TopCat} {k m : ℕ} (φ : SingularCochain M k)
    {z : SingularChain M (k + (m + 1))} (hz : chainBoundary M (k + m) z = 0) (j : ℕ) :
    cap φ z = cap φ ((⇑(SingularSubdivision.singularSd M (k + (m + 1))))^[j] z)
        + chainBoundary M (m + 1) (cap φ (SingularSubdivision.iterHomotopy M (k + (m + 1)) j z))
        + cap (coboundary M k φ) ((show k + (m + 1) + 1 = k + 1 + (m + 1) from by omega) ▸
            SingularSubdivision.iterHomotopy M (k + (m + 1)) j z) := by
  have hb : z + (⇑(SingularSubdivision.singularSd M (k + (m + 1))))^[j] z
      = chainBoundary M (k + (m + 1)) (SingularSubdivision.iterHomotopy M (k + (m + 1)) j z) :=
    SingularExcision.add_singularSd_iterate_eq_boundary hz j
  have hcl := cap_leibniz φ (SingularSubdivision.iterHomotopy M (k + (m + 1)) j z)
    (show k + (m + 1) + 1 = k + 1 + (m + 1) from by omega)
  rw [hcl, ← hb, map_add]
  abel_nf
  simp only [two_smul, ZModModule.add_self, zero_add]

/-- **Sdʲ-bridge on a `∂`-argument** (the NC engine introduces a `Sdʲ` the recipe's Term2/(B) lacks; this
removes it). For ANY cochain `φ` and chain `c`, the cap of `φ` against the boundary of the `j`-fold
subdivision of `c` equals the cap against the un-subdivided boundary, modulo a boundary and the non-cocycle
`δφ`-correction. Pure `singularSd_iterate_chainBoundary` (`∂∘Sdʲ = Sdʲ∘∂`, on the `∂c` cycle) + the shipped
`cap_singularSd_iterate` (at `z = ∂c`); the ℤ/2 swap closes it. Generic in `φ, c` ⟹ **whnf-free**: `rw` it at
the concrete `hVleg` to land the recipe's Sdʲ-free `cap φ (∂fund)` without ever assembling the concrete cap. -/
theorem cap_singularSd_iterate_chainBoundary_arg {M : TopCat} {k m : ℕ} (φ : SingularCochain M k)
    (c : SingularChain M (k + (m + 1) + 1)) (j : ℕ) :
    cap φ (chainBoundary M (k + (m + 1))
        ((⇑(SingularSubdivision.singularSd M (k + (m + 1) + 1)))^[j] c))
      = cap φ (chainBoundary M (k + (m + 1)) c)
        + chainBoundary M (m + 1)
            (cap φ (SingularSubdivision.iterHomotopy M (k + (m + 1)) j
                (chainBoundary M (k + (m + 1)) c)))
        + cap (coboundary M k φ)
            ((show k + (m + 1) + 1 = k + 1 + (m + 1) from by omega) ▸
              SingularSubdivision.iterHomotopy M (k + (m + 1)) j
                (chainBoundary M (k + (m + 1)) c)) := by
  rw [SingularSubdivision.singularSd_iterate_chainBoundary]
  have hz : chainBoundary M (k + m) (chainBoundary M (k + (m + 1)) c) = 0 :=
    chainBoundary_chainBoundary_apply M (k + m) c
  rw [cap_singularSd_iterate φ hz j]
  abel_nf
  simp only [two_smul, ZModModule.add_self, zero_add, add_zero]

/-- **`rcap` subdivision-invariance on a cycle, cocycle form** (STEP-A brick (a), the `rcap` analog of
`cap_singularSd_iterate`). Cochain degree is `l+1` (a successor) so the chain degree `k+(l+1) = (k+l)+1`
is successor-shaped DEFINITIONALLY — `rcap (k:=k) ω z` and `add_singularSd_iterate_eq_boundary` both
apply cast-free (the application has `ω : C^{p+1}`, `l := p`). For a cycle `z` (`∂z = 0`) and a COCYCLE
`ω` (`δω = 0`), `rcap ω z = rcap ω (Sdʲz) + ∂(rcap ω (Dⱼz))` — NO δω-correction term (the cap version
carries `cap (δφ)(Dⱼz)`; for a cocycle that vanishes). From `add_singularSd_iterate_eq_boundary`
(`z + Sdʲz = ∂(Dⱼz)`) → `map_add` → `rcap_cocycle_chainMap (k:=k)` (`∂(rcap (k:=k+1) ω (cast ▸ Dⱼz)) =
rcap (k:=k) ω (∂Dⱼz)`). The single `rcap (k:=k+1)` cast on the `Dⱼz` term matches the chain-map's native
cast. This routes the Sd-slack of `rcap ω` through `∂c`, the precise gap the seam-match needs. -/
theorem rcap_singularSd_iterate {M : TopCat} {k l : ℕ} (ω : SingularCochain M (l + 1))
    (hω : coboundaryₗ M (l + 1) ω = 0) {z : SingularChain M (k + (l + 1))}
    (hz : chainBoundary M (k + l) z = 0) (j : ℕ) :
    SingularCapChainIncl.rcap (k := k) ω z
      = SingularCapChainIncl.rcap (k := k) ω
          ((⇑(SingularSubdivision.singularSd M (k + (l + 1))))^[j] z)
        + chainBoundary M k
            (SingularCapChainIncl.rcap (k := k + 1) ω
              ((show k + (l + 1) + 1 = k + 1 + (l + 1) from by omega) ▸
                SingularSubdivision.iterHomotopy M (k + (l + 1)) j z)) := by
  have hb : z + (⇑(SingularSubdivision.singularSd M (k + (l + 1))))^[j] z
      = chainBoundary M (k + (l + 1)) (SingularSubdivision.iterHomotopy M (k + (l + 1)) j z) :=
    SingularExcision.add_singularSd_iterate_eq_boundary hz j
  have hcm := SingularRightCapBoundary.rcap_cocycle_chainMap (k := k) ω hω
    (SingularSubdivision.iterHomotopy M (k + (l + 1)) j z)
  rw [hcm, ← hb, map_add]
  abel_nf
  simp only [two_smul, ZModModule.add_self, zero_add]

/-- **`rcap` Sd-bridge on a `∂`-argument, cocycle form** (STEP-A brick (b); the `rcap` analog of
`cap_singularSd_iterate_chainBoundary_arg`). For a COCYCLE `ω` (`δω = 0`) and ANY chain `c`, capping `ω`
against the boundary of the `j`-fold subdivision of `c` equals capping against the un-subdivided boundary,
modulo a boundary (NO δω-correction — `ω` is a cocycle). Pure `singularSd_iterate_chainBoundary`
(`∂(Sdʲc) = Sdʲ(∂c)`) + brick (a) `rcap_singularSd_iterate` on the cycle `z := ∂c` (`∂z = ∂∂c = 0`); ℤ/2
swap. Generic in `c` (cochain degree `l+1`, successor) ⟹ whnf-free; this is the brick STEP-B's hRHS
consumes to route the rcap-Sd slack through `∂c` (cover-supported) rather than `c`. -/
theorem rcap_singularSd_iterate_chainBoundary_arg {M : TopCat} {k l : ℕ}
    (ω : SingularCochain M (l + 1)) (hω : coboundaryₗ M (l + 1) ω = 0)
    (c : SingularChain M (k + (l + 1) + 1)) (j : ℕ) :
    SingularCapChainIncl.rcap (k := k) ω
        (chainBoundary M (k + (l + 1)) ((⇑(SingularSubdivision.singularSd M (k + (l + 1) + 1)))^[j] c))
      = SingularCapChainIncl.rcap (k := k) ω (chainBoundary M (k + (l + 1)) c)
        + chainBoundary M k
            (SingularCapChainIncl.rcap (k := k + 1) ω
              ((show k + (l + 1) + 1 = k + 1 + (l + 1) from by omega) ▸
                SingularSubdivision.iterHomotopy M (k + (l + 1)) j
                  (chainBoundary M (k + (l + 1)) c))) := by
  rw [SingularSubdivision.singularSd_iterate_chainBoundary]
  have hz : chainBoundary M (k + l) (chainBoundary M (k + (l + 1)) c) = 0 :=
    chainBoundary_chainBoundary_apply M (k + l) c
  rw [rcap_singularSd_iterate ω hω hz j]
  abel_nf
  simp only [two_smul, ZModModule.add_self, add_zero]

/-- **Seam-localization composite** (bricks 2 + 4 assembled, chain-altitude, whnf-free). For a cover `{A, B}`,
a cochain `φ` vanishing on `A` (`φ ∈ relCochains A`), and an `(A∪B)`-supported cycle `w`, the cap `cap φ w`
decomposes as the pure `B`-cover-part `chainIncl B (cap (pullbackCochain B φ) w')` (the `A`-part dies — brick 2)
PLUS a boundary `∂(cap φ Dⱼw)` PLUS the non-cocycle δφ-correction `cap (δφ)(Dⱼw)` (brick 4). The subdivision
count `j` is the one `cap_cover_localize_to_B` produces; `cap_singularSd_iterate` is applied at that same `j`.
This is the engine the concrete seam-term consumes (via `cap_pullback_chainBoundary_chainIncl` to reach the
ambient cap): the `B`-part heads to the V-link, the δφ-term folds into the χ. -/
theorem seam_cap_localize {M : TopCat} {k m : ℕ} (A B : Set ↑M) (hA : IsOpen A) (hB : IsOpen B)
    (φ : SingularCochain M k) (hφ : φ ∈ relCochains A k)
    {w : SingularChain M (k + (m + 1))} (hw_cyc : chainBoundary M (k + m) w = 0)
    (hw : w ∈ subspaceChains (A ∪ B) (k + (m + 1))) :
    ∃ (j : ℕ) (w' : SingularChain (sub B) (k + (m + 1))),
      cap φ w = chainIncl B (m + 1) (cap (SingularCapChainIncl.pullbackCochain B k φ) w')
        + chainBoundary M (m + 1) (cap φ (SingularSubdivision.iterHomotopy M (k + (m + 1)) j w))
        + cap (coboundary M k φ) ((show k + (m + 1) + 1 = k + 1 + (m + 1) from by omega) ▸
            SingularSubdivision.iterHomotopy M (k + (m + 1)) j w) := by
  obtain ⟨j, w', hloc⟩ := cap_cover_localize_to_B A B hA hB φ hφ w hw
  exact ⟨j, w', by rw [cap_singularSd_iterate φ hw_cyc j, hloc]⟩

/-- **A cocycle pairs to zero against any boundary** (chain-altitude, whnf-free): `⟨a, ∂W⟩ = ⟨δa, W⟩ = 0`.
Stated over an abstract space/degree so its proof never whnf's the giant `fundCycleW` carriers — the
chain-pairing engine that closes the hLHS leg without lifting to the (whnf-walled) homology class square. -/
theorem kronecker_cocycle_boundary_eq_zero {Y : TopCat} {n : ℕ}
    (a : ↥(coboundaryₗ Y n).ker) {c : SingularChain Y n} (hc : c ∈ boundaries Y n) :
    kronecker (↑a) c = 0 := by
  obtain ⟨W, hW⟩ := hc
  rw [← hW, ← kronecker_coboundary_chainBoundary,
    show coboundary Y n ↑a = 0 from LinearMap.mem_ker.mp a.2]
  simp

/-- **hmatch close (explicit seams).** Given the seam-localization `hseam` (the V-part boundary `lhs` equals
the double-seam-transport of the duality chain `d`, **mod a boundary**), the `hmatch` pairing closes:
telescope the double `pullbackCochainMap` off the cochain (`kronecker_double_pullback`), then the cocycle `a`
absorbs the boundary slack (`kronecker_cocycle_boundary_eq_zero`). The seams are EXPLICIT `C(·,·)` variables
so the `_of_chainMatch` call site supplies them by **unification** — which, unlike `rw`, sees through the
concrete anonymous `{toFun, continuous_toFun}` seam structs that whnf-wall the direct rewrite. This isolates
the genuine residual (the seam-localization) as the sole hypothesis `hseam`. -/
theorem hmatch_close {Y Z W : TopCat} (φseam : C(↑Y, ↑Z)) (φsub : C(↑W, ↑Y)) (n : ℕ)
    (a : ↥(coboundaryₗ Z n).ker) (lhs : SingularChain Z n) (d : SingularChain W n)
    (hseam : lhs + SingularFunctoriality.mapChain φseam n
        (SingularFunctoriality.mapChain φsub n d) ∈ boundaries Z n) :
    kronecker (↑a) lhs
      = kronecker (SingularKroneckerFunctoriality.pullbackCochainMap φsub n
          (SingularKroneckerFunctoriality.pullbackCochainMap φseam n (↑a))) d := by
  rw [kronecker_double_pullback]
  have h := kronecker_cocycle_boundary_eq_zero a hseam
  rw [kronecker_add_right] at h
  exact eq_of_sub_eq_zero (by rw [ZModModule.sub_eq_add]; exact h)

/-- **A reindexing homeomorphism's `mapChain` preserves AND reflects boundary-membership** (it is invertible:
`mapChain ⟨φ.symm,_⟩ ∘ mapChain ⟨φ,_⟩ = id` via `mapChain_comp` + `mapChain_id`). Lets the `hmatch` seam
transport (built from the reindexing homeos `seamHomeo` / `subSeamHomeo`) be peeled off the RHS, transporting
the residual to a single subspace. -/
theorem mapChain_homeo_mem_boundaries {Y Z : TopCat} (φ : ↥Y ≃ₜ ↥Z) {n : ℕ} (w : SingularChain Y n) :
    SingularFunctoriality.mapChain ⟨φ, φ.continuous⟩ n w ∈ boundaries Z n ↔ w ∈ boundaries Y n := by
  refine ⟨fun h => ?_, fun h => SingularFunctoriality.mapChain_mem_boundaries _ h⟩
  have h2 := SingularFunctoriality.mapChain_mem_boundaries (⟨φ.symm, φ.symm.continuous⟩ : C(↑Z, ↑Y)) h
  rwa [← SingularFunctoriality.mapChain_comp,
    show (⟨φ.symm, φ.symm.continuous⟩ : C(↑Z, ↑Y)).comp ⟨φ, φ.continuous⟩ = ContinuousMap.id ↑Y from
      by ext x; exact φ.symm_apply_apply x,
    SingularFunctoriality.mapChain_id] at h2

/-- **Reindexing-homeo `mapChain` round-trip cancels.** `mapChain ⟨φ.symm,_⟩ ∘ mapChain ⟨φ,_⟩ = id` — lets the
`hmatch` seam transport be peeled off the V-part boundary to land the residual in a single subspace. -/
theorem mapChain_homeo_symm_self {Y Z : TopCat} (φ : ↥Y ≃ₜ ↥Z) {n : ℕ} (w : SingularChain Y n) :
    SingularFunctoriality.mapChain ⟨φ.symm, φ.symm.continuous⟩ n
        (SingularFunctoriality.mapChain ⟨φ, φ.continuous⟩ n w) = w := by
  rw [← SingularFunctoriality.mapChain_comp,
    show (⟨φ.symm, φ.symm.continuous⟩ : C(↑Z, ↑Y)).comp ⟨φ, φ.continuous⟩ = ContinuousMap.id ↑Y from
      by ext x; exact φ.symm_apply_apply x,
    SingularFunctoriality.mapChain_id]

/-- **Fact-B seam transport (abstract, whnf-safe).** Over ABSTRACT `bz`/`pd` (the concrete `fundCycleW` never
enters, so no whnf wall), the reindexing seam isos move the residual: Fact B in `W` follows from `key` in `V'`
— pull `bz` down through both homeos, `pd` stays direct. The NC call site supplies `bz`/`pd` by unification
(metavar assignment — no whnf). -/
theorem factB_transport {W Z V' : TopCat} (φseam : ↥W ≃ₜ ↥Z) (φsub : ↥Z ≃ₜ ↥V') {n : ℕ}
    (bz : SingularChain W n) (pd : SingularChain V' n)
    (key : SingularFunctoriality.mapChain ⟨φsub, φsub.continuous⟩ n
        (SingularFunctoriality.mapChain ⟨φseam, φseam.continuous⟩ n bz) + pd ∈ boundaries V' n) :
    bz + SingularFunctoriality.mapChain ⟨φseam.symm, φseam.symm.continuous⟩ n
        (SingularFunctoriality.mapChain ⟨φsub.symm, φsub.symm.continuous⟩ n pd) ∈ boundaries W n := by
  have hb := SingularFunctoriality.mapChain_mem_boundaries (⟨φseam.symm, φseam.symm.continuous⟩ : C(↑Z, ↑W))
    (SingularFunctoriality.mapChain_mem_boundaries (⟨φsub.symm, φsub.symm.continuous⟩ : C(↑V', ↑Z)) key)
  rw [map_add, map_add, mapChain_homeo_symm_self, mapChain_homeo_symm_self] at hb
  exact hb

/-- **Cap-Leibniz membership** (the bounding-chain core of KEY): the cap-Leibniz two-term sum
`cap(δa)(c) + cap a (∂c)` is exactly `∂(cap a c)`, hence in `boundaries`. The ambient skeleton of KEY's
bounding chain `W = cap (cochainSplit g) F`. -/
theorem cap_leibniz_mem_boundaries {k m : ℕ} (a : SingularCochain X k)
    (c : SingularChain X (k + m + 1)) (h : k + m + 1 = k + 1 + m) :
    cap (coboundary X k a) (h ▸ c) + cap a (chainBoundary X (k + m) c) ∈ boundaries X m := by
  rw [← cap_leibniz a c h]
  exact ⟨cap a c, rfl⟩

/-- **Subspace cap-Leibniz realization** (KEY's bounding chain, realized in `sub K`): the `K`-realization
of the cap-Leibniz sum `cap(δa)(h▸c) + cap a (∂c)` is a boundary of `sub K`, bounded by the realization of
`cap a c`. Composes `subspaceChainsEquiv_symm_mem_boundaries` (the `chainIncl`-injective subspace bridge).
This is KEY's bounding chain `W = realize(cap (cochainSplit g) F)` — abstract over `a`, `c` (the concrete
`fundCycleW` never enters → no whnf wall). The cap-Leibniz expansion of `∂(cap a c)` happens in the
term-identification bricks downstream. -/
theorem realize_chainBoundary_cap_mem_boundaries (K : Set ↑X) {k n : ℕ} (a : SingularCochain X k)
    (c : SingularChain X (k + (n + 1) + 1))
    (hd : cap a c ∈ subspaceChains K (n + 2))
    (hsum : chainBoundary X (n + 1) (cap a c) ∈ subspaceChains K (n + 1)) :
    (SingularSubspaceChainsEquiv.subspaceChainsEquiv K (n + 1)).symm
        ⟨chainBoundary X (n + 1) (cap a c), hsum⟩ ∈ boundaries (sub K) (n + 1) :=
  SingularSubspaceChainsEquiv.subspaceChainsEquiv_symm_mem_boundaries K n _ hsum (cap a c) hd rfl

/-- **Two-facts ambient reduction** (whnf-dodging). The sub-`S` two-facts equality reduces to its ambient
`chainIncl`-image, via `chainIncl_injective` + per-term `cap_chainIncl` / `cap_pullback_chainBoundary_chainIncl`.
Stated over ABSTRACT carriers `Fcast, F, FR, chainL` so the per-term `cap_chainIncl` rewrites never whnf the
concrete `fundCycleW` (the 200k-whnf wall); applied to the concrete goal via `refine two_facts_via_ambient _ … ?_`
(underscores = the carriers, inferred structurally). The `?_` residual is the ambient two-facts = the V-link + χ
cross-realization core. -/
theorem two_facts_via_ambient {S : Set ↑X} {N p : ℕ}
    (dphi sigmaR : SingularCochain X (N + 2)) (phi : SingularCochain X (N + 1))
    (Fcast FR : SingularChain (sub S) (N + 2 + (p + 1)))
    (F : SingularChain (sub S) (N + 1 + (p + 1) + 1))
    (chainL : SingularChain (sub S) (p + 1))
    (hamb : cap dphi (chainIncl S (N + 2 + (p + 1)) Fcast)
          + cap phi (chainBoundary X (N + 1 + (p + 1)) (chainIncl S (N + 1 + (p + 1) + 1) F))
        = chainIncl S (p + 1) chainL + cap sigmaR (chainIncl S (N + 2 + (p + 1)) FR)) :
    cap (SingularCapChainIncl.pullbackCochain S (N + 2) dphi) Fcast
        + cap (SingularCapChainIncl.pullbackCochain S (N + 1) phi)
            (chainBoundary (sub S) (N + 1 + (p + 1)) F)
      = chainL + cap (SingularCapChainIncl.pullbackCochain S (N + 2) sigmaR) FR := by
  apply chainIncl_injective
  rw [map_add, map_add, ← SingularCapChainIncl.cap_chainIncl,
    cap_pullback_chainBoundary_chainIncl, ← SingularCapChainIncl.cap_chainIncl]
  exact hamb

/-- **Cap–`boundaryExtract` naturality, non-cocycle form** (the V-link cap↔boundary engine). The committed
`cap_boundaryExtract_naturality` (HLHSBridge:36) requires `a` a cocycle (`cap_cocycle_chainMap`); dropping that,
cap-Leibniz adds exactly the δa-correction:
  `chainIncl (cap (pullbackCochain a)(boundaryExtract w)) = ∂(cap a w) + cap (δa)(w)`.
This is the non-cocycle generalization that `cochainSplit` (a NON-cocycle, `δφ ≠ 0`) needs — the same δφ slack
the seam engine extracts. From `cap_chainIncl` + `chainIncl_boundaryExtract` + `cap_leibniz`. -/
theorem cap_boundaryExtract_naturality_noncocycle {S : Set ↑X} {k m : ℕ}
    (a : SingularCochain X k) (w : SingularPairLES.relCycleLift S (k + m)) :
    chainIncl S m (cap (SingularCapChainIncl.pullbackCochain S k a)
        (SingularPairLES.boundaryExtract S (k + m) w))
      = chainBoundary X m (cap a (w : SingularChain X (k + m + 1)))
        + cap (coboundary X k a)
            ((show k + m + 1 = k + 1 + m from by omega) ▸ (w : SingularChain X (k + m + 1))) := by
  rw [← SingularCapChainIncl.cap_chainIncl, SingularPairLES.chainIncl_boundaryExtract,
    cap_leibniz a (w : SingularChain X (k + m + 1)) (show k + m + 1 = k + 1 + m from by omega)]
  abel_nf
  simp only [two_smul, ZModModule.add_self, zero_add]

/-- **Cover-support of the realized boundary** (whnf-free; the `seam_cap_localize` prerequisite). The ambient
boundary of `chainIncl ((subspaceChainsEquiv S).symm s)` is just `∂(↑s)` (chainIncl inverts the pullback,
`chainIncl_subspaceChainsEquiv_symm`), so if the underlying chain's boundary is `K`-supported then so is the
realized one. Applied to the seam-term with `↑s = fundCycleW`, `K = legSplitUᶜ ∪ legSplitVᶜ`, `hbd =
fundCycleW_boundary` (∂fund ∈ subspaceChains(infCompactᶜ)) — feeds `seam_cap_localize`'s cover-support hyp. -/
theorem chainBoundary_chainIncl_subspaceChainsEquiv_symm_mem {S K : Set ↑X} {n : ℕ}
    (s : subspaceChains S (n + 1))
    (hbd : chainBoundary X n (s : SingularChain X (n + 1)) ∈ subspaceChains K n) :
    chainBoundary X n
        (chainIncl S (n + 1) ((SingularSubspaceChainsEquiv.subspaceChainsEquiv S (n + 1)).symm s))
      ∈ subspaceChains K n := by
  rw [SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm]
  exact hbd

/-- **infCompactᶜ = legSplitUᶜ ∪ legSplitVᶜ** (the cover-support set identity). `fundCycleW_boundary` lands
`∂fund` in `subspaceChains(Kᶜ)` with `K = infCompact = legSplitU ∩ legSplitV` (`infCompact_coe`); de Morgan
(`Set.compl_inter`) rewrites that to the cover `legSplitUᶜ ∪ legSplitVᶜ` the seam-localization engine consumes. -/
theorem infCompact_compl_legSplit {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) :
    (↑(SingularCSCMayerVietorisConnecting.infCompact U V
        (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
        (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)).1 : Set ↑X)ᶜ
      = (↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1)ᶜ
        ∪ (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1)ᶜ := by
  rw [SingularCSCMayerVietorisConnecting.infCompact_coe, Set.compl_inter]

/-- **Mod-boundary cover-partition cap-boundary** — the `hpart`-entanglement version of
`SingularConnSquareMatchLHS.cover_partition_cap_boundary`. When the cap of a cocycle `g` against `z` is
cover-partitioned only MODULO A BOUNDARY `cap g z = chainIncl A zA + chainIncl B zB + ∂η` (the form
`hpart`+`hzc0` yield via `exists_boundary_of_homology_eq`), the boundary identity STILL holds — the `∂η`
term drops by `∂∂ = 0` (`chainBoundary_chainBoundary_apply`). This is the V-link chain engine that
consumes the homology-level cover-partition directly: `cap g (∂z) = chainIncl A (∂zA) + chainIncl B (∂zB)`,
relating the seam V-part boundary `∂zB` to the fundamental cycle's boundary `∂z`. The cocycle-`g_rep`
route (NOT the `φ = cochainSplit` route) the connecting square is built on. -/
theorem cover_partition_cap_boundary_mod {k m : ℕ} (A B : Set ↑X) (g : SingularCochain X k)
    (hg : coboundaryₗ X k g = 0) (z : SingularChain X (k + m + 1))
    (zA : SingularChain (sub A) (m + 1)) (zB : SingularChain (sub B) (m + 1))
    (η : SingularChain X (m + 1 + 1))
    (hpart : cap g z = chainIncl A (m + 1) zA + chainIncl B (m + 1) zB
      + chainBoundary X (m + 1) η) :
    chainIncl A m (chainBoundary (sub A) m zA) + chainIncl B m (chainBoundary (sub B) m zB)
      = cap g (chainBoundary X (k + m) z) := by
  have h1 := SingularHomologyMod2.cap_cocycle_chainMap g hg z
  rw [hpart, map_add, map_add, ← SingularRelativeHomologyMod2.chainIncl_chainBoundary,
    ← SingularRelativeHomologyMod2.chainIncl_chainBoundary, chainBoundary_chainBoundary_apply,
    add_zero] at h1
  exact h1

/-- **`boundaryExtract` naturality w.r.t. an ambient pushforward** (the seam-transport building block).
`mapChain φ` of the realized connecting image `chainIncl S (boundaryExtract S w)` equals the ambient
boundary of the pushed-forward lift `mapChain φ (↑w)`, because `chainIncl ∘ boundaryExtract = ∂` (PairLES
`chainIncl_boundaryExtract`) and `mapChain` is a chain map (`chainBoundary_mapChain`). The chain-level
seam-naturality of `boundaryExtract` the connecting-square V-link needs, built fresh (no committed engine
fired — `mapChain_boundaryExtract`/`boundaryExtract_seam` are empty). -/
theorem mapChain_chainIncl_boundaryExtract {Y Z : TopCat} (φ : C(↑Y, ↑Z)) {S : Set ↑Y} {n : ℕ}
    (w : SingularPairLES.relCycleLift S n) :
    SingularFunctoriality.mapChain φ n (chainIncl S n (SingularPairLES.boundaryExtract S n w))
      = chainBoundary Z n (SingularFunctoriality.mapChain φ (n + 1) (w : SingularChain Y (n + 1))) := by
  rw [SingularPairLES.chainIncl_boundaryExtract, ← SingularFunctoriality.chainBoundary_mapChain]

/-- **Chain cover-partition from the `legW` homology hypotheses** (the whnf-dodging bridge — friction
catalog). Stated `legW`-HEADED (not `relativeDualityK`-headed): at application the concrete `hzc0`'s
`legW … (Submodule.Quotient.mk g_rep)` matches the `legW` head SYNTACTICALLY, with `hW`/`z₀`/`hz₀`/`K`/`a`
inferred structurally — so the elaborator NEVER WHNF-reduces `legW (mk g_rep)` (which would reduce the
`liftQ`-on-`mk` straight through to the concrete `cap g_rep fundCycleW`, the 200k whnf wall). Inside, over
FREE carriers, `unfold legW` + `relativeDualityK_mk` reduce symbolically (no concrete cap), then
`exists_boundary_of_homology_eq` extracts `pullbackDualityₗ … a = w + ∂η` from `[zc0] = legW [a]` (hzc0)
+ `[zc0] = [w]` (hpart). This is the cocycle-`g_rep` close-path step 2 (the chain cover-partition). -/
theorem cover_partition_of_legW {W : Set ↑X} {k m : ℕ} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn W)
    (a : LinearMap.ker (relCoboundaryₗ ((↑K.1 : Set ↑X)ᶜ) k))
    (zc0 w : cycles (sub W) (m + 1))
    (hzc0 : Homology.mk (sub W) (m + 1) zc0
        = legW hW z₀ hz₀ K (Submodule.Quotient.mk a))
    (hpart : Homology.mk (sub W) (m + 1) zc0 = Homology.mk (sub W) (m + 1) w) :
    ∃ η : SingularChain (sub W) (m + 1 + 1),
      SingularLocalDualityK.pullbackDualityₗ ((↑K.1 : Set ↑X)ᶜ) W
          (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K)
          (SingularOpenDualityCycle.fundCycleW_mem_W hW z₀ hz₀ K) a
        = (w : SingularChain (sub W) (m + 1)) + chainBoundary (sub W) (m + 1) η := by
  unfold legW at hzc0
  -- `relativeDualityK … (mk a) = Homology.mk ⟨pullbackDualityₗ …⟩` is `relativeDualityK_mk`'s own `rfl` —
  -- over FREE carriers (symbolic `fundCycleW`) the defeq is cheap, so `exact` closes it without an `rw`
  -- (which fails on the shared-`?S` representation `(↑↑K)ᶜ` vs `(↑K.1)ᶜ`).
  exact SingularConnSquareRHSScaffold.exists_boundary_of_homology_eq
    ⟨SingularLocalDualityK.pullbackDualityₗ ((↑K.1 : Set ↑X)ᶜ) W
        (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K)
        (SingularOpenDualityCycle.fundCycleW_mem_W hW z₀ hz₀ K) a,
      SingularLocalDualityK.pullbackDualityₗ_mem_cycles ((↑K.1 : Set ↑X)ᶜ) W
        (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K)
        (SingularOpenDualityCycle.fundCycleW_mem_W hW z₀ hz₀ K)
        (SingularOpenDualityCycle.fundCycleW_boundary hW z₀ hz₀ K) a⟩
    w (hzc0.symm.trans hpart)

/-- **A cover-complex cocycle caps to 0 against any cover-partition** (the chain-level leg-local vanishing —
the cap analog of `rhs_pairing_reduce`'s kronecker vanishing; coach-locked option-A χ-engine 2026-06-23).
A cochain `a` vanishing on BOTH `U`- and `V`-chains (`a ∈ relCochains U ∩ relCochains V`, e.g.
`δ(cochainSplit U g_rep)` for a cocycle `g_rep`, via `cochainSplit_coboundary_mem_U/V`) caps to `0` against
a cover-subordinate partition `chainIncl U u + chainIncl V w`: `cap_chainIncl` pushes the cap inside each
`chainIncl`, where `pullbackCochain_relCochains_eq_zero` kills the relative-cochain leg. The χ-vanishing for
option-A (Sdʲ chain-level absorption): `δφ` capped against the cover-fine boundary `∂(Sdʲ fund_∩)`. -/
theorem cap_relCochains_cover_partition_eq_zero {U V : Set ↑X} {k m : ℕ}
    (a : SingularCochain X k) (haU : a ∈ relCochains U k) (haV : a ∈ relCochains V k)
    (u : SingularChain (sub U) (k + m)) (w : SingularChain (sub V) (k + m)) :
    cap a (chainIncl U (k + m) u + chainIncl V (k + m) w) = 0 := by
  have hsplit : cap a (chainIncl U (k + m) u + chainIncl V (k + m) w)
      = cap a (chainIncl U (k + m) u) + cap a (chainIncl V (k + m) w) :=
    map_add (capₗ k m a) _ _
  have hU0 : cap a (chainIncl U (k + m) u) = 0 := by
    rw [SingularCapChainIncl.cap_chainIncl, pullbackCochain_relCochains_eq_zero k a haU,
      ← capₗ_apply, map_zero, LinearMap.zero_apply, map_zero]
  have hV0 : cap a (chainIncl V (k + m) w) = 0 := by
    rw [SingularCapChainIncl.cap_chainIncl, pullbackCochain_relCochains_eq_zero k a haV,
      ← capₗ_apply, map_zero, LinearMap.zero_apply, map_zero]
  rw [hsplit, hU0, hV0, add_zero]

/-- **One-leg cap vanishing**: a cochain `a` vanishing on `S`-chains (`a ∈ relCochains S`) caps to `0`
against any `S`-supported chain `chainIncl S c`. The building block of `cap_relCochains_cover_partition_eq_zero`
and the V-part U-leg drop: `cap_chainIncl` + `pullbackCochain_relCochains_eq_zero`. -/
theorem cap_relCochains_chainIncl_eq_zero {S : Set ↑X} {k m : ℕ}
    (a : SingularCochain X k) (ha : a ∈ relCochains S k) (c : SingularChain (sub S) (k + m)) :
    cap a (chainIncl S (k + m) c) = 0 := by
  rw [SingularCapChainIncl.cap_chainIncl, pullbackCochain_relCochains_eq_zero k a ha,
    ← capₗ_apply, map_zero, LinearMap.zero_apply, map_zero]

/-- **U-leg drop of a relative-`U` cochain against a cover-partition**: for `a ∈ relCochains U`, capping `a`
against a cover-subordinate partition `chainIncl U u + chainIncl V w` drops the `U`-leg (it vanishes,
`cap_relCochains_chainIncl_eq_zero`), leaving `cap a (chainIncl V w)`. This is the V-part step for option-A:
`φ = cochainSplit U g_rep ∈ relCochains U`, so `cap φ (∂(Sdʲ fund_∩)) = cap φ (chainIncl V w')` — the seam
V-leg that the cross-realization identifies with `chain_L`. -/
theorem cap_relCochains_U_cover_drop {U V : Set ↑X} {k m : ℕ}
    (a : SingularCochain X k) (ha : a ∈ relCochains U k)
    (u : SingularChain (sub U) (k + m)) (w : SingularChain (sub V) (k + m)) :
    cap a (chainIncl U (k + m) u + chainIncl V (k + m) w) = cap a (chainIncl V (k + m) w) := by
  rw [show cap a (chainIncl U (k + m) u + chainIncl V (k + m) w)
        = cap a (chainIncl U (k + m) u) + cap a (chainIncl V (k + m) w) from map_add (capₗ k m a) _ _,
    cap_relCochains_chainIncl_eq_zero a ha u, zero_add]

/-- **Realize cap-Leibniz split** (the cross-realization structural backbone): the `K`-realization of the
boundary `∂(cap a c)` splits as the realize of the two cap-Leibniz terms `cap(δa)c` (the U-part / connecting)
and `cap a (∂c)` (the V-part). `subspaceChainsEquiv K`'s `.symm` is a `LinearEquiv` so it's additive
(`map_add`); the underlying split is `cap_leibniz`. Lets `∂W = realize(∂(cap (cochainSplit g_rep) fund'))`
be matched termwise against `pd + chain_L`. -/
theorem realize_cap_leibniz {K : Set ↑X} {k m : ℕ} (a : SingularCochain X k)
    (c : SingularChain X (k + m + 1)) (h : k + m + 1 = k + 1 + m)
    (h0 : chainBoundary X m (cap a c) ∈ subspaceChains K m)
    (h1 : cap (coboundary X k a) (h ▸ c) ∈ subspaceChains K m)
    (h2 : cap a (chainBoundary X (k + m) c) ∈ subspaceChains K m) :
    (SingularSubspaceChainsEquiv.subspaceChainsEquiv K m).symm
        ⟨chainBoundary X m (cap a c), h0⟩
      = (SingularSubspaceChainsEquiv.subspaceChainsEquiv K m).symm
            ⟨cap (coboundary X k a) (h ▸ c), h1⟩
        + (SingularSubspaceChainsEquiv.subspaceChainsEquiv K m).symm
            ⟨cap a (chainBoundary X (k + m) c), h2⟩ := by
  rw [← map_add]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_add]
  exact cap_leibniz a c h

/-- **The two cap-Leibniz terms, realized, sum to a boundary** (the cross-realization ASSEMBLY ENTRY).
Glues `realize_cap_leibniz` (the split `realize(∂(cap a c)) = realize(cap(δa)) + realize(cap a ∂c)`) with
`realize_chainBoundary_cap_mem_boundaries` (the membership `realize(∂(cap a c)) ∈ boundaries`). The KEY goal
`chain_L + pd ∈ boundaries` reduces through this: identify `pd = realize(cap(δφ)fund')` (U-part) and
`chain_L = realize(cap φ ∂fund')` (V-part), then this lemma closes it. -/
theorem realize_cap_leibniz_terms_mem_boundaries {K : Set ↑X} {k n : ℕ} (a : SingularCochain X k)
    (c : SingularChain X (k + (n + 1) + 1)) (h : k + (n + 1) + 1 = k + 1 + (n + 1))
    (hd : cap a c ∈ subspaceChains K (n + 2))
    (hsum : chainBoundary X (n + 1) (cap a c) ∈ subspaceChains K (n + 1))
    (h1 : cap (coboundary X k a) (h ▸ c) ∈ subspaceChains K (n + 1))
    (h2 : cap a (chainBoundary X (k + (n + 1)) c) ∈ subspaceChains K (n + 1)) :
    (SingularSubspaceChainsEquiv.subspaceChainsEquiv K (n + 1)).symm
          ⟨cap (coboundary X k a) (h ▸ c), h1⟩
        + (SingularSubspaceChainsEquiv.subspaceChainsEquiv K (n + 1)).symm
          ⟨cap a (chainBoundary X (k + (n + 1)) c), h2⟩
      ∈ boundaries (sub K) (n + 1) := by
  rw [← realize_cap_leibniz a c h hsum h1 h2]
  exact realize_chainBoundary_cap_mem_boundaries K a c hd hsum

/-- **Seam-transport `chainIncl` compatibility** (the V-link seam piece): `subSeamHomeo` is identity-on-points,
so including the `subSeamHomeo`-reindex into `X` (`chainIncl T ∘ mapChain⟨subSeamHomeo⟩`) equals the direct
nested inclusion `chainIncl S ∘ chainIncl R`. Both are `mapChain` of the underlying inclusion (`mapChain_ambIncl`),
fused by `mapChain_comp`; the two composite continuous maps agree pointwise (identity-on-points → `rfl`). Lets
`chainIncl(U∩V)(chain_L)` be rewritten off the seam transport onto the direct inclusion of `boundaryExtract zB`. -/
theorem chainIncl_mapChain_subSeamHomeo {S : Set ↑X} {R : Set ↑(sub S)} {T : Set ↑X} (hTS : T ⊆ S)
    (hmem : ∀ p : ↥(sub S), p ∈ R ↔ (p : ↑X) ∈ T) {n : ℕ} (x : SingularChain (sub R) n) :
    chainIncl T n (SingularFunctoriality.mapChain
        ⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩ n x)
      = chainIncl S n (chainIncl R n x) := by
  rw [← SingularMayerVietorisLES.mapChain_ambIncl, ← SingularMayerVietorisLES.mapChain_ambIncl,
    ← SingularMayerVietorisLES.mapChain_ambIncl, ← SingularFunctoriality.mapChain_comp,
    ← SingularFunctoriality.mapChain_comp]
  rfl

/-- **Seam-transport `chainIncl` compatibility (seamHomeo)**: the inner-seam companion of
`chainIncl_mapChain_subSeamHomeo`. `seamHomeo A B : sub(restr A B) ≃ sub(A∩B)` is identity-on-points, so
`chainIncl (A∩B) ∘ mapChain⟨seamHomeo A B⟩ = chainIncl B ∘ chainIncl (restr A B)`. Same `mapChain_ambIncl` +
`mapChain_comp` + `rfl` proof. Lets `chainIncl(...)(chain_L)` peel the INNER seam. -/
theorem chainIncl_mapChain_seamHomeo {Y : TopCat} (A B : Set ↑Y) {n : ℕ}
    (x : SingularChain (sub (SingularExcisionIso.restr A B)) n) :
    chainIncl (A ∩ B) n (SingularFunctoriality.mapChain
        ⟨SingularMayerVietorisLES.seamHomeo A B, (SingularMayerVietorisLES.seamHomeo A B).continuous⟩ n x)
      = chainIncl B n (chainIncl (SingularExcisionIso.restr A B) n x) := by
  rw [← SingularMayerVietorisLES.mapChain_ambIncl, ← SingularMayerVietorisLES.mapChain_ambIncl,
    ← SingularMayerVietorisLES.mapChain_ambIncl, ← SingularFunctoriality.mapChain_comp,
    ← SingularFunctoriality.mapChain_comp]
  rfl

/-- **chain_L realizes to the cover-partition V-part** (the V-link CONNECTION). Chaining the two seam-transport
lemmas + `chainIncl_boundaryExtract` (`chainIncl(restr)∘boundaryExtract = ∂`) + `chainIncl_chainBoundary`
(`chainIncl∘∂ = ∂∘chainIncl`): the `chainIncl T` of the seam-transported `boundaryExtract w` (= the shape of
`chain_L`) equals `chainIncl S (∂(chainIncl B ↑w))`. For the goal (`S=U∪V`, `B=val⁻¹V`, `T=U∩V`, `↑w=zB`) this is
`chainIncl(U∩V)(chain_L) = chainIncl(U∪V)(∂(chainIncl_B zB))` = the V-part of `hbd` — so `chain_L` links to the
committed cover-partition machinery WITHOUT constructing the bounding chain's `φ`/`fund'`. -/
theorem chainIncl_seam_boundaryExtract {S : Set ↑X} {A B : Set ↑(sub S)} {T : Set ↑X}
    (hTS : T ⊆ S) (hmem : ∀ p : ↥(sub S), p ∈ A ∩ B ↔ (p : ↑X) ∈ T) {n : ℕ}
    (w : SingularPairLES.relCycleLift (SingularExcisionIso.restr A B) n) :
    chainIncl T n (SingularFunctoriality.mapChain
        ⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩ n
        (SingularFunctoriality.mapChain
          ⟨SingularMayerVietorisLES.seamHomeo A B, (SingularMayerVietorisLES.seamHomeo A B).continuous⟩ n
          (SingularPairLES.boundaryExtract (SingularExcisionIso.restr A B) n w)))
      = chainIncl S n (chainBoundary (sub S) n
          (chainIncl B (n + 1) (w : SingularChain (sub B) (n + 1)))) := by
  rw [chainIncl_mapChain_subSeamHomeo, chainIncl_mapChain_seamHomeo,
    SingularPairLES.chainIncl_boundaryExtract, SingularRelativeHomologyMod2.chainIncl_chainBoundary]

/-- **Cover form of `∂(fundCycleW)`'s support**: `fundCycleW_boundary` lands `∂fund` in `subspaceChains(Kᶜ)`;
when `Kᶜ` is a cover `P ∪ Q` (for `K = infCompact`, `P ∪ Q = legSplitUᶜ ∪ legSplitVᶜ` via
`infCompact_compl_legSplit`), `∂fund ∈ subspaceChains(P ∪ Q)` — so it splits cover-subordinately for the
V-part leg drop (`cap_relCochains_U_cover_drop`). -/
theorem fundCycleW_boundary_cover {W : Set ↑X} {k m : ℕ} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn W) {P Q : Set ↑X}
    (hcover : ((↑K.1 : Set ↑X)ᶜ) = P ∪ Q) :
    chainBoundary X (k + m) (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K)
      ∈ subspaceChains (P ∪ Q) (k + m) := by
  rw [← hcover]
  exact SingularOpenDualityCycle.fundCycleW_boundary hW z₀ hz₀ K

/-- **cap-Leibniz on a cycle argument** (the V-link Leibniz core, per the hcross DR / Hatcher pp.246-247):
for a cycle `c` (`∂c = 0`), `∂(cap a c) = cap(δa)(h▸c)` — the `cap a (∂c)` Leibniz term drops. This is the
boundary-tracking step of the connecting-square: capping the cover-split cochain `δφ` against the cycle `z₀`
IS the boundary of `cap φ z₀`, with no content beyond `cap_leibniz` + `∂z₀=0`. -/
theorem chainBoundary_cap_cycle_arg {k m : ℕ} (a : SingularCochain X k)
    (c : SingularChain X (k + m + 1)) (hc : chainBoundary X (k + m) c = 0)
    (h : k + m + 1 = k + 1 + m) :
    chainBoundary X m (cap a c) = cap (coboundary X k a) (h ▸ c) := by
  rw [cap_leibniz a c h, hc, ← capₗ_apply, map_zero, add_zero]

/-- **The cap of a cochain against `fundCycleW` is `W`-supported** (the cleaner-witness support fact):
`fundCycleW ∈ subspaceChains W` (`fundCycleW_mem_W`) and cap preserves support (`cap_mem_subspaceChains`),
so `cap a (fundCycleW) ∈ subspaceChains W`. For `W = U∩V`, `K = infCompact`, `a = g_rep`, this makes
`d = cap g_rep fund_∩` a `U∩V`-supported witness — and `∂d = cap g_rep ∂fund_∩` has NO δ-term (g_rep cocycle),
so the witness sidesteps the cochainSplit χ entirely. -/
theorem cap_fundCycleW_mem {W : Set ↑X} {k m : ℕ} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn W) (a : SingularCochain X k) :
    cap a (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K) ∈ subspaceChains W (m + 1) :=
  SingularCapSupport.cap_mem_subspaceChains W a (SingularOpenDualityCycle.fundCycleW_mem_W hW z₀ hz₀ K)

/-- **cap-Leibniz on a cocycle cochain** (the witness `∂d` engine): for a cocycle `a` (`δa = 0`),
`∂(cap a c) = cap a (∂c)` — the `cap(δa)(h▸c)` Leibniz term drops. With `a = g_rep` (cocycle), this is
`∂(cap g_rep fund_∩) = cap g_rep ∂fund_∩` — the boundary of the cleaner witness `d = cap g_rep fund_∩`, with
no δ-term. Dual to `chainBoundary_cap_cycle_arg` (which drops the `cap a (∂c)` term for a cycle `c`). -/
theorem chainBoundary_cap_cocycle_arg {k m : ℕ} (a : SingularCochain X k)
    (ha : coboundary X k a = 0) (c : SingularChain X (k + m + 1)) (h : k + m + 1 = k + 1 + m) :
    chainBoundary X m (cap a c) = cap a (chainBoundary X (k + m) c) := by
  rw [cap_leibniz a c h, ha]
  rw [← capₗ_apply, map_zero, LinearMap.zero_apply, zero_add]

/-- **`subspaceChains` is closed under `∂`** (the witness `hsum` support): if `c ∈ subspaceChains K (n+1)`
(i.e. `c = chainIncl K x`) then `∂c = ∂(chainIncl K x) = chainIncl K (∂x) ∈ subspaceChains K n`
(`chainIncl_chainBoundary`). Gives `∂(cap g_rep fund_∩) ∈ subspaceChains(U∩V)` for the reflection. -/
theorem chainBoundary_mem_subspaceChains {K : Set ↑X} {n : ℕ} (c : SingularChain X (n + 1))
    (hc : c ∈ subspaceChains K (n + 1)) :
    chainBoundary X n c ∈ subspaceChains K n := by
  rw [subspaceChains, LinearMap.mem_range] at hc ⊢
  obtain ⟨x, rfl⟩ := hc
  exact ⟨chainBoundary (sub K) n x, by rw [SingularRelativeHomologyMod2.chainIncl_chainBoundary]⟩

/-- **Connecting-square reflection close** (abstract over free carriers — dodges the concrete `fundCycleW`
whnf wall, the proven `two_facts_via_ambient` technique). Given the cleaner witness `cap a c` is
`K`-supported (`hd`) and the X-level **connecting-square identity** `chainIncl chainL + chainIncl pd =
∂(cap a c)` (`hident`), the sub-`K` chain `chainL + pd` is a boundary: realize `cap a c` in `sub K`
(`realize_chainBoundary_cap_mem_boundaries`), whose `∂` IS `chainL + pd` by `chainIncl`-injectivity +
the realize round-trip. Applied all-underscore so the verbose `fund_∩`/seam terms infer structurally;
isolates `hident` (the genuine cap-product MV-naturality content) as the sole residual. -/
theorem connecting_square_close (K : Set ↑X) {k n : ℕ} (a : SingularCochain X k)
    (c : SingularChain X (k + (n + 1) + 1)) (hd : cap a c ∈ subspaceChains K (n + 1 + 1))
    (chainL pd : SingularChain (sub K) (n + 1))
    (hident : chainIncl K (n + 1) chainL + chainIncl K (n + 1) pd
        = chainBoundary X (n + 1) (cap a c)) :
    chainL + pd ∈ boundaries (sub K) (n + 1) := by
  have hsum : chainBoundary X (n + 1) (cap a c) ∈ subspaceChains K (n + 1) :=
    chainBoundary_mem_subspaceChains _ hd
  have heq : chainL + pd =
      (SingularSubspaceChainsEquiv.subspaceChainsEquiv K (n + 1)).symm
        ⟨chainBoundary X (n + 1) (cap a c), hsum⟩ := by
    apply SingularRelativeHomologyMod2.chainIncl_injective K (n + 1)
    rw [map_add, SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm]
    exact hident
  rw [heq]
  exact realize_chainBoundary_cap_mem_boundaries K a c hd hsum

/-- **Connecting-square close, cocycle / cap-of-boundary form.** For a COCYCLE `a` (`ha : coboundary a = 0`),
states the residual identity with `cap a (∂c)` (cap-of-boundary) instead of `∂(cap a c)` (boundary-of-cap):
on application with a concrete `fundCycleW` witness `c`, `∂(cap a c)` whnf-walls (`chainBoundary` of a cap on
a concrete fundCycleW = 200k) but `cap a (∂c)` does NOT (same form as `cover_partition_cap_boundary_mod`'s
RHS, which builds). Internally bridges via `chainBoundary_cap_cocycle_arg` (`∂(cap a c) = cap a ∂c`, cocycle a),
proven over the ABSTRACT `c` so no wall. -/
theorem connecting_square_close_cocycle (K : Set ↑X) {k n : ℕ} (a : SingularCochain X k)
    (ha : coboundary X k a = 0)
    (c : SingularChain X (k + (n + 1) + 1)) (hd : cap a c ∈ subspaceChains K (n + 1 + 1))
    (chainL pd : SingularChain (sub K) (n + 1))
    (hident : chainIncl K (n + 1) chainL + chainIncl K (n + 1) pd
        = cap a (chainBoundary X (k + (n + 1)) c)) :
    chainL + pd ∈ boundaries (sub K) (n + 1) := by
  refine connecting_square_close K a c hd chainL pd ?_
  rw [chainBoundary_cap_cocycle_arg a ha c (by omega)]
  exact hident

/-- **Connecting-square close, `fundCycleW`-headed form** (the whnf-dodge — coach-locked 2026-06-23, the proven
`cover_partition_of_legW` def-head-match technique). Takes the `fundCycleW` COMPONENTS (`hW`/`z₀`/`hz₀`/`Kc`)
rather than an abstract carrier `c`, so on application Lean unifies the components (`?hW := …`, `?z₀ := …`)
and NEVER substitutes the assembled concrete `Fg` into `c` — the whole-term assignment that whnf-reduces
`cap a Fg` (a concrete value) to 200k. The witness support `hd` is computed INTERNALLY (`cap_fundCycleW_mem`),
over the FREE components, so the body never reduces a concrete fundCycleW. Residual `hident` = cap-of-boundary
form (`cap a (∂(fundCycleW ..))`, like `cover_partition_cap_boundary_mod`'s RHS). -/
theorem connecting_square_close_cocycle_fund (K' : Set ↑X) {k n : ℕ} (a : SingularCochain X k)
    (ha : coboundary X k a = 0) (hW : IsOpen K') (z₀ : SingularChain X (k + (n + 1) + 1))
    (hz₀ : chainBoundary X (k + (n + 1)) z₀ = 0) (Kc : SingularCompactsInOpen.CompactsIn K')
    (chainL pd : SingularChain (sub K') (n + 1))
    (hident : chainIncl K' (n + 1) chainL + chainIncl K' (n + 1) pd
        = cap a (chainBoundary X (k + (n + 1)) (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ Kc))) :
    chainL + pd ∈ boundaries (sub K') (n + 1) :=
  connecting_square_close_cocycle K' a ha (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ Kc)
    (cap_fundCycleW_mem hW z₀ hz₀ Kc a) chainL pd hident

/-- **Cap analog of `pair_fund_eq_pair_z0`** (the shared-z₀ reduction). For a COCYCLE `c` (`hc`) that
vanishes on `C(A)` (`hcv` — e.g. `c ∈ relCochains A`, via `cap_relCochains_chainIncl_eq_zero`), capping a
`fund` that is rel-`A`-homologous to `z₀` (`fund + z₀ = ∂η + a`, `a ∈ subspaceChains A` — from
`fundCycleW_relHomologous`) equals capping `z₀`, up to a boundary: `cap c fund = cap c z₀ + ∂(cap c η)`.
Because `cap c ∂η = ∂(cap c η)` (cocycle, `chainBoundary_cap_cocycle_arg`) and `cap c a = 0` (vanishing).
Reduces both `cap σR_rep fund_∩` and `cap g_rep fund_{U∪V}` to caps against the single shared `z₀`. ℤ/2. -/
theorem cap_fund_eq_cap_z0 {A : Set ↑X} {k m : ℕ} (c : SingularCochain X k)
    (hc : coboundary X k c = 0) (hcv : ∀ d ∈ subspaceChains A (k + m), cap c d = 0)
    (fund z₀ : SingularChain X (k + m)) (η : SingularChain X (k + m + 1))
    (a : SingularChain X (k + m)) (ha : a ∈ subspaceChains A (k + m))
    (heq : fund + z₀ = chainBoundary X (k + m) η + a) :
    cap c fund = cap c z₀ + chainBoundary X m (cap c η) := by
  have hca : cap c a = 0 := hcv a ha
  have hb : cap c (chainBoundary X (k + m) η) = chainBoundary X m (cap c η) :=
    (chainBoundary_cap_cocycle_arg c hc η (by omega)).symm
  have hsum : cap c (fund + z₀) = chainBoundary X m (cap c η) := by
    rw [heq, ← capₗ_apply, map_add, capₗ_apply, capₗ_apply, hb, hca, add_zero]
  rw [← capₗ_apply, map_add, capₗ_apply, capₗ_apply] at hsum
  exact eq_of_sub_eq_zero (by rw [ZModModule.sub_eq_add, ← add_assoc, hsum]; exact ZModModule.add_self _)

/-- **Chain-level form of `fundCycleW_relHomologous`** (the `heq` input for `cap_fund_eq_cap_z0`): the
relBoundaries membership `mk z₀ + mk fund ∈ relBoundaries(Kᶜ)` unfolds to a concrete `fund + z₀ = ∂η + a`
with `a ∈ subspaceChains(Kᶜ)` (`relBoundary_mk` + `mk` surjective + `mk_eq_zero_iff`, all over ℤ/2). -/
theorem fundCycleW_chain_rel {W : Set ↑X} {k m : ℕ} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn W) :
    ∃ (η : SingularChain X (k + m + 1 + 1)) (a : SingularChain X (k + m + 1)),
      SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K + z₀
          = chainBoundary X (k + m + 1) η + a ∧
        a ∈ subspaceChains ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) := by
  obtain ⟨w, hw⟩ := SingularOpenDualityCycle.fundCycleW_relHomologous hW z₀ hz₀ K
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  erw [SingularRelativeHomologyMod2.relBoundary_mk] at hw
  refine ⟨η, chainBoundary X (k + m + 1) η + (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K + z₀), ?_, ?_⟩
  · abel_nf
    simp only [two_smul, ZModModule.add_self, zero_add, add_zero]
  · erw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at hw
    rw [ZModModule.sub_eq_add,
      add_comm z₀ (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K)] at hw
    exact hw

/-- **`hcv` helper** — a relative cochain `a ∈ relCochains S` caps to 0 against every `subspaceChains S`
chain (`d = chainIncl S c`, `cap a (chainIncl S c) = 0` by `cap_relCochains_chainIncl_eq_zero`). The
vanishing hypothesis `cap_fund_eq_cap_z0` needs, for both `σR_rep` (S = infCompactᶜ) and `g_rep` (S = Kᶜ). -/
theorem cap_relCochains_subspaceChains_eq_zero {S : Set ↑X} {k m : ℕ} (a : SingularCochain X k)
    (ha : a ∈ relCochains S k) :
    ∀ d ∈ subspaceChains S (k + m), cap a d = 0 := by
  intro d hd
  rw [subspaceChains, LinearMap.mem_range] at hd
  obtain ⟨c, rfl⟩ := hd
  exact cap_relCochains_chainIncl_eq_zero a ha c

/-- **Cap analog of `kronecker_coboundary_cochainSplit_eq`** (Geom:50 — the σR-connecting engine, cap
altitude). For `ω ∈ ker(relCoboundaryₗ(U∩V))` and a chain `c` whose boundary cover-partitions `∂c = u + w`
(`u ∈ C(U)`, `w ∈ C(V)`): `cap (δ(cochainSplit U ω)) c = cap ω w + ∂(cap (cochainSplit U ω) c)`. Mirrors
the kronecker proof (cap_leibniz instead of the adjunction, so the chain-level `∂(cap φ c)` boundary
appears): `cap φ ∂c = cap φ (u+w) = cap φ w` (`cap φ u = 0`, `φ ∈ relCochains U`); `cap φ w = cap ω w`
(`ω - φ ∈ relCochains V`, `cap (ω-φ) w = 0`). The cap analog the coach named — wires σR_rep (= ω via hσR)
to the V-leg `w` of a cover-partition. ℤ/2. -/
theorem cap_coboundary_cochainSplit_eq (U V : Set ↑X) {N m : ℕ}
    (ω : LinearMap.ker (relCoboundaryₗ (U ∩ V) (N + 1)))
    (c : SingularChain X (N + 1 + m + 1)) (u w : SingularChain X (N + 1 + m))
    (hu : u ∈ subspaceChains U (N + 1 + m)) (hw : w ∈ subspaceChains V (N + 1 + m))
    (hbd : chainBoundary X (N + 1 + m) c = u + w) (h : N + 1 + m + 1 = N + 1 + 1 + m) :
    cap (coboundary X (N + 1) (cochainSplit U (N + 1) ω.1.1)) (h ▸ c)
      = cap ω.1.1 w + chainBoundary X m (cap (cochainSplit U (N + 1) ω.1.1) c) := by
  have hu0 : cap (cochainSplit U (N + 1) ω.1.1) u = 0 :=
    cap_relCochains_subspaceChains_eq_zero _ (cochainSplit_mem_relCochains U (N + 1) ω.1.1) u hu
  have hωw : cap ω.1.1 w = cap (cochainSplit U (N + 1) ω.1.1) w := by
    have hψw : cap (ω.1.1 - cochainSplit U (N + 1) ω.1.1) w = 0 :=
      cap_relCochains_subspaceChains_eq_zero _
        (cochainSplit_compl_mem_relCochains U V (N + 1) ω.1.1 ω.1.2) w hw
    rw [show ω.1.1 - cochainSplit U (N + 1) ω.1.1 = ω.1.1 + cochainSplit U (N + 1) ω.1.1 from by
      rw [ZModModule.sub_eq_add], cap_add_cochain] at hψw
    exact eq_of_sub_eq_zero (by rw [ZModModule.sub_eq_add]; exact hψw)
  have hφbd : cap (cochainSplit U (N + 1) ω.1.1) (chainBoundary X (N + 1 + m) c) = cap ω.1.1 w := by
    rw [hbd, ← capₗ_apply, map_add, capₗ_apply, capₗ_apply, hu0, zero_add, ← hωw]
  have hleib := cap_leibniz (cochainSplit U (N + 1) ω.1.1) c h
  rw [hφbd] at hleib
  rw [hleib]
  abel_nf
  simp only [two_smul, ZModModule.add_self, zero_add, add_zero]

/-- **Subdivision + σR-connecting engine** (step (a), the first consumer of `cap_coboundary_cochainSplit_eq`).
For `ω ∈ ker(relCoboundaryₗ(U∩V))` and `fund` with `∂fund ∈ subspaceChains(U∪V)`, cover-fine subdivide
(`exists_cover_fine_subdivision` gives `∂(Sdʲ fund) = chainIncl_U u' + chainIncl_V w'`), then apply the engine:
`cap(δ(cochainSplit U ω))(Sdʲ fund) = cap ω (chainIncl_V w') + ∂(cap (cochainSplit U ω)(Sdʲ fund))`. The V-leg
`chainIncl_V w'` is the cover-partition piece that matches the seam term downstream. Kernel-pure. -/
theorem cap_coboundary_cochainSplit_subdiv (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) {N m : ℕ}
    (ω : LinearMap.ker (relCoboundaryₗ (U ∩ V) (N + 1)))
    (fund : SingularChain X (N + 1 + m + 1))
    (hbd : chainBoundary X (N + 1 + m) fund ∈ subspaceChains (U ∪ V) (N + 1 + m))
    (h : N + 1 + m + 1 = N + 1 + 1 + m) :
    ∃ (j : ℕ) (w : SingularChain (sub V) (N + 1 + m)),
      cap (coboundary X (N + 1) (cochainSplit U (N + 1) ω.1.1))
          (h ▸ (⇑(SingularSubdivision.singularSd X (N + 1 + m + 1)))^[j] fund)
        = cap ω.1.1 (chainIncl V (N + 1 + m) w)
          + chainBoundary X m
            (cap (cochainSplit U (N + 1) ω.1.1)
              ((⇑(SingularSubdivision.singularSd X (N + 1 + m + 1)))^[j] fund)) := by
  obtain ⟨j, u', w', hsplit⟩ :=
    SKEFTHawking.SingularConnSquareRHSScaffold.exists_cover_fine_subdivision hU hV fund hbd
  exact ⟨j, w', cap_coboundary_cochainSplit_eq U V ω _ (chainIncl U (N + 1 + m) u')
    (chainIncl V (N + 1 + m) w') ⟨u', rfl⟩ ⟨w', rfl⟩ hsplit h⟩

/-- **fundCycleW-headed wrapper of `cap_coboundary_cochainSplit_subdiv`** (def-head-match whnf-dodge).
Stated with `fundCycleW hW z₀ hz₀ Kc` directly in the `fund` slot so an application matches the head
SYNTACTICALLY and infers the components (`hW`/`z₀`/`hz₀`/`Kc`) by unification, never assembling +
whnf-reducing the concrete fundamental into the cap (the documented 200k wall). Body = the engine applied
over free carriers (no whnf). Same technique as `connecting_square_close_cocycle_fund` / `factB_transport`. -/
theorem cap_coboundary_cochainSplit_subdiv_fund (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) {N m : ℕ}
    (ω : LinearMap.ker (relCoboundaryₗ (U ∩ V) (N + 1)))
    {Wset : Set ↑X} (hW : IsOpen Wset) (z₀ : SingularChain X (N + 1 + m + 1))
    (hz₀ : chainBoundary X (N + 1 + m) z₀ = 0) (Kc : SingularCompactsInOpen.CompactsIn Wset)
    (hbd : chainBoundary X (N + 1 + m) (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ Kc)
        ∈ subspaceChains (U ∪ V) (N + 1 + m))
    (h : N + 1 + m + 1 = N + 1 + 1 + m) :
    ∃ (j : ℕ) (w : SingularChain (sub V) (N + 1 + m)),
      cap (coboundary X (N + 1) (cochainSplit U (N + 1) ω.1.1))
          (h ▸ (⇑(SingularSubdivision.singularSd X (N + 1 + m + 1)))^[j]
            (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ Kc))
        = cap ω.1.1 (chainIncl V (N + 1 + m) w)
          + chainBoundary X m
            (cap (cochainSplit U (N + 1) ω.1.1)
              ((⇑(SingularSubdivision.singularSd X (N + 1 + m + 1)))^[j]
                (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ Kc))) :=
  cap_coboundary_cochainSplit_subdiv U V hU hV ω
    (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ Kc) hbd h

/-- **ℤ/2 mid-cancellation**: `a = b + (a + c) ⟹ b = c` in a `ZMod 2` module. Used to extract the V-leg from
the cap-Leibniz-expanded engine relation `heng`. Stated abstractly over `M` so applying it to the concrete
`heng` infers `a`/`b`/`c` with NO dependent-cast motive issue (the `rw [add_*]`/`linear_combination` route fails
on the `⋯ ▸ Sdʲ fund` cast). -/
theorem add_mid_cancel_zmod2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {a b c : M}
    (h : a = b + (a + c)) : b = c := by
  have h2 : a + (b + c) = a := by nth_rewrite 2 [h]; abel
  have hbc : b + c = 0 := add_left_cancel (h2.trans (add_zero a).symm)
  exact sub_eq_zero.mp (by rw [ZModModule.sub_eq_add]; exact hbc)

/-- **fundCycleW-headed `cap_fund_eq_cap_z0`** (the shared-z₀ reduction for a cocycle `c` vanishing on the
compact complement): `cap c (fundCycleW …) = cap c z + ∂(cap c η)`. Composes `fundCycleW_chain_rel` (giving
`fundCycleW + z = ∂η + a`, `a` over `Kᶜ`) with `cap_fund_eq_cap_z0`. Stated fundCycleW-headed + over abstract
`k`/`n` so an application matches the head structurally and amortizes the elaboration (the concrete-`fundCycleW`
`cap_fund_eq_cap_z0` application whnf-walls in the full build). -/
theorem cap_fundCycleW_eq_cap_z0 {W : Set ↑X} {k n : ℕ} (hW : IsOpen W)
    (z : SingularChain X (k + n + 1)) (hz : chainBoundary X (k + n) z = 0)
    (Kc : SingularCompactsInOpen.CompactsIn W)
    {S : Set ↑X} (hS : (↑Kc.1 : Set ↑X)ᶜ = S)
    (c : SingularCochain X k) (hc : coboundary X k c = 0)
    (hcv : ∀ d ∈ subspaceChains S (k + (n + 1)), cap c d = 0) :
    ∃ η : SingularChain X (k + (n + 1) + 1),
      cap c (SingularOpenDualityCycle.fundCycleW hW z hz Kc)
        = cap c z + chainBoundary X (n + 1) (cap c η) := by
  obtain ⟨η, a, heq, hmem⟩ := fundCycleW_chain_rel hW z hz Kc
  rw [hS] at hmem
  exact ⟨η, cap_fund_eq_cap_z0 (A := S) (m := n + 1) c hc hcv _ _ η a hmem heq⟩

/-- **Paired `fundCycleW` rel-homology** (the cross-realization bridge ingredient): for nested compacts
`K₂ ⊆ K₁` in opens `W₁, W₂` sharing the same `z₀`, the two fundamental cycles `fundCycleW(K₁)`, `fundCycleW(K₂)`
are rel-`K₂ᶜ` homologous — `fund₁ + fund₂ ∈ relBoundaries(K₂ᶜ)` — because each is rel-homologous to the SAME `z₀`
(`fundCycleW_relHomologous`) and `relBoundaries_mono` (K₁ᶜ ⊆ K₂ᶜ) lifts the `K₁` relation to `K₂ᶜ`, where the
shared `z₀` cancels (ℤ/2). Generic in `K₁, K₂, z₀` ⟹ whnf-free; feeds `relativeDualityK_cycle_compat_relB` to
transport the descent's `fund_K` cover-partition to `fund_∩` (the cross-realization). -/
theorem fundCycleW_pair_relHomologous {k m : ℕ} {W₁ W₂ : Set ↑X} (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K₁ : SingularCompactsInOpen.CompactsIn W₁) (K₂ : SingularCompactsInOpen.CompactsIn W₂)
    (hsub : (↑K₂.1 : Set ↑X) ⊆ (↑K₁.1 : Set ↑X)) :
    RelativeChain.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1)
          (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)
        + RelativeChain.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1)
          (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂)
      ∈ relBoundaries ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) := by
  have hcompl : (↑K₁.1 : Set ↑X)ᶜ ⊆ (↑K₂.1 : Set ↑X)ᶜ := Set.compl_subset_compl.mpr hsub
  have h1 := SingularOpenDualityCycle.fundCycleW_relHomologous hW₁ z₀ hz₀ K₁
  have h2 := SingularOpenDualityCycle.fundCycleW_relHomologous hW₂ z₀ hz₀ K₂
  have hadd : ∀ (S : Set ↑X) (a b : SingularChain X (k + m + 1)),
      RelativeChain.mk S (k + m + 1) (a + b)
        = RelativeChain.mk S (k + m + 1) a + RelativeChain.mk S (k + m + 1) b := by
    intro S a b; rfl
  have hc1 : RelativeChain.mk ((↑K₁.1 : Set ↑X)ᶜ) (k + m + 1)
      (z₀ + SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)
      ∈ relBoundaries ((↑K₁.1 : Set ↑X)ᶜ) (k + m + 1) := by
    rw [hadd]; exact h1
  have h1' := SingularOpenDualityCycle.relBoundaries_mono hcompl _ hc1
  have hc2 : RelativeChain.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1)
      (z₀ + SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂)
      ∈ relBoundaries ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) := by
    rw [hadd]; exact h2
  have hsum := Submodule.add_mem _ h1' hc2
  have hcalc : RelativeChain.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1)
          (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)
        + RelativeChain.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1)
          (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂)
      = RelativeChain.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1)
            (z₀ + SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)
        + RelativeChain.mk ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1)
            (z₀ + SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂) := by
    rw [hadd, hadd]
    abel_nf
    simp only [two_smul, ZModModule.add_self, zero_add, add_zero]
  rw [hcalc]; exact hsum

/-- **Chain-altitude cross-realization transport** (step 2 of the close, lock-#2-compliant — NO homology-class
lift). For a cocycle `g` and chains `a, b` whose relative sum `mk_S(a+b)` is a relative boundary, there is an
`S`-supported residual `ρ` with `cap g (∂a) = cap g (∂b) + cap g (∂ρ)`. Pure chains: extract `a+b = ∂D + ρ`
(`ρ ∈ subspaceChains S`) from `relBoundaries = range(relBoundary)`, then `∂(a+b) = ∂ρ` (`∂² = 0`) and `cap g`
linearity. The residual `cap g (∂ρ)` (with `ρ` over `S = infCompactᶜ`) is the term that couples the
cross-realization into the χ/σR step — it is NOT a free boundary. Generic ⟹ whnf-free. -/
theorem cap_chainBoundary_relBoundaries_transport {S : Set ↑X} {k n : ℕ} (g : SingularCochain X k)
    (hg : coboundary X k g = 0) (a b : SingularChain X (k + n + 1))
    (hrel : RelativeChain.mk S (k + n + 1) (a + b) ∈ relBoundaries S (k + n + 1)) :
    ∃ ρ : SingularChain X (k + n + 1), ρ ∈ subspaceChains S (k + n + 1) ∧
      cap g (chainBoundary X (k + n) a)
        = cap g (chainBoundary X (k + n) b) + cap g (chainBoundary X (k + n) ρ) := by
  obtain ⟨y, hy⟩ := hrel
  obtain ⟨D, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  erw [relBoundary_mk] at hy
  refine ⟨chainBoundary X (k + n + 1) D + (a + b), ?_, ?_⟩
  · have hz0 : RelativeChain.mk S (k + n + 1) (chainBoundary X (k + n + 1) D + (a + b)) = 0 := by
      have hsplit : RelativeChain.mk S (k + n + 1) (chainBoundary X (k + n + 1) D + (a + b))
          = RelativeChain.mk S (k + n + 1) (chainBoundary X (k + n + 1) D)
            + RelativeChain.mk S (k + n + 1) (a + b) := rfl
      rw [hsplit, hy]
      exact ZModModule.add_self _
    exact (Submodule.Quotient.mk_eq_zero _).mp hz0
  · have hdr : chainBoundary X (k + n) (chainBoundary X (k + n + 1) D + (a + b))
        = chainBoundary X (k + n) a + chainBoundary X (k + n) b := by
      rw [map_add, map_add, chainBoundary_chainBoundary_apply, zero_add]
    rw [hdr, ← capₗ_apply g (chainBoundary X (k + n) a + chainBoundary X (k + n) b), map_add,
      capₗ_apply, capₗ_apply]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]

/-- **Connecting-square V-side assembly** (ℤ/2). The cover-partition seam V-part `chainL` cancels via
`hUV` (the cocycle-`g_rep` cover-partition boundary identity), reducing the connecting-square match
`chainL + capσR = capg_∂fund` to the U-side χ `capσR = U_A + capg_∂ρ`. Pure ZMod-2 additive algebra over
ABSTRACT carriers — the concrete `fundCycleW` never enters, so no whnf wall. -/
theorem connecting_assembly_zmod2 {m : ℕ} (chainL capσR capgDfund U_A capgDrho : SingularChain X m)
    (hChi : capσR = U_A + capgDrho)
    (hUV : U_A + chainL = capgDfund + capgDrho) :
    chainL + capσR = capgDfund := by
  rw [hChi, show chainL + (U_A + capgDrho) = U_A + chainL + capgDrho from by abel, hUV]
  abel_nf
  simp only [two_smul, ZModModule.add_self, add_zero]

/-- **Set-congruence transport of a `RelativeHomology.mk`** (whnf-safe glue for the σR-leg pairing). A
relative-homology class `[mk c]` over `S'` transported along `hSet : S = S'` is the class `[mk c]` over
`S` of the same ambient chain `c` — `subst hSet` collapses the `▸` and the cycle-membership proofs are
irrelevant. Lets the goal's `hSet ▸ RelativeHomology.mk (infCompactᶜ) …` (produced by
`relKroneckerH_relCohomSetCongr_relIncl_collapse`) be re-expressed over `legSplitUᶜ ∪ legSplitVᶜ`, the set
the pairing-form reduction `rhs_pairing_reduce_partition` consumes. -/
theorem relHomology_mk_setCongr_transport {S S' : Set ↑X} (hSet : S = S') {n : ℕ}
    (c : SingularChain X n) (hc' : RelativeChain.mk S' n c ∈ relCycles S' n)
    (hc : RelativeChain.mk S n c ∈ relCycles S n) :
    (hSet ▸ RelativeHomology.mk S' n ⟨RelativeChain.mk S' n c, hc'⟩)
      = RelativeHomology.mk S n ⟨RelativeChain.mk S n c, hc⟩ := by
  subst hSet; rfl

/-- **Kronecker analog of `cap_coboundary_cochainSplit_eq`** (NC:699 — the σR-connecting engine at the
kronecker altitude; a SUB-step inside the `of_chainMatch` spine, NOT a re-spine). For `ω` a relative
cocycle on `U∩V` and a chain `c` whose boundary cover-partitions `∂c = chainIncl U u + chainIncl V w`:
`kronecker (δ(cochainSplit U ω)) c = kronecker ω (chainIncl V w)`. The adjunction
`kronecker (δφ) c = kronecker φ (∂c)` (`kronecker_coboundary_chainBoundary`) drops the cap-Leibniz boundary
term that the cap version carries; the `U`-leg dies (`cochainSplit ∈ relCochains U`) and the `V`-leg's
`φ ↦ ω` swap is the `ω - φ ∈ relCochains V` vanishing (`cochainSplit_compl_mem_relCochains`). ℤ/2. -/
theorem kronecker_coboundary_cochainSplit_eq (U V : Set ↑X) {N : ℕ}
    (ω : LinearMap.ker (relCoboundaryₗ (U ∩ V) (N + 1)))
    (c : SingularChain X (N + 1 + 1))
    (uu : SingularChain (sub U) (N + 1)) (ww : SingularChain (sub V) (N + 1))
    (hbd : chainBoundary X (N + 1) c = chainIncl U (N + 1) uu + chainIncl V (N + 1) ww) :
    kronecker (coboundary X (N + 1) (cochainSplit U (N + 1) ω.1.1)) c
      = kronecker ω.1.1 (chainIncl V (N + 1) ww) := by
  rw [kronecker_coboundary_chainBoundary, hbd, kronecker_add_right]
  have hU0 : kronecker (cochainSplit U (N + 1) ω.1.1) (chainIncl U (N + 1) uu) = 0 :=
    cochainSplit_mem_relCochains U (N + 1) ω.1.1 _ ⟨uu, rfl⟩
  have hVeq : kronecker (cochainSplit U (N + 1) ω.1.1) (chainIncl V (N + 1) ww)
      = kronecker ω.1.1 (chainIncl V (N + 1) ww) := by
    have hψ : kronecker (ω.1.1 - cochainSplit U (N + 1) ω.1.1) (chainIncl V (N + 1) ww) = 0 :=
      cochainSplit_compl_mem_relCochains U V (N + 1) ω.1.1 ω.1.2 _ ⟨ww, rfl⟩
    rw [ZModModule.sub_eq_add, kronecker_add_left, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hψ
    exact hψ.symm
  rw [hU0, zero_add, hVeq]

/-- **V-leg `cochainSplit ↦ ω` swap** (the kronecker leg-lemma): for `ω` a relative cocycle on `U∩V`,
`kronecker (cochainSplit U ω) (chainIncl V w) = kronecker ω (chainIncl V w)`. The `V`-leg half of
`kronecker_coboundary_cochainSplit_eq`, isolated: `ω - cochainSplit U ω ∈ relCochains V` vanishes on the
`V`-supported chain `chainIncl V w`. Used to present the goal RHS `kronecker (cochainSplit U ω↾)(chainIncl V w')`
in `ω↾`-on-the-left form so `kronecker_coboundary_cochainSplit_eq` joins it to `δ(cochainSplit)·(Sdʲ ·)`. -/
theorem kronecker_cochainSplit_V_leg_eq (U V : Set ↑X) {N : ℕ}
    (ω : LinearMap.ker (relCoboundaryₗ (U ∩ V) (N + 1)))
    (w : SingularChain (sub V) (N + 1)) :
    kronecker (cochainSplit U (N + 1) ω.1.1) (chainIncl V (N + 1) w)
      = kronecker ω.1.1 (chainIncl V (N + 1) w) := by
  have hψ : kronecker (ω.1.1 - cochainSplit U (N + 1) ω.1.1) (chainIncl V (N + 1) w) = 0 :=
    cochainSplit_compl_mem_relCochains U V (N + 1) ω.1.1 ω.1.2 _ ⟨w, rfl⟩
  rw [ZModModule.sub_eq_add, kronecker_add_left, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hψ
  exact hψ.symm

/-- **∈-boundaries ← pairing-zero** (route-ii final discharge engine). A cycle `z` whose Kronecker
pairing against EVERY cocycle vanishes is a boundary — homology Kronecker non-degeneracy
(`homology_eq_zero_of_kroneckerH`) + `Homology.mk_eq_zero`. This is the sanctioned final ∈-boundaries
discharge of the L2 KEY: the σR leg pairs via the Fact-A adjunction (sub-step), the spine stays
cap-Leibniz. Kernel-pure; no banned formula, no kronecker spine. -/
theorem mem_boundaries_of_kroneckerH_zero {n : ℕ} (z : SingularChain X n) (hz : z ∈ cycles X n)
    (h : ∀ ω : LinearMap.ker (coboundaryₗ X n), kronecker ω.1 z = 0) :
    z ∈ boundaries X n := by
  have hmk : Homology.mk X n ⟨z, hz⟩ = 0 := by
    apply SKEFTHawking.PoincareDualityConstruct.homology_eq_zero_of_kroneckerH
    intro ω
    obtain ⟨ωc, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
    exact h ωc
  rw [SKEFTHawking.SingularCapHomology.Homology.mk_eq_zero] at hmk
  exact hmk

/-- **Iterated subdivision commutes with `chainIncl`** (the iterate of `singularSd_chainIncl`). For a
`sub S`-chain `d`, `Sdⱼ^X (chainIncl S d) = chainIncl S (Sdⱼ^{sub S} d)`. Subdivision is natural w.r.t.
the inclusion `sub S ↪ X`. Plain induction on `j` from `SingularExcision.singularSd_chainIncl`. Feeds
the STEP-3 seam/σR cross-realization (relating the un-subdivided seam leg to the cover-fine σR leg). -/
theorem singularSd_iterate_chainIncl {S : Set ↑X} {n : ℕ} (j : ℕ) (d : SingularChain (sub S) n) :
    (⇑(SingularSubdivision.singularSd X n))^[j] (chainIncl S n d)
      = chainIncl S n ((⇑(SingularSubdivision.singularSd (sub S) n))^[j] d) := by
  induction j generalizing d with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      SingularExcision.singularSd_chainIncl]

/-- **Kronecker cover-partition vanishing** (the kronecker analog of `cap_relCochains_cover_partition_eq_zero`,
NC:402). A cochain `a` vanishing on BOTH `P`- and `Q`-chains (`a ∈ relCochains P ∩ relCochains Q`, e.g.
`δ(cochainSplit P g_rep↾)` for a cocycle `g_rep↾`, via `cochainSplit_coboundary_mem_U/V`) pairs to `0`
against a cover-subordinate partition `chainIncl P u + chainIncl Q w`: each leg vanishes by
`(mem_relCochains).1`. The STEP-3 hRHS χ-vanishing at the kronecker altitude: `δgamb` paired against the
cover-fine residual `chainIncl P u' + chainIncl Q w'` is zero. ℤ/2. -/
theorem kronecker_relCochains_cover_partition_eq_zero {P Q : Set ↑X} {n : ℕ}
    (a : SingularCochain X n) (haP : a ∈ relCochains P n) (haQ : a ∈ relCochains Q n)
    (u : SingularChain (sub P) n) (w : SingularChain (sub Q) n) :
    kronecker a (chainIncl P n u + chainIncl Q n w) = 0 := by
  rw [kronecker_add_right, (mem_relCochains _ _ _).1 haP _ ⟨u, rfl⟩,
    (mem_relCochains _ _ _).1 haQ _ ⟨w, rfl⟩, add_zero]

/-! ## Small-chains cover-kill infrastructure (LEAF 2, Hatcher Prop 2.21 / excision form)

Foundational kernel-pure bricks assembling the existing machinery (`subspaceChainsEquiv`,
`kronecker_pullbackCochain`, `coboundary_pullbackCochain`, `exists_mvUnion_partition`,
`kronecker_relCochains_cover_partition_eq_zero`) for the cover-supported boundary-cycle kill. Each brick is
a standalone verified statement; the apex assembly carries irreducible subdivision-homotopy slack (see the
residual note at the end). NO banned brick (`_of_crossRealization`/`_of_hcup`/`kronecker_pd_fold_fund`),
no new axiom/sorry. -/

/-- **STEP 1 (subspace boundary lift).** An ambient `(P∪Q)`-supported boundary relation `chainIncl W S_sub
= ∂(chainIncl W COMM_sub)` (with `W = P∪Q`, both chains lifted from `sub W`) transports to the subspace:
`∂COMM_sub = S_sub` in `SingularChain (sub W)`. `chainIncl` is an injective chain map
(`chainIncl_chainBoundary` + `chainIncl_injective`), so the ambient boundary identity descends. This is the
Step-1 lift that turns the cover-supported ambient bounding into a genuine `sub W`-boundary relation, ready
for the `pullbackCochain` transport (Step 2). -/
theorem chainBoundary_sub_of_chainIncl_eq {W : Set ↑X} {n : ℕ}
    (S_sub : SingularChain (sub W) n) (COMM_sub : SingularChain (sub W) (n + 1))
    (hbd : chainIncl W n S_sub = chainBoundary X n (chainIncl W (n + 1) COMM_sub)) :
    chainBoundary (sub W) n COMM_sub = S_sub := by
  apply chainIncl_injective W n
  rw [chainIncl_chainBoundary]
  exact hbd.symm

/-- **STEP 2 (pullbackCochain transport).** Pairing the ambient cochain `gamb` against the inclusion of a
`sub W`-chain equals pairing the pulled-back cochain `pullbackCochain W gamb` against the `sub W`-chain:
`kronecker gamb (chainIncl W c) = kronecker (pullbackCochain W gamb) c`. The `kronecker_pullbackCochain`
adjunction, oriented `gamb`-on-the-ambient side. This moves the whole pairing down into `sub W`, where the
cover `{val⁻¹P, val⁻¹Q}` is global (their union is `univ`). -/
theorem kronecker_chainIncl_eq_pullbackCochain {W : Set ↑X} {n : ℕ}
    (gamb : SingularCochain X n) (c : SingularChain (sub W) n) :
    kronecker gamb (chainIncl W n c) = kronecker (SingularCapChainIncl.pullbackCochain W n gamb) c :=
  (SingularCapSubKDuality.kronecker_pullbackCochain gamb c).symm

/-- **STEP 3a (δ commutes with pullback).** The subspace coboundary of a pulled-back cochain is the
pullback of the ambient coboundary: `δ(pullbackCochain W gamb) = pullbackCochain W (δgamb)`
(`coboundary_pullbackCochain`). In particular `δ(pullbackCochain W gamb)` is a **cocycle** in `sub W`
(it is a coboundary), so its pairing is subdivision-invariant — the property that the non-cocycle `gamb`
itself lacks. -/
theorem coboundary_pullbackCochain_eq {W : Set ↑X} {n : ℕ} (gamb : SingularCochain X n) :
    coboundary (sub W) n (SingularCapChainIncl.pullbackCochain W n gamb)
      = SingularCapChainIncl.pullbackCochain W (n + 1) (coboundary X n gamb) :=
  SingularConnSquareCloseFinal.coboundary_pullbackCochain n gamb

/-- **STEP 3b (δgamb pulls back into both cover-leg relCochains).** When the ambient coboundary
`δgamb = coboundary X n gamb` vanishes on `P`-chains AND `Q`-chains (`δgamb ∈ relCochains P ∩ relCochains
Q` — the `cochainSplit_coboundary_mem_U/V` situation), its `sub W`-pullback `δ(pullbackCochain W gamb)`
lands in `relCochains (val⁻¹P) ∩ relCochains (val⁻¹Q)` over `sub W`. Via `coboundary_pullbackCochain_eq`
(δ↔pullback commutation) + `pullbackCochain_mem_relCochains` (relCochains transports along the inclusion).
This is the cover-fine-kill datum (Step 4 consumes it). -/
theorem coboundary_pullbackCochain_mem_relCochains_cover {W P Q : Set ↑X} {n : ℕ}
    (gamb : SingularCochain X n) (hP : coboundary X n gamb ∈ relCochains P (n + 1))
    (hQ : coboundary X n gamb ∈ relCochains Q (n + 1)) :
    coboundary (sub W) n (SingularCapChainIncl.pullbackCochain W n gamb)
        ∈ relCochains (Subtype.val ⁻¹' P : Set ↑(sub W)) (n + 1)
      ∧ coboundary (sub W) n (SingularCapChainIncl.pullbackCochain W n gamb)
        ∈ relCochains (Subtype.val ⁻¹' Q : Set ↑(sub W)) (n + 1) := by
  rw [coboundary_pullbackCochain_eq]
  exact ⟨SingularConnSquareRHSPairing.pullbackCochain_mem_relCochains _ hP,
    SingularConnSquareRHSPairing.pullbackCochain_mem_relCochains _ hQ⟩

/-- **STEP 4a (cocycle subdivision shift for a general chain).** For an absolute cocycle `a` and ANY chain
`d` of degree `n+1` (NOT required to be a cycle), the pairing decomposes as
`⟨a, d⟩ = ⟨a, Sdᵐd⟩ + ⟨a, Dₘ(∂d)⟩`. From the general (non-cycle) chain-homotopy identity
`∂(Dₘd) + Dₘ(∂d) = d + Sdᵐd` (`iterHomotopy_chainHomotopy`): the `∂(Dₘd)` term dies under the cocycle
(`⟨a, ∂h⟩ = ⟨δa, h⟩ = 0`), leaving the `Sdᵐd` (subdivided) and `Dₘ(∂d)` (boundary-homotopy) terms. The
`Sdᵐd` term is what `kronecker_relCochains_cover_partition_eq_zero` kills after cover-fine subdivision; the
`Dₘ(∂d)` term is the irreducible boundary slack that the apex match absorbs over the shared `z₀`. ℤ/2.
Generalizes `kronecker_singularSd_iterate_cocycle` (Uncond:97, which needs `∂d = 0` to drop the slack). -/
theorem cocycle_kronecker_singularSd_shift {n : ℕ} (a : LinearMap.ker (coboundaryₗ X (n + 1)))
    (d : SingularChain X (n + 1)) (m : ℕ) :
    kronecker a.1 d
      = kronecker a.1 ((⇑(SingularSubdivision.singularSd X (n + 1)))^[m] d)
        + kronecker a.1 (SingularSubdivision.iterHomotopy X n m (chainBoundary X n d)) := by
  have hh := SingularSubdivision.iterHomotopy_chainHomotopy X m n d
  have hmid : kronecker a.1
      (chainBoundary X (n + 1) (SingularSubdivision.iterHomotopy X (n + 1) m d)) = 0 := by
    rw [← kronecker_coboundary_chainBoundary,
      show coboundary X (n + 1) a.1 = coboundaryₗ X (n + 1) a.1 from rfl, LinearMap.mem_ker.mp a.2,
      ← kroneckerₗ_apply, map_zero, LinearMap.zero_apply]
  have hd : d = (⇑(SingularSubdivision.singularSd X (n + 1)))^[m] d
      + chainBoundary X (n + 1) (SingularSubdivision.iterHomotopy X (n + 1) m d)
      + SingularSubdivision.iterHomotopy X n m (chainBoundary X n d) := by
    rw [add_assoc, hh, add_comm d ((⇑(SingularSubdivision.singularSd X (n + 1)))^[m] d),
      ← add_assoc, ZModModule.add_self, zero_add]
  conv_lhs => rw [hd]
  rw [kronecker_add_right, kronecker_add_right, hmid, add_zero]

/-- **STEP 4b (cover-fine subdivision exists in the subspace).** In `sub (P∪Q)` the cover
`{val⁻¹P, val⁻¹Q}` is global (their union is `univ`, `preimage_union_eq_univ`), so every chain becomes
cover-fine after enough barycentric subdivisions: `∃ m, Sdᵐ COMM_sub ∈ mvUnionChains (val⁻¹P) (val⁻¹Q)`.
The geometric input (`exists_iterate_mvUnion` at the global cover) for splitting the subdivided bounding
chain cover-subordinately (Step 4c). -/
theorem exists_iterate_mvUnion_sub {P Q : Set ↑X} (hP : IsOpen P) (hQ : IsOpen Q) (n : ℕ)
    (COMM_sub : SingularChain (sub (P ∪ Q)) n) :
    ∃ m, (⇑(SingularSubdivision.singularSd (sub (P ∪ Q)) n))^[m] COMM_sub
      ∈ SingularRelativeMV.mvUnionChains (Subtype.val ⁻¹' P : Set ↑(sub (P ∪ Q)))
          (Subtype.val ⁻¹' Q) n := by
  apply SingularRelativeMV.exists_iterate_mvUnion
  · exact hP.preimage continuous_subtype_val
  · exact hQ.preimage continuous_subtype_val
  · rw [SingularConnSquareLHSExplicit.preimage_union_eq_univ]
    exact SingularExcision.mem_subspaceChains_of_support (fun _ _ => Set.subset_univ _)

/-- **STEP 4c (cocycle pairing isolates the boundary slack).** For a cocycle `c` in `sub (P∪Q)` lying in
BOTH cover-leg relative cochains (`c ∈ relCochains (val⁻¹P) ∩ relCochains (val⁻¹Q)` — the
`δ(pullbackCochain (P∪Q) gamb)` situation from `coboundary_pullbackCochain_mem_relCochains_cover`), pairing
`c` against any chain `COMM_sub` reduces to the pure boundary-homotopy slack:
`kronecker c COMM_sub = kronecker c (Dₘ(∂COMM_sub))`. The `Sdᵐ COMM_sub` term of `cocycle_kronecker_singularSd_shift`
is cover-fine (`exists_iterate_mvUnion_sub`), so it splits cover-subordinately and vanishes
(`kronecker_relCochains_cover_partition_eq_zero`). What remains is `⟨c, Dₘ(∂COMM_sub)⟩` — the irreducible
subdivision-homotopy slack on the boundary, which the apex cap-Leibniz match absorbs over the shared `z₀`.
This is the honest distillation of the cover-kill: cover-fine subdivision kills the bulk, leaving exactly
the boundary slack. ℤ/2. -/
theorem cocycle_kronecker_eq_boundary_slack {P Q : Set ↑X} (hP : IsOpen P) (hQ : IsOpen Q) {n : ℕ}
    (c : LinearMap.ker (coboundaryₗ (sub (P ∪ Q)) (n + 1)))
    (hcP : c.1 ∈ relCochains (Subtype.val ⁻¹' P : Set ↑(sub (P ∪ Q))) (n + 1))
    (hcQ : c.1 ∈ relCochains (Subtype.val ⁻¹' Q : Set ↑(sub (P ∪ Q))) (n + 1))
    (COMM_sub : SingularChain (sub (P ∪ Q)) (n + 1)) :
    ∃ m, kronecker c.1 COMM_sub
      = kronecker c.1 (SingularSubdivision.iterHomotopy (sub (P ∪ Q)) n m
          (chainBoundary (sub (P ∪ Q)) n COMM_sub)) := by
  obtain ⟨m, hm⟩ := exists_iterate_mvUnion_sub hP hQ (n + 1) COMM_sub
  obtain ⟨u, w, hsplit⟩ :=
    SingularConnSquareLHSExplicit.exists_chainIncl_partition_of_mem_mvUnionChains
      (Subtype.val ⁻¹' P : Set ↑(sub (P ∪ Q))) (Subtype.val ⁻¹' Q) (n + 1) _ hm
  refine ⟨m, ?_⟩
  rw [cocycle_kronecker_singularSd_shift c COMM_sub m, hsplit,
    kronecker_relCochains_cover_partition_eq_zero c.1 hcP hcQ u w, zero_add]

/-- **STEP 5 (apex reduction to the boundary slack).** The full small-chains cover-kill assembly, reduced
to its honest residual. For `P Q` open, `gamb = cochainSplit P φ` whose ambient coboundary lies in both
cover-leg relative cochains (`δgamb ∈ relCochains P ∩ relCochains Q` — the cocycle-`φ` situation via
`cochainSplit_coboundary_mem_U/V`), and a cover-supported boundary relation `chainIncl W S_sub =
∂(chainIncl W COMM_sub)` with `W = P∪Q`: the target pairing `kronecker gamb (chainIncl W S_sub)` equals
EXACTLY the subdivision-homotopy boundary slack `kronecker (δ(pullbackCochain W gamb)) (Dₘ S_sub)` for some
`m`, where `S_sub = ∂COMM_sub`.

Chain of the assembly: Step 2 (`kronecker_chainIncl_eq_pullbackCochain`) moves the pairing into `sub W`;
Step 1 (`chainBoundary_sub_of_chainIncl_eq`) gives `∂COMM_sub = S_sub`; the δ-adjunction
(`kronecker_coboundary_chainBoundary`) turns `gamb`-against-`∂COMM_sub` into the **cocycle**
`δ(pullbackCochain W gamb)`-against-`COMM_sub` (Step 3a/3b make it a cocycle in both cover-leg relCochains);
Step 4c (`cocycle_kronecker_eq_boundary_slack`) kills the cover-fine bulk, leaving the slack.

This is the genuine reduction of LEAF 2's open crux to a single clean residual: the slack `⟨δ(pb gamb),
Dₘ(∂COMM_sub)⟩` is NOT cover-fine-killable in isolation (the subdivision homotopy `Dₘ` of the cover-spanning
cycle `S_sub` need not be cover-subordinate), which is exactly why the apex match absorbs it over the shared
`z₀` rather than closing it locally. ℤ/2. -/
theorem kronecker_cochainSplit_coverSupported_boundary_eq_slack {P Q : Set ↑X} (hP : IsOpen P)
    (hQ : IsOpen Q) {n : ℕ} (φ : SingularCochain X n)
    (hP' : coboundary X n (cochainSplit P n φ) ∈ relCochains P (n + 1))
    (hQ' : coboundary X n (cochainSplit P n φ) ∈ relCochains Q (n + 1))
    (S_sub : SingularChain (sub (P ∪ Q)) n) (COMM_sub : SingularChain (sub (P ∪ Q)) (n + 1))
    (hbd : chainIncl (P ∪ Q) n S_sub
      = chainBoundary X n (chainIncl (P ∪ Q) (n + 1) COMM_sub)) :
    ∃ m, kronecker (cochainSplit P n φ) (chainIncl (P ∪ Q) n S_sub)
      = kronecker (coboundary (sub (P ∪ Q)) n
            (SingularCapChainIncl.pullbackCochain (P ∪ Q) n (cochainSplit P n φ)))
          (SingularSubdivision.iterHomotopy (sub (P ∪ Q)) n m S_sub) := by
  -- the pulled-back cocycle datum
  obtain ⟨hcP, hcQ⟩ :=
    coboundary_pullbackCochain_mem_relCochains_cover (W := P ∪ Q) (cochainSplit P n φ) hP' hQ'
  set c : LinearMap.ker (coboundaryₗ (sub (P ∪ Q)) (n + 1)) :=
    ⟨coboundary (sub (P ∪ Q)) n
        (SingularCapChainIncl.pullbackCochain (P ∪ Q) n (cochainSplit P n φ)),
      by rw [LinearMap.mem_ker]
         exact coboundary_comp_coboundary (sub (P ∪ Q)) n _⟩ with hc_def
  -- Step 1: the subspace boundary relation `∂COMM_sub = S_sub`
  have hsub : chainBoundary (sub (P ∪ Q)) n COMM_sub = S_sub :=
    chainBoundary_sub_of_chainIncl_eq S_sub COMM_sub hbd
  -- Step 4c on the cocycle `c` against `COMM_sub`
  obtain ⟨m, hslack⟩ := cocycle_kronecker_eq_boundary_slack hP hQ c hcP hcQ COMM_sub
  refine ⟨m, ?_⟩
  -- Step 2: move into `sub W`
  rw [kronecker_chainIncl_eq_pullbackCochain]
  -- present `S_sub = ∂COMM_sub`, then the δ-adjunction `⟨pb gamb, ∂COMM_sub⟩ = ⟨δ(pb gamb), COMM_sub⟩`
  rw [← hsub, ← kronecker_coboundary_chainBoundary]
  -- ⊢ kronecker (δ(pb gamb)) COMM_sub = kronecker (δ(pb gamb)) (Dₘ S_sub)
  rw [show coboundary (sub (P ∪ Q)) n
        (SingularCapChainIncl.pullbackCochain (P ∪ Q) n (cochainSplit P n φ)) = c.1 from rfl,
    hslack, hsub]

/-- **Abstract cup–cap joint-match assembly** (the genuine MV-naturality match core, whnf-dodging form).
On a common space `M` (instantiated `M = sub (U ∩ V)`), once BOTH connecting-square legs are realized as
the cap / rcap of the SAME fundamental `F` modulo a boundary, the match closes by the cup-cap duality core
`kronecker_cap_eq_kronecker_rcap` (MatchLHS:73). The boundary slacks `∂e₁` (LHS) and `∂e₂` (RHS) die because
the test cochains `ω` (LHS) and `gM` (RHS) are absolute cocycles (`hω`, `hgM`) — exactly the cocycle property
`SingularConnSquareRHSPairing.relCocycle_props` supplies for the restricted `g_rep↾` (and `ω` carries by
hypothesis). Stated over FREE carriers `ω, gM, F, L, R, e₁, e₂` so the concrete `fundCycleW`/`seam`/`rcap`
terms infer structurally at application (no 200k whnf wall). Over ℤ/2. Kernel-pure. -/
theorem joint_cap_rcap_match {M : TopCat} {N p : ℕ}
    (ω : SingularCochain M (p + 1)) (hω : coboundary M (p + 1) ω = 0)
    (gM : SingularCochain M (N + 1)) (hgM : coboundary M (N + 1) gM = 0)
    (F : SingularChain M (N + 1 + (p + 1)))
    (L : SingularChain M (p + 1)) (R : SingularChain M (N + 1))
    (e₁ : SingularChain M (p + 1 + 1)) (e₂ : SingularChain M (N + 1 + 1))
    (hL : L = cap gM F + chainBoundary M (p + 1) e₁)
    (hR : R = SingularCapChainIncl.rcap ω F + chainBoundary M (N + 1) e₂) :
    kronecker ω L = kronecker gM R := by
  rw [hL, hR, kronecker_add_right, kronecker_add_right,
    ← kronecker_coboundary_chainBoundary, ← kronecker_coboundary_chainBoundary, hω, hgM,
    SingularConnSquareMatchLHS.kronecker_cap_eq_kronecker_rcap gM ω F]
  simp

theorem subHomConnecting_openDuality {N p : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K) :
    SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV (p + 1)
        (SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := p + 1) (hU.union hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          K g)
      = openDuality (k := N + 2) (m := p) (hU.inter hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          (SKEFTHawking.SingularCSCMayerVietorisConnecting.legδ U V hU hV N K g) := by
  -- ▶ ROUTE B (2026-06-23, harness v4.2) — the CHAIN-SAFE route. `_of_chainMatch` reduces the whole
  --   connecting square to the single chain-level residual `hmatch`: the V-part boundary `∂zB`
  --   (`boundaryExtract`) paired against the double-seam-pullback of `a'rep` over the cap realization
  --   (`pullbackDualityₗ` of the cohomology-connecting `σR`). This is the whnf-safe HLHSBridge form
  --   (explicit seam-homeo cochains via `pullbackCochainMap`), NOT the `relativeDualityK`/`absCohomConn`
  --   class lift that walls. Discharge `hmatch` via `SingularConnSquareHLHSBridge.hLHS_cap_mapChain_bridge_mod`
  --   (+ residual `hdual`/`cap_boundaryExtract_naturality`) — the genuine local-PD content over the shared z₀.
  apply SingularConnSquareCloseChainMap.subHomConnecting_openDuality_of_chainMatch hU hV z₀ hz₀ K g
  intro g_rep zc0 hzc0 zA zB hcyc hpart a'rep hzBmem σR_rep hσR
  -- ▶ COACH-LOCKED ROUTE (cap-Leibniz scaffold): hmatch_close (cocycle pairs to 0 against a boundary) →
  --   factB_transport (seam-iso reindex) → KEY (`seam²(boundaryExtract zB) + pullbackDualityₗ σR ∈
  --   boundaries(sub(U∩V))`), then `realize_chainBoundary_cap_mem_boundaries` on `W = cap(cochainSplit g_rep)(F)`
  --   + the two facts (i) χ-term, (ii) seam-term. NO subdivision (cover-level). Cup-form/CrossReal = re-seed, discarded.
  refine hmatch_close _ _ (p + 1) a'rep _ _ ?_
  refine factB_transport _ _ _ _ ?_
  -- ▶ ROUTE ii (resolved turn 10, roadmap §G1): discharge the ∈-boundaries KEY via the PAIRING — the
  --   sanctioned FINAL ∈-boundaries discharge (σR enters via the Fact-A pairing SUB-step; the cap-Leibniz
  --   `of_chainMatch` spine is kept; this is NOT the banned `of_hcup`-as-spine). KEY =
  --   `seam²(boundaryExtract zB) + pullbackDualityₗ(infCompactᶜ)(U∩V)(fundCycleW) σR_rep ∈ boundaries(sub(U∩V))`.
  --   Via `mem_boundaries_of_kroneckerH_zero` (brick 1): (A) the KEY chain is a cycle; (B) it pairs to 0 against
  --   every cocycle (σR leg: cup-cap adjunction `kronecker_cap_eq_kronecker_rcap` + Geom:73 + hσR, slack dies on
  --   the cocycle; seam leg: ∂zB pairing). The exact-χ witness route (route i) is dropped: σR has no exact-chain
  --   bridge (banned hmem) — see roadmap §G1.
  refine mem_boundaries_of_kroneckerH_zero _ ?_ ?_
  · -- (A) cycle: the KEY chain is a cycle. Seam-mapped `boundaryExtract` (boundaryExtract_mem_cycles +
    --   mapChain_mem_cycles ×2) ⊕ pullbackDualityₗ of the σR-cocycle on the infCompact fundamental
    --   (pullbackDualityₗ_mem_cycles; hzS = fundCycleW_boundary).
    refine add_mem ?_ ?_
    · apply SingularFunctoriality.mapChain_mem_cycles
      apply SingularFunctoriality.mapChain_mem_cycles
      apply SingularPairLES.boundaryExtract_mem_cycles
    · apply SingularLocalDualityK.pullbackDualityₗ_mem_cycles
      exact SingularOpenDualityCycle.fundCycleW_boundary _ _ _ _
  · -- (B) pairing: ∀ cocycle ω, kronecker ω.1 (seam²(boundaryExtract zB) + pullbackDualityₗ … σR_rep) = 0.
    intro ω
    -- split (kronecker bilinear) + ℤ/2 reduce (`a+b=0 ↔ a=b`) to the connecting-square LEG MATCH:
    -- the seam leg (ω paired against the V-part `seam²(boundaryExtract zB)` of ∂z₀) equals the σR leg
    -- (ω paired against the cap of σR_rep = the connecting of g_rep) — this IS hcross at the pairing level.
    rw [kronecker_add_right, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]
    -- ⊢ kronecker ω.1 (seam²(boundaryExtract zB)) = kronecker ω.1 (pullbackDualityₗ(infCompactᶜ)(U∩V)(fund) σR_rep)
    -- σR-LEG REDUCTION (GREEN): present the σR cap as `relativeDualityK` (defeq via relativeDualityK_mk +
    -- kroneckerH_mk_mk), then the bridge `kroneckerH_relativeDualityK_mk_eq_relKroneckerH` → the relKroneckerH
    -- connecting pairing form. (hWcyc discharged inline via chainIncl_rcap_mem_relCycles + fundCycleW_boundary.)
    conv_rhs => change kroneckerH (p + 1) (Submodule.Quotient.mk ω) (SingularLocalDualityK.relativeDualityK _ _ (N + 1 + 1) p _ _ (SingularOpenDualityCycle.fundCycleW_boundary _ _ _ _) (RelativeCohomology.mk _ (N + 1 + 1) σR_rep))
    rw [SingularCapSubKDuality.kroneckerH_relativeDualityK_mk_eq_relKroneckerH _ _ _ _ _ (SingularCapSubKDuality.chainIncl_rcap_mem_relCycles _ _ (SingularOpenDualityCycle.fundCycleW_boundary _ _ _ _) ω)]
    -- ⊢ kronecker ω.1 (seam²(boundaryExtract zB)) = relKroneckerH (infCompactᶜ) (mk σR_rep) [chainIncl(rcap ω fund)]
    -- hσR: σR_rep's class IS the connecting of g_rep (relCohomSetCongr/relCohomRestrict-bridged relCohomMvConnecting).
    conv_rhs => rw [show RelativeCohomology.mk _ (N + 1 + 1) σR_rep = Submodule.Quotient.mk σR_rep from rfl, hσR]
    -- ⊢ … = relKroneckerH (infCompactᶜ) (relCohomSetCongr(relCohomMvConnecting (legSplitUᶜ)(legSplitVᶜ)
    --     (relCohomRestrict (relCohomSetCongr (mk g_rep))))) [chainIncl(rcap ω fund)]
    -- PEEL the OUTER set-congr (σR_rep over infCompactᶜ = legSplitUᶜ∪legSplitVᶜ): present the homology as
    -- `relIncl refl …` (shape `y` so the `←` rw pattern isn't a bare metavar), then collapse (TwoCoverBridge:84).
    conv_rhs => rw [← SingularTwoCoverBridge.relIncl_refl_apply (Set.Subset.refl _)
      (RelativeHomology.mk _ (N + 1 + 1) _),
      SingularTwoCoverBridge.relKroneckerH_relCohomSetCongr_relIncl_collapse]
    -- ⊢ … = relKroneckerH (legSplitUᶜ∪legSplitVᶜ) (relCohomMvConnecting (legSplitUᶜ)(legSplitVᶜ)
    --     (relCohomRestrict (relCohomSetCongr (mk g_rep)))) (⋯ ▸ [chainIncl(rcap ω fund)])
    -- REDUCE the MvConnecting's cohomology arg to `mk (g_rep↾)` (push the bridges through mk): convert
    -- `Quotient.mk g_rep → RelativeCohomology.mk` (rfl), then `relCohomSetCongr_mk` + `relCohomRestrict_mk`.
    conv_rhs => rw [show (Submodule.Quotient.mk g_rep : RelativeCohomology _ (N + 1))
        = RelativeCohomology.mk _ (N + 1) g_rep from rfl,
      SingularRelCohomSetCongrMk.relCohomSetCongr_mk,
      SingularRelativeCohomologyRestrict.relCohomRestrict_mk]
    -- ⊢ … = relKroneckerH (legSplitUᶜ∪legSplitVᶜ) (relCohomMvConnecting (legSplitUᶜ)(legSplitVᶜ)
    --     (mk (relCocycleRestrict (⋯ ▸ g_rep)))) (⋯ ▸ [chainIncl(rcap ω fund)])  — the rhs_pairing_reduce form.
    -- ▶ NEXT: (a) `rhs_pairing_reduce`/`_partition` (RHSPairing:42/94) → `kronecker(δ(cochainSplit g_rep↾))(Sdʲc)`
    --   + cover-partition `∂(Sdʲc)=chainIncl u'+chainIncl w'` (handle the `⋯ ▸` homology transport); (b) SEAM leg
    --   `kronecker ω.1 (seam²(boundaryExtract zB))` → V-leg w' match (boundaryExtract/seam = cover-partition V-part;
    --   z₀-reduction via fundCycleW_relHomologous if the Sdʲ slack needs killing).
    -- STEP 1: push the cover-identity transport `hSet ▸` through `RelativeHomology.mk`/`RelativeChain.mk`
    --   so the σR-leg homology is over `legSplitUᶜ ∪ legSplitVᶜ` — the set `rhs_pairing_reduce_partition` reads.
    rw [relHomology_mk_setCongr_transport]
    rotate_left
    · exact (infCompact_compl_legSplit hU hV K).symm
    · -- the transported chain `chainIncl(U∩V)(rcap ω fund)` is a `(legSplitUᶜ∪legSplitVᶜ)`-rel cycle.
      have hbd := SingularOpenDualityCycle.fundCycleW_boundary (hU.inter hV)
        (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
        (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
        (SingularCSCMayerVietorisConnecting.infCompact U V
          (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
          (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K))
      rw [SingularCSCMayerVietorisConnecting.infCompact_coe, Set.compl_inter] at hbd
      exact SingularCapSubKDuality.chainIncl_rcap_mem_relCycles _
        (SingularOpenDualityCycle.fundCycleW_mem_W (hU.inter hV) _ _ _) hbd ω
    -- STEP 2: reduce the σR-leg connecting PAIRING to the explicit cochain Kronecker pairing
    --   `kronecker (δ(cochainSplit P g_rep↾)) (Sdʲ c)` + the cover-partition `∂(Sdʲc) = chainIncl P u' + chainIncl Q w'`.
    obtain ⟨j, u', w', hpair, hsplit⟩ :=
      SingularConnSquareRHSPairing.rhs_pairing_reduce_partition (M := X) (N := N)
        ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ)
        ((↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
        (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
        (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
        _ _ _
    rw [hpair]
    -- ▶ SANCTIONED JOINT COCYCLE CLOSE (roadmap §G1 turn-28). The σR-leg reads `kronecker (δgamb)(Sdʲ c_fund)`
    --   with `δgamb` a COCYCLE. The adjunction `⟨δgamb, Sdʲ c_fund⟩ = ⟨gamb, ∂(Sdʲ c_fund)⟩` (cover-partition
    --   `∂(Sdʲ c_fund) = chainIncl P u' + chainIncl Q w'`, `hsplit`; P-leg drops, `gamb ∈ relCochains P`) lands the
    --   σR-leg at `⟨gamb, chainIncl Q w'⟩` — a VALID, reversible step (NOT the divergence; the divergence was the
    --   subsequent `cross_realization_match` SPLIT into independent hLHS/hRHS leaves, which couple over z₀).
    rw [SingularHomologyMod2.kronecker_coboundary_chainBoundary, hsplit, kronecker_add_right,
      (mem_relCochains _ _ _).1 (cochainSplit_mem_relCochains _ _ _) _ ⟨u', rfl⟩, zero_add]
    -- ⊢ kronecker ω (seam²(boundaryExtract zB)) = kronecker gamb (chainIncl Q w')   (gamb = cochainSplit P g_rep↾)
    -- ▶ RESIDUAL = the genuine cap-product MV-naturality CROSS-REALIZATION (the project's deepest open core,
    --   unclosed across ~6 5q.F compactions). The two legs pair DIFFERENT cochains in DIFFERENT spaces/degrees:
    --     LHS  = ⟨ω, V-part of `cap g_rep fund_{U∪V}`⟩   (ω cocycle on `sub(U∩V)`, deg p+1; zB = the V-part of
    --            `cap g_rep fund_{U∪V}` via hpart/hzc0; seam-transported by `chainIncl_seam_boundaryExtract` NC:568)
    --     RHS  = ⟨g_rep↾, V-part of `∂(Sdʲ(chainIncl(U∩V)(rcap ω fund_∩)))`⟩   (gamb = cochainSplit P g_rep↾, deg N+1)
    --   They are joined by the cup-cap MATCH CORE `kronecker_cap_eq_kronecker_rcap` (MatchLHS:73,
    --   `⟨ω, cap g_rep z⟩ = ⟨g_rep, rcap ω z⟩` = `⟨g_rep ∪ ω, z⟩`) / `kronecker_cap_chainIncl_eq_rcap_chainIncl`
    --   (MatchLHS:83, the cover-wise V-part form), over the SHARED z₀ where the Sdʲ slack dies (∂z₀ = 0,
    --   `pair_fund_eq_pair_z0` RHSPairing:149 / `kronecker_relCocycle_singularSd_invariant` RHSPairing:232).
    --   This is a JOINT close (the legs couple over z₀) — NOT the divergent `cross_realization_match` independent
    --   hLHS/hRHS leaf-split (which is why that split walled). It needs a fresh cross-realization bridge that
    --   carries fund_{U∪V} (the LHS realization) and fund_∩ (the RHS realization) to the SAME z₀ and matches via
    --   the cup-cap core — built over abstract carriers to dodge the concrete-fundCycleW whnf wall (200k).
    --   CONSTRAINT-CLEAN: NO `cup_pair_fund_eq_pair_z0` (cup version banned), NO `relCohomMvConnecting_eq*`,
    --   NO `_of_crossRealization`/`of_hcup_linked`/`kronecker_pd_fold_fund` (spine stays `of_chainMatch`).
    -- ▶ BRICK A (turn 30, GREEN): drop the cochainSplit on the σR V-leg (`kronecker_cochainSplit_V_leg_eq` NC:928,
    --   inferred args — explicit `legSplitUᶜ` args hit the whnf wall). RHS → bare `g_rep↾`-on-the-left.
    rw [kronecker_cochainSplit_V_leg_eq]
    -- ⊢ kronecker ω (seam²(boundaryExtract zB)) = kronecker g_rep↾ (chainIncl (legSplitVᶜ) w')
    -- ▶ ROUTE MAPPED + ASSEMBLY HELPER BUILT (2026-06-24, joint-match). The close is the cup-cap match on the
    --   COMMON space `M := sub (U ∩ V)` via the verified kernel-pure `joint_cap_rcap_match` (NC, above): once
    --   BOTH legs are realized on M as `L = cap gM F + ∂e₁` (LHS) and `R = rcap ω F + ∂e₂` (RHS) with the SAME
    --   fundamental F and `gM = pullbackCochain (U∩V) g_rep↾`, the match is `kronecker_cap_eq_kronecker_rcap`
    --   (MatchLHS:73) and the slacks die because ω, gM are cocycles (ω by hyp; gM via `relCocycle_props`(1) +
    --   `coboundary_pullbackCochain`). The `relCocycle_props` lever (RHSPairing:165) is USED for gM's cocycle
    --   property (slack-killing); it does NOT collapse the σR cover-fine subdivision (the V/U legs of `hsplit`
    --   each survive: g_rep↾ vanishes only on A=legSplitUᶜ∩legSplitVᶜ chains, not on legSplitUᶜ or legSplitVᶜ
    --   separately — so the cup-cap match is irreducible, confirmed this session).
    -- ▶ VERIFIED INGREDIENTS (build with `lean_run_code` / `lean_multi_attempt` this session):
    --   (a) σR-side step-0: `rw [kronecker_chainIncl_eq_pullbackCochain]` ⟹ RHS = `kronecker (pullbackCochain
    --       legSplitVᶜ g_rep↾) w'` (clean, GREEN).
    --   (b) LHS cap-realization: `cover_partition_of_legW (hU.union hV) (castChain z₀) … K _ zc0 _ hzc0 hpart`
    --       ⟹ `hcp : cap g_rep fund_{U∪V} = chainIncl(val⁻¹U) zA + chainIncl(val⁻¹V) zB + ∂η` (zB = the V-part of
    --       `cap g_rep fund_{U∪V}`; GREEN, fires all-underscore).
    --   (c) σR structural fact: `∂(Sdʲ chainIncl(U∩V) c_sub) = chainIncl(U∩V)(∂ Sdʲ_sub c_sub)` via
    --       `singularSd_iterate_chainIncl` + `chainIncl_chainBoundary` ⟹ the whole `hsplit` sum =
    --       `chainIncl(U∩V)(∂ Sdʲ_sub (rcap ω F_sub))` (GREEN).
    -- ▶ RESIDUAL (the irreducible MV-naturality cross-realization, 3 bricks): (1) realize the LHS seam V-part
    --   `seam²(boundaryExtract zB)` ON M as `cap gM F_∩ + ∂e₁` via (b)'s `hcp` + `chainIncl_seam_boundaryExtract`
    --   (NC:568) + `cover_partition_cap_boundary_mod` (NC:387); (2) realize the RHS leg `chainIncl legSplitVᶜ w'`
    --   ON M as `rcap ω F_∩ + ∂e₂` via (c) + `chainIncl_rcap_cover_agree` (RcapCoverAgree:32); (3) reconcile the
    --   LHS fund_{U∪V} with the RHS fund_∩ to the SAME F over z₀ via `fundCycleW_pair_relHomologous` (NC:856) +
    --   `cap_chainBoundary_relBoundaries_transport` (NC:901) [the ρ-residual couples in, killed in ℤ/2]. Then
    --   `refine joint_cap_rcap_match _ ?_ _ ?_ _ _ _ _ _ ?_ ?_` (all-underscore, abstract carriers — dodges whnf).
    --   CONSTRAINT-CLEAN: spine stays `of_chainMatch`; NO banned brick; helper + ingredients all kernel-pure.
    sorry

end SKEFTHawking.SingularConnSquareCloseNC
