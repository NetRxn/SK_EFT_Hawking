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

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
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
  -- ▶ COCYCLE-g_rep CLOSE (route-corrected 2026-06-23): KEY goal = the connecting-square match
  --   `seam²(boundaryExtract zB) + pullbackDualityₗ(infCompactᶜ)(U∩V)(fundCycleW) σR_rep ∈ boundaries(sub(U∩V))`.
  --   g_rep is a COCYCLE ⟹ ∂(cap g_rep fund) = cap g_rep ∂fund EXACTLY (NO χ-term; the φ-route's χ was the
  --   non-cocycle cochainSplit's δ). Close: W' = realize(cap g_rep fund); ∂W' = realize(cap g_rep ∂fund) =
  --   realize(chainIncl_A ∂zA + chainIncl_B ∂zB) [cover_partition_cap_boundary_mod]; chain_L = V-part
  --   (seam-transport, mapChain_chainIncl_boundaryExtract), chain_R = U-part (σR=connecting-of-g_rep).
  --   Engines committed: relativeDualityK_mk, exists_boundary_of_homology_eq, cover_partition_cap_boundary_mod,
  --   mapChain_chainIncl_boundaryExtract. Build chain cover-partition (hzc0+hpart+relativeDualityK_mk) FIRST.
  -- Step 1 [DONE — whnf-dodged via cover_partition_of_legW, the legW-headed free-carrier bridge]:
  --   chain cover-partition `pullbackDualityₗ(Kᶜ)(U∪V)(fundCycleW) g_rep = chainIncl_A zA + chainIncl_B zB + ∂η`.
  --   🔑 the application MUST infer `w` from hpart (NOT pass the explicit ⟨chainIncl..,hcyc⟩) — the explicit
  --   anonymous-constructor forces an elaboration order that whnf-walls; `_` (inferred) dodges it.
  obtain ⟨η, hcp⟩ := cover_partition_of_legW _ _ _ _ g_rep zc0 _ hzc0 hpart
  -- Step 2: push hcp through chainIncl(U∪V) → absolute X: `cap g_rep fund = chainIncl(U∪V)(chainIncl_A zA)
  --   + chainIncl(U∪V)(chainIncl_B zB) + ∂(chainIncl(U∪V) η)` (chainIncl_pullbackDualityₗ + map_add + chainIncl_∂).
  have hcp_abs := congrArg (⇑(chainIncl (U ∪ V) (p + 1 + 1))) hcp
  simp only [map_add, SingularLocalDualityK.chainIncl_pullbackDualityₗ,
    SingularRelativeHomologyMod2.chainIncl_chainBoundary] at hcp_abs
  -- Step 3: cover_partition_cap_boundary_mod on hcp_abs (A=B=U∪V; zA':=chainIncl(val⁻¹U)zA, zB':=chainIncl(val⁻¹V)zB,
  --   η':=chainIncl(U∪V)η) → `chainIncl(U∪V)(∂(chainIncl_A zA)) + chainIncl(U∪V)(∂(chainIncl_B zB)) = cap g_rep ∂fund`.
  have hbd := cover_partition_cap_boundary_mod (U ∪ V) (U ∪ V) _
    (SingularRelativeDuality.relCocycle_coboundary_zero _ g_rep) _ _ _ _ hcp_abs
  -- ▶ CROSS-REALIZATION CORE (cap-product MV-naturality, Hatcher 3.36 — the genuine remaining theorem; both
  --   NC + CrossReal historically stall HERE; surrounding machinery steps 1-3 = hcp/hcp_abs/hbd, now in scope).
  --   Goal = `chain_L + pd ∈ boundaries(sub(U∩V))`. ASSEMBLY MAP (all engines committed):
  --   (1) `refine ⟨W, ?_⟩`, bounding chain W = realize(cap (pullbackCochain g_rep) fund_∩) [a (p+2)-chain];
  --       residual `∂W = chain_L + pd`. (2) ∂W cap-Leibniz-expands (g_rep COCYCLE ⟹ δ-term = 0) to the
  --       two-facts LHS. (3) `two_facts_via_ambient` (NC:240) → AMBIENT hamb (chainIncl-injective, whnf-dodged):
  --       `cap g_rep (∂(chainIncl fund_∩)) = chainIncl chain_L + cap σR (chainIncl FR)` in X.
  --   hamb = THREE sub-bricks: (i) the χ / bounding-chain cochain [GATING] — W-cochain = `cochainSplit g_rep`
  --       (the U-leg over infCompactᶜ; g_rep itself ∉ relCochains(infCompactᶜ)). χ = `σR − δ(cochainSplit g_rep)`
  --       (coboundary) absorbed at CHAIN altitude via cover-fine Sdʲ (coach-locked A, 2026-06-23; B/C ruled out;
  --       see notebook DECISIONS). (ii) V-part chain_L ↔ ∂zB-realize (seamHomeo MVLES:111 = identity-on-points +
  --       subSeamHomeo + boundaryExtract). (iii) hbd (f1fcc707) links cover-partition ∂ to cap g_rep ∂fund_{U∪V}.
  --   NEXT BRICK = (i) cover-subordinate split `cap (δ(cochainSplit g_rep)) (Sdʲ fund_∩) = ∂(primitive_U) + slack`
  --       via `exists_cover_fine_subdivision` (RHSScaffold:102, template = rhs_pairing_reduce proof) + `cap_leibniz`
  --       + cochainSplit_coboundary_mem_U/V. The chain-level analog of rhs_pairing_reduce's kronecker internals.
  sorry

end SKEFTHawking.SingularConnSquareCloseNC
