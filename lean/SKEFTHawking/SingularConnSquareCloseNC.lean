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
  -- now at KEY (boundary-membership in sub(U∩V)); apply the cap-Leibniz scaffold + the two facts.
  -- ▶ Obtain the connecting INPUT cochain rep ω'_rep (the (N+1)-cochain whose `cochainSplit` gives the
  --   absolute-coboundary rep of σR_rep), via hσR's input class (per CrossReal:97-102).
  obtain ⟨ω'_rep, hω'⟩ := Submodule.Quotient.mk_surjective _
    ((SingularRelativeCohomologyRestrict.relCohomRestrict (Set.inter_subset_inter subset_rfl subset_rfl)
        (N + 1))
      ((SingularCompactlySupportedTop.relCohomSetCongr
          (by rw [SingularCSCMayerVietorisConnecting.legSplit_cover U V hU hV K, Set.compl_union]) (N + 1))
        (Submodule.Quotient.mk g_rep)))
  -- bounding chain `W = cap(pullbackCochain(cochainSplit (legSplitUᶜ) ω'_rep))(realize F)` (deg p+2; per
  --   CrossReal:105-115); ∂W via cap_leibniz ⟹ two facts (ii) seam-term + (i) χ-term.
  refine ⟨cap (SingularCapChainIncl.pullbackCochain (U ∩ V) (N + 1)
        (SingularCohomologySnake.cochainSplit
          ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ) (N + 1) ω'_rep.1.1))
      ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 1 + (p + 1 + 1))).symm
        ⟨SingularOpenDualityCycle.fundCycleW (hU.inter hV)
            (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 1 + (p + 1 + 1) by omega) z₀)
            (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
            (SingularCSCMayerVietorisConnecting.infCompact U V
              (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
              (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)),
          SingularOpenDualityCycle.fundCycleW_mem_W (hU.inter hV) _ _ _⟩), ?_⟩
  -- ∂W via cap_leibniz ⟹ `cap(δφ)(h▸F) + cap(φ)(∂F) = chain_L + chain_R`, φ = pullbackCochain(cochainSplit ω'_rep).
  -- `erw` (NOT `rw`): the factB_transport path left the goal's space as `sub (U ∩ Membership.mem V)`, defeq but
  -- not syntactically `sub (U ∩ V)`, which blocks `rw` at reducible transparency (MCP-confirmed erw fires clean).
  erw [SingularHomologyMod2.cap_leibniz _ _ (show N + 1 + (p + 1) + 1 = N + 1 + 1 + (p + 1) by omega)]
  -- ▶ TWO FACTS (cap-naturality core): (i) χ-term `cap(δφ)(F) ~ pullbackDualityₗ σR` (cover-level), (ii) seam-term
  --   `cap(φ)(∂F) ~ seam²(boundaryExtract zB)` (cap_boundaryExtract_naturality + hpart/hzc0). Grind (ii) first.
  -- χ-side prep: move the coboundary inside ⟹ Term1 = `cap(pullbackCochain(δ(cochainSplit ω'_rep)))(F)`.
  erw [SingularConnSquareCloseFinal.coboundary_pullbackCochain]
  -- align chain_R `pullbackDualityₗ σR` to the explicit cap form `cap(pullbackCochain σR_rep)(realize F)`
  --   (CrossReal:89) — now Term1 (χ) and chain_R share `cap(pullbackCochain ·)(realize F)`.
  rw [SingularCapSubKDuality.pullbackDualityₗ_eq_subcap]
  -- ▶ ASSEMBLY: chainIncl-inject the whole two-facts goal to ambient X (where the seam-localization engine
  --   + cap_chainIncl live), then distribute over the two sums.
  -- reduce the sub(U∩V) two-facts to the ambient two-facts via the whnf-dodging abstract reduction
  -- (underscores = the concrete fundCycleW carriers, inferred structurally — no 200k-whnf wall).
  refine two_facts_via_ambient _ _ _ _ _ _ _ ?_
  -- ▶ AMBIENT TWO-FACTS (the V-link + χ cross-realization core):
  --   `cap δφ (chainIncl F) + cap φ (∂(chainIncl F)) = chainIncl(seam²(boundaryExtract zB)) + cap σR (chainIncl F)`.
  -- seam-term cover-support: `∂(chainIncl F) ∈ subspaceChains(legSplitUᶜ ∪ legSplitVᶜ)` (brick 8 + brick 9 + fundCycleW_boundary).
  have hcov : chainBoundary X (N + 1 + (p + 1))
        (chainIncl (U ∩ V) (N + 1 + (p + 1) + 1)
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 1 + (p + 1 + 1))).symm
            ⟨SingularOpenDualityCycle.fundCycleW (hU.inter hV)
                (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 1 + (p + 1 + 1) by omega) z₀)
                (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
                (SingularCSCMayerVietorisConnecting.infCompact U V
                  (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                  (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)),
              SingularOpenDualityCycle.fundCycleW_mem_W (hU.inter hV) _ _ _⟩))
      ∈ subspaceChains
          ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ ∪
            (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1)ᶜ) (N + 1 + (p + 1)) := by
    refine chainBoundary_chainIncl_subspaceChainsEquiv_symm_mem _ ?_
    rw [← infCompact_compl_legSplit hU hV K]
    exact SingularOpenDualityCycle.fundCycleW_boundary (hU.inter hV)
      (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 1 + (p + 1 + 1) by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
      (SingularCSCMayerVietorisConnecting.infCompact U V
        (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
        (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K))
  -- V-link: extract hpart's chain-level cover-partition `[zc0] = [chainIncl_A zA + chainIncl_B zB]` to
  -- `zc0 − (chainIncl_A zA + chainIncl_B zB) ∈ boundaries` (the link relating fund's cap to the V-part zB).
  have hpart_chain := (Submodule.Quotient.eq _).mp hpart
  -- χ per-leg structure (cover-level, the cap-altitude χ route): δφ = `coboundary (cochainSplit legSplitUᶜ ω')`
  -- is a relative `legSplitUᶜ`-cochain (unconditional) AND a relative `legSplitVᶜ`-cochain (ω'_rep a cocycle).
  -- The cocycle fact `δω'_rep = 0` is the ker witness projected to the underlying cochain.
  have hcoc : coboundary X (N + 1) ω'_rep.1.1 = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp ω'_rep.2)
  have hdU := SingularCohomologySnake.cochainSplit_coboundary_mem_U
    ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ) (N + 1) ω'_rep.1.1
  have hdV := SingularCohomologySnake.cochainSplit_coboundary_mem_V
    ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ)
    ((↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
    (N + 1) ω'_rep.1.1 ω'_rep.1.2 hcoc
  -- SEAM-TERM (Term2) localization via brick 5: `cap φ (∂fund) = chainIncl_legSplitVᶜ(cap (pb φ) w')`
  --  + ∂(cap φ Dⱼ) + cap(δφ)(Dⱼ).  φ = cochainSplit ω' ∈ relCochains(legSplitUᶜ) (cochainSplit_mem),
  --  w = ∂(chainIncl F) is a cycle (∂∂=0) and (legSplitUᶜ∪legSplitVᶜ)-supported (hcov). The legSplitVᶜ
  --  cover-part heads to the V-link; ∂(cap φ Dⱼ) + cap(δφ)Dⱼ are the subdivision δφ-slack folded with χ.
  obtain ⟨jseam, wseam, hseam⟩ := seam_cap_localize
    ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ)
    ((↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
    (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    (SingularCohomologySnake.cochainSplit
      ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ) (N + 1) ω'_rep.1.1)
    (SingularCohomologySnake.cochainSplit_mem_relCochains _ (N + 1) ω'_rep.1.1)
    (chainBoundary_chainBoundary_apply X (N + 1 + p) _) hcov
  -- Expand the seam-term (Term2) into its three ambient summands (W is already closed over by
  -- two_facts_via_ambient — the corrections live in the ambient residual, not the sub-witness).
  erw [hseam]
  -- Convert the B-cover-part `chainIncl_legSplitVᶜ(cap (pb φ) wseam)` to the ambient cap form
  -- `cap φ (chainIncl_legSplitVᶜ wseam)` — the form the V-link class-compatibility consumes (relate
  -- this V-realization to `chainIncl(seam²(boundaryExtract zB))` via hpart through the connecting map).
  rw [← SingularCapChainIncl.cap_chainIncl]
  sorry

end SKEFTHawking.SingularConnSquareCloseNC
