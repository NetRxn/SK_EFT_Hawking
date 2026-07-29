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
import SKEFTHawking.SingularConnSquareLHSPairing
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

/-- **Cap subdivision-invariance, NON-CYCLE form** (generalizes `cap_singularSd_iterate` by dropping the
`∂z = 0` hypothesis — 2026-07-01, the `fund_∩`-vs-`heng` bridge). For an ARBITRARY chain `z` (not
necessarily a cycle), `cap φ z` equals `cap φ (Sdʲz)` up to the SAME two correction terms as the cycle case
(the boundary `∂(cap φ Dⱼz)` and the non-cocycle `cap (δφ)(Dⱼz)`) PLUS a NEW fourth term `cap φ (Dⱼ(∂z))`
absorbing the non-cycle defect (zero when `∂z = 0`, recovering `cap_singularSd_iterate` exactly). From the
GENERAL chain homotopy `iterHomotopy_chainHomotopy` (`∂Dⱼz + Dⱼ(∂z) = z + Sdʲz`, no cycle hypothesis needed,
unlike `add_singularSd_iterate_eq_boundary` which specializes it via `∂z=0`) + `cap_leibniz`. `fund_∩` is
never a cycle (only rel-cycle mod `infCompactᶜ`), so THIS is the form the `hL` bridge to `heng`'s χ-engine
needs — `cap_singularSd_iterate` does not apply to it directly. -/
theorem cap_singularSd_iterate_of_chain {M : TopCat} {k m : ℕ} (φ : SingularCochain M k)
    (z : SingularChain M (k + (m + 1))) (j : ℕ) :
    cap φ z = cap φ ((⇑(SingularSubdivision.singularSd M (k + (m + 1))))^[j] z)
        + chainBoundary M (m + 1) (cap φ (SingularSubdivision.iterHomotopy M (k + (m + 1)) j z))
        + cap (coboundary M k φ) ((show k + (m + 1) + 1 = k + 1 + (m + 1) from by omega) ▸
            SingularSubdivision.iterHomotopy M (k + (m + 1)) j z)
        + cap φ (SingularSubdivision.iterHomotopy M (k + m) j (chainBoundary M (k + m) z)) := by
  have hb : chainBoundary M (k + (m + 1)) (SingularSubdivision.iterHomotopy M (k + (m + 1)) j z)
      = z + (⇑(SingularSubdivision.singularSd M (k + (m + 1))))^[j] z
        + SingularSubdivision.iterHomotopy M (k + m) j (chainBoundary M (k + m) z) := by
    have h := SingularSubdivision.iterHomotopy_chainHomotopy M j (k + m) z
    have h2 := congrArg
      (· + SingularSubdivision.iterHomotopy M (k + m) j (chainBoundary M (k + m) z)) h
    simp only [add_assoc, ZModModule.add_self, add_zero] at h2
    show chainBoundary M (k + m + 1) (SingularSubdivision.iterHomotopy M (k + m + 1) j z)
        = z + (⇑(SingularSubdivision.singularSd M (k + m + 1)))^[j] z
          + SingularSubdivision.iterHomotopy M (k + m) j (chainBoundary M (k + m) z)
    rw [h2]
    abel
  have hcl := cap_leibniz φ (SingularSubdivision.iterHomotopy M (k + (m + 1)) j z)
    (show k + (m + 1) + 1 = k + 1 + (m + 1) from by omega)
  rw [hcl, hb, map_add, map_add]
  abel_nf
  simp only [two_smul, ZModModule.add_self, zero_add, add_zero]

/-- **`∂(cap φ z)` bare-vs-subdivided bridge, packaged as a SINGLE `T`-supported correction** (the
`fund_∩`-vs-`heng` bridge, closed form — 2026-07-01). For `z` SUPPORTED in `T` (`hzT`), both non-cocycle
correction terms of `cap_singularSd_iterate_of_chain` (the `δφ`-term on `Dⱼz` and the non-cycle term on
`Dⱼ(∂z)`) are themselves `T`-supported (`iterHomotopy` preserves `subspaceChains`, applied once to `z` and
once to `∂z ∈ subspaceChains T` via `chainBoundary_mem_subspaceChains`), so `cap_chainIncl` packages BOTH
into one ambient `chainIncl T (m+1) E`. A further `∂` then kills the OTHER (already-a-boundary) correction
term outright (`∂∂ = 0`), leaving exactly the two-term shape `cap_realize_on_sub_mod`-style closers need. -/
theorem cap_chainBoundary_singularSd_iterate_bridge {M : TopCat} {k m : ℕ} {T : Set ↑M}
    (φ : SingularCochain M k) (z : SingularChain M (k + (m + 1))) (j : ℕ)
    (hzT : z ∈ subspaceChains T (k + (m + 1))) :
    ∃ E : SingularChain (sub T) (m + 1),
      chainBoundary M m (cap φ z)
        = chainBoundary M m (cap φ ((⇑(SingularSubdivision.singularSd M (k + (m + 1))))^[j] z))
          + chainBoundary M m (chainIncl T (m + 1) E) := by
  obtain ⟨F1, hF1⟩ := SingularExcision.iterHomotopy_mem_subspaceChains hzT j
  obtain ⟨F2, hF2⟩ := SingularExcision.iterHomotopy_mem_subspaceChains
    (SingularRelativeHomologyMod2.chainBoundary_mem_subspaceChains T (k + m) z hzT) j
  have cast_mem : ∀ {p q : ℕ} (h : p = q) (x : SingularChain M p),
      x ∈ subspaceChains T p → (h ▸ x : SingularChain M q) ∈ subspaceChains T q := by
    intro p q h x hx
    cases h
    exact hx
  have hcast : k + (m + 1) + 1 = k + 1 + (m + 1) := by omega
  have hF1cast : (hcast ▸ SingularSubdivision.iterHomotopy M (k + (m + 1)) j z)
      ∈ subspaceChains T (k + 1 + (m + 1)) :=
    cast_mem hcast _ ⟨F1, hF1⟩
  obtain ⟨F1', hF1'⟩ := hF1cast
  refine ⟨cap (SingularCapChainIncl.pullbackCochain T (k + 1) (coboundary M k φ)) F1'
      + (cap (SingularCapChainIncl.pullbackCochain T k φ) F2 : SingularChain (sub T) (m + 1)), ?_⟩
  have hmain := cap_singularSd_iterate_of_chain φ z j
  rw [← hF1'] at hmain
  rw [SingularCapChainIncl.cap_chainIncl (S := T) (k := k + 1) (m := m + 1) (coboundary M k φ) F1']
    at hmain
  have hcc2 : cap φ (chainIncl T (k + m + 1) F2)
      = chainIncl T (m + 1) (cap (SingularCapChainIncl.pullbackCochain T k φ) F2) :=
    SingularCapChainIncl.cap_chainIncl (S := T) (k := k) (m := m + 1) φ F2
  rw [← hF2, hcc2] at hmain
  have step1 : chainBoundary M m (cap φ z)
      = chainBoundary M m (cap φ ((⇑(SingularSubdivision.singularSd M (k + (m + 1))))^[j] z))
        + chainBoundary M m
            (chainBoundary M (m + 1) (cap φ (SingularSubdivision.iterHomotopy M (k + (m + 1)) j z)))
        + chainBoundary M m (chainIncl T (m + 1)
            (cap (SingularCapChainIncl.pullbackCochain T (k + 1) (coboundary M k φ)) F1'))
        + chainBoundary M m (chainIncl T (m + 1)
            (cap (SingularCapChainIncl.pullbackCochain T k φ) F2)) := by
    rw [hmain]
    simp only [map_add]
  have step2 : chainBoundary M m
      (chainBoundary M (m + 1) (cap φ (SingularSubdivision.iterHomotopy M (k + (m + 1)) j z))) = 0 :=
    chainBoundary_chainBoundary_apply M m _
  have step3A : chainBoundary M m (chainIncl T (m + 1)
      (cap (SingularCapChainIncl.pullbackCochain T (k + 1) (coboundary M k φ)) F1'))
      = chainIncl T m (chainBoundary (sub T) m
          (cap (SingularCapChainIncl.pullbackCochain T (k + 1) (coboundary M k φ)) F1')) :=
    (SingularRelativeHomologyMod2.chainIncl_chainBoundary T m
      (cap (SingularCapChainIncl.pullbackCochain T (k + 1) (coboundary M k φ)) F1')).symm
  have step3B : chainBoundary M m (chainIncl T (m + 1)
      (cap (SingularCapChainIncl.pullbackCochain T k φ) F2))
      = chainIncl T m (chainBoundary (sub T) m
          (cap (SingularCapChainIncl.pullbackCochain T k φ) F2)) :=
    (SingularRelativeHomologyMod2.chainIncl_chainBoundary T m
      (cap (SingularCapChainIncl.pullbackCochain T k φ) F2)).symm
  rw [step1, step2, add_zero, step3A, step3B]
  have hincl_add := map_add (chainIncl T (m + 1))
    (cap (SingularCapChainIncl.pullbackCochain T (k + 1) (coboundary M k φ)) F1')
    (cap (SingularCapChainIncl.pullbackCochain T k φ) F2)
  rw [hincl_add]
  have hsplit := map_add (chainBoundary M m)
    (chainIncl T (m + 1)
      (cap (SingularCapChainIncl.pullbackCochain T (k + 1) (coboundary M k φ)) F1'))
    (chainIncl T (m + 1) (cap (SingularCapChainIncl.pullbackCochain T k φ) F2))
  rw [hsplit, step3A, step3B]
  abel

/-- **fundCycleW-headed wrapper of `cap_chainBoundary_singularSd_iterate_bridge`** (def-head-match
whnf-dodge, same technique as `cap_coboundary_cochainSplit_subdiv_fund` / `connecting_square_close_cocycle_fund`).
Stated with `fundCycleW hW z₀ hz₀ Kc` directly in the `z` slot so an application matches the head
SYNTACTICALLY and infers `hW/z₀/hz₀/Kc` by unification, never whnf-reducing the concrete fundamental
into the generic bridge (the documented 200k wall — hit directly applying the generic bridge to the
concrete `fund_∩` term in `case hmk`). -/
theorem cap_chainBoundary_singularSd_iterate_bridge_fund {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (Kc : SingularCompactsInOpen.CompactsIn W) (φ : SingularCochain X k) (j : ℕ) :
    ∃ E : SingularChain (sub W) (m + 1),
      chainBoundary X m (cap φ (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ Kc))
        = chainBoundary X m (cap φ
            ((⇑(SingularSubdivision.singularSd X (k + m + 1)))^[j]
              (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ Kc)))
          + chainBoundary X m (chainIncl W (m + 1) E) :=
  cap_chainBoundary_singularSd_iterate_bridge (T := W) (m := m) φ
    (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ Kc) j
    (SingularOpenDualityCycle.fundCycleW_mem_W hW z₀ hz₀ Kc)

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

/-- **Explicit cover-fine cap bounding chain** (the seam-leg `e₁` in solved form). Given a cover-fine
subdivision split of the un-subdivided boundary `∂(Sdʲc) = uA + wB` (`hsplit`, the exact shape
`exists_cover_fine_subdivision` produces) and the drop of the `A`-part cap (`hA : cap φ uA = 0`, e.g. `φ`
relative to `A`), the cap of `φ` against the *un-subdivided* boundary `∂c` is the pure cover-split `B`-part
`cap φ wB` PLUS the **explicit** subdivision bounding chain `e₁ := cap φ (Dⱼ (∂c))` PLUS the non-cocycle
χ-correction `cap (δφ)(Dⱼ (∂c))`. This is the `solve-for-∂c` rearrangement of `cap_singularSd_iterate_chainBoundary_arg`
with the split fed in — it exhibits the seam-leg slack absorber `e₁` explicitly (as opposed to `seam_cap_localize`,
which re-derives the split internally). Over ℤ/2. -/
theorem cap_chainBoundary_of_cover_fine_split {M : TopCat} {k m : ℕ} (φ : SingularCochain M k)
    (c : SingularChain M (k + (m + 1) + 1)) (j : ℕ)
    (uA wB : SingularChain M (k + (m + 1)))
    (hsplit : chainBoundary M (k + (m + 1))
        ((⇑(SingularSubdivision.singularSd M (k + (m + 1) + 1)))^[j] c) = uA + wB)
    (hA : cap φ uA = 0) :
    cap φ (chainBoundary M (k + (m + 1)) c)
      = cap φ wB
        + chainBoundary M (m + 1)
            (cap φ (SingularSubdivision.iterHomotopy M (k + (m + 1)) j
                (chainBoundary M (k + (m + 1)) c)))
        + cap (coboundary M k φ)
            ((show k + (m + 1) + 1 = k + 1 + (m + 1) from by omega) ▸
              SingularSubdivision.iterHomotopy M (k + (m + 1)) j
                (chainBoundary M (k + (m + 1)) c)) := by
  have h := cap_singularSd_iterate_chainBoundary_arg φ c j
  rw [hsplit, show cap φ (uA + wB) = cap φ uA + cap φ wB from map_add (capₗ k (m + 1) φ) _ _,
    hA, zero_add] at h
  rw [h]
  abel_nf
  simp only [two_smul, ZModModule.add_self, zero_add, add_zero]

/-- **Explicit cover-fine rcap bounding chain** (the σR/pd-leg `e₂` in solved form, cocycle case). The `rcap`
mirror of `cap_chainBoundary_of_cover_fine_split` for a COCYCLE `ω` (`δω = 0`): given the cover-fine split
`∂(Sdʲc) = uA + wB` and the drop of the `A`-part right-cap (`hA : rcap ω uA = 0`), the right-cap of `ω`
against the un-subdivided boundary `∂c` is the pure cover-split `B`-part `rcap ω wB` PLUS the **explicit**
subdivision bounding chain `e₂ := rcap ω (Dⱼ (∂c))` — no χ-correction, since `ω` is a cocycle. Over ℤ/2. -/
theorem rcap_chainBoundary_of_cover_fine_split {M : TopCat} {k l : ℕ}
    (ω : SingularCochain M (l + 1)) (hω : coboundaryₗ M (l + 1) ω = 0)
    (c : SingularChain M (k + (l + 1) + 1)) (j : ℕ)
    (uA wB : SingularChain M (k + (l + 1)))
    (hsplit : chainBoundary M (k + (l + 1))
        ((⇑(SingularSubdivision.singularSd M (k + (l + 1) + 1)))^[j] c) = uA + wB)
    (hA : SingularCapChainIncl.rcap (k := k) ω uA = 0) :
    SingularCapChainIncl.rcap (k := k) ω (chainBoundary M (k + (l + 1)) c)
      = SingularCapChainIncl.rcap (k := k) ω wB
        + chainBoundary M k
            (SingularCapChainIncl.rcap (k := k + 1) ω
              ((show k + (l + 1) + 1 = k + 1 + (l + 1) from by omega) ▸
                SingularSubdivision.iterHomotopy M (k + (l + 1)) j
                  (chainBoundary M (k + (l + 1)) c))) := by
  have h := rcap_singularSd_iterate_chainBoundary_arg ω hω c j
  rw [hsplit, map_add, hA, zero_add] at h
  rw [h]
  abel_nf
  simp only [two_smul, ZModModule.add_self, zero_add, add_zero]

/-
**Cover-fine V-part is an explicit boundary** (the seam-leg `hLF` core, cocycle case). For a COCYCLE
`g` (`δg = 0`), given the cover-fine split `∂(Sdʲc) = uA + wB` (`hsplit`) with the `A`-part cap dropping
(`hA : cap g uA = 0`), the cover-split `B`-part `cap g wB` is the boundary of the **explicit** chain
`cap g c + cap g (Dⱼ (∂c))`. Chains `cap_chainBoundary_of_cover_fine_split` (the χ-term dies since `δg = 0`) with
the cocycle Leibniz `∂(cap g c) = cap g (∂c)`; over ℤ/2 the two boundary terms combine (`map_add`). This is the
form the `joint_realize_match` seam obligation consumes: `L = cap g c + ∂e₁` with `e₁ := cap g (Dⱼ (∂c))`,
after identifying `cap g wB` with the (transported) seam via the cover partition. Over ℤ/2.
-/
theorem cap_cover_fine_Vpart_eq_boundary {M : TopCat} {k m : ℕ} (g : SingularCochain M k)
    (hg : coboundary M k g = 0)
    (c : SingularChain M (k + (m + 1) + 1)) (j : ℕ)
    (uA wB : SingularChain M (k + (m + 1)))
    (hsplit : chainBoundary M (k + (m + 1))
        ((⇑(SingularSubdivision.singularSd M (k + (m + 1) + 1)))^[j] c) = uA + wB)
    (hA : cap g uA = 0) :
    cap g wB
      = chainBoundary M (m + 1)
          (cap g c + cap g (SingularSubdivision.iterHomotopy M (k + (m + 1)) j
              (chainBoundary M (k + (m + 1)) c))) := by
  have h := cap_chainBoundary_of_cover_fine_split g c j uA wB hsplit hA
  have hchi : cap (coboundary M k g)
      ((show k + (m + 1) + 1 = k + 1 + (m + 1) from by omega) ▸
        SingularSubdivision.iterHomotopy M (k + (m + 1)) j
          (chainBoundary M (k + (m + 1)) c)) = 0 := by
    rw [hg, ← capₗ_apply, map_zero, LinearMap.zero_apply]
  have hcocyc : chainBoundary M (m + 1) (cap g c)
      = cap g (chainBoundary M (k + (m + 1)) c) := by
    rw [cap_leibniz g c (show k + (m + 1) + 1 = k + 1 + (m + 1) from by omega), hg,
      ← capₗ_apply, map_zero, LinearMap.zero_apply, zero_add]
  rw [hchi, add_zero, ← hcocyc] at h
  rw [(chainBoundary M (m + 1)).map_add, h]
  abel_nf
  simp only [two_smul, ZModModule.add_self, zero_add, add_zero]

/-
**Cover-fine V-part is an explicit boundary, rcap/pd-leg** (the σR-leg `hRF` core, cocycle case). The
`rcap` mirror of `cap_cover_fine_Vpart_eq_boundary`: for a COCYCLE `ω` (`δω = 0`), given the cover-fine split
`∂(Sdʲc) = uA + wB` with the `A`-part right-cap dropping (`hA : rcap ω uA = 0`), the cover-split `B`-part
`rcap ω wB` is the boundary of the **explicit** chain `rcap ω c + rcap ω (Dⱼ (∂c))` (both right-capped one degree
up, matching the `rcap`-chain-map cast). Chains `rcap_chainBoundary_of_cover_fine_split` with the cocycle
right-cap chain map `SingularRightCapBoundary.rcap_cocycle_chainMap` (`∂(rcapₖ₊₁ ω (cast ▸ c)) = rcapₖ ω (∂c)`);
over ℤ/2 the two boundary terms combine. This exhibits the pd-leg slack absorber `e₂ := rcap ω (Dⱼ (∂c))`
explicitly. Over ℤ/2.
-/
theorem rcap_cover_fine_Vpart_eq_boundary {M : TopCat} {k l : ℕ}
    (ω : SingularCochain M (l + 1)) (hω : coboundaryₗ M (l + 1) ω = 0)
    (c : SingularChain M (k + (l + 1) + 1)) (j : ℕ)
    (uA wB : SingularChain M (k + (l + 1)))
    (hsplit : chainBoundary M (k + (l + 1))
        ((⇑(SingularSubdivision.singularSd M (k + (l + 1) + 1)))^[j] c) = uA + wB)
    (hA : SingularCapChainIncl.rcap (k := k) ω uA = 0) :
    SingularCapChainIncl.rcap (k := k) ω wB
      = chainBoundary M k
          (SingularCapChainIncl.rcap (k := k + 1) ω
              ((show k + (l + 1) + 1 = k + 1 + (l + 1) from by omega) ▸ c)
            + SingularCapChainIncl.rcap (k := k + 1) ω
              ((show k + (l + 1) + 1 = k + 1 + (l + 1) from by omega) ▸
                SingularSubdivision.iterHomotopy M (k + (l + 1)) j
                  (chainBoundary M (k + (l + 1)) c))) := by
  have := rcap_singularSd_iterate_chainBoundary_arg ω hω c j;
  convert this using 1;
  · rw [ hsplit, map_add, hA, zero_add ];
  · rw [ ← SKEFTHawking.SingularRightCapBoundary.rcap_cocycle_chainMap ω hω c, map_add ]

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

/-- **Boundaries membership from an ambient cap-boundary realization** (the plumbing that isolates the
genuine local-PD content). If a `sub K`-chain `x` has `chainIncl K x = ∂(cap a c)` with the cap
`K`-supported, then `x` is a `sub K`-boundary: `x` equals the realized `(subspaceChainsEquiv).symm` of
`∂(cap a c)` (by `chainIncl`-injectivity + `chainIncl_subspaceChainsEquiv_symm`), which is a boundary by
`realize_chainBoundary_cap_mem_boundaries`. Reduces `seam + pd ∈ boundaries` to the ambient identity
`chainIncl (seam+pd) = ∂(cap a c)`. -/
theorem mem_boundaries_of_chainIncl_cap {K : Set ↑X} {k n : ℕ}
    (x : SingularChain (sub K) (n + 1)) (a : SingularCochain X k)
    (c : SingularChain X (k + (n + 1) + 1))
    (hsupp : cap a c ∈ subspaceChains K (n + 2))
    (hsum : chainBoundary X (n + 1) (cap a c) ∈ subspaceChains K (n + 1))
    (hx : chainIncl K (n + 1) x = chainBoundary X (n + 1) (cap a c)) :
    x ∈ boundaries (sub K) (n + 1) := by
  have he : x = (SingularSubspaceChainsEquiv.subspaceChainsEquiv K (n + 1)).symm
      ⟨chainBoundary X (n + 1) (cap a c), hsum⟩ := by
    apply chainIncl_injective K (n + 1)
    rw [SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm, hx]
  rw [he]
  exact realize_chainBoundary_cap_mem_boundaries K a c hsupp hsum

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

/-- **The pd-side fundamental's boundary is leg-cover-supported** (the STEP-A-mirror fact, extracted
to its own command — it is consumed twice in the apex proof, whose cumulative heartbeat budget it
would otherwise pay for twice). `∂fund₂ ∈ C(legSplitUᶜ ∪ legSplitVᶜ)`: `fundCycleW_boundary` lands
it in `C(infCompactᶜ)`, and `infCompact_coe` + `compl_inter` rewrite the set to the leg cover. -/
theorem fund2_boundary_cover (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) {N p : ℕ}
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0) :
    chainBoundary X (N + 2 + p)
      (SingularOpenDualityCycle.fundCycleW (hU.inter hV)
        (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
        (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
          z₀ hz₀)
        (SingularCSCMayerVietorisConnecting.infCompact U V
          (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
          (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
      ∈ subspaceChains
        ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ
          ∪ (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ)
        (N + 2 + p) := by
  have h := SingularOpenDualityCycle.fundCycleW_boundary (hU.inter hV)
    (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
    (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
    (SingularCSCMayerVietorisConnecting.infCompact U V
      (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
      (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K))
  rwa [SingularCSCMayerVietorisConnecting.infCompact_coe, Set.compl_inter] at h

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

/-- **Homology-level connecting-square closer (Approach D1).** Over ℤ/2, two cycles whose homology
classes agree sum to a boundary (`[a] = [b] ⟺ [a + b] = 0`, and `a + a = 0`). This replaces the
on-the-nose chain closer `connecting_square_close` with a *class-level* one: the remaining obligation is
the homology-class square `[seam] = [pd]`, where the subdivision / coboundary slack terms are boundaries
and hence vanish. (Approach-D scaffold reached by Aristotle run 946db1c6, verify-then-graft 2026-06-29.) -/
theorem mem_boundaries_of_mk_eq (K : Set ↑X) {n : ℕ}
    (chainL pd : SingularChain (sub K) (n + 1))
    (hLcyc : chainBoundary (sub K) n chainL = 0)
    (hpdcyc : chainBoundary (sub K) n pd = 0)
    (hmk : Homology.mk (sub K) (n + 1) ⟨chainL, hLcyc⟩
         = Homology.mk (sub K) (n + 1) ⟨pd, hpdcyc⟩) :
    chainL + pd ∈ boundaries (sub K) (n + 1) := by
  have hsumcyc : chainBoundary (sub K) n (chainL + pd) = 0 := by
    rw [map_add, hLcyc, hpdcyc, add_zero]
  have hz : Homology.mk (sub K) (n + 1) ⟨chainL + pd, hsumcyc⟩ = 0 := by
    erw [show (⟨chainL + pd, hsumcyc⟩ : cycles (sub K) (n + 1))
          = ⟨chainL, hLcyc⟩ + ⟨pd, hpdcyc⟩ from rfl,
        SingularCapHomology.Homology.mk_add, hmk,
        ← SingularCapHomology.Homology.mk_add,
        -- v4.32: `ZModModule.add_self`'s `?x + ?x` will not match on the subtype (the `+` comes
        -- via `AddSubgroupClass`, a different instance path). Give `rw` a concrete pattern.
        show (⟨pd, hpdcyc⟩ : cycles (sub K) (n + 1)) + ⟨pd, hpdcyc⟩ = 0 from
          Subtype.ext (by simpa using ZModModule.add_self pd)]
    rfl
  rw [SingularCapHomology.Homology.mk_eq_zero] at hz
  simpa using Submodule.mem_comap.mp hz

/-- **Converse of `mem_boundaries_of_mk_eq`**: over `ℤ/2`, two cycles whose SUM is a boundary represent
the same homology class. (`mk` is `Submodule.Quotient.mk`; `chainL + pd ∈ boundaries` gives
`mk⟨chainL⟩ + mk⟨pd⟩ = mk⟨chainL+pd⟩ = 0`, and over `ℤ/2` `a + b = 0 → a = b`.) -/
theorem mk_eq_of_mem_boundaries (K : Set ↑X) {n : ℕ}
    (chainL pd : SingularChain (sub K) (n + 1))
    (hLcyc : chainBoundary (sub K) n chainL = 0)
    (hpdcyc : chainBoundary (sub K) n pd = 0)
    (hmem : chainL + pd ∈ boundaries (sub K) (n + 1)) :
    Homology.mk (sub K) (n + 1) ⟨chainL, hLcyc⟩
      = Homology.mk (sub K) (n + 1) ⟨pd, hpdcyc⟩ := by
  have hsumcyc : chainBoundary (sub K) n (chainL + pd) = 0 := by
    rw [map_add, hLcyc, hpdcyc, add_zero]
  have hz : Homology.mk (sub K) (n + 1) ⟨chainL + pd, hsumcyc⟩ = 0 := by
    rw [SingularCapHomology.Homology.mk_eq_zero]
    exact Submodule.mem_comap.mpr (by simpa using hmem)
  have hsplit : Homology.mk (sub K) (n + 1) ⟨chainL, hLcyc⟩
      + Homology.mk (sub K) (n + 1) ⟨pd, hpdcyc⟩ = 0 := by
    rw [← SingularCapHomology.Homology.mk_add,
      show (⟨chainL, hLcyc⟩ + ⟨pd, hpdcyc⟩ : cycles (sub K) (n + 1)) = ⟨chainL + pd, hsumcyc⟩ from rfl]
    exact hz
  calc Homology.mk (sub K) (n + 1) ⟨chainL, hLcyc⟩
      = Homology.mk (sub K) (n + 1) ⟨chainL, hLcyc⟩
          + (Homology.mk (sub K) (n + 1) ⟨chainL, hLcyc⟩
            + Homology.mk (sub K) (n + 1) ⟨pd, hpdcyc⟩) := by rw [hsplit, add_zero]
    _ = Homology.mk (sub K) (n + 1) ⟨pd, hpdcyc⟩ := by
        rw [← add_assoc, ZModModule.add_self, zero_add]

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

/-- **Chain-altitude cross-realization transport, cocycle-free** (the RELATIVE-cocycle unblock, 2026-07-01
grind). `cap_chainBoundary_relBoundaries_transport`'s `hg : coboundary X k g = 0` hypothesis is UNUSED in its
own proof (the argument is pure `cap`-linearity over the relative-boundary witness `D`, never needs `g`
closed) — so the same conclusion holds for ANY cochain `g`, including a merely-RELATIVE cocycle like `g_rep`
(closed only mod `Kᶜ`, not globally). This is the bridge `cap_chainBoundary_relBoundaries_transport` couldn't
supply for the coarse/fine partition mismatch: `g_rep` is never a genuine global cocycle, only a
`relCoboundaryₗ Kᶜ`-cocycle. Same proof verbatim, `g` unconstrained. -/
theorem cap_chainBoundary_relBoundaries_transport_free {S : Set ↑X} {k n : ℕ} (g : SingularCochain X k)
    (a b : SingularChain X (k + n + 1))
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

/-- **Raw relative-boundary witness extraction, UN-differentiated** (the coarse/fine bridge companion of
`cap_chainBoundary_relBoundaries_transport_free`, 2026-07-01 grind). That lemma differentiates `a`/`b`
before capping — forcing `cap g fund_K`'s cycle-ness to trivialize the result. This version keeps `a + b`
un-differentiated: `mk_S(a+b) ∈ relBoundaries S` unpacks to an EXPLICIT chain identity `a + b = ∂D + ρ`
(`ρ` supported in `S`) — letting `fund_K` be substituted for `fund_∩` (plus `∂D` plus an `S`-supported `ρ`)
INSIDE an un-differentiated `cap g_rep (·)`, so the substitution's own boundary (`∂(cap g_rep ∂D)`,
`∂(cap g_rep ρ)`) carries the genuine new content instead of vanishing by the cycle argument. Same
extraction machinery as the differentiated version (`Submodule.Quotient.mk_surjective` + `relBoundary_mk`),
minus the final `cap`+`chainBoundary` step. -/
theorem chain_eq_of_relBoundaries_mem {S : Set ↑X} {m : ℕ} (a b : SingularChain X m)
    (hrel : RelativeChain.mk S m (a + b) ∈ relBoundaries S m) :
    ∃ (D : SingularChain X (m + 1)) (ρ : SingularChain X m), ρ ∈ subspaceChains S m ∧
      a + b = chainBoundary X m D + ρ := by
  obtain ⟨y, hy⟩ := hrel
  obtain ⟨D, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  erw [relBoundary_mk] at hy
  refine ⟨D, chainBoundary X m D + (a + b), ?_, ?_⟩
  · have hz0 : RelativeChain.mk S m (chainBoundary X m D + (a + b)) = 0 := by
      have hsplit : RelativeChain.mk S m (chainBoundary X m D + (a + b))
          = RelativeChain.mk S m (chainBoundary X m D) + RelativeChain.mk S m (a + b) := rfl
      rw [hsplit, hy]
      exact ZModModule.add_self _
    exact (Submodule.Quotient.mk_eq_zero _).mp hz0
  · abel_nf
    simp only [two_smul, ZModModule.add_self, zero_add, add_zero]

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

/-- **Pairing-relaxed cup–cap joint match** (the slack-tolerant form of `joint_cap_rcap_match`). The
chain-level `hL : L = cap gM F + ∂e₁` realization is provably TOO STRONG for the connecting square (with
`F = ∂fund` it forces the seam — a genuinely non-nullhomologous cycle — to bound). What the ℤ/2 close
actually needs is the two legs to agree with the cap/rcap of the SHARED `F` **as pairings** — each side's
test cochain absorbs its own boundary/subdivision slack inside the fact's own proof, not here. The match
then closes by the cup-cap duality core alone. No cocycle hypotheses are needed at this level. -/
theorem joint_cap_rcap_match_pairing {M : TopCat} {N p : ℕ}
    (ω : SingularCochain M (p + 1)) (gM : SingularCochain M (N + 1))
    (F : SingularChain M (N + 1 + (p + 1)))
    (L : SingularChain M (p + 1)) (R : SingularChain M (N + 1))
    (hL : kronecker ω L = kronecker ω (cap gM F))
    (hR : kronecker gM R = kronecker gM (SingularCapChainIncl.rcap ω F)) :
    kronecker ω L = kronecker gM R := by
  rw [hL, hR]
  exact SingularConnSquareMatchLHS.kronecker_cap_eq_kronecker_rcap gM ω F

/-- **LHS cap-realization on the common space `M = sub T`** (joint-match brick (1), whnf-dodging GREEN).
A `sub T`-chain `L` whose `chainIncl T` equals the ambient cap `cap g_amb (chainIncl T F)` of a `sub T`-realized
fundamental `F` *is itself* the cap of the **pulled-back** cochain `pullbackCochain T g_amb` against `F`:
`L = cap (pullbackCochain T g_amb) F`. Via `chainIncl`-injectivity + `cap_chainIncl`
(`cap g (chainIncl c) = chainIncl (cap (pullbackCochain g) c)`). This is the form `joint_cap_rcap_match`'s
`hL` consumes (with `gM := pullbackCochain T g_amb`), reached *without* ever whnf-reducing the concrete
`fundCycleW` (the ambient identity `hLF` is supplied separately by the fund-compatibility step). -/
theorem cap_realize_on_sub {T : Set ↑X} {k m : ℕ} (g : SingularCochain X k)
    (L : SingularChain (sub T) m) (F : SingularChain (sub T) (k + m))
    (hLF : chainIncl T m L = cap g (chainIncl T (k + m) F)) :
    L = cap (SingularCapChainIncl.pullbackCochain T k g) F := by
  apply chainIncl_injective T m
  rw [hLF, SingularCapChainIncl.cap_chainIncl]

/-- **RHS rcap-realization on the common space `M = sub T`** (joint-match brick (2), whnf-dodging GREEN).
The right-cap mirror of `cap_realize_on_sub`: a `sub T`-chain `R` whose `chainIncl T` equals the ambient
right cap `rcap b (chainIncl T F)` *is itself* the right cap of the **pulled-back** cochain
`pullbackCochain T b` against `F`: `R = rcap (pullbackCochain T b) F`. Via `chainIncl`-injectivity +
`rcap_chainIncl` (CapSubKDuality:120). This is the form `joint_cap_rcap_match`'s `hR` consumes (with
`ω := pullbackCochain T b`), again without whnf-reducing the concrete fundamental. -/
theorem rcap_realize_on_sub {T : Set ↑X} {k l : ℕ} (b : SingularCochain X l)
    (R : SingularChain (sub T) k) (F : SingularChain (sub T) (k + l))
    (hRF : chainIncl T k R = SingularCapChainIncl.rcap b (chainIncl T (k + l) F)) :
    R = SingularCapChainIncl.rcap (SingularCapChainIncl.pullbackCochain T l b) F := by
  apply chainIncl_injective T k
  rw [hRF, SingularCapSubKDuality.rcap_chainIncl]

/-- **Cast-reconciliation of two equal-degree `castChain`s** (STEP 0, the mechanical blocker). The two
fundamental cycles in the connecting square are built from `castChain h₁ z₀` (LHS, target `N+1+(p+1)+1`)
and `castChain h₂ z₀` (RHS, target `N+2+p+1`); these degree expressions are propositionally — but not
definitionally — equal (`Nat.add` recurses on the 2nd argument). Transporting the first along the numerical
equality `hb : a = c` (with `a, c` the two targets) yields the second, by cast composition + `Nat`-equality
proof irrelevance (`subst hb` collapses the two proofs `h₁.trans hb` and `h₂` to the same `rfl`-shape).
Generic in `z₀`, `h₁`, `h₂`, `hb` ⟹ whnf-free; the reconciliation `fundCycleW_pair_relHomologous`
needs to present both fund's over one shared chain. -/
theorem castChain_cast_reconcile {a b c : ℕ} (h₁ : a = b) (h₂ : a = c) (hb : b = c)
    (z : SingularChain X a) :
    hb ▸ SingularOpenDualityMVConnSquare.castChain h₁ z
      = SingularOpenDualityMVConnSquare.castChain h₂ z := by
  subst hb; rfl

omit [T2Space ↑X] in
/-- **Support-preserving cover re-partition** (the STEP-A fix — the genuine resolution of the cross-realization
V-leg support, kernel-pure GREEN). The `Submodule.mem_sup` partition `c = chainIncl A cA + chainIncl B cB`
loses support: the legs need NOT individually inherit the parent's `S`-support (cancellation across legs).
But if the *parent* chain is `S`-supported (`hS`), a **per-simplex** re-partition assigns each cover-fine
support simplex (each in `A` or `B`, since it survives the ℤ/2 sum) to a leg, where it is ALSO in `S` — so the
re-partition's legs land in `A ∩ S` and `B ∩ S`. Proof: each support simplex `τ` of `c` is subordinate to
`{A∩S, B∩S}` (`range τ ⊆ A` or `⊆ B` via `range_of_mem_subspaceChains` on each leg + `Finsupp.support_add`;
and `⊆ S` via `hS`), so `c ∈ smallChains {A∩S, B∩S} = subspaceChains(A∩S) ⊔ subspaceChains(B∩S)`
(`smallChains_two_eq`), then `exists_chainIncl_partition_of_mem_mvUnionChains`. The V-leg `b` is now over
`sub (B ∩ S)` with `B ∩ S ⊆ S` — exactly the support needed to realize it on the common space. -/
theorem repartition_subspaceChains {A B S : Set ↑X} {n : ℕ}
    (cA : SingularChain (sub A) n) (cB : SingularChain (sub B) n)
    (hS : chainIncl A n cA + chainIncl B n cB ∈ subspaceChains S n) :
    ∃ (a : SingularChain (sub (A ∩ S)) n) (b : SingularChain (sub (B ∩ S)) n),
      chainIncl A n cA + chainIncl B n cB = chainIncl (A ∩ S) n a + chainIncl (B ∩ S) n b := by
  classical
  set c := chainIncl A n cA + chainIncl B n cB with hc
  have hsmall : c ∈ SingularExcision.smallChains ({A ∩ S, B ∩ S} : Set (Set ↑X)) n := by
    refine SingularExcision.mem_smallChains_of_support (fun τ hτ => ?_)
    have hτAB : τ ∈ (chainIncl A n cA).support ∪ (chainIncl B n cB).support :=
      Finsupp.support_add hτ
    have hτS : Set.range (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) τ) ⊆ S :=
      SingularExcision.range_of_mem_subspaceChains hS hτ
    rcases Finset.mem_union.1 hτAB with hA | hB
    · exact ⟨A ∩ S, Set.mem_insert _ _,
        Set.subset_inter (SingularExcision.range_of_mem_subspaceChains ⟨cA, rfl⟩ hA) hτS⟩
    · exact ⟨B ∩ S, Set.mem_insert_of_mem _ rfl,
        Set.subset_inter (SingularExcision.range_of_mem_subspaceChains ⟨cB, rfl⟩ hB) hτS⟩
  rw [SingularExcision.smallChains_two_eq] at hsmall
  obtain ⟨a, b, hab⟩ :=
    SingularConnSquareLHSExplicit.exists_chainIncl_partition_of_mem_mvUnionChains (A ∩ S) (B ∩ S) n c hsmall
  exact ⟨a, b, hab⟩

omit [T2Space ↑X] in
/-- **RHS V-leg realization** (the σR-side cross-realization step, whnf-dodging via `repartition_subspaceChains`).
Pairs `cochainSplit A gR` against a cover-fine cover-partition `chainIncl A u + chainIncl B w` whose SUM is
`S`-supported (`hS`): the support-preserving re-partition lands the legs in `A∩S` (where `cochainSplit A gR`,
being relative on `A`, drops it) and `B∩S` (where, since `gR ∈ relCochains(A∩B)`, the swap `cochainSplit A gR
↦ gR` holds, `cochainSplit_compl_mem_relCochains`). The output `kronecker gR (chainIncl (B∩S) b)` is paired with
the *bare* cocycle `gR` against a chain supported in `B ∩ S ⊆ S` — ready to be realized on the common space
`sub S`. This is the leg-extraction the connecting-square σR side needs (`gR = g_rep↾`, `A = legSplitUᶜ`,
`B = legSplitVᶜ`, `S = U ∩ V`); the `Submodule.mem_sup` `w'` itself is bypassed. Over ℤ/2. Kernel-pure. -/
theorem rhs_realize_V_leg {A B S : Set ↑X} {n : ℕ}
    (gR : SingularCochain X n) (hgR : gR ∈ relCochains (A ∩ B) n)
    (u : SingularChain (sub A) n) (w : SingularChain (sub B) n)
    (hS : chainIncl A n u + chainIncl B n w ∈ subspaceChains S n) :
    ∃ (a : SingularChain (sub (A ∩ S)) n) (b : SingularChain (sub (B ∩ S)) n),
      (chainIncl A n u + chainIncl B n w = chainIncl (A ∩ S) n a + chainIncl (B ∩ S) n b)
      ∧ kronecker (cochainSplit A n gR) (chainIncl A n u + chainIncl B n w)
        = kronecker gR (chainIncl (B ∩ S) n b) := by
  obtain ⟨a, b, hab⟩ := repartition_subspaceChains u w hS
  refine ⟨a, b, hab, ?_⟩
  rw [hab, kronecker_add_right,
    (mem_relCochains _ _ _).1 (cochainSplit_mem_relCochains _ _ _) _
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left n ⟨a, rfl⟩), zero_add]
  have hψ := (mem_relCochains _ _ _).1
    (cochainSplit_compl_mem_relCochains A B n gR hgR)
    _ (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left n ⟨b, rfl⟩)
  rw [ZModModule.sub_eq_add, kronecker_add_left, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hψ
  exact hψ.symm

omit [T2Space ↑X] in
/-- **V-leg pairing well-definedness across cover-splits** (fact-(ii) brick β1 — the anti-`mem_sup`
engine). Two cover-splits of the SAME ambient chain — legs over any subsets `A₁, A₂ ⊆ A`, `B₁, B₂ ⊆ B` —
have EQUAL V-leg pairings against any cochain `g` vanishing on `C(A ∩ B)`: over ℤ/2 the two V-legs' sum
equals the two U-legs' sum, so it is supported in both `B` and `A`, i.e. in `A ∩ B`
(`subspaceChains_inf`), where `g` kills it. This makes ⟨g, V-leg⟩ an invariant of the CHAIN, not the
split — dissolving the `Submodule.mem_sup` witness-ambiguity that walled the cross-realization. -/
theorem kronecker_two_splits_V_leg_eq {A B : Set ↑X} {n : ℕ}
    (g : SingularCochain X n) (hg : g ∈ relCochains (A ∩ B) n)
    {a₁ b₁ a₂ b₂ : SingularChain X n}
    (ha₁ : a₁ ∈ subspaceChains A n) (hb₁ : b₁ ∈ subspaceChains B n)
    (ha₂ : a₂ ∈ subspaceChains A n) (hb₂ : b₂ ∈ subspaceChains B n)
    (heq : a₁ + b₁ = a₂ + b₂) :
    kronecker g b₁ = kronecker g b₂ := by
  have hbsum : b₁ + b₂ = a₁ + a₂ := by
    have h := congrArg (· + (b₁ + a₂)) heq
    abel_nf at h
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add] at h
    abel_nf
    rw [h]
  have hmem : b₁ + b₂ ∈ subspaceChains (A ∩ B) n := by
    rw [← SingularExcision.subspaceChains_inf]
    exact ⟨hbsum ▸ Submodule.add_mem _ ha₁ ha₂, Submodule.add_mem _ hb₁ hb₂⟩
  have h0 := (mem_relCochains _ _ _).1 hg _ hmem
  rw [kronecker_add_right, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0
  exact h0

omit [T2Space ↑X] in
/-- **Boundary-split V-leg vanishing** (fact-(ii) brick β2 — the TERMINATING boundary transport). If a
chain is `∂Ec` for an `(A ∪ B)`-supported `Ec`, the V-leg of ANY cover-split of it pairs to ZERO against
an absolute cocycle `g` vanishing on `C(A ∩ B)`. Construction: cover-fine-subdivide `Ec`
(`exists_cover_split`) — `∂(Sdᵐ Ec)` then splits with legs that are THEMSELVES boundaries of leg-chains,
each `g`-killed by the `δ`-adjunction; and the homotopy correction `Dₘ(∂Ec)` is cover-fine because `∂Ec`'s
OWN split makes it `{A,B}`-small and `D`/`Sd` PRESERVE smallness (`iterHomotopy_mem_smallChains`) — the
step the recursive rcap-slack attempts lacked, which is what terminates the transport. Conclude by the
split-invariance `kronecker_two_splits_V_leg_eq`. ℤ/2. -/
theorem kronecker_boundary_split_V_leg_zero {A B : Set ↑X} {n : ℕ}
    (hA : IsOpen A) (hB : IsOpen B)
    (g : SingularCochain X (n + 1)) (hgc : coboundary X (n + 1) g = 0)
    (hg : g ∈ relCochains (A ∩ B) (n + 1))
    (Ec : SingularChain X (n + 1 + 1)) (hEc : Ec ∈ subspaceChains (A ∪ B) (n + 1 + 1))
    {aZ bZ : SingularChain X (n + 1)}
    (haZ : aZ ∈ subspaceChains A (n + 1)) (hbZ : bZ ∈ subspaceChains B (n + 1))
    (hZsplit : chainBoundary X (n + 1) Ec = aZ + bZ) :
    kronecker g bZ = 0 := by
  classical
  obtain ⟨m, EU, EV, hEsplit⟩ :=
    SingularConnSquareRHSScaffold.exists_cover_split A B hA hB _ Ec hEc
  have hZcyc : chainBoundary X n (chainBoundary X (n + 1) Ec) = 0 :=
    chainBoundary_chainBoundary_apply X n Ec
  -- The homotopy correction, cover-partitioned (∂Ec is {A,B}-small via its OWN split):
  have hZsmall : chainBoundary X (n + 1) Ec ∈ SingularExcision.smallChains {A, B} (n + 1) := by
    rw [SingularExcision.smallChains_two_eq, hZsplit]
    exact Submodule.add_mem _ (Submodule.mem_sup_left haZ) (Submodule.mem_sup_right hbZ)
  have hDsmall := SingularExcision.iterHomotopy_mem_smallChains hZsmall m
  rw [SingularExcision.smallChains_two_eq] at hDsmall
  obtain ⟨DU, DV, hDsplit⟩ :=
    SingularConnSquareLHSExplicit.exists_chainIncl_partition_of_mem_mvUnionChains A B _ _ hDsmall
  -- The constructed split of ∂Ec: Z = Sdᵐ Z + ∂(Dₘ Z), both summands leg-split.
  have hhom := SingularExcision.add_singularSd_iterate_eq_boundary hZcyc m
  have hSdZ : (⇑(SingularSubdivision.singularSd X (n + 1)))^[m] (chainBoundary X (n + 1) Ec)
      = chainIncl A (n + 1) (chainBoundary (sub A) (n + 1) EU)
        + chainIncl B (n + 1) (chainBoundary (sub B) (n + 1) EV) := by
    rw [← SingularSubdivision.singularSd_iterate_chainBoundary, hEsplit, map_add,
      chainIncl_chainBoundary, chainIncl_chainBoundary]
  have hDbd : chainBoundary X (n + 1) (SingularSubdivision.iterHomotopy X (n + 1) m
        (chainBoundary X (n + 1) Ec))
      = chainIncl A (n + 1) (chainBoundary (sub A) (n + 1) DU)
        + chainIncl B (n + 1) (chainBoundary (sub B) (n + 1) DV) := by
    rw [hDsplit, map_add, chainIncl_chainBoundary, chainIncl_chainBoundary]
  have hZ2 : chainBoundary X (n + 1) Ec
      = chainIncl A (n + 1) (chainBoundary (sub A) (n + 1) EU + chainBoundary (sub A) (n + 1) DU)
        + chainIncl B (n + 1)
            (chainBoundary (sub B) (n + 1) EV + chainBoundary (sub B) (n + 1) DV) := by
    have h := congrArg
      (· + (⇑(SingularSubdivision.singularSd X (n + 1)))^[m] (chainBoundary X (n + 1) Ec)) hhom
    abel_nf at h
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add] at h
    rw [map_add, map_add, h, hSdZ, hDbd]
    abel
  have hkey := kronecker_two_splits_V_leg_eq g hg haZ hbZ
    ⟨_, rfl⟩ ⟨_, rfl⟩ (hZsplit.symm.trans hZ2)
  have hfin : kronecker g ((chainIncl B (n + 1)) ((chainBoundary (sub B) (n + 1)) EV
      + (chainBoundary (sub B) (n + 1)) DV)) = 0 := by
    have hcomb : (chainBoundary (sub B) (n + 1)) EV + (chainBoundary (sub B) (n + 1)) DV
        = (chainBoundary (sub B) (n + 1)) (EV + DV) := (map_add _ EV DV).symm
    rw [hcomb, chainIncl_chainBoundary, ← kronecker_coboundary_chainBoundary, hgc]
    simp
  rw [hkey]
  exact hfin

/-- **`∂(Sdʲ(chainIncl T d))` is `T`-supported** (the σR-leg `hMem0` brick, abstract whnf-dodging GREEN).
A `chainIncl T`-supported chain stays `T`-supported under iterated barycentric subdivision
(`singularSd_iterate_mem_subspaceChains`) and under `∂` (`chainBoundary_mem_subspaceChains`). Stated over a
FREE `sub T`-chain `d` so the concrete `rcap ω fund_∩` cap-chain infers structurally at application — the
explicit-`legSplitᶜ` type ascription that defeq-walls is bypassed. Feeds `rhs_realize_V_leg`'s support
hypothesis after `rw [← hsplit]`. ℤ/2. Kernel-pure. -/
theorem chainBoundary_singularSd_iterate_chainIncl_mem {T : Set ↑X} {n : ℕ} (j : ℕ)
    (d : SingularChain (sub T) (n + 1)) :
    chainBoundary X n ((⇑(SingularSubdivision.singularSd X (n + 1)))^[j] (chainIncl T (n + 1) d))
      ∈ subspaceChains T n :=
  chainBoundary_mem_subspaceChains _
    (SingularExcision.singularSd_iterate_mem_subspaceChains
      (c := chainIncl T (n + 1) d) ⟨d, rfl⟩ j)

omit [T2Space ↑X] in
/-- **Pullback transports relative-vanishing to the preimage** (fact-(ii) brick β0'). A cochain vanishing
on `C(S)` pulls back along `sub W ↪ X` to a cochain vanishing on `C(Subtype.val ⁻¹' S)`: a
preimage-supported chain includes to an `S`-supported ambient chain
(`chainIncl_mem_subspaceChains_iff`), where the adjunction
`⟨pullbackCochain W g, d⟩ = ⟨g, chainIncl W d⟩` hands the vanishing back. Lets the ambient `g_rep↾`
enter the sub(U∩V)-intrinsic β-brick machinery as `pullbackCochain (U∩V) g_rep↾`. ℤ/2. -/
theorem pullbackCochain_relCochains_preimage {W S : Set ↑X} {n : ℕ}
    (g : SingularCochain X n) (hg : g ∈ relCochains S n) :
    SingularCapChainIncl.pullbackCochain W n g ∈ relCochains (Subtype.val ⁻¹' S) n := by
  rw [mem_relCochains]
  intro d hd
  rw [SingularCapSubKDuality.kronecker_pullbackCochain]
  exact (mem_relCochains _ _ _).1 hg _
    ((SingularExcisionIso.chainIncl_mem_subspaceChains_iff S W d).mpr hd)

omit [T2Space ↑X] in
/-- **`chainIncl` commutes with degree casts** (fresh-variable form — `cases h` needs bare variables).
With `castChain_cast_reconcile` and `chainIncl_injective` this yields the M'-level reconciliation of the
two `castChain`-instance fundamentals (the σR-side `N+2+p+1` vs the match-side `N+1+(p+1)+1` realize):
their sub(U∩V)-realizations agree up to the same numeric cast. ℤ/2. -/
theorem chainIncl_cast_comm {W : Set ↑X} {a b : ℕ} (h : a = b)
    (x : SingularChain (sub W) a) :
    chainIncl W b (h ▸ x) = h ▸ chainIncl W a x := by
  cases h; rfl

omit [T2Space ↑X] in
/-- **`chainBoundary` commutes with degree casts** (`cast (congrArg …)` canonical spelling, coherent with
`subspaceChains_mem_cast`; fresh-variable form so `cases h` closes it). -/
theorem chainBoundary_cast_comm {a b : ℕ} (h : a = b) (x : SingularChain X (a + 1)) :
    chainBoundary X b (cast (congrArg (SingularChain X) (congrArg (· + 1) h)) x)
      = cast (congrArg (SingularChain X) h) (chainBoundary X a x) := by
  cases h; rfl

/-- **Cast-aware cover-V-projection existence** (the fact-(ii) F-constructor, whnf-dodging abstract form).
For a `W`-supported chain `z` (at ANY degree presentation `n₂ + 1`, transported to the target
presentation `n₁ + 1` by the cast) whose boundary is cover-supported, some iterated subdivision of the
cast chain has a boundary splitting into SUPPORT-PRESERVING repartitioned legs over `A ∩ W` / `B ∩ W`.
All the cast/degree work happens in here over the FREE variable `z` (where `cases h` collapses the cast
before anything must reduce) — the concrete `fundCycleW` enters only as an opaque argument. ℤ/2. -/
theorem exists_cast_cover_V_projection {W A B : Set ↑X} (hA : IsOpen A) (hB : IsOpen B)
    {n₂ n₁ : ℕ} (h : n₂ = n₁) (z : SingularChain X (n₂ + 1))
    (hz : z ∈ subspaceChains W (n₂ + 1))
    (hbd : chainBoundary X n₂ z ∈ subspaceChains (A ∪ B) n₂) :
    ∃ (j : ℕ) (aF : SingularChain (sub (A ∩ W)) n₁) (bF : SingularChain (sub (B ∩ W)) n₁),
      chainBoundary X n₁ ((⇑(SingularSubdivision.singularSd X (n₁ + 1)))^[j]
          (cast (congrArg (SingularChain X) (congrArg (· + 1) h)) z))
        = chainIncl (A ∩ W) n₁ aF + chainIncl (B ∩ W) n₁ bF := by
  cases h
  obtain ⟨j, u, w, hsplit⟩ :=
    SingularConnSquareRHSScaffold.exists_cover_fine_subdivision hA hB z hbd
  have hpar : chainIncl A n₂ u + chainIncl B n₂ w ∈ subspaceChains W n₂ := by
    rw [← hsplit]
    exact SingularRelativeHomologyMod2.chainBoundary_mem_subspaceChains W n₂ _
      (SingularExcision.singularSd_iterate_mem_subspaceChains hz j)
  obtain ⟨aF, bF, hFsplit⟩ := repartition_subspaceChains u w hpar
  exact ⟨j, aF, bF, hsplit.trans hFsplit⟩

omit [T2Space ↑X] in
/-- **Right-cap locality through the subspace inclusion** (fact-(ii) brick β0''). If the ambient image of
a `sub W`-chain `F` is `B'`-supported, so is the ambient image of any intrinsic right cap `rcap b F`:
transport up (`chainIncl_mem_subspaceChains_iff`), apply the intrinsic `rcap_mem_subspaceChains` at the
preimage, transport back down. Stated over FREE `W, B', b, F` — every set infers from the membership
hypothesis, so no concrete coercion spelling ever meets the elaborator. ℤ/2. -/
theorem chainIncl_rcap_subspaceChains {W B' : Set ↑X} {k l : ℕ}
    (b : SingularCochain (sub W) l) (F : SingularChain (sub W) (k + l))
    (hF : chainIncl W (k + l) F ∈ subspaceChains B' (k + l)) :
    chainIncl W k (SingularCapChainIncl.rcap b F) ∈ subspaceChains B' k :=
  (SingularExcisionIso.chainIncl_mem_subspaceChains_iff B' W _).mpr
    (SingularRightCapBoundary.rcap_mem_subspaceChains _ b
      ((SingularExcisionIso.chainIncl_mem_subspaceChains_iff B' W F).mp hF))

/-- **Two-legs assembly for the pullback pairing** (the fact-(ii) frame, EXTRACTED for heartbeat
relief). The apex proof is ONE Lean command whose 200k-heartbeat budget is cumulative across the
whole proof body; this pullback-layer reduction — un-pullback both sides
(`kronecker_chainIncl_eq_pullbackCochain`), collapse the realizes
(`chainIncl_subspaceChainsEquiv_symm`), swap the intrinsic right cap for its `Bv`-leg realization —
previously elaborated inside it and tipped the budget. Packaged over FREE `W/Bv/k/l/g/b/bR/bF`
(fresh budget, no `fundCycleW` anywhere, every unification small and first-order). The remaining
input `hcore` is the bare two-`Bv`-legs core `⟨g, bR-leg⟩ = ⟨g, (rcap b F)-realized-leg⟩`. ℤ/2. -/
theorem pullback_pairing_legs_assemble {W Bv : Set ↑X} {k l : ℕ}
    (g : SingularCochain X k) (b : SingularCochain (sub W) l)
    (bR : SingularChain (sub Bv) k)
    (hbmem : chainIncl Bv k bR ∈ subspaceChains W k)
    (bF : SingularChain (sub Bv) (k + l))
    (hbFmem : chainIncl Bv (k + l) bF ∈ subspaceChains W (k + l))
    (hmem3 : chainIncl W k (SingularCapChainIncl.rcap b
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (k + l)).symm ⟨_, hbFmem⟩))
      ∈ subspaceChains Bv k)
    (hcore : kronecker g (chainIncl Bv k bR)
      = kronecker g (chainIncl Bv k
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv Bv k).symm ⟨_, hmem3⟩))) :
    kronecker (SingularCapChainIncl.pullbackCochain W k g)
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W k).symm ⟨_, hbmem⟩)
      = kronecker (SingularCapChainIncl.pullbackCochain W k g)
        (SingularCapChainIncl.rcap b
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (k + l)).symm ⟨_, hbFmem⟩)) := by
  have e₁ := kronecker_chainIncl_eq_pullbackCochain (W := W) g
    ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W k).symm ⟨_, hbmem⟩)
  have e₂ := kronecker_chainIncl_eq_pullbackCochain (W := W) g
    (SingularCapChainIncl.rcap b
      ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (k + l)).symm ⟨_, hbFmem⟩))
  have e₃ : chainIncl W k ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W k).symm ⟨_, hbmem⟩)
      = chainIncl Bv k bR :=
    SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm (S := W) k ⟨_, hbmem⟩
  have e₄ : chainIncl W k (SingularCapChainIncl.rcap b
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (k + l)).symm ⟨_, hbFmem⟩))
      = chainIncl Bv k ((SingularSubspaceChainsEquiv.subspaceChainsEquiv Bv k).symm ⟨_, hmem3⟩) :=
    (SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm (S := Bv) k ⟨_, hmem3⟩).symm
  exact e₁.symm.trans (((congrArg (kronecker g) e₃).trans hcore).trans
    ((congrArg (kronecker g) e₄.symm).trans e₂))

/-- Membership in `subspaceChains` transports along a degree `▸`-cast (fresh-variable form —
`cases h` collapses the cast; the direct `▸` on a membership fails motive computation). -/
theorem mem_subspaceChains_eq_rec {M : TopCat} {S : Set ↑M} {d₁ d₂ : ℕ} (h : d₁ = d₂)
    {c : SingularChain M d₁}
    (hc : c ∈ SingularRelativeHomologyMod2.subspaceChains S d₁) :
    (h ▸ c : SingularChain M d₂) ∈ SingularRelativeHomologyMod2.subspaceChains S d₂ := by
  cases h; exact hc

/-- **`subspaceChainsEquiv.symm` double-cast collapse** (fresh-variable form): the realize of an
ambient cast, `▸`-transported to a third degree, is the realize of the COMPOSED cast. The
single-choice T₀-reconciliation: with all degree equalities free, `cases` collapses every cast
before anything must reduce; at the concrete site the composed cast has definitionally equal
endpoints (`N+2+p+1 ≡ N+1+1+(p+1)`) so the result collapses onto the pd-side realize by `rfl`. -/
theorem subspaceChainsEquiv_symm_cast_cast {W : Set ↑X} {d₀ d₁ d₂ : ℕ}
    (h₀ : d₀ = d₁) (h₂ : d₁ = d₂) {c : SingularChain X d₀}
    (hc₁ : cast (congrArg (SingularChain X) h₀) c ∈ subspaceChains W d₁)
    (hc₂ : cast (congrArg (SingularChain X) (h₀.trans h₂)) c ∈ subspaceChains W d₂) :
    (h₂ ▸ (SingularSubspaceChainsEquiv.subspaceChainsEquiv W d₁).symm
        ⟨cast (congrArg (SingularChain X) h₀) c, hc₁⟩ : SingularChain (sub W) d₂)
      = (SingularSubspaceChainsEquiv.subspaceChainsEquiv W d₂).symm
          ⟨cast (congrArg (SingularChain X) (h₀.trans h₂)) c, hc₂⟩ := by
  cases h₀; cases h₂; rfl

/-- **Cap of a cocycle against a subdivision-iterate, cycle-free** (the fact-(i) canonical-partition
class input). For a cocycle `g` vanishing on `C(S)`-chains and a chain `f` whose boundary is
`S`-supported: `cap g (Sdᵘ f) + cap g f = ∂(cap g (Dᵤ f))` — the homotopy slack `Dᵤ(∂f)` dies against
`g`'s `S`-vanishing (`iterHomotopy_mem_subspaceChains`), the `∂(Dᵤ f)`-cap is exact by the cocycle
Leibniz. Applied with `g := g_rep` (S := Kᶜ, RC-1 + RC-2), `f := fundCycleW_K`: the subdivided W-leg
cycle `cap g (Sdᵘ fund_K)` is homologous to `cap g fund_K` with a `(U∪V)`-SUPPORTED bounding chain
(`Dᵤ fund_K ∈ C(U∪V)`, support-preserving) — realizable in `sub (U∪V)`, the class-equality feed for
`kronecker_boundaryExtract_class_invariant`. ℤ/2. -/
theorem cap_cocycle_singularSd_iterate_add_eq_boundary {S : Set ↑X} {k m : ℕ}
    (g : SingularCochain X k) (hgc : coboundary X k g = 0) (hgrel : g ∈ relCochains S k)
    (f : SingularChain X (k + m + 1)) (μ : ℕ)
    (hbd : chainBoundary X (k + m) f ∈ subspaceChains S (k + m)) :
    cap (m := m + 1) g ((⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ] f)
        + cap (m := m + 1) g f
      = chainBoundary X (m + 1)
          (cap (m := m + 1 + 1) g (SingularSubdivision.iterHomotopy X (k + m + 1) μ f)) := by
  have hh := SingularSubdivision.iterHomotopy_chainHomotopy X μ (k + m) f
  have hkill : cap (m := m + 1) g (SingularSubdivision.iterHomotopy X (k + m) μ
      (chainBoundary X (k + m) f)) = 0 :=
    cap_relCochains_subspaceChains_eq_zero (m := m + 1) g hgrel _
      (SingularExcision.iterHomotopy_mem_subspaceChains hbd μ)
  have hex : chainBoundary X (m + 1)
        (cap (m := m + 1 + 1) g (SingularSubdivision.iterHomotopy X (k + m + 1) μ f))
      = cap (m := m + 1) g (chainBoundary X (k + m + 1)
          (SingularSubdivision.iterHomotopy X (k + m + 1) μ f)) :=
    chainBoundary_cap_cocycle_arg (m := m + 1) g hgc _ (by omega)
  have hsum : cap (m := m + 1) g (f + (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ] f)
      = cap (m := m + 1) g ((⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ] f)
        + cap (m := m + 1) g f := by
    rw [← capₗ_apply, map_add, capₗ_apply, capₗ_apply]
    exact add_comm _ _
  rw [← hsum, ← hh, ← capₗ_apply, map_add, capₗ_apply, capₗ_apply, hkill, add_zero, hex]

/-- **δφ-cap of an eventually-split chain is exact** (the unsplit-`A∪B` δφ-cap TERMINATOR — closes the
(P)-ledger recursion). For a cocycle `a` vanishing on BOTH cover legs (`a = δ(cochainSplit U ω)` via
`cochainSplit_coboundary_mem_U/V`) and a chain `c` whose subdivision-iterate splits cover-subordinately
(`hsplit`) AND whose boundary also splits (`hsplit'`): `cap a c = ∂(cap a (Dᵥ c))`. The three homotopy
terms die: `Sdᵛ c` by the cover-partition kill, `Dᵥ(∂c)` leg-wise (`iterHomotopy_mem_subspaceChains` +
the one-leg kill), and the `∂(Dᵥ c)`-cap is exact (cocycle Leibniz). The `ρ`/`T∂f₂` δφ-caps of the
(P)-telescope close once their Sd-splits are supplied (`exists_iterate_mvUnion_sub` + partition). ℤ/2. -/
theorem cap_relCochains_pair_split_eq_boundary {P Q : Set ↑X} {k n : ℕ}
    (a : SingularCochain X k) (hac : coboundary X k a = 0)
    (haP : a ∈ relCochains P k) (haQ : a ∈ relCochains Q k)
    (c : SingularChain X (k + n + 1)) (ν : ℕ)
    (u : SingularChain (sub P) (k + n + 1)) (w : SingularChain (sub Q) (k + n + 1))
    (hsplit : (⇑(SingularSubdivision.singularSd X (k + n + 1)))^[ν] c
      = chainIncl P (k + n + 1) u + chainIncl Q (k + n + 1) w)
    (u' : SingularChain (sub P) (k + n)) (w' : SingularChain (sub Q) (k + n))
    (hsplit' : chainBoundary X (k + n) c = chainIncl P (k + n) u' + chainIncl Q (k + n) w') :
    cap (m := n + 1) a c = chainBoundary X (n + 1)
        (cap (m := n + 1 + 1) a (SingularSubdivision.iterHomotopy X (k + n + 1) ν c)) := by
  have hh := SingularSubdivision.iterHomotopy_chainHomotopy X ν (k + n) c
  have h1 : cap (m := n + 1) a ((⇑(SingularSubdivision.singularSd X (k + n + 1)))^[ν] c) = 0 := by
    rw [hsplit]
    exact cap_relCochains_cover_partition_eq_zero (m := n + 1) a haP haQ u w
  have h2 : cap (m := n + 1) a (SingularSubdivision.iterHomotopy X (k + n) ν
      (chainBoundary X (k + n) c)) = 0 := by
    rw [hsplit']
    have hTadd : SingularSubdivision.iterHomotopy X (k + n) ν
        (chainIncl P (k + n) u' + chainIncl Q (k + n) w')
        = SingularSubdivision.iterHomotopy X (k + n) ν (chainIncl P (k + n) u')
          + SingularSubdivision.iterHomotopy X (k + n) ν (chainIncl Q (k + n) w') := by
      simp [SingularSubdivision.iterHomotopy, map_add, Finset.sum_add_distrib]
    rw [hTadd, ← capₗ_apply, map_add, capₗ_apply, capₗ_apply,
      cap_relCochains_subspaceChains_eq_zero (m := n + 1) a haP _
        (SingularExcision.iterHomotopy_mem_subspaceChains ⟨u', rfl⟩ ν),
      cap_relCochains_subspaceChains_eq_zero (m := n + 1) a haQ _
        (SingularExcision.iterHomotopy_mem_subspaceChains ⟨w', rfl⟩ ν),
      add_zero]
  have h3 : (chainBoundary X (k + n + 1)
        (SingularSubdivision.iterHomotopy X (k + n + 1) ν c)
      + SingularSubdivision.iterHomotopy X (k + n) ν (chainBoundary X (k + n) c))
      + (⇑(SingularSubdivision.singularSd X (k + n + 1)))^[ν] c = c := by
    rw [hh]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  have hc : cap (m := n + 1) a c
      = cap (m := n + 1) a ((chainBoundary X (k + n + 1)
            (SingularSubdivision.iterHomotopy X (k + n + 1) ν c)
          + SingularSubdivision.iterHomotopy X (k + n) ν (chainBoundary X (k + n) c))
          + (⇑(SingularSubdivision.singularSd X (k + n + 1)))^[ν] c) := by rw [h3]
  rw [hc, ← capₗ_apply, map_add, map_add, capₗ_apply, capₗ_apply, capₗ_apply, h1, h2, add_zero,
    add_zero]
  exact (chainBoundary_cap_cocycle_arg (m := n + 1) a hac _ (by omega)).symm

/-- **Two `fundCycleW`s over the SAME `z₀` are jointly rel-homologous** (Sun Prop 1(iv), the shared-z₀
fund-compat in chain form): composing the two `fundCycleW_chain_rel`s — the shared `z₀` cancels over
ℤ/2 — gives `fund₁ + fund₂ = ∂η + a₁ + a₂` with `a₁ ∈ C(K₁ᶜ)`, `a₂ ∈ C(K₂ᶜ)`. The cross-realization
coupling input: capping with `g_rep` kills `a₁` (RC-2, `K₁ := K`) and the `∂η`-cap is exact (RC-1),
isolating the `a₂`-slack (`K₂ := infCompact`) that carries the connecting content. -/
theorem fundCycleW_pair_shared_z0_rel {W₁ W₂ : Set ↑X} {k m : ℕ}
    (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K₁ : SingularCompactsInOpen.CompactsIn W₁) (K₂ : SingularCompactsInOpen.CompactsIn W₂) :
    ∃ (η : SingularChain X (k + m + 1 + 1)) (a₁ a₂ : SingularChain X (k + m + 1)),
      SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁
          + SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂
        = chainBoundary X (k + m + 1) η + a₁ + a₂
      ∧ a₁ ∈ subspaceChains ((↑K₁.1 : Set ↑X)ᶜ) (k + m + 1)
      ∧ a₂ ∈ subspaceChains ((↑K₂.1 : Set ↑X)ᶜ) (k + m + 1) := by
  obtain ⟨η₁, a₁, heq₁, ha₁⟩ := fundCycleW_chain_rel hW₁ z₀ hz₀ K₁
  obtain ⟨η₂, a₂, heq₂, ha₂⟩ := fundCycleW_chain_rel hW₂ z₀ hz₀ K₂
  refine ⟨η₁ + η₂, a₁, a₂, ?_, ha₁, ha₂⟩
  have hz : SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁
        + SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂
      = (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁ + z₀)
        + (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂ + z₀) := by
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  rw [hz, heq₁, heq₂, map_add]
  abel

/-- **Ambient cover-fine chain split** (Brick E — the small-chains split pushed to the ambient level):
a `(U∪V)`-supported chain becomes, after enough subdivisions, a SUM of a `U`-supported and a
`V`-supported ambient chain. Realize in `sub (U∪V)` (`subspaceChainsEquiv`), split intrinsically
(`exists_iterate_mvUnion_sub` + `exists_chainIncl_partition_of_mem_mvUnionChains`), push back
(`singularSd_iterate_chainIncl` + `chainIncl_mem_subspaceChains_iff`). The ONE split choice the
fact-(i) canonical partition rides. -/
theorem exists_iterate_cover_split_amb {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (f : SingularChain X n) (hf : f ∈ subspaceChains (U ∪ V) n) :
    ∃ (μ : ℕ) (fA fB : SingularChain X n),
      fA ∈ subspaceChains U n ∧ fB ∈ subspaceChains V n
      ∧ (⇑(SingularSubdivision.singularSd X n))^[μ] f = fA + fB := by
  obtain ⟨μ, hμ⟩ := exists_iterate_mvUnion_sub hU hV n
    ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∪ V) n).symm ⟨f, hf⟩)
  obtain ⟨zA, zB, hzsplit⟩ :=
    SingularConnSquareLHSExplicit.exists_chainIncl_partition_of_mem_mvUnionChains _ _ n _ hμ
  refine ⟨μ, chainIncl (U ∪ V) n (chainIncl _ n zA), chainIncl (U ∪ V) n (chainIncl _ n zB),
    (SingularExcisionIso.chainIncl_mem_subspaceChains_iff U (U ∪ V) _).mpr ⟨zA, rfl⟩,
    (SingularExcisionIso.chainIncl_mem_subspaceChains_iff V (U ∪ V) _).mpr ⟨zB, rfl⟩, ?_⟩
  have hfr : f = chainIncl (U ∪ V) n
      ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∪ V) n).symm ⟨f, hf⟩) :=
    (SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm (U ∪ V) n ⟨f, hf⟩).symm
  rw [hfr, singularSd_iterate_chainIncl, hzsplit, map_add]

/-- **Cap-induced partition over a GIVEN split** (Brick F′ — Brick F's realization core, parametrized:
takes the `(fA, fB)`-decomposition as input instead of choosing one, so the THREE-set split's MV lift
`(f₁, f₂+f₃)` feeds it). Same construction: cap the split legs (support-preserved), realize two-level
via `chainIncl_mem_subspaceChains_iff`, descend the cycle through `chainIncl`-injectivity. -/
theorem cap_induced_partition_of_split {U V S : Set ↑X} {k m : ℕ}
    (g : SingularCochain X k) (hgc : coboundary X k g = 0) (hgrel : g ∈ relCochains S k)
    (f : SingularChain X (k + m + 1)) (μ : ℕ)
    (hbd : chainBoundary X (k + m) f ∈ subspaceChains S (k + m))
    (fA fB : SingularChain X (k + m + 1))
    (hfA : fA ∈ subspaceChains U (k + m + 1)) (hfB : fB ∈ subspaceChains V (k + m + 1))
    (hsplit : (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ] f = fA + fB) :
    ∃ (zA : SingularChain (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (m + 1))
      (zB : SingularChain (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (m + 1)),
      chainIncl (U ∪ V) (m + 1) (chainIncl _ (m + 1) zA) = cap (m := m + 1) g fA
      ∧ chainIncl (U ∪ V) (m + 1) (chainIncl _ (m + 1) zB) = cap (m := m + 1) g fB
      ∧ chainIncl _ (m + 1) zA + chainIncl _ (m + 1) zB ∈ cycles (sub (U ∪ V)) (m + 1) := by
  have hcA : cap (m := m + 1) g fA ∈ subspaceChains U (m + 1) :=
    SingularCapSupport.cap_mem_subspaceChains (m := m + 1) U g hfA
  have hcB : cap (m := m + 1) g fB ∈ subspaceChains V (m + 1) :=
    SingularCapSupport.cap_mem_subspaceChains (m := m + 1) V g hfB
  have hcA' : cap (m := m + 1) g fA ∈ subspaceChains (U ∪ V) (m + 1) :=
    SingularMayerVietoris.subspaceChains_mono Set.subset_union_left (m + 1) hcA
  have hcB' : cap (m := m + 1) g fB ∈ subspaceChains (U ∪ V) (m + 1) :=
    SingularMayerVietoris.subspaceChains_mono Set.subset_union_right (m + 1) hcB
  set yA := (SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∪ V) (m + 1)).symm ⟨_, hcA'⟩
    with hyAdef
  set yB := (SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∪ V) (m + 1)).symm ⟨_, hcB'⟩
    with hyBdef
  have hyA : chainIncl (U ∪ V) (m + 1) yA = cap (m := m + 1) g fA :=
    SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm _ _ _
  have hyB : chainIncl (U ∪ V) (m + 1) yB = cap (m := m + 1) g fB :=
    SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm _ _ _
  have hyAmem : yA ∈ subspaceChains (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (m + 1) :=
    (SingularExcisionIso.chainIncl_mem_subspaceChains_iff U (U ∪ V) yA).mp (hyA.symm ▸ hcA)
  have hyBmem : yB ∈ subspaceChains (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) (m + 1) :=
    (SingularExcisionIso.chainIncl_mem_subspaceChains_iff V (U ∪ V) yB).mp (hyB.symm ▸ hcB)
  refine ⟨(SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm ⟨yA, hyAmem⟩,
    (SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm ⟨yB, hyBmem⟩, ?_, ?_, ?_⟩
  · rw [SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm, hyA]
  · rw [SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm, hyB]
  · have hcycamb : chainBoundary X m
        (cap (m := m + 1) g ((⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ] f)) = 0 := by
      rw [chainBoundary_cap_cocycle_arg (m := m) g hgc _ (by omega),
        SingularSubdivision.singularSd_iterate_chainBoundary]
      exact cap_relCochains_subspaceChains_eq_zero (m := m) g hgrel _
        (SingularExcision.singularSd_iterate_mem_subspaceChains hbd μ)
    have e₁ : chainIncl (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (m + 1)
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm ⟨yA, hyAmem⟩) = yA :=
      SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm _ _ ⟨yA, hyAmem⟩
    have e₂ : chainIncl (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) (m + 1)
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm ⟨yB, hyBmem⟩) = yB :=
      SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm _ _ ⟨yB, hyBmem⟩
    have hsum : chainIncl (U ∪ V) (m + 1)
        (chainIncl _ (m + 1) ((SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm
            ⟨yA, hyAmem⟩)
          + chainIncl _ (m + 1) ((SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm
            ⟨yB, hyBmem⟩))
        = cap (m := m + 1) g ((⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ] f) := by
      rw [map_add, e₁, e₂, hyA, hyB, hsplit, map_add]
    refine LinearMap.mem_ker.mpr ?_
    apply chainIncl_injective (U ∪ V) m
    rw [SingularRelativeHomologyMod2.chainIncl_chainBoundary, hsum, hcycamb, map_zero]

/-- **Ambient THREE-set cover-fine split** (Brick I — the Sun-Lemma-3 subordination; scout report
`Lit-Search/Phase-5qG/research/sun_lemma3_chain_witness.md`). A `(U∪V)`-supported chain subdivides
into pieces supported in `U∩LVᶜ` (= U−LV), `V∩LUᶜ` (= V−LU), and `U∩V` — the three-set cover that
makes the connecting-block boundary computation land in `C(U∩V)`: the MV partition is
`(fA, fB) := (f₁, f₂+f₃)`, `f₃` carries the only genuine bounding chain (`cap φ f₃ ∈ C(U∩V)`), and
`∂f₂ ∈ C(LUᶜ)` activates the E8 termwise kill. Brick E applied twice; `Sd` preserves the first
piece's support. -/
theorem exists_iterate_three_set_split_amb {U V LU LV : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V) (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ)
    (hLU : LU ⊆ U) (hLV : LV ⊆ V) {n : ℕ}
    (f : SingularChain X n) (hf : f ∈ subspaceChains (U ∪ V) n) :
    ∃ (μ : ℕ) (f₁ f₂ f₃ : SingularChain X n),
      f₁ ∈ subspaceChains (U ∩ LVᶜ) n ∧ f₂ ∈ subspaceChains (V ∩ LUᶜ) n
      ∧ f₃ ∈ subspaceChains (U ∩ V) n
      ∧ (⇑(SingularSubdivision.singularSd X n))^[μ] f = f₁ + f₂ + f₃ := by
  have hcov : U ∪ V ⊆ (U ∩ LVᶜ) ∪ ((V ∩ LUᶜ) ∪ (U ∩ V)) := by
    rintro x (hxU | hxV)
    · by_cases hxV : x ∈ V
      · exact Or.inr (Or.inr ⟨hxU, hxV⟩)
      · exact Or.inl ⟨hxU, fun hLVx => hxV (hLV hLVx)⟩
    · by_cases hxU : x ∈ U
      · exact Or.inr (Or.inr ⟨hxU, hxV⟩)
      · exact Or.inr (Or.inl ⟨hxV, fun hLUx => hxU (hLU hLUx)⟩)
  obtain ⟨μ₁, f₁', rest, hf₁', hrest, hsplit₁⟩ :=
    exists_iterate_cover_split_amb (hU.inter hLVc) ((hV.inter hLUc).union (hU.inter hV)) f
      (SingularMayerVietoris.subspaceChains_mono hcov n hf)
  obtain ⟨μ₂, f₂, f₃, hf₂, hf₃, hsplit₂⟩ :=
    exists_iterate_cover_split_amb (hV.inter hLUc) (hU.inter hV) rest hrest
  have hadd : ∀ (k : ℕ) (a b : SingularChain X n),
      (⇑(SingularSubdivision.singularSd X n))^[k] (a + b)
        = (⇑(SingularSubdivision.singularSd X n))^[k] a
          + (⇑(SingularSubdivision.singularSd X n))^[k] b := by
    intro k
    induction k with
    | zero => intro a b; rfl
    | succ k ih => intro a b; simp only [Function.iterate_succ_apply, map_add, ih]
  refine ⟨μ₂ + μ₁, (⇑(SingularSubdivision.singularSd X n))^[μ₂] f₁', f₂, f₃,
    SingularExcision.singularSd_iterate_mem_subspaceChains hf₁' μ₂, hf₂, hf₃, ?_⟩
  rw [Function.iterate_add_apply, hsplit₁, hadd, hsplit₂, add_assoc]

/-- **The cap-induced canonical partition** (Brick F — the fact-(i) partition constructor). For a
cocycle `g` rel-`S` and a `(U∪V)`-supported chain `f` with `S`-supported boundary, the cap
`cap g (Sdᵘ f)` is a CYCLE (cocycle-Leibniz + the `S`-kill on `Sdᵘ∂f`) carrying a canonical
`sub (U∪V)`-cover-partition INDUCED by Brick E's ambient split of `Sdᵘ f`: the partition legs
`zA†/zB†` realize `cap g fA / cap g fB` (cap preserves supports; two-level realization via
`chainIncl_mem_subspaceChains_iff`). Exports the ambient identities + the partition cycle — exactly
the `kronecker_boundaryExtract_class_invariant` (Brick A) + seam-computability feed: the seam of THIS
partition is `∂(cap g fB)` with `fB` fund-side-explicit. -/
theorem exists_cap_induced_partition {U V S : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    {k m : ℕ} (g : SingularCochain X k) (hgc : coboundary X k g = 0)
    (hgrel : g ∈ relCochains S k)
    (f : SingularChain X (k + m + 1)) (hf : f ∈ subspaceChains (U ∪ V) (k + m + 1))
    (hbd : chainBoundary X (k + m) f ∈ subspaceChains S (k + m)) :
    ∃ (μ : ℕ)
      (zA : SingularChain (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (m + 1))
      (zB : SingularChain (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (m + 1))
      (fA fB : SingularChain X (k + m + 1)),
      fA ∈ subspaceChains U (k + m + 1) ∧ fB ∈ subspaceChains V (k + m + 1)
      ∧ (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ] f = fA + fB
      ∧ chainIncl (U ∪ V) (m + 1) (chainIncl _ (m + 1) zA) = cap (m := m + 1) g fA
      ∧ chainIncl (U ∪ V) (m + 1) (chainIncl _ (m + 1) zB) = cap (m := m + 1) g fB
      ∧ chainIncl _ (m + 1) zA + chainIncl _ (m + 1) zB ∈ cycles (sub (U ∪ V)) (m + 1) := by
  obtain ⟨μ, fA, fB, hfA, hfB, hsplit⟩ := exists_iterate_cover_split_amb hU hV f hf
  have hcA : cap (m := m + 1) g fA ∈ subspaceChains U (m + 1) :=
    SingularCapSupport.cap_mem_subspaceChains (m := m + 1) U g hfA
  have hcB : cap (m := m + 1) g fB ∈ subspaceChains V (m + 1) :=
    SingularCapSupport.cap_mem_subspaceChains (m := m + 1) V g hfB
  have hcA' : cap (m := m + 1) g fA ∈ subspaceChains (U ∪ V) (m + 1) :=
    SingularMayerVietoris.subspaceChains_mono Set.subset_union_left (m + 1) hcA
  have hcB' : cap (m := m + 1) g fB ∈ subspaceChains (U ∪ V) (m + 1) :=
    SingularMayerVietoris.subspaceChains_mono Set.subset_union_right (m + 1) hcB
  set yA := (SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∪ V) (m + 1)).symm ⟨_, hcA'⟩
    with hyAdef
  set yB := (SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∪ V) (m + 1)).symm ⟨_, hcB'⟩
    with hyBdef
  have hyA : chainIncl (U ∪ V) (m + 1) yA = cap (m := m + 1) g fA :=
    SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm _ _ _
  have hyB : chainIncl (U ∪ V) (m + 1) yB = cap (m := m + 1) g fB :=
    SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm _ _ _
  have hyAmem : yA ∈ subspaceChains (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (m + 1) :=
    (SingularExcisionIso.chainIncl_mem_subspaceChains_iff U (U ∪ V) yA).mp (hyA.symm ▸ hcA)
  have hyBmem : yB ∈ subspaceChains (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) (m + 1) :=
    (SingularExcisionIso.chainIncl_mem_subspaceChains_iff V (U ∪ V) yB).mp (hyB.symm ▸ hcB)
  refine ⟨μ, (SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm ⟨yA, hyAmem⟩,
    (SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm ⟨yB, hyBmem⟩,
    fA, fB, hfA, hfB, hsplit, ?_, ?_, ?_⟩
  · rw [SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm, hyA]
  · rw [SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm, hyB]
  · -- the partition is a cycle: descend `∂(cap g (Sdᵘ f)) = 0` through `chainIncl`-injectivity
    have hcycamb : chainBoundary X m
        (cap (m := m + 1) g ((⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ] f)) = 0 := by
      rw [chainBoundary_cap_cocycle_arg (m := m) g hgc _ (by omega),
        SingularSubdivision.singularSd_iterate_chainBoundary]
      exact cap_relCochains_subspaceChains_eq_zero (m := m) g hgrel _
        (SingularExcision.singularSd_iterate_mem_subspaceChains hbd μ)
    have e₁ : chainIncl (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (m + 1)
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm ⟨yA, hyAmem⟩) = yA :=
      SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm _ _ ⟨yA, hyAmem⟩
    have e₂ : chainIncl (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V))) (m + 1)
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm ⟨yB, hyBmem⟩) = yB :=
      SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm _ _ ⟨yB, hyBmem⟩
    have hsum : chainIncl (U ∪ V) (m + 1)
        (chainIncl _ (m + 1) ((SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm
            ⟨yA, hyAmem⟩)
          + chainIncl _ (m + 1) ((SingularSubspaceChainsEquiv.subspaceChainsEquiv _ (m + 1)).symm
            ⟨yB, hyBmem⟩))
        = cap (m := m + 1) g ((⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ] f) := by
      rw [map_add, e₁, e₂, hyA, hyB, hsplit, map_add]
    refine LinearMap.mem_ker.mpr ?_
    apply chainIncl_injective (U ∪ V) m
    rw [SingularRelativeHomologyMod2.chainIncl_chainBoundary, hsum, hcycamb, map_zero]

/-- **Seam-transport class invariance** (Brick A conjugated by the seam homeos — the fact-(i) LHS
transport). The `β`-pairing of the double-pushed boundary-extract seam depends only on the HOMOLOGY
CLASS of the partitioned cycle — for any two partitioned cycles in the same class and ANY
relCycleLift witnesses (proof-irrelevant). `kronecker_double_pullback` moves `β` across the homeos
(unification supplies the concrete anonymous-struct seam maps — the `hmatch_close` trick);
`pullbackCochainMap_mem_ker` transports cocycle-ness; Brick A
(`kronecker_boundaryExtract_class_invariant`) fires at the seam level. Lets the apex swap the opaque
legW-partition `(zA, zB)` for the canonical cap-induced partition (Brick F) inside the goal's own
seam term. -/
theorem kronecker_mapChain_boundaryExtract_class_invariant {M Y' Z : TopCat}
    (A B : Set ↑M) (n : ℕ)
    (hcov : (⋃ W ∈ ({A, B} : Set (Set ↑M)), interior W) = Set.univ)
    (φin : C(↑(sub (SingularExcisionIso.restr A B)), ↑Y')) (φout : C(↑Y', ↑Z))
    (β : LinearMap.ker (coboundaryₗ Z n))
    (zA zA' : SingularChain (sub A) (n + 1)) (zB zB' : SingularChain (sub B) (n + 1))
    (hz_cyc : chainIncl A (n + 1) zA + chainIncl B (n + 1) zB ∈ cycles M (n + 1))
    (hz_cyc' : chainIncl A (n + 1) zA' + chainIncl B (n + 1) zB' ∈ cycles M (n + 1))
    (hcls : Homology.mk M (n + 1) ⟨chainIncl A (n + 1) zA + chainIncl B (n + 1) zB, hz_cyc⟩
      = Homology.mk M (n + 1) ⟨chainIncl A (n + 1) zA' + chainIncl B (n + 1) zB', hz_cyc'⟩)
    (w : zB ∈ SingularPairLES.relCycleLift (SingularExcisionIso.restr A B) n)
    (w' : zB' ∈ SingularPairLES.relCycleLift (SingularExcisionIso.restr A B) n) :
    kronecker β.1 (SingularFunctoriality.mapChain φout n (SingularFunctoriality.mapChain φin n
        (SingularPairLES.boundaryExtract (SingularExcisionIso.restr A B) n ⟨zB, w⟩)))
      = kronecker β.1 (SingularFunctoriality.mapChain φout n (SingularFunctoriality.mapChain φin n
        (SingularPairLES.boundaryExtract (SingularExcisionIso.restr A B) n ⟨zB', w'⟩))) := by
  rw [← kronecker_double_pullback φout φin n β.1, ← kronecker_double_pullback φout φin n β.1]
  exact SingularConnSquareLHSPairing.kronecker_boundaryExtract_class_invariant A B n hcov
    zA zA' zB zB' hz_cyc hz_cyc' hcls
    ⟨SingularKroneckerFunctoriality.pullbackCochainMap φin n
        (SingularKroneckerFunctoriality.pullbackCochainMap φout n β.1),
      SingularKroneckerFunctoriality.pullbackCochainMap_mem_ker φin n
        ⟨SingularKroneckerFunctoriality.pullbackCochainMap φout n β.1,
          SingularKroneckerFunctoriality.pullbackCochainMap_mem_ker φout n β⟩⟩

/-- **`legW` on a `Quotient.mk` is the `Homology.mk` of the pulled-back duality chain** (mini-brick G,
legW-HEADED like `cover_partition_of_legW` so the apex's concrete `legW … (mk g_rep)` matches the head
syntactically and is never whnf-reduced; over free carriers the `relativeDualityK`-on-`mk` defeq is
cheap). Exposes the W-leg's canonical cycle representative for the class-equality chain. -/
theorem legW_mk_eq {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : CompactsIn W) (a : LinearMap.ker (relCoboundaryₗ ((↑K.1 : Set ↑X)ᶜ) k)) :
    legW hW z₀ hz₀ K (Submodule.Quotient.mk a)
      = Homology.mk (sub W) (m + 1)
          ⟨SingularLocalDualityK.pullbackDualityₗ ((↑K.1 : Set ↑X)ᶜ) W
              (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K)
              (SingularOpenDualityCycle.fundCycleW_mem_W hW z₀ hz₀ K) a,
            SingularLocalDualityK.pullbackDualityₗ_mem_cycles _ _ _ _
              (SingularOpenDualityCycle.fundCycleW_boundary hW z₀ hz₀ K) a⟩ := by
  unfold legW
  rfl

/-- **`legW` evaluates on any subdivided-cap representative** (Brick H — the fact-(i) class-equality
feed). Any `sub W`-cycle whose ambient image is `cap g (Sdᵘ fund_K)` represents `legW (mk g)`: the
canonical W-leg rep `pullbackDualityₗ` and the subdivided cap differ by the REALIZED Brick-B bound
`cap g (Dᵤ fund_K)` — `(U∪V)`-supported (`iterHomotopy_mem` + cap-support), so the boundary lives in
`sub W` and `mk_eq_of_mem_boundaries` closes. Composed with `hzc0`/`hpart` at the apex this hands the
Brick-F canonical partition's class equality to the seam transport
(`kronecker_mapChain_boundaryExtract_class_invariant`). -/
theorem legW_iterate_cap_class_eq {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : CompactsIn W) (a : LinearMap.ker (relCoboundaryₗ ((↑K.1 : Set ↑X)ᶜ) k))
    (μ : ℕ) (zsum : SingularChain (sub W) (m + 1)) (hcyc : zsum ∈ cycles (sub W) (m + 1))
    (hamb : chainIncl W (m + 1) zsum
      = cap (m := m + 1) a.1.1 ((⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ]
          (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K))) :
    legW hW z₀ hz₀ K (Submodule.Quotient.mk a)
      = Homology.mk (sub W) (m + 1) ⟨zsum, hcyc⟩ := by
  rw [legW_mk_eq hW z₀ hz₀ K a]
  have hgc : coboundary X k a.1.1 = 0 := (SingularConnSquareRHSPairing.relCocycle_props a).1
  have hBB := cap_cocycle_singularSd_iterate_add_eq_boundary a.1.1 hgc a.1.2
    (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K) μ
    (SingularOpenDualityCycle.fundCycleW_boundary hW z₀ hz₀ K)
  have hTmem : cap (m := m + 1 + 1) a.1.1 (SingularSubdivision.iterHomotopy X (k + m + 1) μ
      (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K)) ∈ subspaceChains W (m + 1 + 1) :=
    SingularCapSupport.cap_mem_subspaceChains (m := m + 1 + 1) W a.1.1
      (SingularExcision.iterHomotopy_mem_subspaceChains
        (SingularOpenDualityCycle.fundCycleW_mem_W hW z₀ hz₀ K) μ)
  have hE : chainIncl W (m + 1 + 1)
      ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (m + 1 + 1)).symm ⟨_, hTmem⟩)
      = cap (m := m + 1 + 1) a.1.1 (SingularSubdivision.iterHomotopy X (k + m + 1) μ
          (SingularOpenDualityCycle.fundCycleW hW z₀ hz₀ K)) :=
    SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm W (m + 1 + 1) ⟨_, hTmem⟩
  refine mk_eq_of_mem_boundaries W _ _ _ _
    ⟨(SingularSubspaceChainsEquiv.subspaceChainsEquiv W (m + 1 + 1)).symm ⟨_, hTmem⟩, ?_⟩
  apply chainIncl_injective W (m + 1)
  rw [SingularRelativeHomologyMod2.chainIncl_chainBoundary, hE, map_add,
    SingularLocalDualityK.chainIncl_pullbackDualityₗ, hamb, ← hBB]
  exact add_comm _ _

/-- **The double-support δφ-kill** (Brick J — N2 steps II–IV; the crux's intrinsic-bound engine).
For a cocycle `a` vanishing on both cover legs and a `P`-supported chain `c` that is rel-`(A∪B)`
null-homologous via an AMBIENT bound (`c = ∂D + ρ`, `ρ ∈ C(A∪B)`, `D` unconstrained), the cap
`cap a c` is the boundary of a **`P`-supported** chain — the ambient `D` dissolves: small `D` over
the total cover `(P, A∪B)` (Brick E; `hcover`), collect the remainder
`b := c + ∂(D₁ + Dᵥc)` which is `C(P)`-supported BY THE EQUATION and `C(A∪B)`-supported BY
CONSTRUCTION, hence lives in the intersected legs (`subspaceChains_inf` + distributivity); its
leg-split (Brick E over `(P∩A, P∩B)`) kills `cap a (Sdᵏb)`, the homotopy bound `Dₖb` stays in
`C(P∩(A∪B)) ⊆ C(P)`, and the tail `Dₖ∂b = Dₖ∂c` dies leg-wise via `hbd` (T-additivity). Feeds the
fact-(i) crux with `a := δφ`, `P := U∩V`, `(A,B) := (LUᶜ, LVᶜ)`, `c := f₃ + Sd^jF φ₂'`. ℤ/2. -/
theorem cap_relCochains_pair_double_support_eq_boundary {A B P : Set ↑X}
    (hA : IsOpen A) (hB : IsOpen B) (hP : IsOpen P)
    (hcover : P ∪ (A ∪ B) = Set.univ) {k n : ℕ}
    (a : SingularCochain X k) (hac : coboundary X k a = 0)
    (haA : a ∈ relCochains A k) (haB : a ∈ relCochains B k)
    (c : SingularChain X (k + n + 1)) (hcP : c ∈ subspaceChains P (k + n + 1))
    (D : SingularChain X (k + n + 1 + 1)) (ρ : SingularChain X (k + n + 1))
    (hρ : ρ ∈ subspaceChains (A ∪ B) (k + n + 1))
    (heq : c = chainBoundary X (k + n + 1) D + ρ)
    (u' : SingularChain (sub A) (k + n)) (w' : SingularChain (sub B) (k + n))
    (hbd : chainBoundary X (k + n) c = chainIncl A (k + n) u' + chainIncl B (k + n) w') :
    ∃ E : SingularChain X (n + 1 + 1), E ∈ subspaceChains P (n + 1 + 1)
      ∧ cap (m := n + 1) a c = chainBoundary X (n + 1) E := by
  have hadd : ∀ (d : ℕ) (j : ℕ) (x y : SingularChain X d),
      SingularSubdivision.iterHomotopy X d j (x + y)
        = SingularSubdivision.iterHomotopy X d j x + SingularSubdivision.iterHomotopy X d j y := by
    intro d j x y
    simp [SingularSubdivision.iterHomotopy, map_add, Finset.sum_add_distrib]
  -- small D over the total cover (P, A∪B)
  have hDmem : D ∈ subspaceChains (P ∪ (A ∪ B)) (k + n + 1 + 1) :=
    SingularExcision.mem_subspaceChains_of_support (fun τ _ => by
      rw [hcover]; exact Set.subset_univ _)
  obtain ⟨ν, D₁, D₂, hD₁, hD₂, hDsplit⟩ :=
    exists_iterate_cover_split_amb hP (hA.union hB) D hDmem
  have hhD := SingularSubdivision.iterHomotopy_chainHomotopy X ν (k + n + 1) D
  -- ∂D = ∂D₁ + ∂D₂ + ∂(Dᵥ(∂D)) with Dᵥ(∂D) = Dᵥc + Dᵥρ (T-additive over heq)
  have hDbnd : chainBoundary X (k + n + 1) D
      = chainBoundary X (k + n + 1) D₁ + chainBoundary X (k + n + 1) D₂
        + chainBoundary X (k + n + 1)
            (SingularSubdivision.iterHomotopy X (k + n + 1) ν
              (chainBoundary X (k + n + 1) D)) := by
    have h1 := congrArg (chainBoundary X (k + n + 1)) hhD
    rw [map_add, map_add, chainBoundary_chainBoundary_apply, zero_add, hDsplit, map_add] at h1
    rw [h1]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  have hTsplit : SingularSubdivision.iterHomotopy X (k + n + 1) ν
      (chainBoundary X (k + n + 1) D)
      = SingularSubdivision.iterHomotopy X (k + n + 1) ν c
        + SingularSubdivision.iterHomotopy X (k + n + 1) ν ρ := by
    rw [show chainBoundary X (k + n + 1) D = c + ρ from by
        rw [heq]; abel_nf; simp only [two_smul, ZModModule.add_self, add_zero, zero_add],
      hadd]
  -- b defined by its C(A∪B)-formula (no c inside — rewrite-safe); C(P) comes from the equation
  set b : SingularChain X (k + n + 1) := ρ + chainBoundary X (k + n + 1) D₂
    + chainBoundary X (k + n + 1) (SingularSubdivision.iterHomotopy X (k + n + 1) ν ρ) with hbdef
  have hbeq : c = chainBoundary X (k + n + 1)
      (D₁ + SingularSubdivision.iterHomotopy X (k + n + 1) ν c) + b := by
    conv_lhs => rw [heq]
    rw [hDbnd, hTsplit, hbdef]
    simp only [map_add]
    abel
  have hb2 : b = c + chainBoundary X (k + n + 1)
      (D₁ + SingularSubdivision.iterHomotopy X (k + n + 1) ν c) := by
    have h2 := congrArg (· + chainBoundary X (k + n + 1)
      (D₁ + SingularSubdivision.iterHomotopy X (k + n + 1) ν c)) hbeq
    rw [h2]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  have hbP : b ∈ subspaceChains P (k + n + 1) := by
    rw [hb2]
    exact Submodule.add_mem _ hcP (chainBoundary_mem_subspaceChains _ (Submodule.add_mem _ hD₁
      (SingularExcision.iterHomotopy_mem_subspaceChains hcP ν)))
  have hbAB : b ∈ subspaceChains (A ∪ B) (k + n + 1) :=
    Submodule.add_mem _ (Submodule.add_mem _ hρ (chainBoundary_mem_subspaceChains _ hD₂))
      (chainBoundary_mem_subspaceChains _
        (SingularExcision.iterHomotopy_mem_subspaceChains hρ ν))
  have hbInter : b ∈ subspaceChains ((P ∩ A) ∪ (P ∩ B)) (k + n + 1) := by
    have h := Submodule.mem_inf.mpr ⟨hbP, hbAB⟩
    rw [SingularExcision.subspaceChains_inf, Set.inter_union_distrib_left] at h
    exact h
  -- leg-split b + Brick-C-style kill with the INTRINSIC bound
  obtain ⟨κ, bA, bB, hbA, hbB, hbSplit⟩ :=
    exists_iterate_cover_split_amb (hP.inter hA) (hP.inter hB) b hbInter
  have hhb := SingularSubdivision.iterHomotopy_chainHomotopy X κ (k + n) b
  have hkill1 : cap (m := n + 1) a ((⇑(SingularSubdivision.singularSd X (k + n + 1)))^[κ] b)
      = 0 := by
    rw [hbSplit, ← capₗ_apply, map_add, capₗ_apply, capₗ_apply,
      cap_relCochains_subspaceChains_eq_zero (m := n + 1) a haA _
        (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right (k + n + 1) hbA),
      cap_relCochains_subspaceChains_eq_zero (m := n + 1) a haB _
        (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right (k + n + 1) hbB),
      add_zero]
  have hkill2 : cap (m := n + 1) a (SingularSubdivision.iterHomotopy X (k + n) κ
      (chainBoundary X (k + n) b)) = 0 := by
    have hcbd : chainBoundary X (k + n) b = chainBoundary X (k + n) c := by
      rw [hb2, map_add, chainBoundary_chainBoundary_apply, add_zero]
    rw [hcbd, hbd, hadd, ← capₗ_apply, map_add, capₗ_apply, capₗ_apply,
      cap_relCochains_subspaceChains_eq_zero (m := n + 1) a haA _
        (SingularExcision.iterHomotopy_mem_subspaceChains ⟨u', rfl⟩ κ),
      cap_relCochains_subspaceChains_eq_zero (m := n + 1) a haB _
        (SingularExcision.iterHomotopy_mem_subspaceChains ⟨w', rfl⟩ κ),
      add_zero]
  -- assemble: cap a c = cap a (∂(D₁+Dᵥc)) + cap a b, both exact with C(P)-bounds
  have hcb : cap (m := n + 1) a c
      = cap (m := n + 1) a (chainBoundary X (k + n + 1)
          (D₁ + SingularSubdivision.iterHomotopy X (k + n + 1) ν c))
        + cap (m := n + 1) a b := by
    conv_lhs => rw [hbeq]
    rw [← capₗ_apply, map_add, capₗ_apply, capₗ_apply]
  have hb3' : (chainBoundary X (k + n + 1) (SingularSubdivision.iterHomotopy X (k + n + 1) κ b)
      + SingularSubdivision.iterHomotopy X (k + n) κ (chainBoundary X (k + n) b))
      + (⇑(SingularSubdivision.singularSd X (k + n + 1)))^[κ] b = b := by
    rw [hhb]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  have hcapb : cap (m := n + 1) a b = chainBoundary X (n + 1)
      (cap (m := n + 1 + 1) a (SingularSubdivision.iterHomotopy X (k + n + 1) κ b)) := by
    have hcc : cap (m := n + 1) a b
        = cap (m := n + 1) a ((chainBoundary X (k + n + 1)
            (SingularSubdivision.iterHomotopy X (k + n + 1) κ b)
          + SingularSubdivision.iterHomotopy X (k + n) κ (chainBoundary X (k + n) b))
          + (⇑(SingularSubdivision.singularSd X (k + n + 1)))^[κ] b) := by rw [hb3']
    rw [hcc, ← capₗ_apply, map_add, map_add, capₗ_apply, capₗ_apply, capₗ_apply, hkill1,
      hkill2, add_zero, add_zero]
    exact (chainBoundary_cap_cocycle_arg (m := n + 1) a hac _ (by omega)).symm
  have hE₁ : cap (m := n + 1) a (chainBoundary X (k + n + 1)
      (D₁ + SingularSubdivision.iterHomotopy X (k + n + 1) ν c))
      = chainBoundary X (n + 1) (cap (m := n + 1 + 1) a
          (D₁ + SingularSubdivision.iterHomotopy X (k + n + 1) ν c)) :=
    (chainBoundary_cap_cocycle_arg (m := n + 1) a hac _ (by omega)).symm
  refine ⟨cap (m := n + 1 + 1) a (D₁ + SingularSubdivision.iterHomotopy X (k + n + 1) ν c)
      + cap (m := n + 1 + 1) a (SingularSubdivision.iterHomotopy X (k + n + 1) κ b),
    Submodule.add_mem _
      (SingularCapSupport.cap_mem_subspaceChains (m := n + 1 + 1) P a (Submodule.add_mem _ hD₁
        (SingularExcision.iterHomotopy_mem_subspaceChains hcP ν)))
      (SingularCapSupport.cap_mem_subspaceChains (m := n + 1 + 1) P a
        (SingularMayerVietoris.subspaceChains_mono
          (Set.union_subset Set.inter_subset_left Set.inter_subset_left) (k + n + 1 + 1)
          (SingularExcision.iterHomotopy_mem_subspaceChains hbInter κ))), ?_⟩
  rw [hcb, hcapb, hE₁]
  simp only [map_add]

/-- **The two-fund three-set rel-comparison** (Brick K — N2 step I; the `(D, ρ)`-input for Brick J).
Over the SHARED `z₀`, the three-set third piece `f₃` (of the `Sdᵘ`-split of the `W₁`-fund) and the
`jF`-subdivided `W₂`-fund differ by an ambient boundary plus an `S`-supported slack: compose the two
`fundCycleW_chain_rel`s, the two `iterHomotopy` chain-homotopies, and the exact split witness as
ZERO-FORMS (`X + X = 0` over ℤ/2 — no substitution under `iterHomotopy`, dodging the
substitute-into-T trap) and sum; the shared `z₀`, `fund₁`, `fund₂`, `Sdᵘfund₁` atoms cancel in pairs.
At the apex: `S := infCompactᶜ`, `hK₁S` from `Kᶜ ⊆ infCompactᶜ`, `f₁/f₂`-memberships via the
three-set supports (`U∩LVᶜ ⊆ LVᶜ ⊆ S` etc.). -/
theorem fund_pair_three_set_rel_comparison {W₁ W₂ S : Set ↑X} (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    {k m : ℕ} (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K₁ : CompactsIn W₁) (K₂ : CompactsIn W₂)
    (hK₁S : ((↑K₁.1 : Set ↑X))ᶜ ⊆ S) (hK₂S : ((↑K₂.1 : Set ↑X))ᶜ ⊆ S)
    (μ jF : ℕ) (f₁ f₂ f₃ : SingularChain X (k + m + 1))
    (hf₁ : f₁ ∈ subspaceChains S (k + m + 1)) (hf₂ : f₂ ∈ subspaceChains S (k + m + 1))
    (hsplit : (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ]
        (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁) = f₁ + f₂ + f₃) :
    ∃ (D : SingularChain X (k + m + 1 + 1)) (ρ : SingularChain X (k + m + 1)),
      ρ ∈ subspaceChains S (k + m + 1)
      ∧ f₃ + (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[jF]
          (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂)
        = chainBoundary X (k + m + 1) D + ρ := by
  obtain ⟨η₁, a₁, heq₁, ha₁⟩ := fundCycleW_chain_rel hW₁ z₀ hz₀ K₁
  obtain ⟨η₂, a₂, heq₂, ha₂⟩ := fundCycleW_chain_rel hW₂ z₀ hz₀ K₂
  have hh₁ := SingularSubdivision.iterHomotopy_chainHomotopy X μ (k + m)
    (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)
  have hh₂ := SingularSubdivision.iterHomotopy_chainHomotopy X jF (k + m)
    (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂)
  refine ⟨SingularSubdivision.iterHomotopy X (k + m + 1) μ
        (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁) + η₁ + η₂
      + SingularSubdivision.iterHomotopy X (k + m + 1) jF
        (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂),
    f₁ + f₂ + SingularSubdivision.iterHomotopy X (k + m) μ
        (chainBoundary X (k + m) (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)) + a₁ + a₂
      + SingularSubdivision.iterHomotopy X (k + m) jF
        (chainBoundary X (k + m) (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂)), ?_, ?_⟩
  · refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ hf₁ hf₂) ?_) ?_) ?_) ?_
    · exact SingularMayerVietoris.subspaceChains_mono hK₁S (k + m + 1)
        (SingularExcision.iterHomotopy_mem_subspaceChains
          (SingularOpenDualityCycle.fundCycleW_boundary hW₁ z₀ hz₀ K₁) μ)
    · exact SingularMayerVietoris.subspaceChains_mono hK₁S (k + m + 1) ha₁
    · exact SingularMayerVietoris.subspaceChains_mono hK₂S (k + m + 1) ha₂
    · exact SingularMayerVietoris.subspaceChains_mono hK₂S (k + m + 1)
        (SingularExcision.iterHomotopy_mem_subspaceChains
          (SingularOpenDualityCycle.fundCycleW_boundary hW₂ z₀ hz₀ K₂) jF)
  · have z1 : (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ]
        (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁) + (f₁ + f₂ + f₃) = 0 := by
      rw [hsplit]; exact ZModModule.add_self _
    have z2 : (chainBoundary X (k + m + 1) (SingularSubdivision.iterHomotopy X (k + m + 1) μ
          (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁))
        + SingularSubdivision.iterHomotopy X (k + m) μ
          (chainBoundary X (k + m) (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)))
        + (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁
          + (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ]
            (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)) = 0 := by
      rw [hh₁]; exact ZModModule.add_self _
    have z3 : (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁ + z₀)
        + (chainBoundary X (k + m + 1) η₁ + a₁) = 0 := by
      rw [heq₁]; exact ZModModule.add_self _
    have z4 : (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂ + z₀)
        + (chainBoundary X (k + m + 1) η₂ + a₂) = 0 := by
      rw [heq₂]; exact ZModModule.add_self _
    have z5 : (chainBoundary X (k + m + 1) (SingularSubdivision.iterHomotopy X (k + m + 1) jF
          (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂))
        + SingularSubdivision.iterHomotopy X (k + m) jF
          (chainBoundary X (k + m) (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂)))
        + (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂
          + (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[jF]
            (SingularOpenDualityCycle.fundCycleW hW₂ z₀ hz₀ K₂)) = 0 := by
      rw [hh₂]; exact ZModModule.add_self _
    apply eq_of_sub_eq_zero
    rw [ZModModule.sub_eq_add]
    have S0 := congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·)
      (congrArg₂ (· + ·) z1 z2) z3) z4) z5
    simp only [add_zero] at S0
    rw [← S0, map_add, map_add, map_add]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]

/-- **The FREE two-fund three-set rel-comparison** (Brick K′ — the single-choice form of Brick K).
The second fund is a FREE chain `F₂` equipped with its rel-witness `(η₂, a₂, heq₂)` and boundary
support — so the apex can feed the **cast-presentation of the ONE pd-side `fundCycleW` choice**
(two independent `.choose`s of type-distinct existentials are never provably equal; the shared-`bF`
F-slot of `joint_cap_rcap_match_pairing` forces the cast-fund). Same zero-form summation as K. -/
theorem fund_pair_three_set_rel_comparison_free {W₁ S : Set ↑X} (hW₁ : IsOpen W₁)
    {k m : ℕ} (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K₁ : CompactsIn W₁) (hK₁S : ((↑K₁.1 : Set ↑X))ᶜ ⊆ S)
    (μ jF : ℕ) (f₁ f₂ f₃ : SingularChain X (k + m + 1))
    (hf₁ : f₁ ∈ subspaceChains S (k + m + 1)) (hf₂ : f₂ ∈ subspaceChains S (k + m + 1))
    (hsplit : (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ]
        (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁) = f₁ + f₂ + f₃)
    (F₂ : SingularChain X (k + m + 1)) (η₂ : SingularChain X (k + m + 1 + 1))
    (a₂ : SingularChain X (k + m + 1))
    (heq₂ : F₂ + z₀ = chainBoundary X (k + m + 1) η₂ + a₂)
    (ha₂ : a₂ ∈ subspaceChains S (k + m + 1))
    (hF₂bd : chainBoundary X (k + m) F₂ ∈ subspaceChains S (k + m)) :
    ∃ (D : SingularChain X (k + m + 1 + 1)) (ρ : SingularChain X (k + m + 1)),
      ρ ∈ subspaceChains S (k + m + 1)
      ∧ f₃ + (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[jF] F₂
        = chainBoundary X (k + m + 1) D + ρ := by
  obtain ⟨η₁, a₁, heq₁, ha₁⟩ := fundCycleW_chain_rel hW₁ z₀ hz₀ K₁
  have hh₁ := SingularSubdivision.iterHomotopy_chainHomotopy X μ (k + m)
    (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)
  have hh₂ := SingularSubdivision.iterHomotopy_chainHomotopy X jF (k + m) F₂
  refine ⟨SingularSubdivision.iterHomotopy X (k + m + 1) μ
        (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁) + η₁ + η₂
      + SingularSubdivision.iterHomotopy X (k + m + 1) jF F₂,
    f₁ + f₂ + SingularSubdivision.iterHomotopy X (k + m) μ
        (chainBoundary X (k + m) (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)) + a₁ + a₂
      + SingularSubdivision.iterHomotopy X (k + m) jF
        (chainBoundary X (k + m) F₂), ?_, ?_⟩
  · refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ hf₁ hf₂) ?_) ?_) ?_) ?_
    · exact SingularMayerVietoris.subspaceChains_mono hK₁S (k + m + 1)
        (SingularExcision.iterHomotopy_mem_subspaceChains
          (SingularOpenDualityCycle.fundCycleW_boundary hW₁ z₀ hz₀ K₁) μ)
    · exact SingularMayerVietoris.subspaceChains_mono hK₁S (k + m + 1) ha₁
    · exact ha₂
    · exact SingularExcision.iterHomotopy_mem_subspaceChains hF₂bd jF
  · have z1 : (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ]
        (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁) + (f₁ + f₂ + f₃) = 0 := by
      rw [hsplit]; exact ZModModule.add_self _
    have z2 : (chainBoundary X (k + m + 1) (SingularSubdivision.iterHomotopy X (k + m + 1) μ
          (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁))
        + SingularSubdivision.iterHomotopy X (k + m) μ
          (chainBoundary X (k + m) (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)))
        + (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁
          + (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ]
            (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁)) = 0 := by
      rw [hh₁]; exact ZModModule.add_self _
    have z3 : (SingularOpenDualityCycle.fundCycleW hW₁ z₀ hz₀ K₁ + z₀)
        + (chainBoundary X (k + m + 1) η₁ + a₁) = 0 := by
      rw [heq₁]; exact ZModModule.add_self _
    have z4 : (F₂ + z₀) + (chainBoundary X (k + m + 1) η₂ + a₂) = 0 := by
      rw [heq₂]; exact ZModModule.add_self _
    have z5 : (chainBoundary X (k + m + 1) (SingularSubdivision.iterHomotopy X (k + m + 1) jF F₂)
        + SingularSubdivision.iterHomotopy X (k + m) jF (chainBoundary X (k + m) F₂))
        + (F₂ + (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[jF] F₂) = 0 := by
      rw [hh₂]; exact ZModModule.add_self _
    apply eq_of_sub_eq_zero
    rw [ZModModule.sub_eq_add]
    have S0 := congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·)
      (congrArg₂ (· + ·) z1 z2) z3) z4) z5
    simp only [add_zero] at S0
    rw [← S0, map_add, map_add, map_add]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]

omit [T2Space ↑X] in
/-- **Degree-cast transports membership** (generic `subst`-helper — whnf-free by genericity). -/
theorem subspaceChains_cast_mem {a b : ℕ} (e : a = b) {S : Set ↑X}
    {c : SingularChain X a} (hc : c ∈ subspaceChains S a) :
    (e ▸ c : SingularChain X b) ∈ subspaceChains S b := by subst e; exact hc

omit [T2Space ↑X] in
/-- **Degree-cast commutes with `∂`** (generic `subst`-helper; proof-irrelevance collapses the
residual self-cast). -/
theorem chainBoundary_cast {a b : ℕ} (e : a + 1 = b + 1) (e' : a = b)
    (c : SingularChain X (a + 1)) :
    chainBoundary X b (e ▸ c) = e' ▸ chainBoundary X a c := by subst e'; rfl

omit [T2Space ↑X] in
/-- **`cast` along a `congrArg`-lifted degree equality is the `▸`-recast** (generic bridge between
the two cast spellings; `subst` + proof-irrelevance). -/
theorem singularChain_cast_eq_rec {a b : ℕ} (e : a = b) (c : SingularChain X a) :
    cast (congrArg (SingularChain X) e) c = e ▸ c := by subst e; rfl

omit [T2Space ↑X] in
/-- **Set-recast of a rel-cocycle preserves the raw cochain** (generic `subst`-helper — the `hgg`
feed at the apex: `(hKeq ▸ g_rep).1.1 = g_rep.1.1`). -/
theorem ker_relCoboundary_cast_coe {S T : Set ↑X} (e : S = T) {n : ℕ}
    (x : LinearMap.ker (relCoboundaryₗ S n)) :
    (((e ▸ x : LinearMap.ker (relCoboundaryₗ T n)) : relCochains T n) : SingularCochain X n)
      = ((x : relCochains S n) : SingularCochain X n) := by subst e; rfl

omit [T2Space ↑X] in
/-- **The cast-fund feed** (whnf-free by genericity — `cases h` collapses every `cast` before any
term must reduce, exactly the `exists_cast_cover_V_projection` discipline). Packages ALL the
`F₂`-facts the fact-(i) discharge needs about the CAST presentation of an off-frame fund-object:
support membership, boundary support, and the rel-witness `(η', a')` — transported across the
degree recast in ONE `cases`. -/
theorem cast_fund_feed {n₂ n₁ : ℕ} (h : n₂ = n₁) (z z₀c a : SingularChain X (n₂ + 1))
    (η : SingularChain X (n₂ + 1 + 1)) {S T : Set ↑X}
    (hzmem : z ∈ subspaceChains T (n₂ + 1))
    (hzbd : chainBoundary X n₂ z ∈ subspaceChains S n₂)
    (heq : z + z₀c = chainBoundary X (n₂ + 1) η + a)
    (ha : a ∈ subspaceChains S (n₂ + 1)) :
    (cast (congrArg (SingularChain X) (congrArg (· + 1) h)) z ∈ subspaceChains T (n₁ + 1))
    ∧ (chainBoundary X n₁ (cast (congrArg (SingularChain X) (congrArg (· + 1) h)) z)
        ∈ subspaceChains S n₁)
    ∧ ∃ (η' : SingularChain X (n₁ + 1 + 1)) (a' : SingularChain X (n₁ + 1)),
        cast (congrArg (SingularChain X) (congrArg (· + 1) h)) z
            + cast (congrArg (SingularChain X) (congrArg (· + 1) h)) z₀c
          = chainBoundary X (n₁ + 1) η' + a'
        ∧ a' ∈ subspaceChains S (n₁ + 1) := by
  cases h
  exact ⟨hzmem, hzbd, η, a, heq, ha⟩

/-- **The N2 δφ-kill** (Brick L — N2 steps I–IV assembled on the cast frame: Brick K → generic
cast transports → Brick J). For `c := f₃ + Sd^jF fund_K₂` (the three-set third piece + the
`jF`-subdivided `K₂`-fund), the `δφ`-cap (`φ := cochainSplit LUᶜ g`, the ∩-form cocycle's U-side
split) is the boundary of a **`C(U∩V)`-supported** chain — the crux's only genuine bounding datum,
INTRINSIC per the excision-gap constraint. `(D, ρ)` from Brick K at `S := LUᶜ ∪ LVᶜ`; the ∂c-legs
from the `hIsplit`-∂ rearrangement + `hFsplit`; Brick J with `(A, B, P) := (LUᶜ, LVᶜ, U∩V)`,
`hcover` from `LU∩LV ⊆ U∩V`. -/
theorem fact_i_n2_kill {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ) (hLUU : LU ⊆ U) (hLVV : LV ⊆ V)
    {N p : ℕ}
    (g : LinearMap.ker (relCoboundaryₗ (LUᶜ ∩ LVᶜ) (N + 1)))
    (z₀ : SingularChain X (N + 1 + (p + 1) + 1))
    (hz₀ : chainBoundary X (N + 1 + (p + 1)) z₀ = 0)
    (K₁ : CompactsIn (U ∪ V)) (K₂ : CompactsIn (U ∩ V))
    (hK₁ : ((↑K₁.1 : Set ↑X))ᶜ = LUᶜ ∩ LVᶜ)
    (hK₂ : ((↑K₂.1 : Set ↑X))ᶜ = LUᶜ ∪ LVᶜ)
    (μ jF : ℕ) (f₁ f₂ f₃ : SingularChain X (N + 1 + (p + 1) + 1))
    (hf₁ : f₁ ∈ subspaceChains (U ∩ LVᶜ) (N + 1 + (p + 1) + 1))
    (hf₂ : f₂ ∈ subspaceChains (V ∩ LUᶜ) (N + 1 + (p + 1) + 1))
    (hf₃ : f₃ ∈ subspaceChains (U ∩ V) (N + 1 + (p + 1) + 1))
    (hIsplit : (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[μ]
        (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁) = f₁ + f₂ + f₃)
    (F₂ : SingularChain X (N + 1 + (p + 1) + 1))
    (hF₂mem : F₂ ∈ subspaceChains (U ∩ V) (N + 1 + (p + 1) + 1))
    (η₂ : SingularChain X (N + 1 + (p + 1) + 1 + 1)) (a₂ : SingularChain X (N + 1 + (p + 1) + 1))
    (heq₂ : F₂ + z₀ = chainBoundary X (N + 1 + (p + 1) + 1) η₂ + a₂)
    (ha₂ : a₂ ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + (p + 1) + 1))
    (hF₂bd : chainBoundary X (N + 1 + (p + 1)) F₂
      ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + (p + 1)))
    (aF : SingularChain (sub (LUᶜ ∩ (U ∩ V))) (N + 1 + (p + 1)))
    (bF : SingularChain (sub (LVᶜ ∩ (U ∩ V))) (N + 1 + (p + 1)))
    (hFsplit : chainBoundary X (N + 1 + (p + 1))
        ((⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
          F₂)
      = chainIncl _ (N + 1 + (p + 1)) aF + chainIncl _ (N + 1 + (p + 1)) bF)
    (h : N + 1 + (p + 1) + 1 = N + 1 + 1 + (p + 1)) :
    ∃ E : SingularChain X (p + 1 + 1), E ∈ subspaceChains (U ∩ V) (p + 1 + 1)
      ∧ cap (m := p + 1) (coboundary X (N + 1) (cochainSplit LUᶜ (N + 1) g.1.1))
          (h ▸ (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
            F₂))
        = chainBoundary X (p + 1) E := by
  have hgc : coboundary X (N + 1) g.1.1 = 0 :=
    (SingularConnSquareRHSPairing.relCocycle_props g).1
  -- Brick K at the uncast frame: (D, ρ) with S := LUᶜ ∪ LVᶜ
  have hK₁S : ((↑K₁.1 : Set ↑X))ᶜ ⊆ LUᶜ ∪ LVᶜ := by
    rw [hK₁]; exact fun x hx => Or.inl hx.1
  obtain ⟨D, ρ, hρ, heq⟩ :=
    fund_pair_three_set_rel_comparison_free (S := LUᶜ ∪ LVᶜ) (k := N + 1) (m := p + 1)
      (hU.union hV) z₀ hz₀ K₁ hK₁S μ jF f₁ f₂ f₃
      (SingularMayerVietoris.subspaceChains_mono (fun _ hx => Or.inr hx.2) _ hf₁)
      (SingularMayerVietoris.subspaceChains_mono (fun _ hx => Or.inl hx.2) _ hf₂)
      hIsplit F₂ η₂ a₂ heq₂ ha₂ hF₂bd
  -- the uncast ∂c-legs: u ∈ C(LUᶜ) collects Sd^μ∂fund₁ + ∂f₂ + aFamb; w ∈ C(LVᶜ) collects ∂f₁ + bFamb
  have hbdIsplit := congrArg (chainBoundary X (N + 1 + (p + 1))) hIsplit
  rw [SingularSubdivision.singularSd_iterate_chainBoundary, map_add, map_add] at hbdIsplit
  have hf₃bd : chainBoundary X (N + 1 + (p + 1)) f₃
      = (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1))))^[μ]
          (chainBoundary X (N + 1 + (p + 1))
            (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁))
        + chainBoundary X (N + 1 + (p + 1)) f₁ + chainBoundary X (N + 1 + (p + 1)) f₂ := by
    rw [hbdIsplit]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  have hSdmem : (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1))))^[μ]
      (chainBoundary X (N + 1 + (p + 1))
        (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁))
      ∈ subspaceChains LUᶜ (N + 1 + (p + 1)) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _
      (SingularExcision.singularSd_iterate_mem_subspaceChains
        (hK₁ ▸ SingularOpenDualityCycle.fundCycleW_boundary (hU.union hV) z₀ hz₀ K₁) μ)
  have hf2bdmem : chainBoundary X (N + 1 + (p + 1)) f₂
      ∈ subspaceChains LUᶜ (N + 1 + (p + 1)) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right _
      (chainBoundary_mem_subspaceChains _ hf₂)
  have haFmem : chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) aF
      ∈ subspaceChains LUᶜ (N + 1 + (p + 1)) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ ⟨aF, rfl⟩
  have hf1bdmem : chainBoundary X (N + 1 + (p + 1)) f₁
      ∈ subspaceChains LVᶜ (N + 1 + (p + 1)) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right _
      (chainBoundary_mem_subspaceChains _ hf₁)
  have hbFmem' : chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) bF
      ∈ subspaceChains LVᶜ (N + 1 + (p + 1)) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ ⟨bF, rfl⟩
  set u : SingularChain X (N + 1 + (p + 1)) :=
    (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1))))^[μ]
      (chainBoundary X (N + 1 + (p + 1))
        (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁))
    + chainBoundary X (N + 1 + (p + 1)) f₂
    + chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) aF with hudef
  set w : SingularChain X (N + 1 + (p + 1)) :=
    chainBoundary X (N + 1 + (p + 1)) f₁
    + chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) bF with hwdef
  have humem : u ∈ subspaceChains LUᶜ (N + 1 + (p + 1)) :=
    Submodule.add_mem _ (Submodule.add_mem _ hSdmem hf2bdmem) haFmem
  have hwmem : w ∈ subspaceChains LVᶜ (N + 1 + (p + 1)) :=
    Submodule.add_mem _ hf1bdmem hbFmem'
  have hbd_uncast : chainBoundary X (N + 1 + (p + 1))
      (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
        F₂) = u + w := by
    rw [map_add, hFsplit, hf₃bd, hudef, hwdef]
    abel
  -- cast transports to the (N+1+1)-frame
  have h' : N + 1 + (p + 1) = N + 1 + 1 + p := by omega
  have hD : N + 1 + (p + 1) + 1 + 1 = N + 1 + 1 + (p + 1) + 1 := by omega
  have hDcast : chainBoundary X (N + 1 + 1 + (p + 1)) (hD ▸ D)
      = h ▸ chainBoundary X (N + 1 + (p + 1) + 1) D :=
    chainBoundary_cast hD h D
  have heq' : (h ▸ (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
        F₂)
        : SingularChain X (N + 1 + 1 + (p + 1)))
      = chainBoundary X (N + 1 + 1 + (p + 1)) (hD ▸ D) + (h ▸ ρ) := by
    rw [hDcast, ← singularChain_cast_add, ← heq]
  have hρ' : (h ▸ ρ : SingularChain X (N + 1 + 1 + (p + 1)))
      ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + 1 + (p + 1)) :=
    subspaceChains_cast_mem h hρ
  have hcP : (h ▸ (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
        F₂)
        : SingularChain X (N + 1 + 1 + (p + 1)))
      ∈ subspaceChains (U ∩ V) (N + 1 + 1 + (p + 1)) :=
    subspaceChains_cast_mem h (Submodule.add_mem _ hf₃
      (SingularExcision.singularSd_iterate_mem_subspaceChains hF₂mem jF))
  have hbd' : chainBoundary X (N + 1 + 1 + p)
      (h ▸ (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
        F₂))
      = (h' ▸ u) + (h' ▸ w) :=
    (chainBoundary_cast h h' _).trans (by rw [hbd_uncast, singularChain_cast_add])
  have humem' : (h' ▸ u : SingularChain X (N + 1 + 1 + p))
      ∈ subspaceChains LUᶜ (N + 1 + 1 + p) := subspaceChains_cast_mem h' humem
  have hwmem' : (h' ▸ w : SingularChain X (N + 1 + 1 + p))
      ∈ subspaceChains LVᶜ (N + 1 + 1 + p) := subspaceChains_cast_mem h' hwmem
  rw [subspaceChains, LinearMap.mem_range] at humem' hwmem'
  obtain ⟨uS, huS⟩ := humem'
  obtain ⟨wS, hwS⟩ := hwmem'
  -- Brick J on the cast frame
  have hcover : (U ∩ V) ∪ (LUᶜ ∪ LVᶜ) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hxU : x ∈ LU
    · by_cases hxV : x ∈ LV
      · exact Or.inl ⟨hLUU hxU, hLVV hxV⟩
      · exact Or.inr (Or.inr hxV)
    · exact Or.inr (Or.inl hxU)
  obtain ⟨E, hE, hcap⟩ :=
    cap_relCochains_pair_double_support_eq_boundary hLUc hLVc (hU.inter hV) hcover
      (k := N + 1 + 1) (n := p)
      (coboundary X (N + 1) (cochainSplit LUᶜ (N + 1) g.1.1))
      (coboundary_comp_coboundary X (N + 1) _)
      (cochainSplit_coboundary_mem_U LUᶜ (N + 1) g.1.1)
      (cochainSplit_coboundary_mem_V LUᶜ LVᶜ (N + 1) g.1.1 g.1.2 hgc)
      (h ▸ (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
        F₂))
      hcP (hD ▸ D) (h ▸ ρ) hρ' heq' uS wS (by rw [hbd', ← huS, ← hwS])
  exact ⟨E, hE, hcap⟩

/-- **The fact-(i) ambient core** (Brick M — 18th-push steps 1–7 TOTAL, over the σR-cap-engine).
The ambient boundary of the canonical `fB`-cap plus the ambient `bF`-cap is the boundary of a
**`C(U∩V)`-supported** chain: (1–2) the subdivided-fund cap is a CYCLE (cocycle-Leibniz + the
`K₁ᶜ`-kill via `hK₁`), so `∂(cap g fB) = ∂(cap g f₁) = cap g ∂f₁` (ℤ/2 flip + cocycle-Leibniz);
(3–5) `cap g ∂f₁ + cap g bFamb = cap g w` with `w` the `LVᶜ`-leg of the `∂c`-split, and the
σR-cap-engine (`cap_coboundary_cochainSplit_eq`) gives `cap δφ (h ▸ c) = cap g w + ∂(cap φ c)`;
(6) Brick L kills `cap δφ (h ▸ c) = ∂E₂` with `E₂ ∈ C(U∩V)`; (7) total:
`∂(cap g fB) + cap g bFamb = ∂(E₂ + cap φ c)`, both summands `C(U∩V)`-supported (cap-support).
Statement CAST-FREE — the `h ▸` lives only inside. -/
theorem fact_i_ambient_core {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ) (hLUU : LU ⊆ U) (hLVV : LV ⊆ V)
    {N p : ℕ}
    (g : LinearMap.ker (relCoboundaryₗ (LUᶜ ∩ LVᶜ) (N + 1)))
    (z₀ : SingularChain X (N + 1 + (p + 1) + 1))
    (hz₀ : chainBoundary X (N + 1 + (p + 1)) z₀ = 0)
    (K₁ : CompactsIn (U ∪ V)) (K₂ : CompactsIn (U ∩ V))
    (hK₁ : ((↑K₁.1 : Set ↑X))ᶜ = LUᶜ ∩ LVᶜ)
    (hK₂ : ((↑K₂.1 : Set ↑X))ᶜ = LUᶜ ∪ LVᶜ)
    (μ jF : ℕ) (f₁ f₂ f₃ : SingularChain X (N + 1 + (p + 1) + 1))
    (hf₁ : f₁ ∈ subspaceChains (U ∩ LVᶜ) (N + 1 + (p + 1) + 1))
    (hf₂ : f₂ ∈ subspaceChains (V ∩ LUᶜ) (N + 1 + (p + 1) + 1))
    (hf₃ : f₃ ∈ subspaceChains (U ∩ V) (N + 1 + (p + 1) + 1))
    (hIsplit : (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[μ]
        (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁) = f₁ + f₂ + f₃)
    (F₂ : SingularChain X (N + 1 + (p + 1) + 1))
    (hF₂mem : F₂ ∈ subspaceChains (U ∩ V) (N + 1 + (p + 1) + 1))
    (η₂ : SingularChain X (N + 1 + (p + 1) + 1 + 1)) (a₂ : SingularChain X (N + 1 + (p + 1) + 1))
    (heq₂ : F₂ + z₀ = chainBoundary X (N + 1 + (p + 1) + 1) η₂ + a₂)
    (ha₂ : a₂ ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + (p + 1) + 1))
    (hF₂bd : chainBoundary X (N + 1 + (p + 1)) F₂
      ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + (p + 1)))
    (aF : SingularChain (sub (LUᶜ ∩ (U ∩ V))) (N + 1 + (p + 1)))
    (bF : SingularChain (sub (LVᶜ ∩ (U ∩ V))) (N + 1 + (p + 1)))
    (hFsplit : chainBoundary X (N + 1 + (p + 1))
        ((⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
          F₂)
      = chainIncl _ (N + 1 + (p + 1)) aF + chainIncl _ (N + 1 + (p + 1)) bF) :
    ∃ E : SingularChain X (p + 1 + 1), E ∈ subspaceChains (U ∩ V) (p + 1 + 1)
      ∧ chainBoundary X (p + 1) (cap (m := p + 1 + 1) g.1.1 (f₂ + f₃))
          + cap (m := p + 1) g.1.1 (chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) bF)
        = chainBoundary X (p + 1) E := by
  have hgc : coboundary X (N + 1) g.1.1 = 0 :=
    (SingularConnSquareRHSPairing.relCocycle_props g).1
  -- the ∂c-legs (as in Brick L, uncast)
  have hbdIsplit := congrArg (chainBoundary X (N + 1 + (p + 1))) hIsplit
  rw [SingularSubdivision.singularSd_iterate_chainBoundary, map_add, map_add] at hbdIsplit
  have hf₃bd : chainBoundary X (N + 1 + (p + 1)) f₃
      = (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1))))^[μ]
          (chainBoundary X (N + 1 + (p + 1))
            (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁))
        + chainBoundary X (N + 1 + (p + 1)) f₁ + chainBoundary X (N + 1 + (p + 1)) f₂ := by
    rw [hbdIsplit]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  have hSdKmem : (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1))))^[μ]
      (chainBoundary X (N + 1 + (p + 1))
        (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁))
      ∈ subspaceChains (LUᶜ ∩ LVᶜ) (N + 1 + (p + 1)) :=
    SingularExcision.singularSd_iterate_mem_subspaceChains
      (hK₁ ▸ SingularOpenDualityCycle.fundCycleW_boundary (hU.union hV) z₀ hz₀ K₁) μ
  set u : SingularChain X (N + 1 + (p + 1)) :=
    (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1))))^[μ]
      (chainBoundary X (N + 1 + (p + 1))
        (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁))
    + chainBoundary X (N + 1 + (p + 1)) f₂
    + chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) aF with hudef
  set w : SingularChain X (N + 1 + (p + 1)) :=
    chainBoundary X (N + 1 + (p + 1)) f₁
    + chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) bF with hwdef
  have humem : u ∈ subspaceChains LUᶜ (N + 1 + (p + 1)) :=
    Submodule.add_mem _ (Submodule.add_mem _
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ hSdKmem)
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right _
        (chainBoundary_mem_subspaceChains _ hf₂)))
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ ⟨aF, rfl⟩)
  have hwmem : w ∈ subspaceChains LVᶜ (N + 1 + (p + 1)) :=
    Submodule.add_mem _
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right _
        (chainBoundary_mem_subspaceChains _ hf₁))
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ ⟨bF, rfl⟩)
  have hbd_uncast : chainBoundary X (N + 1 + (p + 1))
      (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
        F₂) = u + w := by
    rw [map_add, hFsplit, hf₃bd, hudef, hwdef]
    abel
  -- the σR-cap-engine + Brick L
  have h : N + 1 + (p + 1) + 1 = N + 1 + 1 + (p + 1) := by omega
  have hengine := cap_coboundary_cochainSplit_eq LUᶜ LVᶜ g
    (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
      F₂) u w humem hwmem hbd_uncast h
  obtain ⟨E₂, hE₂mem, hE₂⟩ := fact_i_n2_kill hU hV hLUc hLVc hLUU hLVV g z₀ hz₀ K₁ K₂ hK₁ hK₂
    μ jF f₁ f₂ f₃ hf₁ hf₂ hf₃ hIsplit F₂ hF₂mem η₂ a₂ heq₂ ha₂ hF₂bd aF bF hFsplit h
  have hgw : cap (m := p + 1) g.1.1 w = chainBoundary X (p + 1) E₂
      + chainBoundary X (p + 1) (cap (m := p + 1 + 1) (cochainSplit LUᶜ (N + 1) g.1.1)
          (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
            F₂)) := by
    have h0 := hE₂.symm.trans hengine
    rw [h0]
    abel_nf
    simp only [two_smul, ZModModule.add_self, zero_add, add_zero]
  -- the cycle-flip: ∂(cap g fB) = cap g ∂f₁
  have hsplit' : (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[μ]
      (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁) = f₁ + (f₂ + f₃) :=
    hIsplit.trans (add_assoc f₁ f₂ f₃)
  have hcyc0 : chainBoundary X (p + 1) (cap (m := p + 1 + 1) g.1.1
      ((⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[μ]
        (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁))) = 0 := by
    rw [chainBoundary_cap_cocycle_arg (m := p + 1) g.1.1 hgc _ (by omega),
      SingularSubdivision.singularSd_iterate_chainBoundary]
    exact cap_relCochains_subspaceChains_eq_zero (m := p + 1) g.1.1 g.1.2 _ hSdKmem
  have hflip : chainBoundary X (p + 1) (cap (m := p + 1 + 1) g.1.1 (f₂ + f₃))
      = cap (m := p + 1) g.1.1 (chainBoundary X (N + 1 + (p + 1)) f₁) := by
    have h1 : cap (m := p + 1 + 1) g.1.1
        ((⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[μ]
          (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁))
        = cap (m := p + 1 + 1) g.1.1 f₁ + cap (m := p + 1 + 1) g.1.1 (f₂ + f₃) := by
      rw [hsplit', map_add]
    have h2 := congrArg (chainBoundary X (p + 1)) h1
    rw [hcyc0, map_add] at h2
    have h3 : chainBoundary X (p + 1) (cap (m := p + 1 + 1) g.1.1 (f₂ + f₃))
        = chainBoundary X (p + 1) (cap (m := p + 1 + 1) g.1.1 f₁) := by
      apply eq_of_sub_eq_zero
      rw [ZModModule.sub_eq_add, h2]
      abel
    exact h3.trans (chainBoundary_cap_cocycle_arg (m := p + 1) g.1.1 hgc f₁ (by omega))
  -- total assembly
  refine ⟨E₂ + cap (m := p + 1 + 1) (cochainSplit LUᶜ (N + 1) g.1.1)
      (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
        F₂),
    Submodule.add_mem _ hE₂mem
      (SingularCapSupport.cap_mem_subspaceChains (m := p + 1 + 1) (U ∩ V) _
        (Submodule.add_mem _ hf₃
          (SingularExcision.singularSd_iterate_mem_subspaceChains hF₂mem jF))), ?_⟩
  rw [hflip, map_add,
    show cap (m := p + 1) g.1.1 (chainBoundary X (N + 1 + (p + 1)) f₁)
        + cap (m := p + 1) g.1.1 (chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) bF)
      = cap (m := p + 1) g.1.1 w from by rw [hwdef, map_add]]
  exact hgw

/-- **Fact-(i) STAGE 1** (the canonical-partition package — Bricks I + F′ + H in ONE existential,
free degrees `{k m}` so every unification is syntactic). For the `K₁`-fund of `W = U ∪ V`: a
three-set split `Sd^μ fund = f₁ + f₂ + f₃` subordinate to `(U∩LVᶜ, V∩LUᶜ, U∩V)`, together with the
cap-induced canonical partition `(zA, zB)` of `cap gW (Sd^μ fund)` whose legs realize
`cap gW f₁ / cap gW (f₂+f₃)`, its cycle membership, and the class equality to `legW (mk gW)`.
Extracted so `fact_i_discharge` consumes ONE `obtain` — the discharge's own statement elaboration
leaves no budget for the Brick-I/F′ unifications in-body (the cumulative-heartbeat law at the
discharge level). -/
theorem fact_i_stage1 {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ) (hLUU : LU ⊆ U) (hLVV : LV ⊆ V)
    {k m : ℕ}
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K₁ : CompactsIn (U ∪ V))
    (gW : LinearMap.ker (relCoboundaryₗ (((↑K₁.1 : Set ↑X))ᶜ) k)) :
    ∃ (μ : ℕ) (f₁ f₂ f₃ : SingularChain X (k + m + 1)),
      f₁ ∈ subspaceChains (U ∩ LVᶜ) (k + m + 1)
      ∧ f₂ ∈ subspaceChains (V ∩ LUᶜ) (k + m + 1)
      ∧ f₃ ∈ subspaceChains (U ∩ V) (k + m + 1)
      ∧ (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ]
          (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁) = f₁ + f₂ + f₃
      ∧ ∃ (zA : SingularChain (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (m + 1))
          (zB : SingularChain (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (m + 1)),
          chainIncl (U ∪ V) (m + 1) (chainIncl _ (m + 1) zA) = cap (m := m + 1) gW.1.1 f₁
          ∧ chainIncl (U ∪ V) (m + 1) (chainIncl _ (m + 1) zB)
              = cap (m := m + 1) gW.1.1 (f₂ + f₃)
          ∧ ∃ (hcyc : chainIncl _ (m + 1) zA + chainIncl _ (m + 1) zB
                ∈ cycles (sub (U ∪ V)) (m + 1)),
              legW (hU.union hV) z₀ hz₀ K₁ (Submodule.Quotient.mk gW)
                = Homology.mk (sub (U ∪ V)) (m + 1) ⟨_, hcyc⟩ := by
  have hgWc : coboundary X k gW.1.1 = 0 :=
    (SingularConnSquareRHSPairing.relCocycle_props gW).1
  obtain ⟨μ, f₁, f₂, f₃, hf₁, hf₂, hf₃, hIsplit⟩ :=
    exists_iterate_three_set_split_amb hU hV hLUc hLVc hLUU hLVV
      (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁)
      (SingularOpenDualityCycle.fundCycleW_mem_W (hU.union hV) z₀ hz₀ K₁)
  have hsplit' : (⇑(SingularSubdivision.singularSd X (k + m + 1)))^[μ]
      (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁) = f₁ + (f₂ + f₃) :=
    hIsplit.trans (add_assoc f₁ f₂ f₃)
  obtain ⟨zA, zB, hzA, hzB, hcyc⟩ :=
    cap_induced_partition_of_split (U := U) (V := V) (k := k) (m := m) gW.1.1 hgWc gW.1.2
      (SingularOpenDualityCycle.fundCycleW (hU.union hV) z₀ hz₀ K₁) μ
      (SingularOpenDualityCycle.fundCycleW_boundary (hU.union hV) z₀ hz₀ K₁)
      f₁ (f₂ + f₃)
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ hf₁)
      (Submodule.add_mem _
        (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ hf₂)
        (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right _ hf₃))
      hsplit'
  refine ⟨μ, f₁, f₂, f₃, hf₁, hf₂, hf₃, hIsplit, zA, zB, hzA, hzB, hcyc, ?_⟩
  exact legW_iterate_cap_class_eq (hU.union hV) z₀ hz₀ K₁ gW μ _ hcyc
    (by rw [map_add, hzA, hzB, hsplit']; simp only [map_add])

/-- **SUN FACT (i), discharged** (the fact-(i) closer — 18th-push steps 0–7 assembled over the
13-brick substrate; free variables throughout, applied at the apex with ONE `exact`). The seam
pairing of the GIVEN legW-partition equals the pairing against the cap of the fine V-leg:
(0) three-set split (Brick I) of the K₁-fund; (1–2) canonical cap-induced partition (Brick F′) +
class-equality (Bricks B/H via `legW_iterate_cap_class_eq`) + seam transport (Brick-A-conjugated);
(3) canonical-seam evaluation (`chainIncl_seam_boundaryExtract`); (4–5) the V-kills + Leibniz + the
(χ)-W-form; (6) rel-comparison (Brick K) → double-support kill (Brick J); (7) boundaries-membership
+ β-kill. STATEMENT DRAFT — proof to be filled per the 21st-push checklist. -/
theorem fact_i_discharge {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ) (hLUU : LU ⊆ U) (hLVV : LV ⊆ V)
    {N p : ℕ}
    (g : LinearMap.ker (relCoboundaryₗ (LUᶜ ∩ LVᶜ) (N + 1)))
    (z₀ : SingularChain X (N + 1 + (p + 1) + 1))
    (hz₀ : chainBoundary X (N + 1 + (p + 1)) z₀ = 0)
    (K₁ : CompactsIn (U ∪ V)) (K₂ : CompactsIn (U ∩ V))
    (gW : LinearMap.ker (relCoboundaryₗ ((↑K₁.1 : Set ↑X))ᶜ (N + 1)))
    (hgg : g.1.1 = gW.1.1)
    (hK₁ : ((↑K₁.1 : Set ↑X))ᶜ = LUᶜ ∩ LVᶜ)
    (hK₂ : ((↑K₂.1 : Set ↑X))ᶜ = LUᶜ ∪ LVᶜ)
    (hcov : (⋃ W ∈ ({(Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))), Subtype.val ⁻¹' V} :
        Set (Set ↑(sub (U ∪ V)))), interior W) = Set.univ)
    (zc0 : ↥(cycles (sub (U ∪ V)) (p + 1 + 1)))
    (hzc0 : Homology.mk (sub (U ∪ V)) (p + 1 + 1) zc0
      = legW (k := N + 1) (m := p + 1) (hU.union hV) z₀ hz₀ K₁ (Submodule.Quotient.mk gW))
    (zA : SingularChain (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (p + 1 + 1))
    (zB : SingularChain (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (p + 1 + 1))
    (hcyc : chainIncl _ (p + 1 + 1) zA + chainIncl _ (p + 1 + 1) zB
      ∈ cycles (sub (U ∪ V)) (p + 1 + 1))
    (hpart : Homology.mk (sub (U ∪ V)) (p + 1 + 1) zc0
      = Homology.mk (sub (U ∪ V)) (p + 1 + 1) ⟨_, hcyc⟩)
    (hzBmem : zB ∈ SingularPairLES.relCycleLift
      (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1))
    {Y' : TopCat}
    (φin : C(↑(sub (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))
      (Subtype.val ⁻¹' V))), ↑Y'))
    (φout : C(↑Y', ↑(sub (U ∩ V))))
    (hseam : ∀ (w : SingularPairLES.relCycleLift
        (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)),
      chainIncl (U ∩ V) (p + 1) (SingularFunctoriality.mapChain φout (p + 1)
          (SingularFunctoriality.mapChain φin (p + 1)
            (SingularPairLES.boundaryExtract
              (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1) w)))
        = chainIncl (U ∪ V) (p + 1) (chainBoundary (sub (U ∪ V)) (p + 1)
            (chainIncl (Subtype.val ⁻¹' V) (p + 1 + 1) (w : SingularChain _ (p + 1 + 1)))))
    (F₂ : SingularChain X (N + 1 + (p + 1) + 1))
    (hF₂mem : F₂ ∈ subspaceChains (U ∩ V) (N + 1 + (p + 1) + 1))
    (η₂ : SingularChain X (N + 1 + (p + 1) + 1 + 1)) (a₂ : SingularChain X (N + 1 + (p + 1) + 1))
    (heq₂ : F₂ + z₀ = chainBoundary X (N + 1 + (p + 1) + 1) η₂ + a₂)
    (ha₂ : a₂ ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + (p + 1) + 1))
    (hF₂bd : chainBoundary X (N + 1 + (p + 1)) F₂
      ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + (p + 1)))
    (jF : ℕ)
    (aF : SingularChain (sub (LUᶜ ∩ (U ∩ V))) (N + 1 + (p + 1)))
    (bF : SingularChain (sub (LVᶜ ∩ (U ∩ V))) (N + 1 + (p + 1)))
    (hFsplit : chainBoundary X (N + 1 + (p + 1))
        ((⇑(SingularSubdivision.singularSd X (N + 1 + (p + 1) + 1)))^[jF]
          F₂)
      = chainIncl _ (N + 1 + (p + 1)) aF + chainIncl _ (N + 1 + (p + 1)) bF)
    (hbFmem : chainIncl _ (N + 1 + (p + 1)) bF ∈ subspaceChains (U ∩ V) (N + 1 + (p + 1)))
    (β : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) (p + 1))) :
    kronecker β.1 (SingularFunctoriality.mapChain φout (p + 1)
        (SingularFunctoriality.mapChain φin (p + 1)
          (SingularPairLES.boundaryExtract
            (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
            ⟨zB, hzBmem⟩)))
      = kronecker β.1 (cap (SingularCapChainIncl.pullbackCochain (U ∩ V) (N + 1) g.1.1)
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 1 + (p + 1))).symm
            ⟨_, hbFmem⟩)) := by
  -- (0–2) STAGE 1: three-set split + canonical partition + class equality (ONE obtain)
  obtain ⟨μ, f₁, f₂, f₃, hf₁, hf₂, hf₃, hIsplit, zAc, zBc, hzAc, hzBc, hcycc, hcls⟩ :=
    fact_i_stage1 (k := N + 1) (m := p + 1) hU hV hLUc hLVc hLUU hLVV z₀ hz₀ K₁ gW
  -- STAGE 2: seam transport — swap the opaque legW-partition (zA, zB) for the canonical (zAc, zBc)
  have hzBcmem : zBc ∈ SingularPairLES.relCycleLift
      (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))
      (p + 1) :=
    SingularMvDeltaPartition.zB_mem_relCycleLift _ _ (p + 1) zAc zBc hcycc
  have htrans := kronecker_mapChain_boundaryExtract_class_invariant
    (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) (p + 1) hcov φin φout β
    zA zAc zB zBc hcyc hcycc (hpart.symm.trans (hzc0.trans hcls)) hzBmem hzBcmem
  rw [htrans]
  -- STAGES 3–7: the ambient core (Brick M) + seam-evaluation + realization + β-kill
  obtain ⟨EM, hEMmem, hEMeq⟩ :=
    fact_i_ambient_core hU hV hLUc hLVc hLUU hLVV g z₀ hz₀ K₁ K₂ hK₁ hK₂
      μ jF f₁ f₂ f₃ hf₁ hf₂ hf₃ hIsplit F₂ hF₂mem η₂ a₂ heq₂ ha₂ hF₂bd aF bF hFsplit
  -- (3) seam-evaluation on the canonical partition → the ambient ∂(cap g fB)
  have hzBcg : chainIncl (U ∪ V) (p + 1 + 1) (chainIncl _ (p + 1 + 1) zBc)
      = cap (m := p + 1 + 1) g.1.1 (f₂ + f₃) := by rw [hgg]; exact hzBc
  have hambL : chainIncl (U ∩ V) (p + 1)
      (SingularFunctoriality.mapChain φout (p + 1) (SingularFunctoriality.mapChain φin (p + 1)
        (SingularPairLES.boundaryExtract (SingularExcisionIso.restr
          (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
          ⟨zBc, hzBcmem⟩)))
      = chainBoundary X (p + 1) (cap (m := p + 1 + 1) g.1.1 (f₂ + f₃)) := by
    rw [hseam ⟨zBc, hzBcmem⟩, SingularRelativeHomologyMod2.chainIncl_chainBoundary, hzBcg]
  -- (3') the goal-RHS ambient realization
  have hambR : chainIncl (U ∩ V) (p + 1)
      (cap (SingularCapChainIncl.pullbackCochain (U ∩ V) (N + 1) g.1.1)
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 1 + (p + 1))).symm
          ⟨chainIncl _ (N + 1 + (p + 1)) bF, hbFmem⟩))
      = cap (m := p + 1) g.1.1 (chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) bF) := by
    rw [← SingularCapChainIncl.cap_chainIncl,
      SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm]
  -- (4) the sub-level sum is a boundary (chainIncl-injectivity + Brick M)
  rw [subspaceChains, LinearMap.mem_range] at hEMmem
  obtain ⟨E', hE'⟩ := hEMmem
  have hsum_mem : SingularFunctoriality.mapChain φout (p + 1)
        (SingularFunctoriality.mapChain φin (p + 1)
          (SingularPairLES.boundaryExtract (SingularExcisionIso.restr
            (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) (p + 1)
            ⟨zBc, hzBcmem⟩))
      + cap (SingularCapChainIncl.pullbackCochain (U ∩ V) (N + 1) g.1.1)
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 1 + (p + 1))).symm
            ⟨chainIncl _ (N + 1 + (p + 1)) bF, hbFmem⟩)
      ∈ boundaries (sub (U ∩ V)) (p + 1) := by
    refine ⟨E', ?_⟩
    apply chainIncl_injective (U ∩ V) (p + 1)
    rw [SingularRelativeHomologyMod2.chainIncl_chainBoundary, hE', map_add, hambL, hambR]
    exact hEMeq.symm
  -- (5) β kills the boundary; ℤ/2 splits the sum into the equality
  have h0 := kronecker_cocycle_boundary_eq_zero β hsum_mem
  rw [kronecker_add_right] at h0
  exact eq_of_sub_eq_zero (by rw [ZModModule.sub_eq_add]; exact h0)


/-- **The γ-computation** (the fact-(ii) two-legs closer, EXTRACTED — single-choice form). The two
goal legs are V-legs of cover-splits of two parents sharing ONE fundamental presentation `zsub`:
the pd-side parent `Camb` (whose un-subdivided boundary is EXACTLY `chainIncl (rcap β ∂zsub)` —
`hCore`, the single-choice core cancellation) and the F-side subdivision split `hQ` of `∂(Sdʲᶠ zsub)`
itself. The jP-slack telescopes through `add_singularSd_iterate_eq_boundary` on the cycle `∂Camb`;
the jF-slack routes through `rcap_singularSd_iterate_chainBoundary_arg` (cast-free by design); the
two `∂Camb` cores cancel over ℤ/2, leaving `∂E` cover-split with
`E := Dⱼₚ(∂Camb) + chainIncl (rcap β (cast ▸ Dⱼꜰ(∂zsub)))` — `(A ∪ B)`-supported since `D`/`rcap`/
`chainIncl` all preserve support (`hzbdcov` seeds it). β2 (`kronecker_boundary_split_V_leg_zero`)
kills the combined V-pairing; ℤ/2 splits it into the equality. ℤ/2. -/
theorem gamma_two_legs_close {A B W : Set ↑X} (hA : IsOpen A) (hB : IsOpen B) {n l : ℕ}
    (g : SingularCochain X (n + 1)) (hgc : coboundary X (n + 1) g = 0)
    (hg : g ∈ relCochains (A ∩ B) (n + 1))
    (β : SingularCochain (sub W) (l + 1))
    (hβ : coboundaryₗ (sub W) (l + 1) β = 0)
    (zsub : SingularChain (sub W) (n + 1 + (l + 1) + 1))
    (hzbdcov : chainIncl W (n + 1 + (l + 1))
        (chainBoundary (sub W) (n + 1 + (l + 1)) zsub)
      ∈ subspaceChains (A ∪ B) (n + 1 + (l + 1)))
    (Camb : SingularChain X (n + 1 + 1)) (jP : ℕ)
    (hCore : chainBoundary X (n + 1) Camb
      = chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β
          (chainBoundary (sub W) (n + 1 + (l + 1)) zsub)))
    {a₁ b₁ : SingularChain X (n + 1)}
    (ha₁ : a₁ ∈ subspaceChains A (n + 1)) (hb₁ : b₁ ∈ subspaceChains B (n + 1))
    (hP₁ : chainBoundary X (n + 1)
        ((⇑(SingularSubdivision.singularSd X (n + 1 + 1)))^[jP] Camb) = a₁ + b₁)
    (jF : ℕ) {a₂ b₂ : SingularChain (sub W) (n + 1 + (l + 1))}
    (ha₂ : chainIncl W (n + 1 + (l + 1)) a₂ ∈ subspaceChains A (n + 1 + (l + 1)))
    (hb₂ : chainIncl W (n + 1 + (l + 1)) b₂ ∈ subspaceChains B (n + 1 + (l + 1)))
    (hQ : chainBoundary (sub W) (n + 1 + (l + 1))
        ((⇑(SingularSubdivision.singularSd (sub W) (n + 1 + (l + 1) + 1)))^[jF] zsub)
      = a₂ + b₂) :
    kronecker g b₁
      = kronecker g (chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β b₂)) := by
  classical
  -- jP-side telescope on the cycle ∂Camb: ∂Camb + Sdʲᵖ(∂Camb) = ∂(Dⱼₚ(∂Camb)), Sdʲᵖ(∂Camb) = a₁+b₁.
  have hcyc : chainBoundary X n (chainBoundary X (n + 1) Camb) = 0 :=
    chainBoundary_chainBoundary_apply X n Camb
  have hhomP := SingularExcision.add_singularSd_iterate_eq_boundary hcyc jP
  have hSdP : (⇑(SingularSubdivision.singularSd X (n + 1)))^[jP] (chainBoundary X (n + 1) Camb)
      = a₁ + b₁ := by
    rw [← SingularSubdivision.singularSd_iterate_chainBoundary, hP₁]
  -- jF-side rcap Sd-bridge (intrinsic, cast-free by design), split via hQ, pushed through chainIncl,
  -- with the single-choice core cancellation folded in (hCore).
  have hrc := rcap_singularSd_iterate_chainBoundary_arg β hβ zsub jF
  rw [hQ, map_add] at hrc
  have hIncl := congrArg (chainIncl W (n + 1)) hrc
  rw [map_add, map_add, SingularRelativeHomologyMod2.chainIncl_chainBoundary, ← hCore] at hIncl
  -- The two ∂Camb cores cancel over ℤ/2 in ∂E, E := Dⱼₚ(∂Camb) + chainIncl(rcap β (cast ▸ Dⱼꜰ(∂zsub))).
  set DP := SingularSubdivision.iterHomotopy X (n + 1) jP (chainBoundary X (n + 1) Camb) with hDP
  set DF := chainIncl W (n + 1 + 1) (SingularCapChainIncl.rcap (k := n + 1 + 1) β
      ((show n + 1 + (l + 1) + 1 = n + 1 + 1 + (l + 1) from by omega) ▸
        SingularSubdivision.iterHomotopy (sub W) (n + 1 + (l + 1)) jF
          (chainBoundary (sub W) (n + 1 + (l + 1)) zsub))) with hDF
  have hDPbd : chainBoundary X (n + 1) DP
      = chainBoundary X (n + 1) Camb + (a₁ + b₁) := by
    rw [← hhomP, hSdP]
  have hDFbd : chainBoundary X (n + 1) DF
      = chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β a₂)
        + chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β b₂)
        + chainBoundary X (n + 1) Camb := by
    rw [hIncl]
    abel_nf
    simp only [two_smul, ZModModule.add_self, zero_add, add_zero]
  have hsplitE : chainBoundary X (n + 1) (DP + DF)
      = (a₁ + chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β a₂))
        + (b₁ + chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β b₂)) := by
    rw [map_add, hDPbd, hDFbd]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  -- E is (A ∪ B)-supported: hzbdcov seeds; D/rcap/chainIncl preserve.
  have hbdmem : chainBoundary X (n + 1) Camb ∈ subspaceChains (A ∪ B) (n + 1) := by
    rw [hCore]
    exact chainIncl_rcap_subspaceChains β _ hzbdcov
  have hDPmem : DP ∈ subspaceChains (A ∪ B) (n + 1 + 1) :=
    SingularExcision.iterHomotopy_mem_subspaceChains hbdmem jP
  have hDFmem : DF ∈ subspaceChains (A ∪ B) (n + 1 + 1) := by
    rw [hDF]
    refine (SingularExcisionIso.chainIncl_mem_subspaceChains_iff (A ∪ B) W _).mpr ?_
    refine SingularRightCapBoundary.rcap_mem_subspaceChains _ β ?_
    exact mem_subspaceChains_eq_rec _
      (SingularExcision.iterHomotopy_mem_subspaceChains
        ((SingularExcisionIso.chainIncl_mem_subspaceChains_iff (A ∪ B) W _).mp hzbdcov) jF)
  -- β2 kills the combined V-pairing; ℤ/2 splits it.
  have hzero := kronecker_boundary_split_V_leg_zero hA hB g hgc hg (DP + DF)
    (Submodule.add_mem _ hDPmem hDFmem)
    (Submodule.add_mem _ ha₁ (chainIncl_rcap_subspaceChains β a₂ ha₂))
    (Submodule.add_mem _ hb₁ (chainIncl_rcap_subspaceChains β b₂ hb₂))
    hsplitE
  rw [kronecker_add_right, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hzero
  exact hzero

/-- **Fact-(ii) discharge** (the FULL single-choice pipeline, extracted to its own command for
heartbeat isolation). Everything is free: `f` is the ONE fundamental presentation (pd-spelling
`n+2+l+1`), `hP` the pd-side repartitioned split of `∂(Sdʲᵖ (chainIncl (rcap β f_sub)))`, `hQsplit`
the F-side split of `∂(Sdʲᶠ (cast f))` (the `exists_cast_cover_V_projection` output shape). Builds
the F-spelling realize `zsub`, its cover-supported boundary (`chainBoundary_cast_comm` +
`subspaceChains_mem_cast`), the T₀ double-cast collapse (`subspaceChainsEquiv_symm_cast_cast` — the
composed cast has DEFEQ endpoints so it lands on the pd-side realize), the core cancellation
(`rcap_cocycle_chainMap`), realizes the F-side legs, and fires `gamma_two_legs_close`; the
`hmem3`-wrapper collapse lands the conclusion in the exact goal shape of the apex core. ℤ/2. -/
theorem fact_ii_two_legs_discharge {A B W : Set ↑X} (hA : IsOpen A) (hB : IsOpen B) {n l : ℕ}
    (g : ↥(relCoboundaryₗ (A ∩ B) (n + 1)).ker)
    (β : SingularCochain (sub W) (l + 1)) (hβ : coboundaryₗ (sub W) (l + 1) β = 0)
    {f : SingularChain X (n + 2 + l + 1)}
    (hfmem : f ∈ subspaceChains W (n + 2 + l + 1))
    (hfbd : chainBoundary X (n + 2 + l) f ∈ subspaceChains (A ∪ B) (n + 2 + l))
    (jP : ℕ) {aR : SingularChain (sub (A ∩ W)) (n + 1)} {bR : SingularChain (sub (B ∩ W)) (n + 1)}
    (hP : chainBoundary X (n + 1) ((⇑(SingularSubdivision.singularSd X (n + 1 + 1)))^[jP]
        (chainIncl W (n + 1 + 1) (SingularCapChainIncl.rcap (k := n + 1 + 1) β
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 2 + l + 1)).symm ⟨f, hfmem⟩))))
      = chainIncl (A ∩ W) (n + 1) aR + chainIncl (B ∩ W) (n + 1) bR)
    (jF : ℕ) {aF : SingularChain (sub (A ∩ W)) (n + 1 + (l + 1))}
    {bF : SingularChain (sub (B ∩ W)) (n + 1 + (l + 1))}
    (hQsplit : chainBoundary X (n + 1 + (l + 1))
        ((⇑(SingularSubdivision.singularSd X (n + 1 + (l + 1) + 1)))^[jF]
          (cast (congrArg (SingularChain X) (congrArg (· + 1)
            (show n + 2 + l = n + 1 + (l + 1) by omega))) f))
      = chainIncl (A ∩ W) (n + 1 + (l + 1)) aF + chainIncl (B ∩ W) (n + 1 + (l + 1)) bF)
    (hbFmem : chainIncl (B ∩ W) (n + 1 + (l + 1)) bF ∈ subspaceChains W (n + 1 + (l + 1)))
    (hmem3 : chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1 + (l + 1))).symm ⟨_, hbFmem⟩))
      ∈ subspaceChains (B ∩ W) (n + 1)) :
    kronecker g.1.1 (chainIncl (B ∩ W) (n + 1) bR)
      = kronecker g.1.1 (chainIncl (B ∩ W) (n + 1)
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (B ∩ W) (n + 1)).symm
            ⟨_, hmem3⟩)) := by
  classical
  have hgprops := SingularConnSquareRHSPairing.relCocycle_props g
  -- the F-spelling realize of the ONE choice:
  have hfcmem := SingularCapSubKDuality.subspaceChains_mem_cast
    (congrArg (· + 1) (show n + 2 + l = n + 1 + (l + 1) by omega)) hfmem
  set zsub := (SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1 + (l + 1) + 1)).symm
    ⟨_, hfcmem⟩ with hzsubdef
  have hchz := SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm
    (S := W) (n + 1 + (l + 1) + 1) ⟨_, hfcmem⟩
  -- ∂zsub's ambient image is cover-supported (∂ commutes with chainIncl and with the cast):
  have hbdchain : chainIncl W (n + 1 + (l + 1))
        (chainBoundary (sub W) (n + 1 + (l + 1)) zsub)
      = cast (congrArg (SingularChain X) (show n + 2 + l = n + 1 + (l + 1) by omega))
          (chainBoundary X (n + 2 + l) f) :=
    (SingularRelativeHomologyMod2.chainIncl_chainBoundary W (n + 1 + (l + 1)) zsub).trans
      ((congrArg (chainBoundary X (n + 1 + (l + 1))) hchz).trans
        (chainBoundary_cast_comm (show n + 2 + l = n + 1 + (l + 1) by omega) f))
  have hzbdcov : chainIncl W (n + 1 + (l + 1)) (chainBoundary (sub W) (n + 1 + (l + 1)) zsub)
      ∈ subspaceChains (A ∪ B) (n + 1 + (l + 1)) :=
    hbdchain.symm ▸ SingularCapSubKDuality.subspaceChains_mem_cast
      (show n + 2 + l = n + 1 + (l + 1) by omega) hfbd
  -- the T₀ double-cast collapse onto the pd-side realize (single choice):
  have hfX := SingularCapSubKDuality.subspaceChains_mem_cast
    ((congrArg (· + 1) (show n + 2 + l = n + 1 + (l + 1) by omega)).trans
      (by omega : n + 1 + (l + 1) + 1 = n + 1 + 1 + (l + 1))) hfmem
  have hswap := subspaceChainsEquiv_symm_cast_cast
    (congrArg (· + 1) (show n + 2 + l = n + 1 + (l + 1) by omega))
    (by omega : n + 1 + (l + 1) + 1 = n + 1 + 1 + (l + 1)) hfcmem hfX
  -- the single-choice core cancellation: ∂(pd-parent) = chainIncl (rcap β ∂zsub).
  have hCore : chainBoundary X (n + 1)
      (chainIncl W (n + 1 + 1) (SingularCapChainIncl.rcap (k := n + 1 + 1) β
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 2 + l + 1)).symm ⟨f, hfmem⟩)))
      = chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β
          (chainBoundary (sub W) (n + 1 + (l + 1)) zsub)) :=
    (SingularRelativeHomologyMod2.chainIncl_chainBoundary W (n + 1) _).symm.trans
      (congrArg (chainIncl W (n + 1))
        ((congrArg (chainBoundary (sub W) (n + 1))
          (congrArg (fun t => SingularCapChainIncl.rcap (k := n + 1 + 1) β t) hswap).symm).trans
          (SingularRightCapBoundary.rcap_cocycle_chainMap β hβ zsub)))
  -- pd-side leg supports:
  have ha₁ := SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left (n + 1)
    (⟨aR, rfl⟩ : chainIncl _ (n + 1) aR ∈ subspaceChains _ (n + 1))
  have hb₁ := SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left (n + 1)
    (⟨bR, rfl⟩ : chainIncl _ (n + 1) bR ∈ subspaceChains _ (n + 1))
  -- F-side legs, realized (the aF-mirror of the apex e₅/hbFmem pattern):
  have haFmem : chainIncl (A ∩ W) (n + 1 + (l + 1)) aF ∈ subspaceChains W (n + 1 + (l + 1)) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right (n + 1 + (l + 1)) ⟨aF, rfl⟩
  have e₆ : chainIncl W (n + 1 + (l + 1))
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1 + (l + 1))).symm ⟨_, haFmem⟩)
      = chainIncl (A ∩ W) (n + 1 + (l + 1)) aF :=
    SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm (S := W) (n + 1 + (l + 1))
      ⟨_, haFmem⟩
  have e₇ : chainIncl W (n + 1 + (l + 1))
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1 + (l + 1))).symm ⟨_, hbFmem⟩)
      = chainIncl (B ∩ W) (n + 1 + (l + 1)) bF :=
    SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm (S := W) (n + 1 + (l + 1))
      ⟨_, hbFmem⟩
  have ha₂ := e₆.symm ▸ SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left
    (n + 1 + (l + 1)) (⟨aF, rfl⟩ : chainIncl _ (n + 1 + (l + 1)) aF
      ∈ subspaceChains _ (n + 1 + (l + 1)))
  have hb₂ := e₇.symm ▸ SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left
    (n + 1 + (l + 1)) (⟨bF, rfl⟩ : chainIncl _ (n + 1 + (l + 1)) bF
      ∈ subspaceChains _ (n + 1 + (l + 1)))
  -- the F-side split realized intrinsically (chainIncl-injective off hQsplit):
  have hQamb : chainIncl W (n + 1 + (l + 1))
        (chainBoundary (sub W) (n + 1 + (l + 1))
          ((⇑(SingularSubdivision.singularSd (sub W) (n + 1 + (l + 1) + 1)))^[jF] zsub))
      = chainIncl W (n + 1 + (l + 1))
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1 + (l + 1))).symm ⟨_, haFmem⟩
            + (SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1 + (l + 1))).symm
              ⟨_, hbFmem⟩) :=
    (SingularRelativeHomologyMod2.chainIncl_chainBoundary W (n + 1 + (l + 1)) _).trans
      (((congrArg (chainBoundary X (n + 1 + (l + 1)))
          (singularSd_iterate_chainIncl jF zsub).symm).trans
        ((congrArg (fun t => chainBoundary X (n + 1 + (l + 1))
            ((⇑(SingularSubdivision.singularSd X (n + 1 + (l + 1) + 1)))^[jF] t)) hchz).trans
          (hQsplit.trans
            ((map_add (chainIncl W (n + 1 + (l + 1))) _ _).trans
              (congrArg₂ (· + ·) e₆ e₇)).symm))))
  have hQ := SingularRelativeHomologyMod2.chainIncl_injective W (n + 1 + (l + 1)) hQamb
  -- γ fires; the hmem3-wrapper collapse lands the goal shape.
  exact (gamma_two_legs_close hA hB g.1.1 hgprops.1 g.1.2 β hβ zsub hzbdcov _ jP hCore
    ha₁ hb₁ hP jF ha₂ hb₂ hQ).trans
    (congrArg (kronecker g.1.1)
      (SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm (S := B ∩ W) (n + 1)
        ⟨_, hmem3⟩).symm)

omit [T2Space ↑X] in
/-- **Joint cross-realization assembly** (the G1 close skeleton, whnf-dodging GREEN). Combines the two
realized legs on the common space `M = sub T` (with `T = U ∩ V`) into the connecting-square match. The
SEAM leg is supplied realized as `cap gM F + ∂e₁` (`hL`, PART-2 fund-compat output); the σR leg is supplied
as the ambient pairing reduced to `kronecker gM (rcap ω F + ∂e₂)` (`hR`, PART-1 σR-realize output). The
join is the cup–cap duality core `joint_cap_rcap_match` (both `ω` and `gM` are absolute cocycles, so the
boundary slacks `∂e₁`/`∂e₂` die). Stated over FREE carriers `gM, F, seam, u', w', e₁, e₂` so the concrete
`fundCycleW`/`seam`/`relCocycleRestrict` terms infer structurally at application — no 200k whnf wall.
Reduces the apex `refine_2` goal to exactly the two realize equalities `hL`, `hR`. ℤ/2. Kernel-pure. -/
theorem joint_close_seam_sigmaR {N p : ℕ} {T A B : Set ↑X}
    (ω : LinearMap.ker (coboundaryₗ (sub T) (p + 1)))
    (gM : SingularCochain (sub T) (N + 1)) (hgM : coboundary (sub T) (N + 1) gM = 0)
    (gR : SingularCochain X (N + 1))
    (F : SingularChain (sub T) (N + 1 + (p + 1)))
    (seam : SingularChain (sub T) (p + 1))
    (u' : SingularChain (sub A) (N + 1)) (w' : SingularChain (sub B) (N + 1))
    (e₁ : SingularChain (sub T) (p + 1 + 1)) (e₂ : SingularChain (sub T) (N + 1 + 1))
    (hL : seam = cap gM F + chainBoundary (sub T) (p + 1) e₁)
    (hR : kronecker (cochainSplit A (N + 1) gR)
            (chainIncl A (N + 1) u' + chainIncl B (N + 1) w')
          = kronecker gM (SingularCapChainIncl.rcap ω.1 F + chainBoundary (sub T) (N + 1) e₂)) :
    kronecker ω.1 seam
      = kronecker (cochainSplit A (N + 1) gR)
          (chainIncl A (N + 1) u' + chainIncl B (N + 1) w') := by
  rw [hR]
  exact joint_cap_rcap_match ω.1 (LinearMap.mem_ker.mp ω.2) gM hgM F seam
    (SingularCapChainIncl.rcap ω.1 F + chainBoundary (sub T) (N + 1) e₂) e₁ e₂ hL rfl

omit [T2Space ↑X] in
/-- **LHS cap-realization on the common space, modulo a `sub T`-boundary** (the genuine local-PD `?hL`
brick — whnf-dodging GREEN). The `mod`-boundary upgrade of `cap_realize_on_sub`: when the ambient
realize equality only holds up to a `sub T`-boundary `∂(chainIncl E)`, the `sub T`-chain `L` is the cap of
the pulled-back cochain against `F` *plus the same boundary `∂E`*. Via `chainIncl`-injectivity, `cap_chainIncl`
(pushes the cap inside `chainIncl`), and `chainIncl_chainBoundary` (`∂` commutes with `chainIncl`). This is the
form `joint_cap_rcap_match`'s `hL` consumes, with the essential subdivision/cover slack `∂E` retained — the
on-the-nose `cap_realize_on_sub` is too rigid (the two fundamental realizations agree only mod `∂`). -/
theorem cap_realize_on_sub_mod {T : Set ↑X} {k m : ℕ} (g : SingularCochain X k)
    (L : SingularChain (sub T) m) (F : SingularChain (sub T) (k + m))
    (E : SingularChain (sub T) (m + 1))
    (hLF : chainIncl T m L = cap g (chainIncl T (k + m) F)
        + chainBoundary X m (chainIncl T (m + 1) E)) :
    L = cap (SingularCapChainIncl.pullbackCochain T k g) F + chainBoundary (sub T) m E := by
  apply chainIncl_injective T m
  rw [map_add, hLF, SingularCapChainIncl.cap_chainIncl,
    SingularRelativeHomologyMod2.chainIncl_chainBoundary]

omit [T2Space ↑X] in
/-- **RHS rcap-realization on the common space, modulo a `sub T`-boundary** (the genuine local-PD `?hR`
brick — whnf-dodging GREEN). The right-cap mirror of `cap_realize_on_sub_mod`: a `sub T`-chain `R` whose
`chainIncl T` equals the ambient right cap of a `sub T`-realized `F` up to a `sub T`-boundary is the right cap
of the pulled-back cochain plus the same boundary. Via `chainIncl`-injectivity, `rcap_chainIncl`
(CapSubKDuality:120), and `chainIncl_chainBoundary`. The form `joint_cap_rcap_match`'s `hR` consumes. -/
theorem rcap_realize_on_sub_mod {T : Set ↑X} {k l : ℕ} (b : SingularCochain X l)
    (R : SingularChain (sub T) k) (F : SingularChain (sub T) (k + l))
    (E : SingularChain (sub T) (k + 1))
    (hRF : chainIncl T k R = SingularCapChainIncl.rcap b (chainIncl T (k + l) F)
        + chainBoundary X k (chainIncl T (k + 1) E)) :
    R = SingularCapChainIncl.rcap (SingularCapChainIncl.pullbackCochain T l b) F
        + chainBoundary (sub T) k E := by
  apply chainIncl_injective T k
  rw [map_add, hRF, SingularCapSubKDuality.rcap_chainIncl,
    SingularRelativeHomologyMod2.chainIncl_chainBoundary]

omit [T2Space ↑X] in
/-- **Joint cap/rcap realize-close on the common space `sub T`** (the G1 close assembly, whnf-dodging GREEN).
Packages the two realize-mod bricks (`cap_realize_on_sub_mod`, `rcap_realize_on_sub_mod`) with
`joint_cap_rcap_match`. Given the genuine local-PD ambient identities — the seam `L` realizes the ambient cap
`cap g (chainIncl F)` mod a `sub T`-boundary (`hLF`), and `R` realizes the ambient right cap `rcap ω (chainIncl F)`
mod a `sub T`-boundary (`hRF`) — the two Kronecker legs agree: `kronecker ω L = kronecker (pullbackCochain g) R`.
Stated over FREE carriers `g, ω, F, L, R, e₁, e₂` so the concrete `fundCycleW`/`seam`/`relCocycleRestrict` terms
infer STRUCTURALLY at application — no 200k whnf wall. Reduces the apex to exactly the two ambient identities
`hLF`, `hRF` (the genuine fund-class compatibility over the shared `z₀`). ℤ/2. Kernel-pure. -/
theorem joint_realize_match {T : Set ↑X} {N p : ℕ} (g : SingularCochain X (N + 1))
    (ω : SingularCochain X (p + 1))
    (hω : coboundary (sub T) (p + 1) (SingularCapChainIncl.pullbackCochain T (p + 1) ω) = 0)
    (hg : coboundary (sub T) (N + 1) (SingularCapChainIncl.pullbackCochain T (N + 1) g) = 0)
    (F : SingularChain (sub T) (N + 1 + (p + 1))) (L : SingularChain (sub T) (p + 1))
    (R : SingularChain (sub T) (N + 1))
    (e₁ : SingularChain (sub T) (p + 1 + 1)) (e₂ : SingularChain (sub T) (N + 1 + 1))
    (hLF : chainIncl T (p + 1) L = cap g (chainIncl T (N + 1 + (p + 1)) F)
        + chainBoundary X (p + 1) (chainIncl T (p + 1 + 1) e₁))
    (hRF : chainIncl T (N + 1) R = SingularCapChainIncl.rcap ω (chainIncl T (N + 1 + (p + 1)) F)
        + chainBoundary X (N + 1) (chainIncl T (N + 1 + 1) e₂)) :
    kronecker (SingularCapChainIncl.pullbackCochain T (p + 1) ω) L
      = kronecker (SingularCapChainIncl.pullbackCochain T (N + 1) g) R :=
  joint_cap_rcap_match (SingularCapChainIncl.pullbackCochain T (p + 1) ω) hω
    (SingularCapChainIncl.pullbackCochain T (N + 1) g) hg F L R e₁ e₂
    (cap_realize_on_sub_mod g L F e₁ hLF)
    (rcap_realize_on_sub_mod ω R F e₂ hRF)

/-- **Space-generic Kronecker non-degeneracy boundary closer.** Over ℤ/2, a cycle `z` of an arbitrary
space `Y` that pairs to `0` against every cocycle is a boundary (universal coefficients
`homology_eq_zero_of_kroneckerH` + `Homology.mk_eq_zero`). The space-generic companion of
`mem_boundaries_of_kroneckerH_zero` (which is fixed to the ambient `X`); needed to discharge the
connecting-square residual in the SUBSPACE `sub (U∩V)`. -/
theorem mem_boundaries_of_kroneckerH_zero_space {Y : TopCat} {n : ℕ} (z : SingularChain Y n)
    (hz : z ∈ cycles Y n)
    (h : ∀ ω : LinearMap.ker (coboundaryₗ Y n), kronecker ω.1 z = 0) :
    z ∈ boundaries Y n := by
  have hmk : Homology.mk Y n ⟨z, hz⟩ = 0 := by
    apply SKEFTHawking.PoincareDualityConstruct.homology_eq_zero_of_kroneckerH
    intro ω
    obtain ⟨ωc, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
    exact h ωc
  rw [SKEFTHawking.SingularCapHomology.Homology.mk_eq_zero] at hmk
  exact hmk

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
  -- ▶ S1 ∈-BOUNDARIES ROUTE (turn 53). S2 exact-hident is DEAD (SETTLED_FORKS `L2-hident-exact-equality-dead`): the
  --   exact `chainIncl seam + chainIncl pd = cap g_rep ∂fund` cannot absorb the non-zero Sdʲ-slack — `seam[zB]` relates
  --   to the cover-split `[w']` only HOMOLOGICALLY (hpart is homology-level), not exactly. The COACH-LOCKED ∈-boundaries
  --   route (NC:1465-1468): KEY `seam²(boundaryExtract zB) + pullbackDualityₗ σR_rep ∈ boundaries(sub(U∩V))` discharges via
  --   `realize_chainBoundary_cap_mem_boundaries` (NC:304) on `W := cap (cochainSplit g_rep) F` + the two facts (χ-term via
  --   the cover-level engine `cap_coboundary_cochainSplit_eq` NC:752, seam-term) — the Sdʲ-slack lives IN the ∂W boundary.
  -- NOTE (2026-07-02, heartbeat relief): the fact-(i) feed blocks that lived here (STEP A's
  -- cover-fine hsplit obtain, STEP B's heng χ-engine, STEP C's hpdg W-leg partition, STEP D's
  -- hsub/hfc fund-compat bridge, and the in-case htest/Dfc/ρfc/hη/heq1-heq3'/hfundK/hEbridge
  -- chain) are REMOVED from this command: the apex is ONE Lean command with a cumulative 200k
  -- heartbeat budget, and these ~15 heavy elaborations (needed only by the still-open fact (i))
  -- starved the fact-(ii) discharge. They are all banked (recipes: the L2 lab notebook 2026-07-01
  -- sections; git: 60a57754 and earlier) and will return EXTRACTED as a standalone
  -- fact_i_discharge lemma over free variables, per the same pattern as fact_ii_two_legs_discharge.
  have hKeq : ((↑K.1 : Set ↑X))ᶜ
      = (↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ
        ∩ (↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1 : Set ↑X)ᶜ := by
    rw [SingularCSCMayerVietorisConnecting.legSplit_cover U V hU hV K, Set.compl_union]
  -- APPROACH D (homology-level closer; Aristotle 946db1c6 scaffold, grafted 2026-06-29). Instead of the
  -- on-the-nose chain closer (residual false modulo a non-zero Sdʲ slack), close the membership
  -- `seam + pd ∈ boundaries (sub (U∩V))` at HOMOLOGY-CLASS level via `mem_boundaries_of_mk_eq`: both
  -- `seam` and `pd` are cycles, and the remaining obligation is the class square `[seam] = [pd]`.
  refine mem_boundaries_of_mk_eq (U ∩ V) _ _ ?cycSeam ?cycPd ?hmk
  case cycSeam =>
    exact SingularFunctoriality.mapChain_mem_cycles _
      (SingularFunctoriality.mapChain_mem_cycles _
        (SingularPairLES.boundaryExtract_mem_cycles _ (p + 1) ⟨zB, hzBmem⟩))
  case cycPd =>
    refine SingularLocalDualityK.pullbackDualityₗ_mem_cycles _ _ _ _ ?_ σR_rep
    have hbd := SingularOpenDualityCycle.fundCycleW_boundary (hU.inter hV)
      (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
      (SingularCSCMayerVietorisConnecting.infCompact U V
        (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
        (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K))
    exact hbd
  case hmk =>
    -- The class-level Poincaré-duality / Mayer–Vietoris-connecting square `[seam] = [pd]`, reduced to
    -- `chainL + pd ∈ boundaries (sub (U∩V)) (p+1)`, then discharged by Kronecker non-degeneracy in the
    -- SUBSPACE `sub (U∩V)` (`mem_boundaries_of_kroneckerH_zero_space`). KEY: against a cocycle `β` all
    -- subdivision (`Sdʲ`) and coboundary slack DIES (`kronecker β ∂(·) = 0`), so the pairing route is
    -- non-circular and dodges the class-level `hmem` obstacle.
    apply mk_eq_of_mem_boundaries
    refine mem_boundaries_of_kroneckerH_zero_space _ ?_ ?_
    · -- `chainL + pd` is a cycle of `sub (U∩V)` (both summands are cycles).
      refine Submodule.add_mem _
        (SingularFunctoriality.mapChain_mem_cycles _
          (SingularFunctoriality.mapChain_mem_cycles _
            (SingularPairLES.boundaryExtract_mem_cycles _ (p + 1) ⟨zB, hzBmem⟩))) ?_
      refine SingularLocalDualityK.pullbackDualityₗ_mem_cycles _ _ _ _ ?_ σR_rep
      exact SingularOpenDualityCycle.fundCycleW_boundary (hU.inter hV)
        (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
        (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
        (SingularCSCMayerVietorisConnecting.infCompact U V
          (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
          (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K))
    · -- Per-cocycle pairing identity: `kronecker β chainL = kronecker β pd` (the genuine PD–MV content).
      intro β
      -- NOTE (2026-07-02, heartbeat relief): the fact-(i) in-case feed chain that lived here
      -- (htest / Dfc,ρfc / hη / heq1→heq3' / hfundK / hEbridge — the seam-side hL machinery)
      -- is REMOVED from this command for budget (see the note above STEP A's former site);
      -- recipes banked in the L2 lab notebook 2026-07-01 sections + git 60a57754; to be rebuilt
      -- EXTRACTED (fact_i_discharge over free variables) when fact (i) is attacked.
      -- hR START (2026-07-01 continuation): `pd = pullbackDualityₗ (infCompactᶜ)(U∩V) fund_∩ ⋯ σR_rep` is
      -- LITERALLY a sub(U∩V)-cap (`pullbackDualityₗ_eq_subcap`), so `kronecker β pd` reduces via the
      -- cup-cap adjunction (`kronecker_cup_cap`) to a CUP pairing against `fund_∩`'s sub(U∩V) representative
      -- — no boundary slack needed (fund_∩'s cap against any rel-cocycle is already an ambient cycle,
      -- `pullbackDualityₗ_mem_cycles`).
      have hfundmem2 : SingularOpenDualityCycle.fundCycleW (hU.inter hV)
          (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          (SingularCSCMayerVietorisConnecting.infCompact U V
            (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
            (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K))
        ∈ subspaceChains (U ∩ V) (N + 2 + p + 1) :=
        SingularOpenDualityCycle.fundCycleW_mem_W (hU.inter hV) _ _ _
      have hpd_cap : SingularLocalDualityK.pullbackDualityₗ
          ((↑(SingularCSCMayerVietorisConnecting.infCompact U V
              (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
              (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)).1 : Set ↑X)ᶜ)
          (U ∩ V)
          (SingularOpenDualityCycle.fundCycleW (hU.inter hV)
            (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
            (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
            (SingularCSCMayerVietorisConnecting.infCompact U V
              (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
              (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
          hfundmem2 σR_rep
        = cap (SingularCapChainIncl.pullbackCochain (U ∩ V) (N + 2) σR_rep.1.1)
            ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 2 + p + 1)).symm
              ⟨SingularOpenDualityCycle.fundCycleW (hU.inter hV)
                (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
                (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
                (SingularCSCMayerVietorisConnecting.infCompact U V
                  (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                  (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)),
                hfundmem2⟩) :=
        SingularCapSubKDuality.pullbackDualityₗ_eq_subcap _ hfundmem2 σR_rep
      have hpd_kronecker : kronecker β.1
          (SingularLocalDualityK.pullbackDualityₗ
            ((↑(SingularCSCMayerVietorisConnecting.infCompact U V
                (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)).1 : Set ↑X)ᶜ)
            (U ∩ V)
            (SingularOpenDualityCycle.fundCycleW (hU.inter hV)
              (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
              (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
              (SingularCSCMayerVietorisConnecting.infCompact U V
                (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
            hfundmem2 σR_rep)
          = kronecker (cup (SingularCapChainIncl.pullbackCochain (U ∩ V) (N + 2) σR_rep.1.1) β.1)
              ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 2 + p + 1)).symm
                ⟨SingularOpenDualityCycle.fundCycleW (hU.inter hV)
                  (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
                  (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
                  (SingularCSCMayerVietorisConnecting.infCompact U V
                    (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                    (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)),
                  hfundmem2⟩) := by
        rw [hpd_cap, SingularCapChainIncl.kronecker_cup_cap]
      rw [kronecker_add_right, hpd_kronecker]
      -- SEAM PEEL (2026-07-01, resolves the 3 documented failed `rw` attempts): the mismatch was NEVER the
      -- set description — it was `rw`'s reducible-transparency matching. `erw` (default transparency) unifies
      -- the goal's anonymous-struct seam homeos against `kronecker_double_pullback`'s explicit `C(·,·)`
      -- variables directly (the same erw-for-defeq-set-reprs fix recorded in the friction catalog for
      -- `chainIncl_seam_boundaryExtract` and `cap_leibniz` at this same `sub (U ∩ Membership.mem V)` seam).
      erw [← kronecker_double_pullback]
      -- Goal now: kronecker (pullbackCochainMap ⟨seamHomeo⟩ (pullbackCochainMap ⟨subSeamHomeo⟩ β))
      --             (boundaryExtract (restr (val⁻¹U)(val⁻¹V)) ⟨zB,hzBmem⟩)
      --           + kronecker (cup (pullbackCochain (U∩V) σR_rep) β) (fund_∩_sub) = 0
      -- — the seam leg is the double-pulled-back β paired against the bare V-part boundary extract; the pd
      -- leg is the cup pairing against fund_∩'s sub(U∩V) representative.
      -- REMAINING (the genuine Hatcher-3.36 / Sun-Lemma-3 content, at the sanctioned pairing altitude where
      -- β-cocycle slack death applies): evaluate BOTH legs to the connecting pairing of g_rep over the shared
      -- z₀ — seam leg via the cover-partition (hpart/hzc0: zB = V-part of cap g_rep fund) + connectingLift /
      -- kroneckerH_mvConnecting_cover_partition@ConnSquareLHSPairing; pd leg via hσR (σR_rep = connecting of
      -- g_rep's restriction) + the rhs_pairing_reduce family; ℤ/2 cancels the matched pair.
      -- pd-leg step 1 (cup → ambient σR pairing): ⟨cup (pullback σR) β, fund_sub⟩ = ⟨σR, chainIncl (rcap β fund_sub)⟩.
      erw [← SingularConnSquareClose.kronecker_chainIncl_rcap_eq_cup]
      -- pd-leg step 2 (chain pairing → relKroneckerH class pairing, turn-15 bridge reversed): the ambient
      -- pairing of σR_rep against the chainIncl'd rcap IS the relative-Kronecker pairing of σR_rep's class.
      erw [← SingularConnSquareClose.relKroneckerH_chainIncl_rcap_eq_kronecker
        _ _ (SingularOpenDualityCycle.fundCycleW_boundary _ _ _ _) σR_rep β
        (SingularCapSubKDuality.chainIncl_rcap_mem_relCycles _ _
          (SingularOpenDualityCycle.fundCycleW_boundary _ _ _ _) β)]
      -- pd-leg step 3: expose the connecting class. Turn-16 friction fix: the goal presents σR's class as
      -- `RelativeCohomology.mk` while hσR's LHS is `Submodule.Quotient.mk` — convert via rfl first, then hσR.
      rw [← show (Submodule.Quotient.mk σR_rep : RelativeCohomology _ (N + 1 + 1))
          = RelativeCohomology.mk _ (N + 1 + 1) σR_rep from rfl]
      erw [hσR]
      -- pd-leg step 4 (turn-18 recipe): peel the OUTER relCohomSetCongr — shape the homology as
      -- `relIncl refl` (the ← rw needs the mk-shaped y so the pattern isn't a bare metavariable), collapse.
      rw [← SingularTwoCoverBridge.relIncl_refl_apply (Set.Subset.refl _)
        (RelativeHomology.mk _ (N + 1 + 1) _)]
      erw [SingularTwoCoverBridge.relKroneckerH_relCohomSetCongr_relIncl_collapse]
      -- pd-leg step 5 (turn-19 recipe): mk-push — reduce the MvConnecting's cohomology arg to `mk (g_rep↾)`
      -- (the mk-pushing lemmas want `RelativeCohomology.mk`, so convert the inner Quotient.mk first, rfl).
      rw [show (Submodule.Quotient.mk g_rep : RelativeCohomology _ (N + 1))
          = RelativeCohomology.mk _ (N + 1) g_rep from rfl,
        SingularRelCohomSetCongrMk.relCohomSetCongr_mk,
        SingularRelativeCohomologyRestrict.relCohomRestrict_mk]
      -- pd-leg step 6 (turn-20 helper): push the collapse's `▸` through the RelativeHomology.mk, landing the
      -- homology over legSplitUᶜ ∪ legSplitVᶜ (the set rhs_pairing_reduce_partition consumes); the relCycles
      -- witness over the union comes from the cover form of the fundamental's boundary support.
      rw [relHomology_mk_setCongr_transport ((infCompact_compl_legSplit hU hV K).symm) _ _
        (SingularCapSubKDuality.chainIncl_rcap_mem_relCycles _ _
          (fundCycleW_boundary_cover _ _ _ _
            (infCompact_compl_legSplit hU hV K)) β)]
      -- pd-leg step 7 (turn-23 whnf dodge + the partition-exposing reduce): abstract the concrete
      -- `relCocycleRestrict` MAP to an opaque `RR` (the documented 200k-wall source), then evaluate the
      -- connecting pairing via `rhs_pairing_reduce_partition` — the UNCONDITIONAL cover-fine engine.
      generalize hRRdef :
        SingularRelativeCohomologyRestrict.relCocycleRestrict (Set.Subset.refl _) (N + 1) = RR
      obtain ⟨jP, uP, wP, hpair2, hsplit2⟩ :=
        SingularConnSquareRHSPairing.rhs_pairing_reduce_partition _ _
          (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
          (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
          (RR (hKeq ▸ g_rep))
          (chainIncl (U ∩ V) (N + 1 + 1) (SingularCapChainIncl.rcap β.1
            ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 2 + p + 1)).symm
              ⟨SingularOpenDualityCycle.fundCycleW (hU.inter hV)
                (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
                (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
                (SingularCSCMayerVietorisConnecting.infCompact U V
                  (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
                  (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)), hfundmem2⟩)))
          (SingularCapSubKDuality.chainIncl_rcap_mem_relCycles _ _
            (fundCycleW_boundary_cover _ _ _ _ (infCompact_compl_legSplit hU hV K)) β)
      erw [hpair2]
      -- pd-leg step 8 (banked turn-21b engine): δ↔∂ adjunction + U-leg drop + cochainSplit↦ω swap in one —
      -- the pd leg is now the bare `⟨g_rep↾, chainIncl legSplitVᶜ wP⟩` V-leg pairing.
      erw [kronecker_coboundary_cochainSplit_eq _ _ (RR (hKeq ▸ g_rep)) _ uP wP hsplit2]
      -- pd-leg step 9 (turn-39/41 kept machinery): realize the V-leg ON sub(U∩V). The mem_sup leg wP need
      -- not be (U∩V)-supported, but the support-preserving REPARTITION (rhs_realize_V_leg) lands a new leg
      -- bR over legSplitVᶜ∩(U∩V) ⊆ U∩V. Support feeder: the parent chain is (U∩V)-supported (turn-23 form).
      have hMem0 : chainIncl _ (N + 1) uP + chainIncl _ (N + 1) wP
          ∈ subspaceChains (U ∩ V) (N + 1) :=
        hsplit2 ▸ chainBoundary_singularSd_iterate_chainIncl_mem (T := U ∩ V) jP _
      obtain ⟨aR, bR, hbRchain, hbR⟩ :=
        rhs_realize_V_leg (RR (hKeq ▸ g_rep)).1.1 (RR (hKeq ▸ g_rep)).1.2 uP wP hMem0
      -- Swap the bare-gRk V-leg pairing back to the cochainSplit form, re-add the (killed) U-leg, then hbR.
      have hsum : kronecker (cochainSplit
            (↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ (N + 1)
            (RR (hKeq ▸ g_rep)).1.1)
            (chainIncl _ (N + 1) uP + chainIncl _ (N + 1) wP)
          = kronecker (cochainSplit
            (↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ (N + 1)
            (RR (hKeq ▸ g_rep)).1.1) (chainIncl _ (N + 1) wP) := by
        rw [kronecker_add_right]
        erw [(mem_relCochains _ _ _).1 (cochainSplit_mem_relCochains _ _ _) _ ⟨uP, rfl⟩, zero_add]
      erw [← kronecker_cochainSplit_V_leg_eq
        (↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1 : Set ↑X)ᶜ _
        (RR (hKeq ▸ g_rep)) wP, ← hsum, hbR]
      -- Realize the repartitioned V-leg on sub(U∩V) (bR's support is inside U∩V) and pull the cochain back:
      -- the pd leg lands as an INTRINSIC sub(U∩V) pairing ⟨pullbackCochain(U∩V) g_rep↾, R_sub⟩.
      have hbmem : chainIncl _ (N + 1) bR ∈ subspaceChains (U ∩ V) (N + 1) :=
        SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right (N + 1) ⟨bR, rfl⟩
      erw [show (chainIncl _ (N + 1) bR : SingularChain X (N + 1)) = chainIncl (U ∩ V) (N + 1)
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 1)).symm ⟨_, hbmem⟩) from
        (SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm _ _ ⟨_, hbmem⟩).symm,
        kronecker_chainIncl_eq_pullbackCochain]
      -- FINAL MATCH SETUP: un-peel the seam back to the intrinsic ⟨β, seam²(bE zB)⟩ form and ℤ/2-convert
      -- `A + B = 0` to the `joint_cap_rcap_match` shape `⟨β, L⟩ = ⟨gM, R⟩`.
      erw [kronecker_double_pullback]
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]
      -- THE SHARED cover-V-projection F — SINGLE-CHOICE discipline: a FRESH cover-split of the CAST
      -- fund₂ (the same `.choose` the pd side carries), so every fund-object in fact (ii) is a cast-
      -- presentation of ONE term and all reconciliations are `cases`-able cast-commutes. (fund₁-based
      -- splits would introduce a SECOND independent choice — see the 9th-push notebook analysis.)
      -- Elaboration discipline (the 10th-push wall, bisected): `h` must be `show`-typed — a bare
      -- `by omega` leaves n₁ UN-INFERABLE in an `obtain` (no expected type), and the elaborator's
      -- search for it is the whnf-wall; `hbd` mirrors the STEP-A green tactic-block (raw
      -- `fundCycleW_boundary` with explicit args + `rwa [infCompact_coe, compl_inter]`), never the
      -- `_ _ _ _`-underscored cover wrapper (its metas unify against the huge concrete instance).
      obtain ⟨jF, aF, bF, hFsplit⟩ := exists_cast_cover_V_projection
        (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
        (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
        (show N + 2 + p = N + 1 + (p + 1) by omega)
        (SingularOpenDualityCycle.fundCycleW (hU.inter hV)
          (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          (SingularCSCMayerVietorisConnecting.infCompact U V
            (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
            (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K)))
        hfundmem2
        (fund2_boundary_cover U V hU hV K z₀ hz₀)
      have hbFmem : chainIncl _ (N + 1 + (p + 1)) bF
          ∈ subspaceChains (U ∩ V) (N + 1 + (p + 1)) :=
        SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right (N + 1 + (p + 1)) ⟨bF, rfl⟩
      -- The pairing-relaxed joint match: ω/gM/L/R unify from the goal; the TWO SUN FACTS remain.
      refine joint_cap_rcap_match_pairing _ _
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 1 + (p + 1))).symm
          ⟨_, hbFmem⟩) _ _ ?_ ?_
      -- SUN FACT (i) — the seam fact, discharged by the EXTRACTED single-choice `fact_i_discharge`
      -- (Bricks A–M + K′; the F₂-slot receives the cast-presentation of THE pd-side fund choice,
      -- its rel-witness cast-transported through `cast_fund_feed` in one `cases`).
      · obtain ⟨η₂c, a₂c, heq₂c, ha₂c⟩ := fundCycleW_chain_rel (hU.inter hV)
          (SingularOpenDualityMVConnSquare.castChain (by omega : N + p + 3 = N + 2 + p + 1) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
            z₀ hz₀)
          (SingularCSCMayerVietorisConnecting.infCompact U V
            (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
            (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K))
        rw [infCompact_compl_legSplit hU hV K] at ha₂c
        obtain ⟨hF₂mem', hF₂bd', η₂', a₂', heq₂', ha₂'⟩ :=
          cast_fund_feed (show N + 2 + p = N + 1 + (p + 1) by omega) _ _ a₂c η₂c
            hfundmem2 (fund2_boundary_cover U V hU hV K z₀ hz₀) heq₂c ha₂c
        rw [singularChain_cast_eq_rec
            (congrArg (· + 1) (show N + 2 + p = N + 1 + (p + 1) by omega))
            (SingularOpenDualityMVConnSquare.castChain
              (by omega : N + p + 3 = N + 2 + p + 1) z₀),
          castChain_cast_reconcile (by omega : N + p + 3 = N + 2 + p + 1)
            (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) _ z₀] at heq₂'
        have hgg : (RR (hKeq ▸ g_rep)).1.1 = g_rep.1.1 := by
          rw [← hRRdef]
          exact ker_relCoboundary_cast_coe hKeq g_rep
        exact fact_i_discharge hU hV
          (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV
            K).1.isCompact'.isClosed.isOpen_compl
          (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV
            K).1.isCompact'.isClosed.isOpen_compl
          (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).2
          (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).2
          (RR (hKeq ▸ g_rep))
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
            z₀ hz₀)
          K
          (SingularCSCMayerVietorisConnecting.infCompact U V
            (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K)
            (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K))
          g_rep hgg hKeq (infCompact_compl_legSplit hU hV K)
          (SingularSubHomologyMV.cover_preimage U V hU hV)
          zc0 hzc0 zA zB hcyc hpart hzBmem _ _
          (chainIncl_seam_boundaryExtract (fun x hx => Or.inl hx.1) (fun q => Iff.rfl))
          _ hF₂mem' η₂' a₂' heq₂' ha₂' hF₂bd'
          jF aF bF hFsplit hbFmem β
      -- SUN FACT (ii) — the rcap fact: ⟨pullbackCochain (U∩V) g_rep↾, R_sub⟩ =
      -- ⟨pullbackCochain g_rep↾, rcap β F⟩. Assembly (per the β-brick architecture): reduce both sides to
      -- ambient ⟨gRk, (Vᶜ∩(U∩V))-leg⟩ pairings; the two legs are V-legs of splits of two parents P₁ (bR's,
      -- via hbRchain+hsplit2) and P₂ (rcap β applied to hsplit+hFsplit's split) whose SUM is ∂(chainIncl E)
      -- with E cover-supported (the Sd-homotopy on the CYCLE rcap β ∂fund — `add_singularSd_iterate_eq_
      -- boundary` — plus the fund₁↔fund₂ cast bridge); then `kronecker_boundary_split_V_leg_zero` (β2)
      -- kills the combined V-pairing and ℤ/2 splits it into the desired equality.
      · -- ▶ NEXT (intrinsic-frame assembly — the ambient un-pullback rw's whnf-wall on this goal, both
        -- spellings; STAY in sub(U∩V) and EXACT-apply the β-bricks, never goal-rewrite):
        -- (0) β0' brick: `pullbackCochain_relCochains_preimage` — g ∈ relCochains S ⟹ pullbackCochain W g
        --     ∈ relCochains (val⁻¹S) (via kronecker_pullbackCochain + chainIncl_mem_subspaceChains_iff.mpr);
        --     gives hg-intrinsic for G; hgc-intrinsic via coboundary_pullbackCochain_eq + relCocycle_props.
        -- (1) R_sub ∈ subspaceChains_{M'}(val⁻¹(Vᶜ∩∩)) via chainIncl_mem_subspaceChains_iff.mp on its
        --     defining chainIncl identity; rcap β F ∈ same via rcap_mem_subspaceChains-in-M' + hF_mem
        --     (hF_mem := iff.mp on F's defining identity). Realize both as val⁻¹Vᶜ-legs (M'-equiv).
        -- (2) Parents: P₁ := ∂(Sdʲᴾ(rcap β fund₂_sub)) [intrinsic; bridges to hsplit2/hbRchain via
        --     singularSd_iterate_chainIncl + chainIncl_injective], P₂ := rcap β (∂(Sdʲˢᵈ fund₁_sub))
        --     [bridges to hsplit/hFsplit the same way]. P₁ + P₂ = ∂E_M' + cast-slack: the jP-side via
        --     add_singularSd_iterate_eq_boundary on the CYCLE rcap β (∂fund_sub) (∂∂ = 0), the jSd-side via
        --     rcap-linearity + rcap_cocycle_chainMap (β cocycle); fund₁↔fund₂ via castChain_cast_reconcile.
        --     E_M' := DⱼP(rcap β f) + rcap β (Dⱼˢᵈ f) is (val⁻¹infCompactᶜ)-supported (D/rcap preserve).
        -- (3) β2 on the combined split of the parents' sum kills the combined V-pairing; ℤ/2 splits it.
        -- FRAME DODGE (recorded): the pullback layer is discharged by PURE TERM COMPOSITION —
        -- now via the EXTRACTED `pullback_pairing_legs_assemble` (heartbeat relief: the apex proof
        -- is one command with a cumulative 200k budget; the e-block composition moved out). hmem3
        -- (the rcap Bv-support, β0'' + e₅-transport) stays constructed here, unascribed (sets infer).
        have e₅ : chainIncl (U ∩ V) (N + 1 + (p + 1))
              ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V)
                (N + 1 + (p + 1))).symm ⟨_, hbFmem⟩)
            = chainIncl _ (N + 1 + (p + 1)) bF :=
          SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm (S := U ∩ V)
            (N + 1 + (p + 1)) ⟨_, hbFmem⟩
        have hmem3 := chainIncl_rcap_subspaceChains β.1 _
          (e₅.symm ▸ (⟨bF, rfl⟩ : chainIncl _ (N + 1 + (p + 1)) bF
            ∈ subspaceChains _ (N + 1 + (p + 1))))
        refine pullback_pairing_legs_assemble (RR (hKeq ▸ g_rep)).1.1 β.1 bR hbmem bF hbFmem
          hmem3 ?_
        -- ==== the single-choice γ-application (fact (ii) CLOSES here) ====
        -- Everything heavy lives in the extracted `fact_ii_two_legs_discharge` (fresh budget);
        -- hA2/hB2 pre-pin the ↑↑ᶜ spelling (one small defeq each) so the big application's A/B
        -- unify syntactically against the goal/RR/hbRchain forms; hP2 pre-composes the pd split.
        have hA2 : IsOpen ((↑(SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1
              : Set ↑X)ᶜ) :=
          (SingularCSCMayerVietorisConnecting.legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
        have hB2 : IsOpen ((↑(SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1
              : Set ↑X)ᶜ) :=
          (SingularCSCMayerVietorisConnecting.legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
        have hP2 := hsplit2.trans hbRchain
        exact fact_ii_two_legs_discharge hA2 hB2
          (RR (hKeq ▸ g_rep)) β.1 (LinearMap.mem_ker.mp β.2) hfundmem2
          (fund2_boundary_cover U V hU hV K z₀ hz₀)
          jP hP2 jF hFsplit hbFmem hmem3
end SKEFTHawking.SingularConnSquareCloseNC
