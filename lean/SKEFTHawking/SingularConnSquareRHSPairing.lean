import Mathlib
import SKEFTHawking.SingularConnSquareRHSScaffold
import SKEFTHawking.SingularRelCohomMvConnectingGeom
import SKEFTHawking.SingularExcisionIso
import SKEFTHawking.SingularCohomologySnake

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — RHS pairing reduction (gap-free, pairing form)

The RHS leg of the Poincaré-duality connecting-square match, reduced to an **explicit cochain pairing**
via the *pairing-form* MV-connecting realization (`relKroneckerH_relCohomMvConnecting_cover_partition`,
which is **unconditional** — it needs only a cover-partition `∂c = u + w`, NOT the union-level membership
`δφ ∈ relCochains (U'∪V')` that the *class*-form rep requires). This is the gap-free route around the
small-simplices / excision obstruction: a relative `(U'∪V')`-cycle `c` is swapped for a cover-fine
subdivision `Sdʲc` (preserving the homology class, `relHomology_mk_singularSd_iterate`), whose boundary
splits cover-subordinately (`exists_cover_fine_subdivision`); the pairing form then reads the connecting
pairing off as `⟨δ(cochainSplit U' ωR), Sdʲc⟩`.

The subdivision `Sdʲ` is **carried** into the output (it cannot be dropped: `kronecker δφ (Sdʲc) = ⟨δφ,c⟩`
fails for a non-cycle `c` — `δφ` is a coboundary, not a cocycle, so the subdivision-homotopy slack
`⟨δφ, T(∂c)⟩` need not vanish). The downstream cap-Leibniz match over the shared `z₀` absorbs it.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularConnSquareRHSScaffold
  SKEFTHawking.SingularRelCohomMvConnectingGeom SKEFTHawking.SingularRelativeCohomologyMVConnecting
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularSubdivision SKEFTHawking.SingularExcisionIso
  SKEFTHawking.SingularCohomologySnake

namespace SKEFTHawking.SingularConnSquareRHSPairing

/-- **RHS pairing reduction (gap-free).** The cohomology-MV-connecting pairing of `relCohomMvConnecting (mk ωR)`
against the class of a relative `(U'∪V')`-cycle `c` equals the explicit chain-level Kronecker pairing of the
seam-supported coboundary `δ(cochainSplit U' ωR)` against a cover-fine subdivision `Sdʲc`. Via the pairing form
`relKroneckerH_relCohomMvConnecting_cover_partition` (unconditional in the union-level membership), after a
class-preserving subdivision swap so `∂(Sdʲc)` splits cover-subordinately. The `Sdʲ` is intrinsic (the
coboundary `δφ` is not a cocycle, so it cannot be peeled off a non-cycle `c`). -/
theorem rhs_pairing_reduce {M : TopCat} [T2Space ↑M] {N : ℕ} (U' V' : Set ↑M)
    (hU' : IsOpen U') (hV' : IsOpen V')
    (ωR : LinearMap.ker (relCoboundaryₗ (U' ∩ V') (N + 1)))
    (c : SingularChain M (N + 1 + 1))
    (hccyc : RelativeChain.mk (U' ∪ V') (N + 1 + 1) c ∈ relCycles (U' ∪ V') (N + 1 + 1)) :
    ∃ j : ℕ,
      relKroneckerH (U' ∪ V')
          (relCohomMvConnecting U' V' hU' hV' N (RelativeCohomology.mk (U' ∩ V') (N + 1) ωR))
          (RelativeHomology.mk (U' ∪ V') (N + 1 + 1)
            ⟨RelativeChain.mk (U' ∪ V') (N + 1 + 1) c, hccyc⟩)
        = kronecker (coboundary M (N + 1) (cochainSplit U' (N + 1) ωR.1.1))
            ((⇑(SingularSubdivision.singularSd M (N + 1 + 1)))^[j] c) := by
  have hc : chainBoundary M (N + 1) c ∈ subspaceChains (U' ∪ V') (N + 1) := by
    have h := hccyc
    rw [show relCycles (U' ∪ V') (N + 1 + 1) = LinearMap.ker (relBoundary (U' ∪ V') (N + 1)) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff] at h
    exact h
  obtain ⟨j, u', w', hsplit⟩ := exists_cover_fine_subdivision hU' hV' c hc
  refine ⟨j, ?_⟩
  have hu : chainIncl U' (N + 1) u' ∈ subspaceChains U' (N + 1) := ⟨u', rfl⟩
  have hw : chainIncl V' (N + 1) w' ∈ subspaceChains V' (N + 1) := ⟨w', rfl⟩
  have hSdcyc : RelativeChain.mk (U' ∪ V') (N + 1 + 1)
      ((⇑(SingularSubdivision.singularSd M (N + 1 + 1)))^[j] c) ∈ relCycles (U' ∪ V') (N + 1 + 1) := by
    rw [show relCycles (U' ∪ V') (N + 1 + 1) = LinearMap.ker (relBoundary (U' ∪ V') (N + 1)) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff, hsplit]
    exact Submodule.add_mem _
      (SKEFTHawking.SingularMayerVietoris.subspaceChains_mono Set.subset_union_left (N + 1) hu)
      (SKEFTHawking.SingularMayerVietoris.subspaceChains_mono Set.subset_union_right (N + 1) hw)
  have hwcyc : RelativeChain.mk (U' ∩ V') (N + 1) (chainIncl V' (N + 1) w')
      ∈ relCycles (U' ∩ V') (N + 1) := by
    rw [show relCycles (U' ∩ V') (N + 1) = LinearMap.ker (relBoundary (U' ∩ V') N) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff,
      ← SingularExcision.subspaceChains_inf]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have hUcyc : chainBoundary M N (chainIncl U' (N + 1) u')
          + chainBoundary M N (chainIncl V' (N + 1) w') = 0 := by
        rw [← map_add, ← hsplit]; exact chainBoundary_chainBoundary_apply M N _
      have hVU : chainBoundary M N (chainIncl V' (N + 1) w')
          = chainBoundary M N (chainIncl U' (N + 1) u') :=
        eq_of_sub_eq_zero (by rw [ZModModule.sub_eq_add, add_comm]; exact hUcyc)
      rw [hVU, ← chainIncl_chainBoundary]; exact ⟨_, rfl⟩
    · rw [← chainIncl_chainBoundary]; exact ⟨_, rfl⟩
  rw [relHomology_mk_singularSd_iterate c hc hccyc j hSdcyc,
    relKroneckerH_relCohomMvConnecting_cover_partition U' V' hU' hV' N ωR _
      (chainIncl U' (N + 1) u') (chainIncl V' (N + 1) w') hu hw hsplit hwcyc hSdcyc]

/-- **Fundamental-cycle → `z₀` pairing reduction** (the cap-not-cycle resolution / shared-z₀ bridge):
a cocycle `c` (e.g. `gL ∪ b`, where `gL` is *relative* on `A=Kᶜ`) that **vanishes on `C(A)`** pairs
identically against `fund` and `z₀` whenever they differ by a boundary plus an `A`-chain
(`fund + z₀ = ∂η + a`, `a ∈ C(A)` — supplied by `fundCycleW_relHomologous`: `fund + z₀ ∈ relBoundaries A`).
Because `⟨c, ∂η⟩ = ⟨δc, η⟩ = 0` (cocycle) and `⟨c, a⟩ = 0` (vanishing on `A`). This is what lets the
connecting-square match reduce **both legs to pairings against the single shared absolute cycle `z₀`**
(`∂z₀ = 0`), the goal's "⟨g∪a', ∂z₀⟩ over the shared z₀". Over ℤ/2. Kernel-pure. -/
theorem pair_fund_eq_pair_z0 {X : TopCat} {n : ℕ} {A : Set ↑X} (c : SingularCochain X n)
    (hc : coboundary X n c = 0) (hcv : ∀ d ∈ subspaceChains A n, kronecker c d = 0)
    (fund z₀ : SingularChain X n) (η : SingularChain X (n + 1)) (a : SingularChain X n)
    (ha : a ∈ subspaceChains A n) (heq : fund + z₀ = chainBoundary X n η + a) :
    kronecker c fund = kronecker c z₀ := by
  have hca : kronecker c a = 0 := hcv a ha
  have h0 : kronecker c fund + kronecker c z₀ = 0 := by
    rw [← kronecker_add_right, heq, kronecker_add_right, ← kronecker_coboundary_chainBoundary, hc, hca]
    simp
  exact eq_of_sub_eq_zero (by rw [ZModModule.sub_eq_add]; exact h0)

/-- **A relative cocycle's ambient representative is an absolute cocycle that vanishes on `C(A)`** —
the two `pair_fund_eq_pair_z0` hypotheses, extracted from `gL : ker (relCoboundaryₗ A n)`. The absolute
cocycle part is `relCoboundaryₗ_coe` (`↑(relCoboundaryₗ f) = coboundary ↑f`) + the kernel hypothesis; the
vanishing part is `mem_relCochains` (a relative cochain pairs to 0 against every `C(A)`-chain). Lets the
connecting-square match instantiate `pair_fund_eq_pair_z0` with `c := gL.1.1`, `A := Kᶜ`. -/
theorem relCocycle_props {X : TopCat} {A : Set ↑X} {n : ℕ} (gL : LinearMap.ker (relCoboundaryₗ A n)) :
    coboundary X n gL.1.1 = 0 ∧ (∀ c ∈ subspaceChains A n, kronecker gL.1.1 c = 0) := by
  refine ⟨?_, (mem_relCochains (S := A) n gL.1.1).1 gL.1.2⟩
  have h := congrArg Subtype.val gL.2
  rw [relCoboundaryₗ_coe] at h
  simpa using h

/-- **Relative-boundary chain witness** (the `heq` foundation): if `mk_S w` is a relative boundary then
`w` differs from a genuine boundary by an `S`-chain — `∃ η a, a ∈ C(S) ∧ w = ∂η + a`. Extracts the
`range (relBoundary S n)` membership down to the chain level (`relBoundary_mk` + the
`RelativeChain.mk` kernel = `C(S)`). Feeds `pair_fund_eq_pair_z0`'s `heq` from `fundCycleW_relHomologous`
(`mk_Kᶜ(z₀ + fund) ∈ relBoundaries Kᶜ`). Over ℤ/2 (`a := ∂η + w`). Kernel-pure. -/
theorem exists_relBoundary_witness {X : TopCat} {S : Set ↑X} {n : ℕ} (w : SingularChain X n)
    (hw : RelativeChain.mk S n w ∈ relBoundaries S n) :
    ∃ (η : SingularChain X (n + 1)) (a : SingularChain X n),
      a ∈ subspaceChains S n ∧ w = chainBoundary X n η + a := by
  obtain ⟨rc, hrc⟩ := hw
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective _ rc
  erw [relBoundary_mk] at hrc
  refine ⟨η, chainBoundary X n η + w, ?_, ?_⟩
  · have hd : chainBoundary X n η - w ∈ subspaceChains S n :=
      (Submodule.Quotient.eq (subspaceChains S n)).mp hrc
    rwa [ZModModule.sub_eq_add] at hd
  · rw [← add_assoc, ZModModule.add_self, zero_add]

/-- **Cup of two cocycles is a cocycle** (over ℤ/2, the `hc` for the cup-form match leg
`c := cup (gL↾) b`): `δ(f ⌣ g) = 0` when `δf = 0` and `δg = 0`, via the cup-Leibniz `coboundary_cup`. -/
theorem cup_cocycle {X : TopCat} {p q : ℕ} (f : SingularCochain X p) (g : SingularCochain X q)
    (hf : coboundary X p f = 0) (hg : coboundary X q g = 0) :
    coboundary X (p + q) (SingularCohomologyMod2.cup f g) = 0 := by
  funext τ
  rw [SingularCohomologyMod2.coboundary_cup, hf, hg]
  simp

end SKEFTHawking.SingularConnSquareRHSPairing
