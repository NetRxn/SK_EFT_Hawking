/-
# Phase 5q.H (E1 CSC-PD tower) — integral cap-iso `capEquiv` assembly

Assembles the integral cap-with-`[M]` isomorphism `capEquivInt : Cohomology M k ≃ Homology M (m+1)`
(the `IntCapIso.capEquiv` field) from the completed pieces:
* `compactlySupportedTopEquivInt` (CSC-cohomology collapse onto ordinary cohomology, compact `M`);
* `fundamentalDuality_bijective_of_openDuality_univ_bijectiveInt` (the d1 ⊤-collapse bridge);
* `relativeDualityInt_empty_eq_capHInt` (the duality-over-`∅` = `capHInt` crux) transported across the
  colimit ⊤-stage by `relativeDualityInt_set_congr` (`(↑⊤)ᶜ = ∅`).

The payoff `fundamentalDualityInt_top_eq_capHInt` establishes `IntCapIso.capEquiv_apply` — the assembled
`D_univ` reads off as `capHInt · [M]`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCompactlySupportedTopInt
import SKEFTHawking.SingularFundamentalDualityTopInt
import SKEFTHawking.SingularDualityEmptyInt
import SKEFTHawking.IntersectionFormUnimodularInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCohomologyColimitInt
open SKEFTHawking.SingularCompactlySupportedTopInt
open SKEFTHawking.SingularRelativeCohomologyEmptyInt
open SKEFTHawking.SingularDualityEmptyInt
open SKEFTHawking.SingularFundamentalDualityInt
open SKEFTHawking.SingularFundamentalDualityTopInt
open SKEFTHawking.SingularOpenDualityInt

namespace SKEFTHawking.SingularIntCapEquivAssembly

variable {X : TopCat}

/-- **Set-congruence of `relativeDualityInt`**: for `S = T`, the integral duality map over `S` is the
duality map over `T` precomposed with `relCohomSetCongrInt`. A `subst` of the set. Integral mirror of
`SingularRelativeDualityCongr.relativeDuality_set_congr`. -/
theorem relativeDualityInt_set_congr {S T : Set ↑X} (hST : S = T) (k m : ℕ)
    (z : SingularChainInt X (k + m + 1)) (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (ω : RelativeCohomologyInt S k) :
    relativeDualityInt S k m z hzS ω
      = relativeDualityInt T k m z (hST ▸ hzS) (relCohomSetCongrInt hST k ω) := by
  subst hST
  rfl

/-- **The assembled `D_M` reads off as `capHInt · [z]`** (forward form): on the CSC-cohomology of a
compact `M`, `fundamentalDualityInt k m z hz` equals `capHInt k m · [z]` transported by the collapse
`compactlySupportedTopEquivInt`. Chains the ⊤-stage `lift_of`, the `(↑⊤)ᶜ = ∅` set-congruence, and the
duality-over-`∅` crux `relativeDualityInt_empty_eq_capHInt`. -/
theorem fundamentalDualityInt_eq_capHInt_top {M : TopCat} [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (z : SingularChainInt M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (c : CompactlySupportedCohomologyInt (M := M) k) :
    fundamentalDualityInt k m z hz c
      = capHInt k m (compactlySupportedTopEquivInt k c) (Homology.mk M (k + m + 1) ⟨z, hz⟩) := by
  have hcT : (↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ = (∅ : Set ↑M) := by
    rw [TopologicalSpace.Compacts.coe_top, Set.compl_univ]
  obtain ⟨w, rfl⟩ := (SKEFTHawking.SingularDirectLimitTop.of_top_bijective
    (cohomGInt (M := M) k) (cohomFInt k)).surjective c
  have hlift : fundamentalDualityInt k m z hz
        (Module.DirectLimit.of ℤ (TopologicalSpace.Compacts ↑M) (cohomGInt k) (cohomFInt k) ⊤ w)
      = relativeDualityInt ((↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ) k m z
          (by rw [hz]; exact Submodule.zero_mem _) w :=
    Module.DirectLimit.lift_of _ _ w
  have htop : compactlySupportedTopEquivInt k
        (Module.DirectLimit.of ℤ (TopologicalSpace.Compacts ↑M) (cohomGInt k) (cohomFInt k) ⊤ w)
      = relCohomologyEmptyEquivInt k (relCohomSetCongrInt hcT k w) := by
    simp only [compactlySupportedTopEquivInt]
    erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  rw [hlift, htop, relativeDualityInt_set_congr hcT k m z _ w,
    relativeDualityInt_empty_eq_capHInt]

/-- **The integral cap-with-`[z]` isomorphism** `Cohomology M k ≃ Homology M (m+1)`, given a bijective
`D_univ` (`openDuality univ`, from the pdWindow cover-induction). This is the `IntCapIso.capEquiv` field:
the CSC-cohomology collapse composed with the (bijective) fixed-target duality. -/
noncomputable def capEquivInt {M : TopCat} [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChainInt M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (hD : Function.Bijective ⇑(openDuality (k := k) (m := m) hop z hz)) :
    Cohomology M k ≃ₗ[ℤ] Homology M (m + 1) :=
  (compactlySupportedTopEquivInt k).symm.trans
    (LinearEquiv.ofBijective (fundamentalDualityInt k m z hz)
      (fundamentalDuality_bijective_of_openDuality_univ_bijectiveInt hop z hz hD))

/-- **`capEquivInt` is `capHInt · [z]`** — the `IntCapIso.capEquiv_apply` obligation: the assembled
cap-iso underlying map is the integral cap-with-`[z]`. -/
theorem capEquivInt_apply {M : TopCat} [T2Space ↑M] [CompactSpace ↑M] {k m : ℕ}
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChainInt M (k + m + 1)) (hz : chainBoundary M (k + m) z = 0)
    (hD : Function.Bijective ⇑(openDuality (k := k) (m := m) hop z hz))
    (a : Cohomology M k) :
    capEquivInt hop z hz hD a = capHInt k m a (Homology.mk M (k + m + 1) ⟨z, hz⟩) := by
  rw [capEquivInt, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
    fundamentalDualityInt_eq_capHInt_top, LinearEquiv.apply_symm_apply]

/-- **`IntCapIso` from the assembled `capEquivInt` plus a Kronecker perfect-pairing datum.** Verifies
`capEquivInt` inhabits the `IntCapIso.capEquiv` slot (degree 2, cap-with-`[z]`) — so the integral cap-iso
`IntCapIso [z]` reduces to exactly the `H₂`-free Kronecker pairing `kronEquiv` (given a bijective
`D_univ` at the `(2,1)` window, i.e. the first conjunct of `pdWindowPInt_univ`). -/
noncomputable def intCapIsoOfCapEquiv {M : TopCat} [T2Space ↑M] [CompactSpace ↑M]
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChainInt M (2 + 1 + 1)) (hz : chainBoundary M (2 + 1) z = 0)
    (hD : Function.Bijective ⇑(openDuality (k := 2) (m := 1) hop z hz))
    (kron : Homology M 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology M 2))
    (hkron : ∀ (h : Homology M 2) (b : Cohomology M 2), kron h b = kroneckerHInt 2 b h) :
    IntCapIso (Homology.mk M (2 + 1 + 1) ⟨z, hz⟩) where
  capEquiv := capEquivInt hop z hz hD
  capEquiv_apply a := capEquivInt_apply hop z hz hD a
  kronEquiv := kron
  kronEquiv_apply := hkron

/-- **The integral intersection matrix is unimodular from the assembled cap-equiv** — the reduction
reaches σ÷16's actual input (an even-unimodular intersection form). Composes `intCapIsoOfCapEquiv` with
the DONE `interMatrix_isUnimodular_of_capIso`. The whole `Hᵏ_c`-PD → σ÷16 leg now rests on exactly:
`hD` (the `(2,1)` window of `pdWindowPInt_univ`, from the cover-induction) + `kronEquiv` (the `H₂`-free
Kronecker perfect pairing). -/
theorem interMatrix_unimodular_of_capEquiv {M : TopCat} [T2Space ↑M] [CompactSpace ↑M]
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChainInt M (2 + 1 + 1)) (hz : chainBoundary M (2 + 1) z = 0)
    (hD : Function.Bijective ⇑(openDuality (k := 2) (m := 1) hop z hz))
    (kron : Homology M 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology M 2))
    (hkron : ∀ (h : Homology M 2) (b : Cohomology M 2), kron h b = kroneckerHInt 2 b h)
    (B : IntH2Basis M) :
    IsUnimodular (interMatrix (intFundamentalClassOfHomology (Homology.mk M (2 + 1 + 1) ⟨z, hz⟩)) B) :=
  interMatrix_isUnimodular_of_capIso B (intCapIsoOfCapEquiv hop z hz hD kron hkron)

/-- **`16 ∣ σ` from the assembled cap-equiv — the FULL integral Poincaré-duality leg of the σ÷16
theorem.** Wires `intCapIsoOfCapEquiv` through `intPoincareDualityOfCapIso` into
`sixteen_dvd_manifold_sig_of_intPD`. This is the crispest statement of what remains: the entire
`Hᵏ_c`-PD → `16 ∣ σ` leg is kernel-pure glue, resting on EXACTLY five named inputs —
`hD` (the `(2,1)` window of `pdWindowPInt_univ`, from the cover-induction), the `H₂`-free Kronecker
pairing (`kron`+`hkron`) and its basis `B`, the spin-Wu datum `D` (even-form structure), and the
topological Rokhlin factor `htopo` (`2 ∣ σ/8`, = E2's Guillou–Marin content). -/
theorem sixteen_dvd_latticeSig_of_capEquiv {M : TopCat} [T2Space ↑M] [CompactSpace ↑M]
    (hop : IsOpen (Set.univ : Set ↑M))
    (z : SingularChainInt M (2 + 1 + 1)) (hz : chainBoundary M (2 + 1) z = 0)
    (hD : Function.Bijective ⇑(openDuality (k := 2) (m := 1) hop z hz))
    (kron : Homology M 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology M 2))
    (hkron : ∀ (h : Homology M 2) (b : Cohomology M 2), kron h b = kroneckerHInt 2 b h)
    (B : IntH2Basis M)
    (D : SpinWuDatum (intFundamentalClassOfHomology (Homology.mk M (2 + 1 + 1) ⟨z, hz⟩)))
    (htopo : (2 : ℤ) ∣
      latticeSig (interMatrix (intFundamentalClassOfHomology (Homology.mk M (2 + 1 + 1) ⟨z, hz⟩)) B) / 8) :
    (16 : ℤ) ∣
      latticeSig (interMatrix (intFundamentalClassOfHomology (Homology.mk M (2 + 1 + 1) ⟨z, hz⟩)) B) :=
  sixteen_dvd_manifold_sig_of_intPD _ B D
    (intPoincareDualityOfCapIso (intCapIsoOfCapEquiv hop z hz hD kron hkron)) htopo

end SKEFTHawking.SingularIntCapEquivAssembly
