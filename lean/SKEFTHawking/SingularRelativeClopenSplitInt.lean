import Mathlib
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularClopenSplitInt
import SKEFTHawking.SingularRelativeDisjointUnionHn

/-!
# THE RELATIVE CLOPEN-SPLIT ENGINE, INTEGRALLY: `Hₙ(X, S; ℤ) ≅ Hₙ(U, S∩U; ℤ) × Hₙ(Uᶜ, S∩Uᶜ; ℤ)`

The **integral** mirror of `SingularRelativeDisjointUnionHn.relSplitHnEquiv` (mod 2) and the
relative analogue of `SingularClopenSplitInt.splitHIntEquiv` (absolute, integral). For a clopen
decomposition `X = U ⊔ Uᶜ` of the ambient `X : TopCat` and an **arbitrary** subspace `S : Set ↑X`,
integral relative singular homology splits over the two clopen pieces:

`RelHomologyInt S n ≅ RelHomologyInt (restr S U) n × RelHomologyInt (restr S Uᶜ) n`,

where `restr S U = Subtype.val ⁻¹' S : Set ↑(sub U)` is `S` pulled back to the clopen piece.

## Why this is the missing brick

The two on-main relatives were each half of what the local-homology route needs:

* `SingularRelativeDisjointUnionHn` is relative but **mod 2** — it cannot see the ℤ-summands the
  `H₂ ≅ ℤ` computations are made of;
* `SingularClopenSplitInt` is integral but **absolute** — `Hₙ(X;ℤ) ≅ Hₙ(U;ℤ) × Hₙ(Uᶜ;ℤ)`, blind to
  the subspace filtration `S`.

This module is their pushout. Its immediate consumers:

1. **Local homology of a disjoint compact** — `Hₙ(M | K₀ ⊔ K₁) ≅ Hₙ(M|K₀) × Hₙ(M|K₁)` when the two
   compacts have disjoint open neighbourhoods: excise into `U = U₀ ⊔ U₁` (which *is* clopen-split as
   an ambient space, even though `M` is connected), split there, excise back
   (`relLocalDisjointEquivInt` in §5).
2. **The pair-level transport** `(ESub, CollarInE) → 16 × (ResE, collar)`: `ESub` is sixteen disjoint
   resolution pieces, and the collar is an arbitrary subspace of it — exactly the shape
   `relSplitHnIntEquiv` handles and `SingularClopenSplitInt` cannot.

## Mechanism (the mod-2 argument, integrally)

A singular simplex has connected image, so it lands wholly in `U` or in `Uᶜ`; hence every absolute
chain splits at every degree (`subspaceChainsInt_sup_compl_eq_top`). The relative ingredient is that
this split is compatible with the subspace-chain filtration `C•(S;ℤ)`: the reflection
`chainIncl_mem_subspaceChainsInt_iff` plus the disjoint-support separation
(`chainIncl_mem_subspaceChainsInt_of_add`) show the `U`-part of any `S`-subspace chain is again an
`S`-subspace chain.

The simplex-level disjointness input (`simplexIncl_range_disjoint`) is **coefficient-free** and is
reused verbatim from the mod-2 development. The one place the mod-2 proof genuinely used
characteristic 2 — recovering `z = ∂w` from `∂w + z = 0` — is *simpler* over ℤ: state the separation
on `∂w - z` and read off `∂w = z` by `sub_eq_zero`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularRelativeDisjointUnionHn (simplexIncl_range_disjoint)
open SKEFTHawking.SingularLineMinusPointInt (subspaceChainsInt_sup_compl_eq_top)

namespace SKEFTHawking.SingularRelativeClopenSplitInt

variable {X : TopCat}

/-! ## §1. The disjoint-support separation of an `S`-subspace chain (integral) -/

/-- **The disjoint-support separation** (integral): if a `U`-chain plus a `Uᶜ`-chain lies in the
`S`-subspace chains, then the `U`-summand does on its own. Their supports are disjoint
(`simplexIncl_range_disjoint`, coefficient-free), so every `U`-supported simplex survives in the
sum's support and is therefore `S`-valued. -/
theorem chainIncl_mem_subspaceChainsInt_of_add {U : Set ↑X} (S : Set ↑X) (n : ℕ)
    (cU : SingularChainInt (sub U) n) (cUc : SingularChainInt (sub Uᶜ) n)
    (h : chainIncl U n cU + chainIncl Uᶜ n cUc ∈ subspaceChainsInt S n) :
    chainIncl U n cU ∈ subspaceChainsInt S n := by
  classical
  refine mem_subspaceChainsInt_of_support (fun τ hτ => ?_)
  refine range_of_mem_subspaceChainsInt h ?_
  have hτrange : τ ∈ Set.range (simplexIncl U n) := by
    have := Finsupp.mapDomain_support (s := cU) (f := simplexIncl U n)
      (by rw [chainIncl, Finsupp.lmapDomain_apply] at hτ; exact hτ)
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.1 this
    exact ⟨σ, rfl⟩
  have hUc0 : (chainIncl Uᶜ n cUc) τ = 0 := by
    by_contra hne
    exact simplexIncl_range_disjoint hτrange
      (by
        rw [chainIncl, Finsupp.lmapDomain_apply] at hne
        by_contra hnr
        exact hne (Finsupp.mapDomain_notin_range cUc τ hnr))
  have hUne : (chainIncl U n cU) τ ≠ 0 := Finsupp.mem_support_iff.1 hτ
  rw [Finsupp.mem_support_iff, Finsupp.add_apply, hUc0, add_zero]
  exact hUne

/-! ## §2. The relative injectivity core -/

/-- **The relative injectivity core** (integral): if
`relChainInclInt S U aU + relChainInclInt S Uᶜ aUc = 0` in `Cₙ(X, S; ℤ)`, then each summand is `0`. -/
theorem relChainInclInt_sum_eq_zero_split {U : Set ↑X} (S : Set ↑X) (n : ℕ)
    (aU : RelativeChainInt (restr S U) n) (aUc : RelativeChainInt (restr S Uᶜ) n)
    (h : relChainInclInt S U n aU + relChainInclInt S Uᶜ n aUc = 0) :
    aU = 0 ∧ aUc = 0 := by
  obtain ⟨cU, rfl⟩ := Submodule.Quotient.mk_surjective _ aU
  obtain ⟨cUc, rfl⟩ := Submodule.Quotient.mk_surjective _ aUc
  rw [show (Submodule.Quotient.mk cU : RelativeChainInt (restr S U) n)
        = RelativeChainInt.mk (restr S U) n cU from rfl,
    show (Submodule.Quotient.mk cUc : RelativeChainInt (restr S Uᶜ) n)
        = RelativeChainInt.mk (restr S Uᶜ) n cUc from rfl,
    relChainInclInt_mk, relChainInclInt_mk] at h
  have hsum : chainIncl U n cU + chainIncl Uᶜ n cUc ∈ subspaceChainsInt S n := by
    refine (RelativeChainInt.mk_eq_zero_iff S n (chainIncl U n cU + chainIncl Uᶜ n cUc)).1 ?_
    rw [show RelativeChainInt.mk S n (chainIncl U n cU + chainIncl Uᶜ n cUc)
        = RelativeChainInt.mk S n (chainIncl U n cU)
          + RelativeChainInt.mk S n (chainIncl Uᶜ n cUc) from (Submodule.Quotient.mk_add _)]
    exact h
  have hU : chainIncl U n cU ∈ subspaceChainsInt S n :=
    chainIncl_mem_subspaceChainsInt_of_add S n cU cUc hsum
  have hUc : chainIncl Uᶜ n cUc ∈ subspaceChainsInt S n := by
    have heq : chainIncl Uᶜ n cUc
        = (chainIncl U n cU + chainIncl Uᶜ n cUc) - chainIncl U n cU := by abel
    rw [heq]
    exact Submodule.sub_mem _ hsum hU
  refine ⟨?_, ?_⟩
  · rw [show (Submodule.Quotient.mk cU : RelativeChainInt (restr S U) n)
        = RelativeChainInt.mk (restr S U) n cU from rfl, RelativeChainInt.mk_eq_zero_iff]
    exact (chainIncl_mem_subspaceChainsInt_iff S U cU).1 hU
  · rw [show (Submodule.Quotient.mk cUc : RelativeChainInt (restr S Uᶜ) n)
        = RelativeChainInt.mk (restr S Uᶜ) n cUc from rfl, RelativeChainInt.mk_eq_zero_iff]
    exact (chainIncl_mem_subspaceChainsInt_iff S Uᶜ cUc).1 hUc

/-- **The two-piece relative-chain map is surjective** (integral): every relative chain of `(X, S)`
splits across the clopen partition. -/
theorem relChainInclInt_sum_surjective {U : Set ↑X} (hU : IsClopen U) (S : Set ↑X) (n : ℕ)
    (w : RelativeChainInt S n) :
    ∃ (wU : RelativeChainInt (restr S U) n) (wUc : RelativeChainInt (restr S Uᶜ) n),
      w = relChainInclInt S U n wU + relChainInclInt S Uᶜ n wUc := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hc : (c : SingularChainInt X n)
      ∈ subspaceChainsInt (S := U) n ⊔ subspaceChainsInt (S := Uᶜ) n := by
    rw [subspaceChainsInt_sup_compl_eq_top hU]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hc
  obtain ⟨_, ⟨cU, rfl⟩, _, ⟨cUc, rfl⟩, hsum⟩ := hc
  refine ⟨RelativeChainInt.mk (restr S U) n cU, RelativeChainInt.mk (restr S Uᶜ) n cUc, ?_⟩
  rw [relChainInclInt_mk, relChainInclInt_mk,
    show (Submodule.Quotient.mk c : RelativeChainInt S n) = RelativeChainInt.mk S n c from rfl,
    ← hsum,
    show RelativeChainInt.mk S n (chainIncl U n cU + chainIncl Uᶜ n cUc)
      = RelativeChainInt.mk S n (chainIncl U n cU) + RelativeChainInt.mk S n (chainIncl Uᶜ n cUc)
      from (Submodule.Quotient.mk_add _)]

/-! ## §3. The cycle and boundary splits -/

/-- **The relative cycle split** (integral). -/
theorem relCyclesInt_split {U : Set ↑X} (S : Set ↑X) (n : ℕ)
    (aU : RelativeChainInt (restr S U) n) (aUc : RelativeChainInt (restr S Uᶜ) n)
    (h : relChainInclInt S U n aU + relChainInclInt S Uᶜ n aUc ∈ relCyclesInt S n) :
    aU ∈ relCyclesInt (restr S U) n ∧ aUc ∈ relCyclesInt (restr S Uᶜ) n := by
  cases n with
  | zero => exact ⟨Submodule.mem_top, Submodule.mem_top⟩
  | succ m =>
    rw [relCyclesInt, LinearMap.mem_ker, map_add, relBoundaryInt_relChainInclInt,
      relBoundaryInt_relChainInclInt] at h
    obtain ⟨h1, h2⟩ := relChainInclInt_sum_eq_zero_split S m _ _ h
    exact ⟨LinearMap.mem_ker.mpr h1, LinearMap.mem_ker.mpr h2⟩

/-- **The relative boundary split** (integral). Over ℤ the separation is applied to `∂w - z`, so the
bounding witness is read off directly by `sub_eq_zero` — no characteristic-2 step. -/
theorem relBoundariesInt_split {U : Set ↑X} (hU : IsClopen U) (S : Set ↑X) (n : ℕ)
    (zU : RelativeChainInt (restr S U) n) (zUc : RelativeChainInt (restr S Uᶜ) n)
    (h : relChainInclInt S U n zU + relChainInclInt S Uᶜ n zUc ∈ relBoundariesInt S n) :
    zU ∈ relBoundariesInt (restr S U) n ∧ zUc ∈ relBoundariesInt (restr S Uᶜ) n := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨wU, wUc, rfl⟩ := relChainInclInt_sum_surjective hU S (n + 1) w
  rw [map_add, relBoundaryInt_relChainInclInt, relBoundaryInt_relChainInclInt] at hw
  have hkey : relChainInclInt S U n (relBoundaryInt (restr S U) n wU - zU)
      + relChainInclInt S Uᶜ n (relBoundaryInt (restr S Uᶜ) n wUc - zUc) = 0 := by
    rw [map_sub, map_sub, sub_add_sub_comm, hw, sub_self]
  obtain ⟨h1, h2⟩ := relChainInclInt_sum_eq_zero_split S n _ _ hkey
  exact ⟨⟨wU, sub_eq_zero.mp h1⟩, ⟨wUc, sub_eq_zero.mp h2⟩⟩

/-! ## §4. The additivity map and its bijectivity -/

/-- **The relative additivity map** `Hₙ(U, S∩U; ℤ) × Hₙ(Uᶜ, S∩Uᶜ; ℤ) → Hₙ(X, S; ℤ)`. -/
noncomputable def relSplitHnInt (U : Set ↑X) (S : Set ↑X) (n : ℕ) :
    RelHomologyInt (restr S U) n × RelHomologyInt (restr S Uᶜ) n →ₗ[ℤ] RelHomologyInt S n :=
  (excisionMapInt S U n).coprod (excisionMapInt S Uᶜ n)

theorem relSplitHnInt_apply (U : Set ↑X) (S : Set ↑X) (n : ℕ)
    (a : RelHomologyInt (restr S U) n) (b : RelHomologyInt (restr S Uᶜ) n) :
    relSplitHnInt U S n (a, b) = excisionMapInt S U n a + excisionMapInt S Uᶜ n b := rfl

theorem relSplitHnInt_surjective {U : Set ↑X} (hU : IsClopen U) (S : Set ↑X) (n : ℕ) :
    Function.Surjective (relSplitHnInt U S n) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨wU, wUc, hzsplit⟩ := relChainInclInt_sum_surjective hU S n (z : RelativeChainInt S n)
  have hcyc : relChainInclInt S U n wU + relChainInclInt S Uᶜ n wUc ∈ relCyclesInt S n :=
    hzsplit ▸ z.2
  obtain ⟨hwU, hwUc⟩ := relCyclesInt_split S n wU wUc hcyc
  refine ⟨(RelHomologyInt.mk (restr S U) n ⟨wU, hwU⟩,
      RelHomologyInt.mk (restr S Uᶜ) n ⟨wUc, hwUc⟩), ?_⟩
  rw [relSplitHnInt_apply]
  show excisionMapInt S U n (RelHomologyInt.mk (restr S U) n ⟨wU, hwU⟩)
      + excisionMapInt S Uᶜ n (RelHomologyInt.mk (restr S Uᶜ) n ⟨wUc, hwUc⟩)
    = RelHomologyInt.mk S n z
  rw [excisionMapInt_mk, excisionMapInt_mk,
    show (RelHomologyInt.mk S n ⟨relChainInclInt S U n wU, _⟩
        + RelHomologyInt.mk S n ⟨relChainInclInt S Uᶜ n wUc, _⟩)
      = RelHomologyInt.mk S n (⟨relChainInclInt S U n wU, _⟩
          + ⟨relChainInclInt S Uᶜ n wUc, _⟩) from (Submodule.Quotient.mk_add _)]
  refine congrArg (RelHomologyInt.mk S n) (Subtype.ext ?_)
  simpa using hzsplit.symm

theorem relSplitHnInt_injective {U : Set ↑X} (hU : IsClopen U) (S : Set ↑X) (n : ℕ) :
    Function.Injective (relSplitHnInt U S n) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro ⟨a, b⟩ hab
  rw [LinearMap.mem_ker] at hab
  obtain ⟨zU, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨zUc, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [relSplitHnInt_apply] at hab
  rw [show (Submodule.Quotient.mk zU : RelHomologyInt (restr S U) n)
        = RelHomologyInt.mk (restr S U) n zU from rfl,
    show (Submodule.Quotient.mk zUc : RelHomologyInt (restr S Uᶜ) n)
        = RelHomologyInt.mk (restr S Uᶜ) n zUc from rfl,
    excisionMapInt_mk, excisionMapInt_mk,
    show (RelHomologyInt.mk S n ⟨relChainInclInt S U n (zU : RelativeChainInt (restr S U) n), _⟩
        + RelHomologyInt.mk S n
          ⟨relChainInclInt S Uᶜ n (zUc : RelativeChainInt (restr S Uᶜ) n), _⟩)
      = RelHomologyInt.mk S n (⟨relChainInclInt S U n zU, _⟩
          + ⟨relChainInclInt S Uᶜ n zUc, _⟩) from (Submodule.Quotient.mk_add _)] at hab
  have hb : (relChainInclInt S U n (zU : RelativeChainInt (restr S U) n)
      + relChainInclInt S Uᶜ n (zUc : RelativeChainInt (restr S Uᶜ) n))
        ∈ relBoundariesInt S n :=
    (RelHomologyInt.mk_eq_zero_iff S n _).1 hab
  obtain ⟨hzU, hzUc⟩ := relBoundariesInt_split hU S n zU zUc hb
  have e1 : (Submodule.Quotient.mk zU : RelHomologyInt (restr S U) n) = 0 :=
    (RelHomologyInt.mk_eq_zero_iff (restr S U) n zU).mpr hzU
  have e2 : (Submodule.Quotient.mk zUc : RelHomologyInt (restr S Uᶜ) n) = 0 :=
    (RelHomologyInt.mk_eq_zero_iff (restr S Uᶜ) n zUc).mpr hzUc
  rw [Submodule.mem_bot]
  exact Prod.ext e1 e2

/-- **The integral relative clopen-split isomorphism**
`Hₙ(U, S∩U; ℤ) × Hₙ(Uᶜ, S∩Uᶜ; ℤ) ≅ Hₙ(X, S; ℤ)` for a clopen partition `X = U ⊔ Uᶜ` and an
arbitrary subspace `S ⊆ X`. -/
noncomputable def relSplitHnIntEquiv {U : Set ↑X} (hU : IsClopen U) (S : Set ↑X) (n : ℕ) :
    (RelHomologyInt (restr S U) n × RelHomologyInt (restr S Uᶜ) n) ≃ₗ[ℤ] RelHomologyInt S n :=
  LinearEquiv.ofBijective (relSplitHnInt U S n)
    ⟨relSplitHnInt_injective hU S n, relSplitHnInt_surjective hU S n⟩

end SKEFTHawking.SingularRelativeClopenSplitInt
