import Mathlib
import SKEFTHawking.SingularRelativeMVInt

/-!
# Integral relative Mayer–Vietoris: the connecting map `δ` and left-exactness (brick 18c)

The ℤ analog of the mod-2 `SingularRelativeMV` connecting apparatus (lines 265–618, 764–819,
1047–1066). The on-main `SingularRelativeMVInt` supplies the chain SES apparatus (`relMvChainDiagInt`,
`relMvChain_exactInt`, `bBoundaryInt`), the `Q`-form middle exactness `relMv_exact_middleInt`, and the
small-chains iso `iotaEquivInt` (`Hₙ₊₁(Q) ≅ Hₙ₊₁(M, U∪V)`). This module builds the missing
**connecting homomorphism** `δ : Hₙ₊₁(Q) → Hₙ(M, U∩V)` snake-lemma–style and its two exactness
statements:

* `relMv_exact_connectingInt` (`Q`-form): `range δ = ker Δ_*`, and
* `relMv_exact_connectingInt'` (textbook form): `range (relMvDeltaInt) = ker (relMvHomDiagInt)`.

The keystone consumer is **`relMvHomDiagInt_injective_of_acyclic`**: `relMvHomDiagInt U V k` is
injective once `Hₖ₊₁(M, U∪V; ℤ) = 0` (every element `= 0`), the ℤ gluing step of Hatcher 3.27.

Because `Δ` is **injective** (`relMvChainDiagInt_injective`), the snake extraction `∂_B b ↦ Δ⁻¹(∂_B b)`
is a genuine *linear* map (via `LinearEquiv.ofInjective Δ`), avoiding any non-canonical `C(U)+C(V)`
splitting. The only structural change from the mod-2 development is the sum-sign convention: the ℤ
`Σ` is a **difference** (`relMvChainSumInt`), so `c − c = 0` (via `sub_self`) replaces the mod-2
`c + c = 0` (via `ZModModule.add_self`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularRelativeMVInt

namespace SKEFTHawking.SingularRelativeMVInt

variable {M : TopCat}

/-! ## §1. The chain-level snake apparatus toward the connecting map `δ` -/

/-- `Δ` is a **chain map**: `Δ ∘ ∂_{U∩V} = ∂_B ∘ Δ`. -/
theorem relMvChainDiagInt_chainMap (U V : Set ↑M) (n : ℕ) (w : RelativeChainInt (U ∩ V) (n + 1)) :
    relMvChainDiagInt U V n (relBoundaryInt (U ∩ V) n w)
      = bBoundaryInt U V n (relMvChainDiagInt U V (n + 1) w) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [show (Submodule.Quotient.mk c : RelativeChainInt (U ∩ V) (n + 1))
        = RelativeChainInt.mk (U ∩ V) (n + 1) c from rfl,
    relBoundaryInt_mk, relMvChainDiagInt_mk, relMvChainDiagInt_mk, bBoundaryInt_mk]

/-- `∂_B² = 0` on the middle term (pointwise). -/
theorem bBoundaryInt_bBoundaryInt_apply (U V : Set ↑M) (n : ℕ)
    (p : RelativeChainInt U (n + 1 + 1) × RelativeChainInt V (n + 1 + 1)) :
    bBoundaryInt U V n (bBoundaryInt U V (n + 1) p) = 0 := by
  obtain ⟨pu, pv⟩ := p
  rw [bBoundaryInt, bBoundaryInt, LinearMap.prodMap_apply, LinearMap.prodMap_apply,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply, relBoundaryInt_comp_relBoundaryInt,
    relBoundaryInt_comp_relBoundaryInt, LinearMap.zero_apply, LinearMap.zero_apply]
  rfl

/-- The **lift submodule** `L_n = { b ∈ B_{n+1} | Σ(∂_B b) = 0 }` — middle `(n+1)`-chains whose boundary
maps to a `Q`-cycle. Every `Q`-`(n+1)`-cycle lifts here (`Σ` surjective). -/
noncomputable def relLiftInt (U V : Set ↑M) (n : ℕ) :
    Submodule ℤ (RelativeChainInt U (n + 1) × RelativeChainInt V (n + 1)) :=
  LinearMap.ker ((relMvChainSumInt U V n).comp (bBoundaryInt U V n))

/-- For `b ∈ L`, `∂_B b ∈ ker Σ = range Δ` (`relMvChain_exactInt`). -/
theorem bBoundaryInt_mem_range_relMvChainDiagInt (U V : Set ↑M) (n : ℕ) (b : relLiftInt U V n) :
    bBoundaryInt U V n (b : RelativeChainInt U (n + 1) × RelativeChainInt V (n + 1))
      ∈ LinearMap.range (relMvChainDiagInt U V n) := by
  have hsum : relMvChainSumInt U V n (bBoundaryInt U V n (b : _)) = 0 := by
    have := LinearMap.mem_ker.mp b.2; rwa [LinearMap.comp_apply] at this
  obtain ⟨a, ha⟩ := (relMvChain_exactInt U V n _).mp hsum
  exact ⟨a, ha⟩

/-- The snake **extraction** `L_n → C(M,U∩V)_n`, `b ↦ Δ⁻¹(∂_B b)` — linear because `Δ` is injective
(`LinearEquiv.ofInjective`). -/
noncomputable def extractAInt (U V : Set ↑M) (n : ℕ) :
    relLiftInt U V n →ₗ[ℤ] RelativeChainInt (U ∩ V) n :=
  (LinearEquiv.ofInjective (relMvChainDiagInt U V n)
      (relMvChainDiagInt_injective U V n)).symm.toLinearMap.comp
    ((bBoundaryInt U V n).restrict (fun b hb => bBoundaryInt_mem_range_relMvChainDiagInt U V n ⟨b, hb⟩))

/-- The extraction recovers `∂_B b` after re-applying `Δ`: `Δ (extractA b) = ∂_B b`. -/
theorem relMvChainDiagInt_extractAInt (U V : Set ↑M) (n : ℕ) (b : relLiftInt U V n) :
    relMvChainDiagInt U V n (extractAInt U V n b)
      = bBoundaryInt U V n (b : RelativeChainInt U (n + 1) × RelativeChainInt V (n + 1)) := by
  rw [extractAInt, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofInjective_symm_apply,
    LinearMap.restrict_coe_apply]

/-- The extracted chain is a **relative cycle** of `(M, U∩V)`: `∂(extractA b) = 0`
(from `∂_B² = 0` + `Δ` injective). -/
theorem extractAInt_mem_relCyclesInt (U V : Set ↑M) (n : ℕ) (b : relLiftInt U V n) :
    extractAInt U V n b ∈ relCyclesInt (U ∩ V) n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    show extractAInt U V (m + 1) b ∈ LinearMap.ker (relBoundaryInt (U ∩ V) m)
    rw [LinearMap.mem_ker]
    apply relMvChainDiagInt_injective U V m
    rw [map_zero, relMvChainDiagInt_chainMap, relMvChainDiagInt_extractAInt,
      bBoundaryInt_bBoundaryInt_apply]

/-- The connecting map on lift-chains: `L_n →ₗ Hₙ(M,U∩V)`, `b ↦ [extractA b]`. -/
noncomputable def relConnectingLiftInt (U V : Set ↑M) (n : ℕ) :
    relLiftInt U V n →ₗ[ℤ] RelHomologyInt (U ∩ V) n :=
  (Submodule.mkQ _).comp ((extractAInt U V n).codRestrict (relCyclesInt (U ∩ V) n)
    (extractAInt_mem_relCyclesInt U V n))

theorem relConnectingLiftInt_apply (U V : Set ↑M) (n : ℕ) (b : relLiftInt U V n) :
    relConnectingLiftInt U V n b = RelHomologyInt.mk (U ∩ V) n
      ⟨extractAInt U V n b, extractAInt_mem_relCyclesInt U V n b⟩ := rfl

/-- `Σ b` is a `Q`-cycle for `b ∈ L`: `∂_Q (Σ b) = Σ(∂_B b) = 0`. -/
theorem relMvChainSumInt_mem_qCyclesInt (U V : Set ↑M) (n : ℕ) (b : relLiftInt U V n) :
    relMvChainSumInt U V (n + 1) (b : RelativeChainInt U (n + 1) × RelativeChainInt V (n + 1))
      ∈ qCyclesInt U V (n + 1) := by
  have h0 : qBoundaryInt U V n (relMvChainSumInt U V (n + 1) (b : _)) = 0 := by
    rw [← relMvChainSumInt_chainMap]
    have := LinearMap.mem_ker.mp b.2; rwa [LinearMap.comp_apply] at this
  exact LinearMap.mem_ker.mpr h0

/-- The surjection `L_n ↠ Hₙ₊₁(Q)`, `b ↦ [Σ b]` — every `Q`-`(n+1)`-cycle lifts to the middle term. -/
noncomputable def relLiftToQHomInt (U V : Set ↑M) (n : ℕ) :
    relLiftInt U V n →ₗ[ℤ] QHomologyInt U V (n + 1) :=
  (Submodule.mkQ _).comp
    ((show relLiftInt U V n →ₗ[ℤ] QChainInt U V (n + 1) from
        (relMvChainSumInt U V (n + 1)).comp (relLiftInt U V n).subtype).codRestrict
      (qCyclesInt U V (n + 1)) (fun b => relMvChainSumInt_mem_qCyclesInt U V n b))

theorem relLiftToQHomInt_apply (U V : Set ↑M) (n : ℕ) (b : relLiftInt U V n) :
    relLiftToQHomInt U V n b = QHomologyInt.mk U V (n + 1)
      ⟨relMvChainSumInt U V (n + 1) (b : _), relMvChainSumInt_mem_qCyclesInt U V n b⟩ := rfl

theorem relLiftToQHomInt_surjective (U V : Set ↑M) (n : ℕ) :
    Function.Surjective (relLiftToQHomInt U V n) := by
  intro h
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨b, hb⟩ := relMvChainSumInt_surjective U V (n + 1) (z : QChainInt U V (n + 1))
  have hbL : b ∈ relLiftInt U V n := by
    rw [relLiftInt, LinearMap.mem_ker, LinearMap.comp_apply, relMvChainSumInt_chainMap, hb]
    exact LinearMap.mem_ker.mp z.2
  refine ⟨⟨b, hbL⟩, ?_⟩
  rw [relLiftToQHomInt_apply]
  exact congrArg (QHomologyInt.mk U V (n + 1)) (Subtype.ext hb)

/-- **Snake-lemma well-definedness**: `ker(b ↦ [Σ b]) ≤ ker(b ↦ [extractA b])`. If `[Σ b] = 0` in
`Hₙ₊₁(Q)`, write `Σ b = ∂_Q q'`, lift `q' = Σ b'`; then `b − ∂_B b' = Δ a'` (exactness), whence
`extractA b = ∂ a'` is a relative boundary. -/
theorem relConnectingInt_ker_le (U V : Set ↑M) (n : ℕ) :
    LinearMap.ker (relLiftToQHomInt U V n) ≤ LinearMap.ker (relConnectingLiftInt U V n) := by
  intro b hb
  rw [LinearMap.mem_ker, relLiftToQHomInt_apply, QHomologyInt.mk_eq_zero_iff] at hb
  rw [LinearMap.mem_ker, relConnectingLiftInt_apply]
  obtain ⟨q', hq'⟩ := hb
  obtain ⟨b', hb'⟩ := relMvChainSumInt_surjective U V (n + 2) q'
  have hker : relMvChainSumInt U V (n + 1)
      ((b : RelativeChainInt U (n + 1) × RelativeChainInt V (n + 1))
        - bBoundaryInt U V (n + 1) b') = 0 := by
    rw [map_sub, relMvChainSumInt_chainMap, hb', hq', sub_self]
  obtain ⟨a', ha'⟩ := (relMvChain_exactInt U V (n + 1) _).mp hker
  refine (RelHomologyInt.mk_eq_zero_iff (U ∩ V) n _).2 ?_
  show extractAInt U V n b ∈ relBoundariesInt (U ∩ V) n
  have hextract : extractAInt U V n b = relBoundaryInt (U ∩ V) n a' := by
    apply relMvChainDiagInt_injective U V n
    rw [relMvChainDiagInt_extractAInt, relMvChainDiagInt_chainMap, ha', map_sub,
      bBoundaryInt_bBoundaryInt_apply, sub_zero]
  rw [hextract]
  exact LinearMap.mem_range_self _ a'

/-- **The relative MV connecting homomorphism** `δ : Hₙ₊₁(M, U∪V) → Hₙ(M, U∩V)` — in its `Q`-form
`Hₙ₊₁(Q) → Hₙ(M, U∩V)`, the snake descent of `relConnectingLiftInt` through `relLiftToQHomInt`. -/
noncomputable def relConnectingInt (U V : Set ↑M) (n : ℕ) :
    QHomologyInt U V (n + 1) →ₗ[ℤ] RelHomologyInt (U ∩ V) n :=
  (Submodule.liftQ (LinearMap.ker (relLiftToQHomInt U V n)) (relConnectingLiftInt U V n)
    (relConnectingInt_ker_le U V n)).comp
    (LinearMap.quotKerEquivOfSurjective (relLiftToQHomInt U V n)
      (relLiftToQHomInt_surjective U V n)).symm.toLinearMap

/-- The connecting map on the class of a lift-chain `b ∈ L_n` is `[extractA b]`. -/
theorem relConnectingInt_relLiftToQHomInt (U V : Set ↑M) (n : ℕ) (b : relLiftInt U V n) :
    relConnectingInt U V n (relLiftToQHomInt U V n b) = relConnectingLiftInt U V n b := by
  rw [relConnectingInt, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-! ## §2. The `U`/`V`-factors of `extractA` and the `Q`-form connecting exactness -/

/-- The `U`-factor of `extractA b` is the boundary of `(↑b).1` (so its `Hₙ(M,U)` class vanishes). -/
theorem relMapChainInt_extractAInt_left (U V : Set ↑M) (n : ℕ) (b : relLiftInt U V n) :
    relMapChainInt (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_left hx) n (extractAInt U V n b)
      = relBoundaryInt U n (b : RelativeChainInt U (n + 1) × RelativeChainInt V (n + 1)).1 := by
  have h := relMvChainDiagInt_extractAInt U V n b
  rw [relMvChainDiagInt, LinearMap.prod_apply, bBoundaryInt, LinearMap.prodMap_apply] at h
  exact congrArg Prod.fst h

/-- The `V`-factor of `extractA b` is the boundary of `(↑b).2`. -/
theorem relMapChainInt_extractAInt_right (U V : Set ↑M) (n : ℕ) (b : relLiftInt U V n) :
    relMapChainInt (ContinuousMap.id ↑M) (fun _ hx => Set.inter_subset_right hx) n (extractAInt U V n b)
      = relBoundaryInt V n (b : RelativeChainInt U (n + 1) × RelativeChainInt V (n + 1)).2 := by
  have h := relMvChainDiagInt_extractAInt U V n b
  rw [relMvChainDiagInt, LinearMap.prod_apply, bBoundaryInt, LinearMap.prodMap_apply] at h
  exact congrArg Prod.snd h

/-- **Relative MV exactness at `Hₙ(M, U∩V)`** (`Q`-form): `range δ = ker(relMvHomDiagInt)`. With
`Hₙ₊₁(Q) = 0` (the inductive hypothesis), this gives injectivity of `Hₙ(M,U∩V) → Hₙ(M,U) ⊕ Hₙ(M,V)` —
the gluing step of Hatcher 3.27. -/
theorem relMv_exact_connectingInt (U V : Set ↑M) (n : ℕ) :
    Function.Exact (relConnectingInt U V n) (relMvHomDiagInt U V n) := by
  intro x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hxU : relInclInt Set.inter_subset_left n (RelHomologyInt.mk (U ∩ V) n z) = 0 :=
      congrArg Prod.fst hx
    have hxV : relInclInt Set.inter_subset_right n (RelHomologyInt.mk (U ∩ V) n z) = 0 :=
      congrArg Prod.snd hx
    rw [relInclInt_mk, RelHomologyInt.mk_eq_zero_iff, relCyclesMapInt_coe] at hxU hxV
    obtain ⟨wU, hwU⟩ := hxU
    obtain ⟨wV, hwV⟩ := hxV
    have hbeq : bBoundaryInt U V n (wU, wV) = relMvChainDiagInt U V n (z : RelativeChainInt (U ∩ V) n) := by
      rw [bBoundaryInt, LinearMap.prodMap_apply, hwU, hwV]; rfl
    have hbL : (wU, wV) ∈ relLiftInt U V n := by
      rw [relLiftInt, LinearMap.mem_ker, LinearMap.comp_apply, hbeq, relMvChainSumInt_relMvChainDiagInt]
    have hextract : extractAInt U V n ⟨(wU, wV), hbL⟩ = (z : RelativeChainInt (U ∩ V) n) := by
      apply relMvChainDiagInt_injective U V n
      rw [relMvChainDiagInt_extractAInt]; exact hbeq
    refine ⟨relLiftToQHomInt U V n ⟨(wU, wV), hbL⟩, ?_⟩
    rw [relConnectingInt_relLiftToQHomInt, relConnectingLiftInt_apply]
    exact congrArg (RelHomologyInt.mk (U ∩ V) n) (Subtype.ext hextract)
  · rintro ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := relLiftToQHomInt_surjective U V n y
    rw [relConnectingInt_relLiftToQHomInt, relConnectingLiftInt_apply]
    refine Prod.ext ?_ ?_
    · show relInclInt Set.inter_subset_left n (RelHomologyInt.mk (U ∩ V) n _) = 0
      rw [relInclInt_mk, RelHomologyInt.mk_eq_zero_iff, relCyclesMapInt_coe]
      show relMapChainInt (ContinuousMap.id ↑M) _ n (extractAInt U V n b) ∈ relBoundariesInt U n
      rw [relMapChainInt_extractAInt_left]
      exact LinearMap.mem_range_self _ _
    · show relInclInt Set.inter_subset_right n (RelHomologyInt.mk (U ∩ V) n _) = 0
      rw [relInclInt_mk, RelHomologyInt.mk_eq_zero_iff, relCyclesMapInt_coe]
      show relMapChainInt (ContinuousMap.id ↑M) _ n (extractAInt U V n b) ∈ relBoundariesInt V n
      rw [relMapChainInt_extractAInt_right]
      exact LinearMap.mem_range_self _ _

/-! ## §3. The textbook connecting map and connecting exactness (`Hₙ(M, U∪V)` form) -/

/-- **The relative MV connecting map** `δ : Hₙ₊₁(M, U∪V) → Hₙ(M, U∩V)` in textbook form — the `Q`-form
connecting map `relConnectingInt` pulled back along the small-chains iso `iotaEquivInt`. -/
noncomputable def relMvDeltaInt (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ) :
    RelHomologyInt (U ∪ V) (k + 1) →ₗ[ℤ] RelHomologyInt (U ∩ V) k :=
  (relConnectingInt U V k).comp (iotaEquivInt U V hU hV k).symm.toLinearMap

/-- **Relative MV exactness at `Hₙ(M, U∩V)`** in textbook form: `range δ = ker(relMvHomDiagInt)`. The
gluing step of Hatcher 3.27 (`Hₖ₊₁(M,U∪V) = 0` ⟹ `Hₖ(M,U∩V) → Hₖ(M,U) ⊕ Hₖ(M,V)` injective). -/
theorem relMv_exact_connectingInt' (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ) :
    Function.Exact (relMvDeltaInt U V hU hV k) (relMvHomDiagInt U V k) := by
  intro x
  rw [relMv_exact_connectingInt U V k x]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨iotaEquivInt U V hU hV k y, ?_⟩
    rw [relMvDeltaInt, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨(iotaEquivInt U V hU hV k).symm y, rfl⟩

/-- **MV gluing injectivity** (Hatcher 3.27, ℤ): `Hₖ(M | A∪B) → Hₖ(M | A) ⊕ Hₖ(M | B)` is injective when
`Hₖ₊₁(M | A∩B) = 0` (the inductive hypothesis). In the `U = M∖A`, `V = M∖B` form: `relMvHomDiagInt` is
injective once `Hₖ₊₁(M, U∪V) = 0`, directly from the relative MV exactness `range δ = ker Δ_*`. -/
theorem relMvHomDiagInt_injective_of_acyclic {U V : Set ↑M} (hU : IsOpen U) (hV : IsOpen V) (k : ℕ)
    (h : ∀ x : RelHomologyInt (U ∪ V) (k + 1), x = 0) :
    Function.Injective (relMvHomDiagInt U V k) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, hy⟩ := (relMv_exact_connectingInt' U V hU hV k x).mp hx
  rw [← hy, h y, map_zero]

end SKEFTHawking.SingularRelativeMVInt
