import Mathlib
import SKEFTHawking.IntCapProductInt
import SKEFTHawking.SingularCapChainInclInt
import SKEFTHawking.SingularRelHomologyInt

/-!
# Phase 5q.H close-out — the **integral** relative cap product `⌢ : Hᵏ(X) × H_{k+m+1}(X,S) → H_{m+1}(X,S)`

The ℤ (integral) port of `SingularRelativeCapHomology.capRelH` (the mod-2 relative cap arc), capping an
**absolute** cohomology class `a ∈ Hᵏ(X;ℤ)` against a **relative** homology class `z ∈ H_{k+m+1}(X,S;ℤ)`:

  `capRelHInt k m : Hᵏ(X;ℤ) → H_{k+m+1}(X,S;ℤ) → H_{m+1}(X,S;ℤ)`.

This is the relative extension of the absolute integral cap `SingularCohomologyInt.capHInt`
(`IntCapProductInt`). The construction mirrors the mod-2 template `SingularRelativeCapHomology` verbatim
in structure — capping an absolute cochain against a **subspace** chain lands in the subspace chains again
(`cap_mem_subspaceChainsInt`, via the Alexander–Whitney back face `SingularCapChainInclInt.capInt_chainIncl`),
so `capInt a` descends through the relative-chain quotient (`capRelChainInt`), a cocycle caps a relative
cycle to a relative cycle, and a coboundary caps a relative cycle to a relative boundary.

## The coefficient port — structurally blind, mechanically re-instantiated over ℤ with explicit signs

The mod-2 arc is **not literally coefficient-blind** (its chain types are `ZMod 2`-fixed); but the proof
*architecture* ports directly, and the **absolute** integral cap `IntCapProductInt` already banks all sign
bookkeeping: the signed cap chain-map `∂(a ⌢ c) = (-1)ᵏ · (a ⌢ ∂c)` for a cocycle `a`
(`capInt_cocycle_chainMap`) and the signed cap-Leibniz (`capInt_leibniz`). The only genuine additions over
the mod-2 file are the `(-1)ᵏ` units the char-2 shadow drops — carried here through the relative descent
(they vanish at the consumer degree `k = 2`, but the port is degree-generic).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCapChainInclInt

namespace SKEFTHawking.SingularRelativeCapHomologyInt

variable {X : TopCat} {S : Set X} {k m : ℕ}

/-! ## §1. Capping an absolute cochain preserves the subspace chains -/

/-- **Capping an absolute cochain against a subspace chain stays in the subspace chains** (over ℤ). On a
subspace simplex `chainIncl S d`, `a ⌢ (chainIncl d) = chainIncl ((pullbackCochainInt a) ⌢ d)`
(`SingularCapChainInclInt.capInt_chainIncl`) — the *back* face `capInt` keeps is again a subspace simplex. -/
theorem cap_mem_subspaceChainsInt (a : SingularCochainInt X k) {c : SingularChainInt X (k + m)}
    (hc : c ∈ subspaceChainsInt S (k + m)) : capInt (m := m) a c ∈ subspaceChainsInt S m := by
  rw [subspaceChainsInt, LinearMap.mem_range] at hc
  obtain ⟨d, rfl⟩ := hc
  exact ⟨capInt (SingularCapChainInclInt.pullbackCochainInt S k a) d,
    (SingularCapChainInclInt.capInt_chainIncl (S := S) a d).symm⟩

/-! ## §2. The relative cap at the chain level and its (signed) relative chain-map property -/

/-- **The integral relative cap chain map** for a fixed absolute cochain `a : Cᵏ(X;ℤ)`:
`a ⌢ · : C_{k+m}(X, S;ℤ) → C_m(X, S;ℤ)`, `[c] ↦ [a ⌢ c]`, well-defined by `cap_mem_subspaceChainsInt`. -/
noncomputable def capRelChainInt (a : SingularCochainInt X k) :
    RelativeChainInt S (k + m) →ₗ[ℤ] RelativeChainInt S m :=
  Submodule.mapQ (subspaceChainsInt S (k + m)) (subspaceChainsInt S m) (capInt (m := m) a)
    (fun _ hc => cap_mem_subspaceChainsInt a hc)

@[simp] theorem capRelChainInt_mk (a : SingularCochainInt X k) (c : SingularChainInt X (k + m)) :
    capRelChainInt (S := S) (m := m) a (RelativeChainInt.mk S (k + m) c)
      = RelativeChainInt.mk S m (capInt a c) :=
  rfl

/-- **The signed relative chain-map property.** For an absolute cocycle `a` (`δa = 0`),
`∂(a ⌢ z) = (-1)ᵏ · (a ⌢ ∂z)` on relative chains (descends `capInt_cocycle_chainMap`). -/
theorem capRelChainInt_relBoundaryInt (a : LinearMap.ker (coboundaryₗ X k))
    (z : RelativeChainInt S (k + m + 1)) :
    relBoundaryInt S m (capRelChainInt (m := m + 1) a.1 z)
      = (-1 : ℤ) ^ k • capRelChainInt (m := m) a.1 (relBoundaryInt S (k + m) z) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  show relBoundaryInt S m (RelativeChainInt.mk S (m + 1) (capInt a.1 c))
      = (-1 : ℤ) ^ k • capRelChainInt (m := m) a.1
          (relBoundaryInt S (k + m) (RelativeChainInt.mk S (k + m + 1) c))
  rw [relBoundaryInt_mk, relBoundaryInt_mk, capRelChainInt_mk,
    capInt_cocycle_chainMap a.1 (LinearMap.mem_ker.mp a.2) c]
  exact (Submodule.Quotient.mk_smul _ _ _)

/-! ## §3. Descending the chain argument to relative homology (for a fixed cocycle) -/

/-- For a fixed absolute cocycle `a`, `capRelChainInt a` sends relative `(k+m+1)`-cycles to relative
`(m+1)`-cycles (`∂(a ⌢ z) = (-1)ᵏ·(a ⌢ ∂z) = 0` in `C(X, S;ℤ)`). -/
noncomputable def capRelCyclesIntₗ (a : LinearMap.ker (coboundaryₗ X k)) :
    relCyclesInt S (k + m + 1) →ₗ[ℤ] relCyclesInt S (m + 1) :=
  LinearMap.restrict (capRelChainInt (m := m + 1) a.1) (fun z hz => by
    show capRelChainInt (m := m + 1) a.1 z ∈ LinearMap.ker (relBoundaryInt S m)
    rw [LinearMap.mem_ker, capRelChainInt_relBoundaryInt,
      show relBoundaryInt S (k + m) z = 0 from LinearMap.mem_ker.mp hz, map_zero, smul_zero])

@[simp] theorem capRelCyclesIntₗ_coe (a : LinearMap.ker (coboundaryₗ X k))
    (z : relCyclesInt S (k + m + 1)) :
    (capRelCyclesIntₗ (m := m) a z : RelativeChainInt S (m + 1))
      = capRelChainInt (m := m + 1) a.1 (z : RelativeChainInt S (k + m + 1)) :=
  LinearMap.restrict_coe_apply _ _ _

/-- For a fixed absolute cocycle `a`, `capRelChainInt a` descends to a `ℤ`-linear map on relative
homology `H_{k+m+1}(X,S;ℤ) → H_{m+1}(X,S;ℤ)`. -/
noncomputable def capRelHomologyInt (a : LinearMap.ker (coboundaryₗ X k)) :
    RelHomologyInt S (k + m + 1) →ₗ[ℤ] RelHomologyInt S (m + 1) :=
  Submodule.mapQ _ _ (capRelCyclesIntₗ a) (by
    rintro ⟨z, hz⟩ hzb
    rw [Submodule.mem_comap]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hzb
    obtain ⟨w, hw⟩ := hzb
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype, capRelCyclesIntₗ_coe]
    refine ⟨(-1 : ℤ) ^ k • capRelChainInt (m := m + 2) a.1 w, ?_⟩
    rw [map_smul, capRelChainInt_relBoundaryInt, smul_smul,
      show (-1 : ℤ) ^ k * (-1) ^ k = 1 from by rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩,
      one_smul]
    exact congrArg (capRelChainInt (m := m + 1) a.1) hw)

@[simp] theorem capRelHomologyInt_mk (a : LinearMap.ker (coboundaryₗ X k))
    (z : relCyclesInt S (k + m + 1)) :
    capRelHomologyInt (m := m) a (RelHomologyInt.mk S (k + m + 1) z)
      = RelHomologyInt.mk S (m + 1) (capRelCyclesIntₗ a z) :=
  Submodule.mapQ_apply _ _ _ _

/-! ## §4. Linearity in the cochain and the cohomology-argument descent -/

/-- `capRelCyclesIntₗ` is additive in the cochain. -/
theorem capRelCyclesIntₗ_add (a a' : LinearMap.ker (coboundaryₗ X k)) (z : relCyclesInt S (k + m + 1)) :
    capRelCyclesIntₗ (m := m) (a + a') z = capRelCyclesIntₗ a z + capRelCyclesIntₗ a' z := by
  apply Subtype.ext
  simp only [Submodule.coe_add, capRelCyclesIntₗ_coe]
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChainInt S (k + m + 1))
  rw [← hc]
  show Submodule.Quotient.mk (capInt (m := m + 1) (a.1 + a'.1) c)
    = Submodule.Quotient.mk (capInt (m := m + 1) a.1 c)
      + Submodule.Quotient.mk (capInt (m := m + 1) a'.1 c)
  rw [capInt_add_cochain]
  exact map_add (Submodule.mkQ (subspaceChainsInt S (m + 1))) _ _

/-- `capRelCyclesIntₗ` commutes with the `ℤ`-action in the cochain. -/
theorem capRelCyclesIntₗ_smul (s : ℤ) (a : LinearMap.ker (coboundaryₗ X k))
    (z : relCyclesInt S (k + m + 1)) :
    capRelCyclesIntₗ (m := m) (s • a) z = s • capRelCyclesIntₗ a z := by
  apply Subtype.ext
  simp only [SetLike.val_smul, capRelCyclesIntₗ_coe]
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChainInt S (k + m + 1))
  rw [← hc]
  show Submodule.Quotient.mk (capInt (m := m + 1) (s • a.1) c)
    = s • Submodule.Quotient.mk (capInt (m := m + 1) a.1 c)
  rw [capInt_smul_cochain]
  exact map_smul (Submodule.mkQ (subspaceChainsInt S (m + 1))) _ _

/-- `capRelHomologyInt` is additive in the cochain. -/
theorem capRelHomologyInt_add (a a' : LinearMap.ker (coboundaryₗ X k)) :
    capRelHomologyInt (S := S) (m := m) (a + a') = capRelHomologyInt a + capRelHomologyInt a' := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show capRelHomologyInt (a + a') (RelHomologyInt.mk S (k + m + 1) z)
    = capRelHomologyInt a (RelHomologyInt.mk S (k + m + 1) z)
      + capRelHomologyInt a' (RelHomologyInt.mk S (k + m + 1) z)
  rw [capRelHomologyInt_mk, capRelHomologyInt_mk, capRelHomologyInt_mk, capRelCyclesIntₗ_add]
  rfl

/-- `capRelHomologyInt` commutes with the `ℤ`-action in the cochain. -/
theorem capRelHomologyInt_smul (s : ℤ) (a : LinearMap.ker (coboundaryₗ X k)) :
    capRelHomologyInt (S := S) (m := m) (s • a) = s • capRelHomologyInt a := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show capRelHomologyInt (s • a) (RelHomologyInt.mk S (k + m + 1) z)
    = s • capRelHomologyInt a (RelHomologyInt.mk S (k + m + 1) z)
  rw [capRelHomologyInt_mk, capRelHomologyInt_mk, capRelCyclesIntₗ_smul]
  rfl

/-- The map `a ↦ capRelHomologyInt a`, packaged `ℤ`-linear in the cochain. -/
noncomputable def capRelHomologyIntₗ :
    LinearMap.ker (coboundaryₗ X k) →ₗ[ℤ]
      (RelHomologyInt S (k + m + 1) →ₗ[ℤ] RelHomologyInt S (m + 1)) where
  toFun := capRelHomologyInt
  map_add' := capRelHomologyInt_add
  map_smul' := capRelHomologyInt_smul

/-- Degree-cast transport of subspace-chain membership through `chainBoundary`. -/
private theorem chainBoundary_cast_memInt {a b : ℕ} (z : SingularChainInt X (a + 1))
    (e : a + 1 = b + 1) (eb : a = b) (hz : chainBoundary X a z ∈ subspaceChainsInt S a) :
    chainBoundary X b (e ▸ z) ∈ subspaceChainsInt S b := by
  subst eb
  rw [show e = rfl from rfl]
  simpa using hz

/-- **The cohomology-argument descent (relative form, over ℤ).** For a `j`-cochain `g`, its coboundary
`δg` caps a relative `(j+1+m+1)`-cycle representative `z` (with `∂z ∈ C(S;ℤ)`) to a relative
`(m+1)`-boundary: `capInt_leibniz` gives `∂(g ⌢ z) = (-1)^{j+1}·((δg) ⌢ z) + (-1)ʲ·(g ⌢ ∂z)`, the first
summand a (relative) boundary, the second a subspace chain (`cap_mem_subspaceChainsInt`, since
`∂z ∈ C(S)`) — so the relative class of `(δg) ⌢ z` is a relative boundary. The relative mirror of
`SingularCohomologyInt.capInt_coboundary_cycle_mem_boundaries`. -/
theorem cap_coboundaryInt_relCycle_mem_relBoundariesInt {j : ℕ} (g : SingularCochainInt X j)
    (z : SingularChainInt X (j + 1 + m + 1))
    (hz : chainBoundary X (j + 1 + m) z ∈ subspaceChainsInt S (j + 1 + m)) :
    RelativeChainInt.mk S (m + 1) (capInt (m := m + 1) (coboundary X j g) z)
      ∈ relBoundariesInt S (m + 1) := by
  have e : j + 1 + m + 1 = j + (m + 1) + 1 := by omega
  have h : j + (m + 1) + 1 = j + 1 + (m + 1) := by omega
  have hleib := capInt_leibniz (a := g) (c := e ▸ z) (m := m + 1) h
  have hcancel : (h ▸ (e ▸ z) : SingularChainInt X (j + 1 + (m + 1))) = z := by
    rw [eqRec_eq_cast, eqRec_eq_cast, cast_cast, cast_eq]
  rw [hcancel] at hleib
  have hsub : chainBoundary X (j + (m + 1)) (e ▸ z) ∈ subspaceChainsInt S (j + (m + 1)) :=
    chainBoundary_cast_memInt (a := j + 1 + m) (b := j + (m + 1)) z e (by omega) hz
  have hgsub : capInt (m := m + 1) g (chainBoundary X (j + (m + 1)) (e ▸ z))
      ∈ subspaceChainsInt S (m + 1) :=
    cap_mem_subspaceChainsInt g hsub
  have hQ0 : RelativeChainInt.mk S (m + 1)
      (capInt (m := m + 1) g (chainBoundary X (j + (m + 1)) (e ▸ z))) = 0 :=
    (RelativeChainInt.mk_eq_zero_iff S (m + 1) _).mpr hgsub
  refine ⟨(-1 : ℤ) ^ (j + 1) • RelativeChainInt.mk S (m + 2) (capInt (m := m + 2) g (e ▸ z)), ?_⟩
  rw [map_smul, relBoundaryInt_mk, hleib]
  show (-1 : ℤ) ^ (j + 1) • Submodule.Quotient.mk
        ((-1 : ℤ) ^ (j + 1) • capInt (m := m + 1) (coboundary X j g) z
          + (-1 : ℤ) ^ j • capInt (m := m + 1) g (chainBoundary X (j + (m + 1)) (e ▸ z)))
      = Submodule.Quotient.mk (capInt (m := m + 1) (coboundary X j g) z)
  rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
  show (-1 : ℤ) ^ (j + 1) • ((-1 : ℤ) ^ (j + 1) • RelativeChainInt.mk S (m + 1) _
      + (-1 : ℤ) ^ j • RelativeChainInt.mk S (m + 1) _)
      = RelativeChainInt.mk S (m + 1) _
  rw [hQ0, smul_zero, add_zero, smul_smul,
    show (-1 : ℤ) ^ (j + 1) * (-1) ^ (j + 1) = 1 from by
      rw [← pow_add]; exact Even.neg_one_pow ⟨j + 1, rfl⟩,
    one_smul]

/-- **The integral relative cap product on (co)homology**
`capRelHInt k m : Hᵏ(X;ℤ) → H_{k+m+1}(X, S;ℤ) → H_{m+1}(X, S;ℤ)` — capping an **absolute** cohomology
class against a **relative** homology class. The relative mirror of `SingularCohomologyInt.capHInt`. -/
noncomputable def capRelHInt (k m : ℕ) :
    Cohomology X k →ₗ[ℤ]
      RelHomologyInt S (k + m + 1) →ₗ[ℤ] RelHomologyInt S (m + 1) :=
  Submodule.liftQ _ capRelHomologyIntₗ (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker]
    ext x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.zero_apply]
    show capRelHomologyInt a (RelHomologyInt.mk S (k + m + 1) z) = 0
    rw [capRelHomologyInt_mk, RelHomologyInt.mk_eq_zero_iff]
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChainInt S (k + m + 1))
    have hcmk : (z : RelativeChainInt S (k + m + 1)) = RelativeChainInt.mk S (k + m + 1) c := hc.symm
    have hzc : chainBoundary X (k + m) c ∈ subspaceChainsInt S (k + m) := by
      have hz2 : relBoundaryInt S (k + m) (z : RelativeChainInt S (k + m + 1)) = 0 :=
        LinearMap.mem_ker.mp z.2
      rw [hcmk, relBoundaryInt_mk, RelativeChainInt.mk_eq_zero_iff] at hz2
      exact hz2
    have hval : (capRelCyclesIntₗ (m := m) a z : RelativeChainInt S (m + 1))
        = RelativeChainInt.mk S (m + 1) (capInt (m := m + 1) a.1 c) := by
      rw [capRelCyclesIntₗ_coe, hcmk]; rfl
    rw [hval]
    cases k with
    | zero =>
        rw [show coboundaryRange X 0 = (⊥ : Submodule ℤ (SingularCochainInt X 0)) from rfl,
          Submodule.mem_bot] at ha
        rw [show (a.1 : SingularCochainInt X 0) = 0 from ha, capInt_zero_cochain,
          show RelativeChainInt.mk S (m + 1) (0 : SingularChainInt X (m + 1)) = 0 from by
            rw [RelativeChainInt.mk_eq_zero_iff]; exact Submodule.zero_mem _]
        exact Submodule.zero_mem _
    | succ j =>
        rw [show coboundaryRange X (j + 1) = LinearMap.range (coboundaryₗ X j) from rfl] at ha
        obtain ⟨g, hg⟩ := ha
        rw [← hg]
        exact cap_coboundaryInt_relCycle_mem_relBoundariesInt g c hzc)

@[simp] theorem capRelHInt_mk_mk (a : LinearMap.ker (coboundaryₗ X k)) (z : relCyclesInt S (k + m + 1)) :
    capRelHInt (S := S) k m (Cohomology.mk X k a) (RelHomologyInt.mk S (k + m + 1) z)
      = RelHomologyInt.mk S (m + 1) (capRelCyclesIntₗ a z) :=
  rfl

end SKEFTHawking.SingularRelativeCapHomologyInt
