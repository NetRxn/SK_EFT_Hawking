/-
# Phase 5q.H (E1 integral topology) — the small-chains kernel complex `K = ker(π)` is acyclic & projective

The complex fed to the reusable contraction engine (`AcyclicProjectiveContractionInt`) to obtain the
cohomology Mayer–Vietoris middle-exactness node `(B)`. With `π = piMapInt : Q → RelChain(U∪V)` (the
degreewise surjection of the relative-homology MV chain SES, `Q = C(M)/(C(U)+C(V))`), the kernel
`K n = ker(π n)` is:
* **projective** — a retract of the FREE `Q` (the split SES: `RelChain(U∪V)` is free, so `π` has a section
  `g`; `id − g∘π` retracts `Q` onto `K`), via `Module.Projective.of_split`;
* **acyclic** (`ker (dK n) = range (dK (n+1))`) — the `⊆` half is the excision/subdivision argument
  mirroring `iotaInt_injective` (a `K`-cycle `[c]` with `∂c ∈ C(U)+C(V)` is `∂` of `Dₘ c ∈ C(U∪V)` modulo
  small chains); `K 0 = 0` since every 0-simplex is small.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `native_decide`, no `maxHeartbeats`, no axiom.
-/
import Mathlib
import SKEFTHawking.SingularSmallChainsSplitInt
import SKEFTHawking.SingularRelativeMVInt
import SKEFTHawking.SingularH0PathConnected
import SKEFTHawking.AcyclicProjectiveContractionInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeMVInt SKEFTHawking.SingularSmallChainsSplitInt
open SKEFTHawking.SingularSubdivisionInt SKEFTHawking.SingularExcisionInt
open SKEFTHawking.SingularExcisionIsoInt

namespace SKEFTHawking.SingularKComplexAcyclicInt

variable {M : TopCat}

/-- **Every small `0`-simplex of `U ∪ V` is small in `U` or in `V`.** A `0`-simplex's image is the single
point `simplexPoint τ` (`eq_constSimplex`); if it lies in `U ∪ V` it lies in `U` or `V`. -/
theorem smallSimplices_union_zero (U V : Set M) :
    SmallSimplices (U ∪ V) 0 ⊆ SmallSimplices U 0 ∪ SmallSimplices V 0 := by
  intro τ hτ
  have hsub : Set.range (M.toSSetObjEquiv (op (SimplexCategory.mk 0)) τ) ⊆ {SingularH0PathConnected.simplexPoint τ} := by
    rintro _ ⟨t, rfl⟩
    rw [Set.mem_singleton_iff, SingularH0PathConnected.simplexPoint, Subsingleton.elim t default]
  have hpt : SingularH0PathConnected.simplexPoint τ ∈ U ∪ V := hτ ⟨default, rfl⟩
  rcases hpt with hU | hV
  · exact Or.inl (hsub.trans (Set.singleton_subset_iff.mpr hU))
  · exact Or.inr (hsub.trans (Set.singleton_subset_iff.mpr hV))

/-- `C(U∪V)₀ ≤ C(U)₀ + C(V)₀` — every `0`-chain of `U∪V` is small (`smallSimplices_union_zero`). -/
theorem subspaceChains_union_le_mvUnion_zero (U V : Set M) :
    subspaceChainsInt (U ∪ V) 0 ≤ mvUnionChainsInt U V 0 := by
  rw [subspaceChainsInt_eq_supported, mvUnionChainsInt_eq_supported]
  exact Finsupp.supported_mono (smallSimplices_union_zero U V)

/-- **`K₀ = ker(π₀) = ⊥`** — since `C(U∪V)₀ = C(U)₀+C(V)₀`, `π₀ : C(M)/(C(U)+C(V)) → C(M)/C(U∪V)` is
injective in degree 0. -/
theorem ker_piMapInt_zero (U V : Set M) : LinearMap.ker (piMapInt U V 0) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker,
    show (Submodule.Quotient.mk c : QChainInt U V 0) = QChainInt.mk U V 0 c from rfl, piMapInt_mk,
    RelativeChainInt.mk_eq_zero_iff] at hx
  rw [show (Submodule.Quotient.mk c : QChainInt U V 0) = QChainInt.mk U V 0 c from rfl,
    QChainInt.mk_eq_zero_iff]
  exact subspaceChains_union_le_mvUnion_zero U V hx

/-- `π = piMapInt` is surjective (it is `Submodule.mapQ … id`). -/
theorem piMapInt_surjective (U V : Set M) (n : ℕ) : Function.Surjective (piMapInt U V n) := by
  intro y
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨QChainInt.mk U V n c, piMapInt_mk U V n c⟩

/-- **`K n = ker(π n)` is a projective ℤ-module** — a retract of the free `Q n`. Since `RelChain(U∪V) n`
is free, `π n` splits (`g` a right inverse); `id − g∘π` is a retraction of `Q n` onto `ker(π n)`. -/
theorem kmod_projective (U V : Set M) (n : ℕ) :
    Module.Projective ℤ ↥(LinearMap.ker (piMapInt U V n)) := by
  haveI : Module.Free ℤ (QChainInt U V n) := free_qChain U V n
  haveI : Module.Free ℤ (RelativeChainInt (U ∪ V) n) := free_relChainUnion U V n
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (piMapInt U V n)
    (LinearMap.range_eq_top.mpr (piMapInt_surjective U V n))
  set φ : QChainInt U V n →ₗ[ℤ] QChainInt U V n := LinearMap.id - g.comp (piMapInt U V n) with hφ
  have hr : ∀ x, φ x ∈ LinearMap.ker (piMapInt U V n) := by
    intro x
    rw [LinearMap.mem_ker, hφ]
    simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply, map_sub]
    have hgy : piMapInt U V n (g (piMapInt U V n x)) = piMapInt U V n x := by
      simpa using LinearMap.congr_fun hg (piMapInt U V n x)
    rw [hgy, sub_self]
  refine Module.Projective.of_split (LinearMap.ker (piMapInt U V n)).subtype
    (φ.codRestrict _ hr) ?_
  ext y
  obtain ⟨x, hx⟩ := y
  rw [LinearMap.mem_ker] at hx
  simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.codRestrict_apply, hφ,
    LinearMap.sub_apply, LinearMap.id_apply]
  rw [hx, map_zero, sub_zero]

/-- `∂_Q` sends `ker(π (n+1))` into `ker(π n)` (`π` is a chain map, `piMapInt_chainMap`). -/
theorem qBoundaryInt_mem_ker (U V : Set M) (n : ℕ) :
    ∀ x ∈ LinearMap.ker (piMapInt U V (n + 1)), qBoundaryInt U V n x ∈ LinearMap.ker (piMapInt U V n) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [piMapInt_chainMap, hx, map_zero]

/-- **The `K`-complex boundary** `dK n : K (n+1) → K n`, the restriction of `∂_Q` to `K = ker π`. -/
noncomputable def dK (U V : Set M) (n : ℕ) :
    ↥(LinearMap.ker (piMapInt U V (n + 1))) →ₗ[ℤ] ↥(LinearMap.ker (piMapInt U V n)) :=
  LinearMap.restrict (qBoundaryInt U V n) (qBoundaryInt_mem_ker U V n)

@[simp] theorem dK_coe (U V : Set M) (n : ℕ) (x : ↥(LinearMap.ker (piMapInt U V (n + 1)))) :
    (dK U V n x : QChainInt U V n) = qBoundaryInt U V n (x : QChainInt U V (n + 1)) :=
  LinearMap.restrict_coe_apply _ _ _

/-- `dK ∘ dK = 0` (from `∂_Q ∘ ∂_Q = 0`). -/
theorem dK_comp_dK (U V : Set M) (n : ℕ) : (dK U V n).comp (dK U V (n + 1)) = 0 := by
  ext x
  rw [LinearMap.comp_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero, dK_coe, dK_coe]
  have := LinearMap.congr_fun (qBoundaryInt_comp_qBoundaryInt U V n) (x : QChainInt U V (n + 1 + 1))
  simpa using this

/-- **`dK 0` is surjective** (`H₀(K) = 0`), because `K₀ = ⊥` is subsingleton. -/
theorem dK_zero_surjective (U V : Set M) : Function.Surjective (dK U V 0) := by
  haveI : Subsingleton ↥(LinearMap.ker (piMapInt U V 0)) := by
    rw [ker_piMapInt_zero U V]; infer_instance
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The MV small chains `C(U)+C(V)` are the `{U,V}`-small chains. -/
theorem mvUnionChainsInt_eq_smallChainsInt (U V : Set M) (n : ℕ) :
    mvUnionChainsInt U V n = smallChainsInt ({U, V} : Set (Set M)) n := by
  rw [mvUnionChainsInt, Submodule.add_eq_sup, ← smallChainsInt_two_eq]

/-- **`K` is acyclic**: `ker (dK n) = range (dK (n+1))` (`U, V` open). The `⊇` half is `dK∘dK=0`; the
`⊆` half is the excision/subdivision argument mirroring `iotaInt_injective` — a `K`-cycle `[c]`
(`∂c` small) is `∂` of the subdivision homotopy `Dₘ c ∈ C(U∪V)` modulo small chains. -/
theorem dK_exact (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    LinearMap.ker (dK U V n) = LinearMap.range (dK U V (n + 1)) := by
  refine le_antisymm ?_ (LinearMap.range_le_ker_iff.mpr (dK_comp_dK U V n))
  intro k hk
  rw [LinearMap.mem_ker] at hk
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (k : QChainInt U V (n + 1))
  have hcmk : (k : QChainInt U V (n + 1)) = QChainInt.mk U V (n + 1) c := hc.symm
  -- c is a (U∪V)-chain (k ∈ ker π), with small boundary (dK n k = 0)
  have hc_sub : c ∈ subspaceChainsInt (U ∪ V) (n + 1) := by
    have hk0 : piMapInt U V (n + 1) (k : QChainInt U V (n + 1)) = 0 := LinearMap.mem_ker.mp k.2
    rw [hcmk, piMapInt_mk, RelativeChainInt.mk_eq_zero_iff] at hk0
    exact hk0
  have hdc : chainBoundary M n c ∈ mvUnionChainsInt U V n := by
    have h0 : (dK U V n k : QChainInt U V n) = 0 := by rw [hk]; rfl
    rw [dK_coe, hcmk, qBoundaryInt_mk, QChainInt.mk_eq_zero_iff] at h0
    exact h0
  -- subdivide the cycle small
  obtain ⟨m, hm⟩ := exists_iterate_mvUnionInt U V hU hV (n + 1) c hc_sub
  have hc'_sub : iterHomotopyInt M (n + 1) m c ∈ subspaceChainsInt (U ∪ V) (n + 2) :=
    iterHomotopyInt_mem_subspaceChainsInt hc_sub m
  have hDdc : iterHomotopyInt M n m (chainBoundary M n c) ∈ mvUnionChainsInt U V (n + 1) := by
    rw [mvUnionChainsInt_eq_smallChainsInt]
    refine iterHomotopyInt_mem_smallChainsInt ?_ m
    rw [← mvUnionChainsInt_eq_smallChainsInt]; exact hdc
  have hh := iterHomotopyInt_chainHomotopy M m n c
  have hkey : c - chainBoundary M (n + 1) (iterHomotopyInt M (n + 1) m c)
      ∈ mvUnionChainsInt U V (n + 1) := by
    have heq : c - chainBoundary M (n + 1) (iterHomotopyInt M (n + 1) m c)
        = (⇑(singularSdInt M (n + 1)))^[m] c + iterHomotopyInt M n m (chainBoundary M n c) := by
      generalize hA : chainBoundary M (n + 1) (iterHomotopyInt M (n + 1) m c) = A at hh ⊢
      generalize hB : iterHomotopyInt M n m (chainBoundary M n c) = B at hh ⊢
      generalize hS : (⇑(singularSdInt M (n + 1)))^[m] c = S at hh ⊢
      rw [eq_sub_iff_add_eq] at hh
      rw [← hh]; abel
    rw [heq]; exact Submodule.add_mem _ hm hDdc
  -- assemble the K-boundary witness
  have hmem' : QChainInt.mk U V (n + 2) (iterHomotopyInt M (n + 1) m c)
      ∈ LinearMap.ker (piMapInt U V (n + 2)) := by
    rw [LinearMap.mem_ker, piMapInt_mk, RelativeChainInt.mk_eq_zero_iff]; exact hc'_sub
  refine ⟨⟨QChainInt.mk U V (n + 2) (iterHomotopyInt M (n + 1) m c), hmem'⟩, ?_⟩
  apply Subtype.ext
  rw [dK_coe, hcmk]
  show QChainInt.mk U V (n + 1) (chainBoundary M (n + 1) (iterHomotopyInt M (n + 1) m c))
      = QChainInt.mk U V (n + 1) c
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [show chainBoundary M (n + 1) (iterHomotopyInt M (n + 1) m c) - c
      = -(c - chainBoundary M (n + 1) (iterHomotopyInt M (n + 1) m c)) from by abel]
  exact Submodule.neg_mem _ hkey

/-- **`Hom(K, A)` is acyclic in positive degrees** — the payoff. Applying the reusable contraction engine
(`AcyclicProjectiveContractionInt.cocycle_eq_coboundary`) to the projective (`kmod_projective`) acyclic
(`dK_exact`, `dK_zero_surjective`) `K`-complex: every `K`-cochain cocycle `g` (`g ∘ dK (n+1) = 0`) is a
`K`-coboundary `g = h ∘ dK n`. This is the engine that lifts the chase's common `Hom(Q)` cocycle to
`RelativeCohomologyInt(U∪V)` (the node `(B)`). -/
theorem hom_K_cocycle_eq_coboundary (U V : Set M) (hU : IsOpen U) (hV : IsOpen V)
    {A : Type*} [AddCommGroup A] [Module ℤ A] (n : ℕ)
    (g : ↥(LinearMap.ker (piMapInt U V (n + 1))) →ₗ[ℤ] A)
    (hg : g.comp (dK U V (n + 1)) = 0) :
    ∃ h : ↥(LinearMap.ker (piMapInt U V n)) →ₗ[ℤ] A, g = h.comp (dK U V n) := by
  have hcob := @AcyclicProjectiveContractionInt.cocycle_eq_coboundary
    (fun j => ↥(LinearMap.ker (piMapInt U V j))) _ _ (kmod_projective U V) _ _ _
    (dK U V) (dK_comp_dK U V) (dK_exact U V hU hV) (dK_zero_surjective U V) n g hg
  exact ⟨_, hcob⟩

end SKEFTHawking.SingularKComplexAcyclicInt
