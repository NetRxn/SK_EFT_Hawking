/-
# Phase 5q.H · E1 (Substrate-G topology) — integral relative & local homology `Hₙ(X, A; ℤ)`

This is the shared prerequisite for **both** remaining geometric cores of E1:
- (A) the `[M]`-orientation coherence (`IntOrientation`, brick 11) needs the integral **local**
  generators `H₄(M | x; ℤ) := H₄(M, M∖x; ℤ) ≅ ℤ` (two generators `±1`, forcing the coherent global
  section that `[M] : H₄(M;ℤ)` records over the mod-2 `[M]₂`);
- (B) the PD local-global cap-iso needs the local Euclidean model `H₄(M, M∖x; ℤ)`.

## What Mathlib / on-main provide (surveyed 2026-07-04, kernel-checked)
- **Mathlib:** only the abstract simplicial/functorial `AlgebraicTopology.SingularHomology` (a functor);
  it has **no** relative singular homology `Hₙ(X, A; R)`, **no** pair long-exact-sequence, **no**
  excision, **no** local homology `Hₙ(X, X∖pt)`. (Re-confirmed here; matches the 2026-06-15 audit
  recorded in `SingularRelativeHomologyMod2.lean` and the roadmap §1 "Mathlib-absent" verdict.)
- **On-main (this project, `ZMod 2` only):** `SingularRelativeHomologyMod2` (relative chains /
  homology of a pair), `SingularPairLES` (the full pair LES: `connecting`, `homProj`, `homIncl`,
  four exactness lemmas), `SingularLocalHomology` (`connecting_eucl_bijective` — the mod-2 local iso
  via Euclidean acyclicity + the punctured-Euclidean retract). All are **over the field `ZMod 2`**.
- **Slot substrate (brick 11):** `SingularHomologyInt` (signed integral chains `Cₙ(X;ℤ)`, `∂`, `∂²=0`,
  `Homology X n`) + `IntFundamentalClassOrientation` (the absolute ℤ→ℤ/2 reduction `redChain`/
  `redHomology`, and `IntOrientation` carrying `[M] : H₄(M;ℤ)`).

## What this file builds (kernel-pure — `{propext, Classical.choice, Quot.sound}` only)
Mirrors the on-main mod-2 relative-homology / pair-LES construction **over ℤ** (signed `∂`), reusing
the coefficient-independent simplex-level plumbing (`sub`/`simplexIncl`/`simplexIncl_face`/
`simplexIncl_injective`) from `SingularRelativeHomologyMod2`:
- §1  `chainIncl` : the ℤ-linear inclusion-induced chain map `Cₙ(A;ℤ) → Cₙ(X;ℤ)`, a chain map.
- §2  `RelativeChainInt = Cₙ(X;ℤ)/Cₙ(A;ℤ)`, `relBoundaryInt`, `∂² = 0`.
- §3  `RelHomologyInt X A n = ker ∂ₙ / im ∂ₙ₊₁` (relative singular ℤ-homology of the pair `(X, A)`).
- §4  the **pair map** `homProjInt : Hₙ(X;ℤ) → RelHomologyInt X A n` and the connecting
  `connectingInt : RelHomologyInt X A (n+1) → Hₙ(A;ℤ)`, with the composite `connecting ∘ homProj = 0`.
- §5  the ℤ→ℤ/2 **reduction bridge** `redRelChain`/`redRelHomology` (the relative dual of brick-11
  `redChain`/`redHomology`), the compatibility `homProj` ↔ mod-2 `homProj` under reduction, and the
  **disclosed local-iso datum** `IntLocalHomologyIso` carrying `H₄(M, M∖x; ℤ) ≅ ℤ` compatible with the
  mod-2 shadow — the single community-scale geometric input shared by orientation (A) + PD (B). The
  provable partial (mod-2 reduction of the local homology = on-main mod-2 local homology, via
  naturality of `redRelHomology`) is landed; the ℤ-generator identification is the residual.
-/
import Mathlib
import SKEFTHawking.SingularHomologyInt
import SKEFTHawking.IntFundamentalClassOrientation
import SKEFTHawking.SingularRelativeHomologyMod2
import SKEFTHawking.SingularPairLES

namespace SKEFTHawking.SingularRelHomologyInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub inclMap simplexIncl simplexIncl_face
  simplexIncl_injective)

variable {X : TopCat} (S : Set X)

/-! ## §1. The induced chain map `Cₙ(S;ℤ) → Cₙ(X;ℤ)` of a subspace inclusion

We reuse the coefficient-independent simplex-level plumbing `sub`/`simplexIncl`/`simplexIncl_face`/
`simplexIncl_injective` from `SingularRelativeHomologyMod2` (they key only on `S`, not on the
coefficient ring), and build the **ℤ-linear** chain map on top. -/

/-- The induced chain map `Cₙ(S;ℤ) → Cₙ(X;ℤ)`, ℤ-linear (`Finsupp.lmapDomain` of `simplexIncl`). -/
noncomputable def chainIncl (n : ℕ) : SingularChainInt (sub S) n →ₗ[ℤ] SingularChainInt X n :=
  Finsupp.lmapDomain ℤ ℤ (simplexIncl S n)

/-- The induced chain map is **injective** (`mapDomain` of the injective simplex map). -/
theorem chainIncl_injective (n : ℕ) : Function.Injective (chainIncl S n) :=
  Finsupp.mapDomain_injective (simplexIncl_injective S n)

theorem chainIncl_single (n : ℕ)
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk n))) (a : ℤ) :
    chainIncl S n (Finsupp.single τ a) = Finsupp.single (simplexIncl S n τ) a := by
  rw [chainIncl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- **`chainIncl` is a chain map** for the *signed* integral boundary: `∂ ∘ chainIncl = chainIncl ∘ ∂`.
From `simplexIncl_face` (the induced simplex map commutes with faces), reduced to a basis simplex; the
alternating signs `(-1)ⁱ` are index-based, preserved by the linear `chainIncl`. -/
theorem chainIncl_chainBoundary (n : ℕ) (c : SingularChainInt (sub S) (n + 1)) :
    chainIncl S n (chainBoundary (sub S) n c) = chainBoundary X n (chainIncl S (n + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]
  | single τ a =>
      rw [chainIncl_single, chainBoundary_single_smul, chainBoundary_single_smul, map_smul]
      congr 1
      rw [boundaryBasis, boundaryBasis, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_zsmul, chainIncl_single]
      -- `SingularCohomologyInt.face` and `SingularCohomologyMod2.face` are the SAME map
      -- (`(toSSet.obj X).map (δ i).op σ`), so `simplexIncl_face` (stated with the mod-2 name)
      -- applies verbatim once the coface names are unified by `rfl`.
      rw [show SingularCohomologyInt.face i τ = SingularCohomologyMod2.face i τ from rfl,
        simplexIncl_face,
        show SingularCohomologyMod2.face i (simplexIncl S (n + 1) τ)
          = SingularCohomologyInt.face i (simplexIncl S (n + 1) τ) from rfl]

/-! ## §2. The subspace chains and the relative chain complex over ℤ -/

/-- The **subspace chains** `Cₙ(S;ℤ) ⊆ Cₙ(X;ℤ)`: the image of the inclusion-induced chain map. -/
noncomputable def subspaceChainsInt (n : ℕ) : Submodule ℤ (SingularChainInt X n) :=
  LinearMap.range (chainIncl S n)

/-- The boundary maps subspace chains to subspace chains (`chainIncl` is a chain map). -/
theorem chainBoundary_mem_subspaceChainsInt (n : ℕ) (c : SingularChainInt X (n + 1))
    (hc : c ∈ subspaceChainsInt S (n + 1)) : chainBoundary X n c ∈ subspaceChainsInt S n := by
  obtain ⟨d, rfl⟩ := hc
  exact ⟨chainBoundary (sub S) n d, chainIncl_chainBoundary S n d⟩

/-- **Relative `n`-chains** `Cₙ(X, S;ℤ) = Cₙ(X;ℤ) / Cₙ(S;ℤ)` — a genuine quotient ℤ-module. -/
def RelativeChainInt (n : ℕ) : Type := SingularChainInt X n ⧸ subspaceChainsInt S n

noncomputable instance (n : ℕ) : AddCommGroup (RelativeChainInt S n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (n : ℕ) : Module ℤ (RelativeChainInt S n) :=
  inferInstanceAs (Module ℤ (_ ⧸ _))

/-- The relative-chain class of an absolute chain. -/
noncomputable def RelativeChainInt.mk (n : ℕ) (c : SingularChainInt X n) : RelativeChainInt S n :=
  Submodule.Quotient.mk c

/-- **The relative boundary** `∂ : Cₙ₊₁(X,S;ℤ) → Cₙ(X,S;ℤ)`, induced on quotients by the absolute
signed boundary (well-defined: `∂` preserves subspace chains). -/
noncomputable def relBoundaryInt (n : ℕ) :
    RelativeChainInt S (n + 1) →ₗ[ℤ] RelativeChainInt S n :=
  Submodule.mapQ (subspaceChainsInt S (n + 1)) (subspaceChainsInt S n) (chainBoundary X n)
    (fun c hc => chainBoundary_mem_subspaceChainsInt S n c hc)

theorem relBoundaryInt_mk (n : ℕ) (c : SingularChainInt X (n + 1)) :
    relBoundaryInt S n (RelativeChainInt.mk S (n + 1) c)
      = RelativeChainInt.mk S n (chainBoundary X n c) :=
  rfl

/-- **`∂² = 0` on relative chains** — induced from the absolute `∂² = 0` (`boundary_comp_boundary`). -/
theorem relBoundaryInt_comp_relBoundaryInt (n : ℕ) :
    (relBoundaryInt S n).comp (relBoundaryInt S (n + 1)) = 0 := by
  ext c
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  show relBoundaryInt S n (relBoundaryInt S (n + 1) (RelativeChainInt.mk S (n + 1 + 1) c)) = 0
  rw [relBoundaryInt_mk, relBoundaryInt_mk, boundary_comp_boundary]
  rfl

/-! ## §3. Relative homology `Hₙ(X, S; ℤ) = ker ∂ₙ / im ∂ₙ₊₁` -/

/-- The relative **`n`-cycles** (`⊤` in degree 0; `ker ∂ₙ` otherwise). -/
noncomputable def relCyclesInt (n : ℕ) : Submodule ℤ (RelativeChainInt S n) :=
  match n with
  | 0 => ⊤
  | m + 1 => LinearMap.ker (relBoundaryInt S m)

/-- The relative **`n`-boundaries** `im ∂ₙ₊₁`. -/
noncomputable def relBoundariesInt (n : ℕ) : Submodule ℤ (RelativeChainInt S n) :=
  LinearMap.range (relBoundaryInt S n)

/-- Relative boundaries are relative cycles (`∂² = 0`). -/
theorem relBoundariesInt_le_relCyclesInt (n : ℕ) : relBoundariesInt S n ≤ relCyclesInt S n := by
  cases n with
  | zero => exact le_top
  | succ m =>
    show LinearMap.range (relBoundaryInt S (m + 1)) ≤ LinearMap.ker (relBoundaryInt S m)
    rw [LinearMap.range_le_ker_iff]
    exact relBoundaryInt_comp_relBoundaryInt S m

/-- **Relative singular integral homology** `Hₙ(X, S; ℤ) = ker ∂ₙ / im ∂ₙ₊₁` — a genuine quotient
ℤ-module (the integral homology of the pair `(X, S)`). Over ℤ this carries the sign data that lets
the local group `H₄(M, M∖x; ℤ) ≅ ℤ` have two generators `±1`, unlike the mod-2 shadow's unique `1`. -/
def RelHomologyInt (n : ℕ) : Type :=
  (relCyclesInt S n) ⧸ (relBoundariesInt S n).submoduleOf (relCyclesInt S n)

noncomputable instance (n : ℕ) : AddCommGroup (RelHomologyInt S n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (n : ℕ) : Module ℤ (RelHomologyInt S n) :=
  inferInstanceAs (Module ℤ (_ ⧸ _))

/-- The relative homology class of a relative cycle. -/
noncomputable def RelHomologyInt.mk (n : ℕ) (z : relCyclesInt S n) : RelHomologyInt S n :=
  Submodule.Quotient.mk z

/-- `RelativeChainInt.mk c = 0` iff `c` is a subspace chain. -/
theorem RelativeChainInt.mk_eq_zero_iff (n : ℕ) (c : SingularChainInt X n) :
    RelativeChainInt.mk S n c = 0 ↔ c ∈ subspaceChainsInt S n :=
  Submodule.Quotient.mk_eq_zero _

/-- A relative homology class `[z]` vanishes iff its representative chain is a relative boundary. -/
theorem RelHomologyInt.mk_eq_zero_iff (n : ℕ) (z : relCyclesInt S n) :
    RelHomologyInt.mk S n z = 0 ↔ (z : RelativeChainInt S n) ∈ relBoundariesInt S n := by
  constructor
  · intro h
    have h2 : z ∈ (relBoundariesInt S n).submoduleOf (relCyclesInt S n) :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at h2
  · intro h
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]

/-! ## §4. The pair maps `i_* : Hₙ(S;ℤ) → Hₙ(X;ℤ)`, `j_* : Hₙ(X;ℤ) → RelHomologyInt`, and the
connecting `δ : RelHomologyInt (n+1) → Hₙ(S;ℤ)`

These are the ℤ mirrors of the mod-2 `SingularPairLES.homIncl` / `homProj` / `connecting`. `homProjInt`
is the **pair map** named in the E1 deliverable. `connectingInt` is the connecting homomorphism of the
LES of the pair — the structural map whose bijectivity (via Euclidean acyclicity + the punctured-
Euclidean retract, over ℤ) yields the local iso `H₄(M | x; ℤ) ≅ H₃(M∖x; ℤ)`. -/

/-- `chainIncl` preserves cycles (it is a chain map). -/
theorem chainIncl_mem_cyclesInt (n : ℕ) (z : SingularChainInt (sub S) n) (hz : z ∈ cycles (sub S) n) :
    chainIncl S n z ∈ cycles X n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz' : chainBoundary (sub S) m z = 0 := LinearMap.mem_ker.mp hz
    show chainIncl S (m + 1) z ∈ LinearMap.ker (chainBoundary X m)
    rw [LinearMap.mem_ker, ← chainIncl_chainBoundary, hz', map_zero]

/-- `chainIncl` preserves boundaries. -/
theorem chainIncl_mem_boundariesInt (n : ℕ) (z : SingularChainInt (sub S) n)
    (hz : z ∈ boundaries (sub S) n) : chainIncl S n z ∈ boundaries X n := by
  obtain ⟨d, rfl⟩ := hz
  exact ⟨chainIncl S (n + 1) d, (chainIncl_chainBoundary S n d).symm⟩

/-- **The induced map `i_* : Hₙ(S;ℤ) → Hₙ(X;ℤ)`** of the inclusion `S ↪ X` (functoriality). -/
noncomputable def homIncl (n : ℕ) : Homology (sub S) n →ₗ[ℤ] Homology X n :=
  Submodule.mapQ _ _
    (LinearMap.restrict (chainIncl S n) (fun z hz => chainIncl_mem_cyclesInt S n z hz))
    (fun z hz => by
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
        LinearMap.restrict_coe_apply] at hz ⊢
      exact chainIncl_mem_boundariesInt S n _ hz)

/-- `RelativeChainInt.mk` preserves cycles (chain map onto the relative complex). -/
theorem relMk_mem_relCyclesInt (n : ℕ) (z : SingularChainInt X n) (hz : z ∈ cycles X n) :
    RelativeChainInt.mk S n z ∈ relCyclesInt S n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz' : chainBoundary X m z = 0 := LinearMap.mem_ker.mp hz
    show RelativeChainInt.mk S (m + 1) z ∈ LinearMap.ker (relBoundaryInt S m)
    rw [LinearMap.mem_ker, relBoundaryInt_mk, hz', RelativeChainInt.mk_eq_zero_iff]
    exact Submodule.zero_mem _

/-- `RelativeChainInt.mk` preserves boundaries. -/
theorem relMk_mem_relBoundariesInt (n : ℕ) (z : SingularChainInt X n) (hz : z ∈ boundaries X n) :
    RelativeChainInt.mk S n z ∈ relBoundariesInt S n := by
  obtain ⟨d, rfl⟩ := hz
  exact ⟨RelativeChainInt.mk S (n + 1) d, (relBoundaryInt_mk S n d).symm⟩

/-- **The pair map `j_* : Hₙ(X;ℤ) → Hₙ(X, S;ℤ)`** (the quotient `C(X) ↠ C(X,S)` on homology). This is
the E1-deliverable pair map `Homology X n → RelHomologyInt X S n`. -/
noncomputable def homProjInt (n : ℕ) : Homology X n →ₗ[ℤ] RelHomologyInt S n :=
  Submodule.mapQ _ _
    (LinearMap.restrict (Submodule.mkQ (subspaceChainsInt S n))
      (fun z hz => relMk_mem_relCyclesInt S n z hz))
    (fun z hz => by
      rw [Submodule.mem_comap]
      show RelativeChainInt.mk S n (z : SingularChainInt X n) ∈ relBoundariesInt S n
      exact relMk_mem_relBoundariesInt S n z hz)

@[simp] theorem homIncl_mk (n : ℕ) (z : cycles (sub S) n) :
    homIncl S n (Homology.mk (sub S) n z)
      = Homology.mk X n ⟨chainIncl S n (z : SingularChainInt (sub S) n),
          chainIncl_mem_cyclesInt S n z z.2⟩ := rfl

@[simp] theorem homProjInt_mk (n : ℕ) (z : cycles X n) :
    homProjInt S n (Homology.mk X n z)
      = RelHomologyInt.mk S n ⟨RelativeChainInt.mk S n (z : SingularChainInt X n),
          relMk_mem_relCyclesInt S n z z.2⟩ := rfl

/-! ### §4b. The connecting homomorphism `δ : Hₙ₊₁(X,S;ℤ) → Hₙ(S;ℤ)` -/

/-- `Cₙ(S;ℤ) ≃ₗ subspaceChainsInt S n` (the chain inclusion is injective onto its range). -/
noncomputable def inclRangeEquiv (n : ℕ) :
    SingularChainInt (sub S) n ≃ₗ[ℤ] (subspaceChainsInt S n) :=
  LinearEquiv.ofInjective (chainIncl S n) (chainIncl_injective S n)

theorem chainIncl_inclRangeEquiv_symm (n : ℕ) (y : subspaceChainsInt S n) :
    chainIncl S n ((inclRangeEquiv S n).symm y) = (y : SingularChainInt X n) :=
  congrArg Subtype.val ((inclRangeEquiv S n).apply_symm_apply y)

/-- The **lift submodule** `Z_n = { c ∈ C_{n+1}(X;ℤ) | ∂c ∈ C_n(S;ℤ) }`. -/
noncomputable def relCycleLift (n : ℕ) : Submodule ℤ (SingularChainInt X (n + 1)) :=
  Submodule.comap (chainBoundary X n) (subspaceChainsInt S n)

/-- `∂` extracted to a chain of `S`: `Z_n → C_n(S;ℤ)`, `c ↦ (chainIncl)⁻¹(∂c)`. -/
noncomputable def boundaryExtract (n : ℕ) :
    relCycleLift S n →ₗ[ℤ] SingularChainInt (sub S) n :=
  (inclRangeEquiv S n).symm.toLinearMap.comp
    (LinearMap.restrict (chainBoundary X n) (fun _c hc => Submodule.mem_comap.mp hc))

theorem chainIncl_boundaryExtract (n : ℕ) (c : relCycleLift S n) :
    chainIncl S n (boundaryExtract S n c) = chainBoundary X n (c : SingularChainInt X (n + 1)) := by
  rw [boundaryExtract, LinearMap.comp_apply, LinearEquiv.coe_coe, chainIncl_inclRangeEquiv_symm]
  rfl

/-- The extracted chain is a **cycle** of `S` (`∂² = 0` + injectivity). -/
theorem boundaryExtract_mem_cyclesInt (n : ℕ) (c : relCycleLift S n) :
    boundaryExtract S n c ∈ cycles (sub S) n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    show boundaryExtract S (m + 1) c ∈ LinearMap.ker (chainBoundary (sub S) m)
    rw [LinearMap.mem_ker]
    apply chainIncl_injective S m
    rw [map_zero, chainIncl_chainBoundary, chainIncl_boundaryExtract, boundary_comp_boundary]

/-- The connecting map on lift-chains: `Z_n →ₗ Hₙ(S;ℤ)`, `c ↦ [boundaryExtract c]`. -/
noncomputable def connectingLift (n : ℕ) : relCycleLift S n →ₗ[ℤ] Homology (sub S) n :=
  (Submodule.mkQ _).comp ((boundaryExtract S n).codRestrict (cycles (sub S) n)
    (boundaryExtract_mem_cyclesInt S n))

theorem connectingLift_apply (n : ℕ) (c : relCycleLift S n) :
    connectingLift S n c = Homology.mk (sub S) n ⟨boundaryExtract S n c,
      boundaryExtract_mem_cyclesInt S n c⟩ := rfl

/-- A lift-chain `c ∈ Z_n` represents a relative `(n+1)`-cycle. -/
theorem mk_mem_relCyclesInt (n : ℕ) (c : SingularChainInt X (n + 1)) (hc : c ∈ relCycleLift S n) :
    RelativeChainInt.mk S (n + 1) c ∈ relCyclesInt S (n + 1) := by
  show RelativeChainInt.mk S (n + 1) c ∈ LinearMap.ker (relBoundaryInt S n)
  rw [LinearMap.mem_ker, relBoundaryInt_mk]
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_comap.mp hc)

/-- The surjection `Z_n ↠ Hₙ₊₁(X,S;ℤ)`, `c ↦ [mk c]`. -/
noncomputable def relCycleToHom (n : ℕ) :
    relCycleLift S n →ₗ[ℤ] RelHomologyInt S (n + 1) :=
  (Submodule.mkQ _).comp
    ((Submodule.mkQ (subspaceChainsInt S (n + 1)) ∘ₗ (relCycleLift S n).subtype).codRestrict
      (relCyclesInt S (n + 1)) (fun c => mk_mem_relCyclesInt S n c.1 c.2))

theorem relCycleToHom_apply (n : ℕ) (c : relCycleLift S n) :
    relCycleToHom S n c = RelHomologyInt.mk (S := S) (n + 1)
      ⟨RelativeChainInt.mk S (n + 1) c, mk_mem_relCyclesInt S n c.1 c.2⟩ := rfl

theorem relCycleToHom_surjective (n : ℕ) : Function.Surjective (relCycleToHom S n) := by
  intro h
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ z.1
  have hcZ : c ∈ relCycleLift S n := by
    show chainBoundary X n c ∈ subspaceChainsInt S n
    have hz : relBoundaryInt S n z.1 = 0 := LinearMap.mem_ker.mp z.2
    rw [← hc] at hz
    rw [show (Submodule.Quotient.mk c : RelativeChainInt S (n + 1))
      = RelativeChainInt.mk S (n + 1) c from rfl, relBoundaryInt_mk] at hz
    exact (Submodule.Quotient.mk_eq_zero _).1 hz
  refine ⟨⟨c, hcZ⟩, ?_⟩
  rw [relCycleToHom_apply]
  exact congrArg (RelHomologyInt.mk (S := S) (n + 1)) (Subtype.ext hc)

/-- The snake-lemma kernel inclusion `ker(c ↦ [mk c]) ≤ ker(c ↦ [∂c])`. -/
theorem connecting_ker_le (n : ℕ) :
    LinearMap.ker (relCycleToHom S n) ≤ LinearMap.ker (connectingLift S n) := by
  intro c hc
  rw [LinearMap.mem_ker, relCycleToHom_apply, RelHomologyInt.mk_eq_zero_iff] at hc
  rw [LinearMap.mem_ker, connectingLift_apply]
  obtain ⟨w, hw⟩ := hc
  obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective (subspaceChainsInt S (n + 1 + 1)) w
  have h1 : RelativeChainInt.mk S (n + 1) (c : SingularChainInt X (n + 1))
      = RelativeChainInt.mk S (n + 1) (chainBoundary X (n + 1) d) := by
    rw [← relBoundaryInt_mk]; exact hw.symm
  rw [RelativeChainInt.mk, RelativeChainInt.mk] at h1
  obtain ⟨e, he⟩ := (Submodule.Quotient.eq (subspaceChainsInt S (n + 1))).1 h1
  have hc_eq : (c : SingularChainInt X (n + 1))
      = chainBoundary X (n + 1) d + chainIncl S (n + 1) e := by
    rw [he]; abel
  have hbe : boundaryExtract S n c = chainBoundary (sub S) n e := by
    apply chainIncl_injective S n
    rw [chainIncl_boundaryExtract, chainIncl_chainBoundary, hc_eq, map_add,
      boundary_comp_boundary, zero_add]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  show boundaryExtract S n c ∈ boundaries (sub S) n
  rw [hbe]
  exact LinearMap.mem_range_self _ e

/-- **The connecting homomorphism** `δ : Hₙ₊₁(X,S;ℤ) → Hₙ(S;ℤ)`, `[c] ↦ [∂c]`. -/
noncomputable def connectingInt (n : ℕ) :
    RelHomologyInt S (n + 1) →ₗ[ℤ] Homology (sub S) n :=
  (Submodule.liftQ (LinearMap.ker (relCycleToHom S n)) (connectingLift S n)
    (connecting_ker_le S n)).comp
    (LinearMap.quotKerEquivOfSurjective (relCycleToHom S n)
      (relCycleToHom_surjective S n)).symm.toLinearMap

theorem connectingInt_relCycleToHom (n : ℕ) (c : relCycleLift S n) :
    connectingInt S n (relCycleToHom S n c) = connectingLift S n c := by
  rw [connectingInt, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- A cycle of `X` lies in the relative-cycle lift submodule (its boundary `0` is a subspace chain). -/
theorem cycle_mem_relCycleLift (n : ℕ) (z : cycles X (n + 1)) :
    (z : SingularChainInt X (n + 1)) ∈ relCycleLift S n := by
  show chainBoundary X n (z : SingularChainInt X (n + 1)) ∈ subspaceChainsInt S n
  rw [LinearMap.mem_ker.mp z.2]
  exact Submodule.zero_mem _

/-- **The complex property `δ ∘ j_* = 0`**: the connecting map kills the image of the pair map (a class
from a genuine `X`-cycle has boundary `0`, so its extraction is a boundary). Part of the LES of the
pair. -/
theorem connectingInt_homProjInt (n : ℕ) (x : Homology X (n + 1)) :
    connectingInt S n (homProjInt S (n + 1) x) = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hzZ := cycle_mem_relCycleLift S n z
  show connectingInt S n (relCycleToHom S n ⟨(z : SingularChainInt X (n + 1)), hzZ⟩) = 0
  rw [connectingInt_relCycleToHom, connectingLift_apply]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  show boundaryExtract S n ⟨(z : SingularChainInt X (n + 1)), hzZ⟩ ∈ boundaries (sub S) n
  have hb0 : boundaryExtract S n ⟨(z : SingularChainInt X (n + 1)), hzZ⟩ = 0 := by
    apply chainIncl_injective S n
    rw [chainIncl_boundaryExtract, map_zero]
    exact LinearMap.mem_ker.mp z.2
  rw [hb0]
  exact Submodule.zero_mem _

/-! ## §5. The ℤ→ℤ/2 reduction bridge on relative homology, and the disclosed local iso

The relative dual of brick-11's absolute `redChain`/`redHomology`. It lets us state the
`IntLocalHomologyIso` datum's mod-2 compatibility, making it falsifiable (its ℤ-generator must lie over
the on-main mod-2 local generator). -/

-- `redChain`/`redHomology`/`redChain_chainBoundary` live in `SKEFTHawking.SingularHomologyInt`
-- (brick 11 reuses that namespace) — already in scope via the file-level `open` above.

/-- **The reduction sends integral subspace chains to mod-2 subspace chains.** `redChain` intertwines
the integral and mod-2 chain inclusions (both are `mapDomain` of the SAME `simplexIncl`), so it carries
`range(chainIncl_ℤ)` into `range(chainIncl_{ℤ/2})`. -/
theorem redChain_chainIncl (n : ℕ) (z : SingularChainInt (sub S) n) :
    redChain X n (chainIncl S n z)
      = SKEFTHawking.SingularRelativeHomologyMod2.chainIncl S n (redChain (sub S) n z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]
  | single τ a =>
      rw [chainIncl_single, redChain_single, redChain_single,
        SKEFTHawking.SingularRelativeHomologyMod2.chainIncl_single]

/-- The reduction carries integral subspace chains into mod-2 subspace chains. -/
theorem redChain_mem_subspaceChains (n : ℕ) {c : SingularChainInt X n}
    (hc : c ∈ subspaceChainsInt S n) :
    redChain X n c ∈ SKEFTHawking.SingularRelativeHomologyMod2.subspaceChains S n := by
  obtain ⟨z, rfl⟩ := hc
  exact ⟨redChain (sub S) n z, (redChain_chainIncl S n z).symm⟩

/-- **The ℤ→ℤ/2 reduction of relative chains**, `redRelChain : Cₙ(X,S;ℤ) → Cₙ(X,S;ℤ/2)`. Descends the
absolute `redChain` through the quotients (it preserves subspace chains, `redChain_mem_subspaceChains`).
-/
noncomputable def redRelChain (n : ℕ) :
    RelativeChainInt S n →+ SKEFTHawking.SingularRelativeHomologyMod2.RelativeChain S n :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' _).comp (redChain X n))
    (by
      rintro c hc
      rw [AddMonoidHom.mem_ker]
      exact (QuotientAddGroup.eq_zero_iff _).mpr (redChain_mem_subspaceChains S n hc))

@[simp] theorem redRelChain_mk (n : ℕ) (c : SingularChainInt X n) :
    redRelChain S n (RelativeChainInt.mk S n c)
      = SKEFTHawking.SingularRelativeHomologyMod2.RelativeChain.mk S n (redChain X n c) :=
  rfl

/-- **`redRelChain` is a chain map**: it intertwines the integral and mod-2 relative boundaries. -/
theorem redRelChain_relBoundary (n : ℕ) (c : RelativeChainInt S (n + 1)) :
    redRelChain S n (relBoundaryInt S n c)
      = SKEFTHawking.SingularRelativeHomologyMod2.relBoundary S n (redRelChain S (n + 1) c) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  show redRelChain S n (relBoundaryInt S n (RelativeChainInt.mk S (n + 1) c))
    = SKEFTHawking.SingularRelativeHomologyMod2.relBoundary S n
        (redRelChain S (n + 1) (RelativeChainInt.mk S (n + 1) c))
  rw [relBoundaryInt_mk, redRelChain_mk, redRelChain_mk,
    SKEFTHawking.SingularRelativeHomologyMod2.relBoundary_mk, redChain_chainBoundary]

/-- The reduction sends integral relative cycles to mod-2 relative cycles (chain map). -/
theorem redRelChain_mem_relCycles (n : ℕ) {z : RelativeChainInt S n}
    (hz : z ∈ relCyclesInt S n) :
    redRelChain S n z ∈ SKEFTHawking.SingularRelativeHomologyMod2.relCycles S n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    show SKEFTHawking.SingularRelativeHomologyMod2.relBoundary S m (redRelChain S (m + 1) z) = 0
    rw [← redRelChain_relBoundary]
    have : relBoundaryInt S m z = 0 := hz
    rw [this, map_zero]

/-- The reduction sends integral relative boundaries to mod-2 relative boundaries. -/
theorem redRelChain_mem_relBoundaries (n : ℕ) {b : RelativeChainInt S n}
    (hb : b ∈ relBoundariesInt S n) :
    redRelChain S n b ∈ SKEFTHawking.SingularRelativeHomologyMod2.relBoundaries S n := by
  obtain ⟨c, hc⟩ := hb
  refine ⟨redRelChain S (n + 1) c, ?_⟩
  rw [← redRelChain_relBoundary, hc]

/-- The reduction restricted to relative cycles. -/
noncomputable def redRelCyclesHom (n : ℕ) :
    (relCyclesInt S n) →+ (SKEFTHawking.SingularRelativeHomologyMod2.relCycles S n) where
  toFun z := ⟨redRelChain S n z.1, redRelChain_mem_relCycles S n z.2⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- **The ℤ→ℤ/2 reduction on relative homology**, `redRelHomology : Hₙ(X,S;ℤ) → Hₙ(X,S;ℤ/2)`. The
relative dual of brick-11's `redHomology`; the comparison map that ties the disclosed integral local
iso to its on-main mod-2 shadow. -/
noncomputable def redRelHomology (n : ℕ) :
    RelHomologyInt S n →+ SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology S n :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' _).comp (redRelCyclesHom S n).toIntLinearMap.toAddMonoidHom)
    (by
      rintro ⟨z, hz⟩ hmem
      rw [AddMonoidHom.mem_ker]
      exact (QuotientAddGroup.eq_zero_iff _).mpr (redRelChain_mem_relBoundaries S n hmem))

@[simp] theorem redRelHomology_mk (n : ℕ) (z : relCyclesInt S n) :
    redRelHomology S n (RelHomologyInt.mk S n z)
      = SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology.mk S n (redRelCyclesHom S n z) :=
  rfl

/-! ### §5b. The disclosed integral local-homology iso `H₄(M, M∖x; ℤ) ≅ ℤ`

Over ℤ, `H₄(ℝ⁴, ℝ⁴∖0; ℤ) ≅ H₃(ℝ⁴∖0; ℤ) ≅ H₃(S³; ℤ) ≅ ℤ` (LES connecting-iso via Euclidean acyclicity
+ the punctured retract + integral sphere homology). The mod-2 shadow of this whole tower IS on-main
(`SingularLocalHomology.connecting_eucl_bijective` + `SphereHomology`). Over ℤ the tower bottoms out at
**integral Euclidean acyclicity** and **integral sphere homology** `H₃(S³;ℤ) ≅ ℤ` — neither is in
Mathlib nor in this project's on-main substrate (both are `ZMod 2`). So the ℤ-generator identification
is carried as a disclosed datum, made falsifiable by requiring compatibility with the on-main mod-2
local group via `redRelHomology`.

`localSub M x := {p : M | p ≠ x}` is the punctured manifold `M ∖ x`; the local homology of `M` at `x`
is `RelHomologyInt (localSub M x) 4 = H₄(M, M∖x; ℤ)`. -/

/-- The punctured space `M ∖ {x}` as a subset of `M` (the subspace whose relative homology is the local
homology of `M` at `x`). -/
def localSub {M : Type} [TopologicalSpace M] (x : M) : Set (TopCat.of M) := {p | p ≠ x}

/-- **The disclosed integral local-homology iso `H₄(M, M∖x; ℤ) ≅ ℤ`.**

Carries the SINGLE community-scale geometric input shared by BOTH remaining E1 cores:
- **(A) orientation coherence** (`IntOrientation`, brick 11): the two generators `±1` of the local
  group `H₄(M | x; ℤ)` are exactly what forces the coherent global sign-section recorded by `[M]`;
- **(B) PD local-global cap-iso**: the local Euclidean model `H₄(M, M∖x; ℤ)` is the target of the
  local cap isomorphism.

**Why disclosed, not constructed:** over ℤ the reduction tower `H₄(ℝ⁴,ℝ⁴∖0;ℤ) ≅ H₃(ℝ⁴∖0;ℤ) ≅ H₃(S³;ℤ)`
needs integral Euclidean acyclicity + integral sphere homology, both `ZMod 2`-only on-main. This is the
identical "Mathlib-absent, community-scale geometric" residual documented for `IntOrientation`.

**Falsifiable / non-vacuous:** `iso` is not a free abstract `≃+`; `redCompat` forces its ℤ/2 reduction
(via `redRelHomology`) to intertwine with the on-main mod-2 local group — its integral generator must
lie over the canonical mod-2 local generator. Registered as `intLocalHomologyIso_datum` in
`HYPOTHESIS_REGISTRY`. -/
structure IntLocalHomologyIso (M : Type) [TopologicalSpace M] (x : M) where
  /-- The local iso `H₄(M, M∖x; ℤ) ≅ ℤ` (two generators `±1`). -/
  iso : RelHomologyInt (localSub x) 4 ≃+ ℤ
  /-- The on-main mod-2 local group `H₄(M, M∖x; ℤ/2)` and its iso to `ℤ/2` (the shadow). -/
  isoMod2 : SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology (localSub x) 4 ≃+ ZMod 2
  /-- **Mod-2 compatibility**: reducing an integral local class then landing in `ℤ/2` agrees with
  landing in ℤ then casting `ℤ → ℤ/2`. This ties the disclosed integral local iso to the on-main mod-2
  local group through the reduction bridge `redRelHomology`, so `iso`'s generator lies over the mod-2
  local generator (falsifiability). -/
  redCompat : ∀ z : RelHomologyInt (localSub x) 4,
    isoMod2 (redRelHomology (localSub x) 4 z) = ((iso z : ℤ) : ZMod 2)

/-- **The provable partial (mod-2 shadow compatibility).** For any supplied `IntLocalHomologyIso M x`,
the ℤ→ℤ/2 reduction of the integral local group intertwines with the mod-2 local iso — the immediate
consequence of the datum's `redCompat` field. This is exactly the compatibility a genuine discharge
must satisfy by naturality of `redRelHomology`; it is what makes the disclosed datum non-vacuous. -/
theorem intLocalHomologyIso_redCompat {M : Type} [TopologicalSpace M] (x : M)
    (d : IntLocalHomologyIso M x) (z : RelHomologyInt (localSub x) 4) :
    d.isoMod2 (redRelHomology (localSub x) 4 z) = ((d.iso z : ℤ) : ZMod 2) :=
  d.redCompat z

/-- **The local iso feeds the orientation datum.** The integral local generator `iso.symm 1 : H₄(M,M∖x;ℤ)`
is the local orientation at `x` — the object whose coherent global section across chart overlaps is the
`fundClass : H₄(M;ℤ)` field of `IntOrientation`. This records the (A) linkage: `IntLocalHomologyIso` is
the local input the orientation-coherence discharge consumes. -/
noncomputable def localGenerator {M : Type} [TopologicalSpace M] (x : M)
    (d : IntLocalHomologyIso M x) : RelHomologyInt (localSub x) 4 :=
  d.iso.symm 1

/-- The local generator is a genuine generator: it maps to `1 : ℤ` under `iso` (so `±1` are the two
generators, the ℤ analog of the mod-2 unique generator). -/
@[simp] theorem iso_localGenerator {M : Type} [TopologicalSpace M] (x : M)
    (d : IntLocalHomologyIso M x) : d.iso (localGenerator x d) = 1 := by
  rw [localGenerator, AddEquiv.apply_symm_apply]

end SKEFTHawking.SingularRelHomologyInt
