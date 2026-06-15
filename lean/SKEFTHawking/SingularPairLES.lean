/-
# Phase 5q.F (w₂-foundation, brick 6b) — the long exact sequence of a pair `(X, S)`

The LES `⋯ → Hₙ(S) → Hₙ(X) → Hₙ(X,S) →(δ) Hₙ₋₁(S) → ⋯` (singular ℤ/2 homology). Built by hand on
this phase's relative homology (`SingularRelativeHomologyMod2`, brick 6a): the induced maps `i_*`, `j_*`
and the **connecting homomorphism** `δ : Hₙ₊₁(X,S) → Hₙ(S)`, `[c] ↦ [∂c]` (the snake-lemma boundary).
The δ-adjacent exactness pins the **local homology** `Hₙ(ℝⁿ,ℝⁿ∖0) ≅ ℤ/2` (→ the fundamental class →
Poincaré duality). Kernel-pure (`{propext, Classical.choice, Quot.sound}`).

The connecting map extracts `∂c ∈ C_n(S)` (the subspace chains) back to a genuine chain of `S` via the
injective chain inclusion's range-inverse (`inclRangeEquiv`), then takes its homology class.
-/
import Mathlib
import SKEFTHawking.SingularRelativeHomologyMod2

namespace SKEFTHawking.SingularPairLES

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2

variable {X : TopCat} (S : Set X)

/-! ## §1. The range-inverse of the chain inclusion -/

/-- `C_n(S) ≃ₗ subspaceChains S n` — the chain inclusion is injective, so it is a linear isomorphism
onto its range (`= subspaceChains S n`). The inverse extracts a chain of `S` from a subspace chain. -/
noncomputable def inclRangeEquiv (n : ℕ) :
    SingularChain (sub S) n ≃ₗ[ZMod 2] (subspaceChains S n) :=
  LinearEquiv.ofInjective (chainIncl S n) (chainIncl_injective S n)

/-- The defining property: `chainIncl` of the extracted chain recovers the subspace chain. -/
theorem chainIncl_inclRangeEquiv_symm (n : ℕ) (y : subspaceChains S n) :
    chainIncl S n ((inclRangeEquiv S n).symm y) = (y : SingularChain X n) := by
  have := (inclRangeEquiv S n).apply_symm_apply y
  exact congrArg Subtype.val this

/-! ## §2. The connecting homomorphism `δ : Hₙ₊₁(X,S) → Hₙ(S)` -/

/-- The **lift submodule** `Z_n = { c ∈ C_{n+1}(X) | ∂c ∈ C_n(S) }` — the absolute chains whose boundary
lands in the subspace. Every relative `(n+1)`-cycle lifts to such a chain. -/
noncomputable def relCycleLift (n : ℕ) : Submodule (ZMod 2) (SingularChain X (n + 1)) :=
  Submodule.comap (chainBoundary X n) (subspaceChains S n)

/-- `∂` extracted to a chain of `S`: `Z_n → C_n(S)`, `c ↦ (chainIncl)⁻¹(∂c)`. -/
noncomputable def boundaryExtract (n : ℕ) :
    relCycleLift S n →ₗ[ZMod 2] SingularChain (sub S) n :=
  (inclRangeEquiv S n).symm.toLinearMap.comp
    (LinearMap.restrict (chainBoundary X n) (fun _c hc => Submodule.mem_comap.mp hc))

/-- The extraction recovers `∂c` after re-including: `chainIncl (boundaryExtract c) = ∂c`. -/
theorem chainIncl_boundaryExtract (n : ℕ) (c : relCycleLift S n) :
    chainIncl S n (boundaryExtract S n c) = chainBoundary X n (c : SingularChain X (n + 1)) := by
  rw [boundaryExtract, LinearMap.comp_apply, LinearEquiv.coe_coe, chainIncl_inclRangeEquiv_symm]
  rfl

/-- The extracted chain is a **cycle** of `S`: `∂(boundaryExtract c) = 0` (from `∂² = 0` + injectivity).
For `n = 0` this is vacuous (`cycles ⊤`). -/
theorem boundaryExtract_mem_cycles (n : ℕ) (c : relCycleLift S n) :
    boundaryExtract S n c ∈ cycles (sub S) n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    show boundaryExtract S (m + 1) c ∈ LinearMap.ker (chainBoundary (sub S) m)
    rw [LinearMap.mem_ker]
    apply chainIncl_injective S m
    rw [map_zero, chainIncl_chainBoundary, chainIncl_boundaryExtract,
      chainBoundary_chainBoundary_apply]

/-- The connecting map on lift-chains: `Z_n →ₗ Hₙ(S)`, `c ↦ [boundaryExtract c]`. -/
noncomputable def connectingLift (n : ℕ) : relCycleLift S n →ₗ[ZMod 2] Homology (sub S) n :=
  (Submodule.mkQ _).comp ((boundaryExtract S n).codRestrict (cycles (sub S) n)
    (boundaryExtract_mem_cycles S n))

theorem connectingLift_apply (n : ℕ) (c : relCycleLift S n) :
    connectingLift S n c = Homology.mk (sub S) n ⟨boundaryExtract S n c,
      boundaryExtract_mem_cycles S n c⟩ := rfl

/-! ## §2b. Descent of `connectingLift` to relative homology -/

/-- A lift-chain `c ∈ Z_n` represents a relative `(n+1)`-cycle: `mk c ∈ Hₙ₊₁(X,S)`. -/
theorem mk_mem_relCycles (n : ℕ) (c : SingularChain X (n + 1)) (hc : c ∈ relCycleLift S n) :
    RelativeChain.mk S (n + 1) c ∈ relCycles S (n + 1) := by
  show RelativeChain.mk S (n + 1) c ∈ LinearMap.ker (relBoundary S n)
  rw [LinearMap.mem_ker, relBoundary_mk]
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_comap.mp hc)

/-- The surjection `Z_n ↠ Hₙ₊₁(X,S)`, `c ↦ [mk c]` — every relative cycle lifts to an absolute chain
whose boundary lands in the subspace. -/
noncomputable def relCycleToHom (n : ℕ) :
    relCycleLift S n →ₗ[ZMod 2] RelativeHomology S (n + 1) :=
  (Submodule.mkQ _).comp
    ((Submodule.mkQ (subspaceChains S (n + 1)) ∘ₗ (relCycleLift S n).subtype).codRestrict
      (relCycles S (n + 1)) (fun c => mk_mem_relCycles S n c.1 c.2))

theorem relCycleToHom_apply (n : ℕ) (c : relCycleLift S n) :
    relCycleToHom S n c = RelativeHomology.mk (S := S) (n + 1)
      ⟨RelativeChain.mk S (n + 1) c, mk_mem_relCycles S n c.1 c.2⟩ := rfl

theorem relCycleToHom_surjective (n : ℕ) : Function.Surjective (relCycleToHom S n) := by
  intro h
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ z.1
  have hcZ : c ∈ relCycleLift S n := by
    show chainBoundary X n c ∈ subspaceChains S n
    have hz : relBoundary S n z.1 = 0 := LinearMap.mem_ker.mp z.2
    rw [← hc] at hz
    rw [show (Submodule.Quotient.mk c : RelativeChain S (n + 1)) = RelativeChain.mk S (n + 1) c from
      rfl, relBoundary_mk] at hz
    exact (Submodule.Quotient.mk_eq_zero _).1 hz
  refine ⟨⟨c, hcZ⟩, ?_⟩
  rw [relCycleToHom_apply]
  exact congrArg (RelativeHomology.mk (S := S) (n + 1)) (Subtype.ext hc)

/-- The snake-lemma kernel inclusion: `ker(c ↦ [mk c]) ≤ ker(c ↦ [∂c])`. If `[mk c] = 0`, then
`mk c` is a relative boundary, so `c` differs from a `C(X)`-boundary by a subspace chain `chainIncl e`,
whence `∂c = chainIncl(∂e)` and `boundaryExtract c = ∂e` is a boundary in `S`. -/
theorem connecting_ker_le (n : ℕ) :
    LinearMap.ker (relCycleToHom S n) ≤ LinearMap.ker (connectingLift S n) := by
  intro c hc
  rw [LinearMap.mem_ker, relCycleToHom_apply, RelativeHomology.mk_eq_zero_iff] at hc
  rw [LinearMap.mem_ker, connectingLift_apply]
  -- `[mk ↑c] = 0` ⟹ `mk ↑c` is a relative boundary `relBoundary (mk d)`
  obtain ⟨w, hw⟩ := hc
  obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective (subspaceChains S (n + 1 + 1)) w
  have h1 : RelativeChain.mk S (n + 1) (c : SingularChain X (n + 1))
      = RelativeChain.mk S (n + 1) (chainBoundary X (n + 1) d) := by
    rw [← relBoundary_mk]; exact hw.symm
  rw [RelativeChain.mk, RelativeChain.mk] at h1
  obtain ⟨e, he⟩ := (Submodule.Quotient.eq (subspaceChains S (n + 1))).1 h1
  -- he : chainIncl e = ↑c - ∂d, so ↑c = ∂d + chainIncl e, hence ∂c = chainIncl(∂e)
  have hc_eq : (c : SingularChain X (n + 1)) = chainBoundary X (n + 1) d + chainIncl S (n + 1) e := by
    rw [he]; abel
  have hbe : boundaryExtract S n c = chainBoundary (sub S) n e := by
    apply chainIncl_injective S n
    rw [chainIncl_boundaryExtract, chainIncl_chainBoundary, hc_eq, map_add,
      chainBoundary_chainBoundary_apply, zero_add]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  show boundaryExtract S n c ∈ boundaries (sub S) n
  rw [hbe]
  exact LinearMap.mem_range_self _ e

/-- **The connecting homomorphism** `δ : Hₙ₊₁(X,S) → Hₙ(S)`, `[c] ↦ [∂c]` — descends `connectingLift`
through the surjection `relCycleToHom` (`connecting_ker_le` is the snake-lemma well-definedness). -/
noncomputable def connecting (n : ℕ) :
    RelativeHomology S (n + 1) →ₗ[ZMod 2] Homology (sub S) n :=
  (Submodule.liftQ (LinearMap.ker (relCycleToHom S n)) (connectingLift S n)
    (connecting_ker_le S n)).comp
    (LinearMap.quotKerEquivOfSurjective (relCycleToHom S n)
      (relCycleToHom_surjective S n)).symm.toLinearMap

/-- The connecting map computes as `[c] ↦ [∂c]`: on the class of a lift-chain `c ∈ Z_n` it is
`[boundaryExtract c]`. -/
theorem connecting_relCycleToHom (n : ℕ) (c : relCycleLift S n) :
    connecting S n (relCycleToHom S n c) = connectingLift S n c := by
  rw [connecting, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-! ## §3. The induced maps `i_* : Hₙ(S) → Hₙ(X)` and `j_* : Hₙ(X) → Hₙ(X,S)` -/

/-- `chainIncl` preserves cycles (it is a chain map). -/
theorem chainIncl_mem_cycles (n : ℕ) (z : SingularChain (sub S) n) (hz : z ∈ cycles (sub S) n) :
    chainIncl S n z ∈ cycles X n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz' : chainBoundary (sub S) m z = 0 := LinearMap.mem_ker.mp hz
    show chainIncl S (m + 1) z ∈ LinearMap.ker (chainBoundary X m)
    rw [LinearMap.mem_ker, ← chainIncl_chainBoundary, hz', map_zero]

/-- `chainIncl` preserves boundaries. -/
theorem chainIncl_mem_boundaries (n : ℕ) (z : SingularChain (sub S) n)
    (hz : z ∈ boundaries (sub S) n) : chainIncl S n z ∈ boundaries X n := by
  obtain ⟨d, rfl⟩ := hz
  exact ⟨chainIncl S (n + 1) d, (chainIncl_chainBoundary S n d).symm⟩

/-- **The induced map `i_* : Hₙ(S) → Hₙ(X)`** of the inclusion `S ↪ X` (functoriality of homology). -/
noncomputable def homIncl (n : ℕ) : Homology (sub S) n →ₗ[ZMod 2] Homology X n :=
  Submodule.mapQ _ _ (LinearMap.restrict (chainIncl S n) (fun z hz => chainIncl_mem_cycles S n z hz))
    (fun z hz => by
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
        LinearMap.restrict_coe_apply] at hz ⊢
      exact chainIncl_mem_boundaries S n _ hz)

/-- `RelativeChain.mk` preserves cycles (it is a chain map onto the relative complex). -/
theorem relMk_mem_relCycles (n : ℕ) (z : SingularChain X n) (hz : z ∈ cycles X n) :
    RelativeChain.mk S n z ∈ relCycles S n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz' : chainBoundary X m z = 0 := LinearMap.mem_ker.mp hz
    show RelativeChain.mk S (m + 1) z ∈ LinearMap.ker (relBoundary S m)
    rw [LinearMap.mem_ker, relBoundary_mk, hz', RelativeChain.mk_eq_zero_iff]
    exact Submodule.zero_mem _

/-- `RelativeChain.mk` preserves boundaries. -/
theorem relMk_mem_relBoundaries (n : ℕ) (z : SingularChain X n) (hz : z ∈ boundaries X n) :
    RelativeChain.mk S n z ∈ relBoundaries S n := by
  obtain ⟨d, rfl⟩ := hz
  exact ⟨RelativeChain.mk S (n + 1) d, (relBoundary_mk S n d).symm⟩

/-- **The induced map `j_* : Hₙ(X) → Hₙ(X,S)`** (the quotient `C(X) ↠ C(X,S)` on homology). -/
noncomputable def homProj (n : ℕ) : Homology X n →ₗ[ZMod 2] RelativeHomology S n :=
  Submodule.mapQ _ _
    (LinearMap.restrict (Submodule.mkQ (subspaceChains S n))
      (fun z hz => relMk_mem_relCycles S n z hz))
    (fun z hz => by
      rw [Submodule.mem_comap]
      show RelativeChain.mk S n (z : SingularChain X n) ∈ relBoundaries S n
      exact relMk_mem_relBoundaries S n z hz)

@[simp] theorem homIncl_mk (n : ℕ) (z : cycles (sub S) n) :
    homIncl S n (Homology.mk (sub S) n z)
      = Homology.mk X n ⟨chainIncl S n (z : SingularChain (sub S) n),
          chainIncl_mem_cycles S n z z.2⟩ := rfl

@[simp] theorem homProj_mk (n : ℕ) (z : cycles X n) :
    homProj S n (Homology.mk X n z)
      = RelativeHomology.mk S n ⟨RelativeChain.mk S n (z : SingularChain X n),
          relMk_mem_relCycles S n z z.2⟩ := rfl

/-! ## §4. Exactness of the LES of the pair -/

/-- A cycle of `X` lies in the relative-cycle lift submodule (its boundary `0` is a subspace chain). -/
theorem cycle_mem_relCycleLift (n : ℕ) (z : cycles X (n + 1)) :
    (z : SingularChain X (n + 1)) ∈ relCycleLift S n := by
  show chainBoundary X n (z : SingularChain X (n + 1)) ∈ subspaceChains S n
  rw [LinearMap.mem_ker.mp z.2]
  exact Submodule.zero_mem _

/-- **The complex property `δ ∘ j_* = 0`**: the connecting map kills the image of `j_*` (a class from a
genuine `X`-cycle has boundary `0`, so its extraction is a boundary). -/
theorem connecting_homProj (n : ℕ) (x : Homology X (n + 1)) :
    connecting S n (homProj S (n + 1) x) = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hzZ := cycle_mem_relCycleLift S n z
  show connecting S n (relCycleToHom S n ⟨(z : SingularChain X (n + 1)), hzZ⟩) = 0
  rw [connecting_relCycleToHom, connectingLift_apply]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  show boundaryExtract S n ⟨(z : SingularChain X (n + 1)), hzZ⟩ ∈ boundaries (sub S) n
  have hb0 : boundaryExtract S n ⟨(z : SingularChain X (n + 1)), hzZ⟩ = 0 := by
    apply chainIncl_injective S n
    rw [chainIncl_boundaryExtract, map_zero]
    exact LinearMap.mem_ker.mp z.2
  rw [hb0]
  exact Submodule.zero_mem _

/-- **Exactness at `Hₙ₊₁(X,S)`**: `ker δ = im j_*`. -/
theorem exact_homProj_connecting (n : ℕ) :
    Function.Exact (homProj S (n + 1)) (connecting S n) := by
  intro y
  obtain ⟨c, rfl⟩ := relCycleToHom_surjective S n y
  rw [connecting_relCycleToHom, connectingLift_apply]
  constructor
  · intro h
    have hb : boundaryExtract S n c ∈ boundaries (sub S) n := by
      have h2 := (Submodule.Quotient.mk_eq_zero _).1 h
      rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at h2
    obtain ⟨e, he⟩ := hb
    have hcyc : (c : SingularChain X (n + 1)) - chainIncl S (n + 1) e ∈ cycles X (n + 1) := by
      show _ ∈ LinearMap.ker (chainBoundary X n)
      rw [LinearMap.mem_ker, map_sub, ← chainIncl_boundaryExtract S n c, ← he,
        chainIncl_chainBoundary, sub_self]
    refine ⟨Homology.mk X (n + 1) ⟨_, hcyc⟩, ?_⟩
    rw [homProj_mk, relCycleToHom_apply]
    refine congrArg (RelativeHomology.mk (S := S) (n + 1)) (Subtype.ext ?_)
    show RelativeChain.mk S (n + 1) ((c : SingularChain X (n + 1)) - chainIncl S (n + 1) e)
      = RelativeChain.mk S (n + 1) (c : SingularChain X (n + 1))
    rw [RelativeChain.mk, RelativeChain.mk]
    refine (Submodule.Quotient.eq _).2 ?_
    have hsub : ((c : SingularChain X (n + 1)) - chainIncl S (n + 1) e)
        - (c : SingularChain X (n + 1)) = -chainIncl S (n + 1) e := by abel
    rw [hsub]
    exact Submodule.neg_mem _ ⟨e, rfl⟩
  · rintro ⟨x, hx⟩
    rw [← connectingLift_apply, ← connecting_relCycleToHom, ← hx]
    exact connecting_homProj S n x

/-- **The complex property `i_* ∘ δ = 0`**: `i_*` kills the image of `δ` (the extracted boundary
re-includes to `∂c`, a boundary in `X`). -/
theorem homIncl_connecting (n : ℕ) (y : RelativeHomology S (n + 1)) :
    homIncl S n (connecting S n y) = 0 := by
  obtain ⟨c, rfl⟩ := relCycleToHom_surjective S n y
  rw [connecting_relCycleToHom, connectingLift_apply, homIncl_mk]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  show chainIncl S n (boundaryExtract S n c) ∈ boundaries X n
  rw [chainIncl_boundaryExtract]
  exact LinearMap.mem_range_self _ _

/-- **Exactness at `Hₙ(S)`**: `ker i_* = im δ`. -/
theorem exact_connecting_homIncl (n : ℕ) :
    Function.Exact (connecting S n) (homIncl S n) := by
  intro w₀
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w₀
  constructor
  · intro h
    have hb : chainIncl S n (w : SingularChain (sub S) n) ∈ boundaries X n := by
      have h2 : homIncl S n (Homology.mk (sub S) n w) = 0 := h
      rw [homIncl_mk] at h2
      have h3 := (Submodule.Quotient.mk_eq_zero _).1 h2
      rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at h3
    obtain ⟨d, hd⟩ := hb
    have hdZ : d ∈ relCycleLift S n := by
      show chainBoundary X n d ∈ subspaceChains S n
      rw [hd]; exact ⟨w, rfl⟩
    refine ⟨relCycleToHom S n ⟨d, hdZ⟩, ?_⟩
    rw [connecting_relCycleToHom, connectingLift_apply]
    have hbe : boundaryExtract S n ⟨d, hdZ⟩ = (w : SingularChain (sub S) n) := by
      apply chainIncl_injective S n
      rw [chainIncl_boundaryExtract]; exact hd
    exact congrArg (Homology.mk (sub S) n) (Subtype.ext hbe)
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact homIncl_connecting S n y

/-- **The complex property `j_* ∘ i_* = 0`**: a class pulled in from `S` becomes a subspace chain,
hence `0` in the relative complex. -/
theorem homProj_homIncl (n : ℕ) (w : Homology (sub S) n) :
    homProj S n (homIncl S n w) = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  show homProj S n (homIncl S n (Homology.mk (sub S) n z)) = 0
  rw [homIncl_mk, homProj_mk]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  show RelativeChain.mk S n (chainIncl S n (z : SingularChain (sub S) n)) ∈ relBoundaries S n
  rw [(RelativeChain.mk_eq_zero_iff S n _).2 ⟨z, rfl⟩]
  exact Submodule.zero_mem _

/-- **Exactness at `Hₙ(X)`**: `ker j_* = im i_*` (snake-lemma argument: `[mk c] = 0` ⟹ `c` differs
from a boundary by a subspace cycle `chainIncl e`, whence `[c] = i_*[e]`). -/
theorem exact_homIncl_homProj (n : ℕ) :
    Function.Exact (homIncl S n) (homProj S n) := by
  intro x
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro h
    have h2 : homProj S n (Homology.mk X n c) = 0 := h
    rw [homProj_mk, RelativeHomology.mk_eq_zero_iff] at h2
    obtain ⟨w, hw⟩ := h2
    obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective (subspaceChains S (n + 1)) w
    have h1 : RelativeChain.mk S n (c : SingularChain X n)
        = RelativeChain.mk S n (chainBoundary X n d) := by
      rw [← relBoundary_mk]; exact hw.symm
    rw [RelativeChain.mk, RelativeChain.mk] at h1
    obtain ⟨e, he⟩ := (Submodule.Quotient.eq (subspaceChains S n)).1 h1
    have hecyc : e ∈ cycles (sub S) n := by
      cases n with
      | zero => exact Submodule.mem_top
      | succ m =>
        show e ∈ LinearMap.ker (chainBoundary (sub S) m)
        rw [LinearMap.mem_ker]
        apply chainIncl_injective S m
        rw [map_zero, chainIncl_chainBoundary, he, map_sub, chainBoundary_chainBoundary_apply,
          LinearMap.mem_ker.mp c.2, sub_zero]
    refine ⟨Homology.mk (sub S) n ⟨e, hecyc⟩, ?_⟩
    rw [homIncl_mk]
    refine (Submodule.Quotient.eq _).2 ?_
    rw [Submodule.submoduleOf, Submodule.mem_comap]
    show chainIncl S n e - (c : SingularChain X n) ∈ boundaries X n
    rw [he]
    have hsub : ((c : SingularChain X n) - chainBoundary X n d) - (c : SingularChain X n)
        = -chainBoundary X n d := by abel
    rw [hsub]
    exact Submodule.neg_mem _ ⟨d, rfl⟩
  · rintro ⟨w, hw⟩
    rw [← hw]
    exact homProj_homIncl S n w

end SKEFTHawking.SingularPairLES
