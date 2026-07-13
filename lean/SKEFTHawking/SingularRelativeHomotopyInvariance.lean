/-
# Relative (pair) homotopy invariance of singular ℤ/2 homology — the mod-2 mirror

The mod-2 counterpart of `SingularRelativeHomotopyInvarianceInt.relHomologyInt_map_eq_of_homotopic_pair`:
two maps of pairs `f, g : (X, A) → (Y, B)` homotopic THROUGH maps of pairs induce the SAME map
`Hₙ(X, A; ℤ/2) → Hₙ(Y, B; ℤ/2)`. Built with NO new prism: the in-tree ℤ/2 prism operator
(`SingularPrism.prismOp`, chain homotopy `∂P + P∂ = g_# + f_#` over ℤ/2) already restricts — a prism
simplex over an `A`-supported simplex realises inside `H(A × I) ⊆ B` (`range_realize_prismSimplex`),
so the absolute chain homotopy DESCENDS to the relative complex (`prismOp_mem_subspaceChains`), where
the `P∂` term dies and `∂P` is a relative boundary. Over ℤ/2 the endpoint sum is `g_# + f_#`, so the
two induced maps coincide directly.

`RelativeHomology.map_bijective_of_homotopyEquiv_pair` is the pair analogue of the absolute
`SingularHomotopyInvariance.Homology.map_bijective_of_homotopyEquiv`: a pair homotopy equivalence
induces an isomorphism on relative homology (degree `≥ 1`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularRelativeFunctoriality

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularHomotopyInvariance (slice endMap_eq_mapChain)
open SKEFTHawking.SingularExcision (single_mem_subspaceChains_of_subordinate)
open SKEFTHawking.SingularDisjointUnion (range_realize_simplexIncl)

namespace SKEFTHawking.SingularRelativeHomotopyInvariance

/-! ## §1. The prism restricts: `A`-supported chains have `B`-supported prisms -/

/-- **A prism simplex over an `A`-supported simplex realises in `H(A × I)`**: if the homotopy `H`
maps `A × I` into `B` and `σ` realises inside `A`, every prism simplex `prismSimplex H σ i` realises
inside `B` — its realisation is `H ∘ (σ∘α i, β i)`, pointwise `H(σ(…), t)` with `σ(…) ∈ A`. The
topological content is coefficient-free (shared with the integral version). -/
theorem range_realize_prismSimplex {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    {A : Set ↑X} {B : Set ↑Y} (hH : ∀ a ∈ A, ∀ t : unitInterval, H (a, t) ∈ B)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)))
    (hσ : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ A) (i : Fin (n + 1)) :
    Set.range (Y.toSSetObjEquiv (op (SimplexCategory.mk (n + 1))) (prismSimplex H σ i)) ⊆ B := by
  rw [prismSimplex, Equiv.apply_symm_apply]
  rintro y ⟨p, rfl⟩
  exact hH _ (hσ ⟨_, rfl⟩) _

/-- **The ℤ/2 prism operator carries `A`-chains to `B`-chains** when the homotopy maps `A × I` into
`B` — the whole content of "the absolute prism descends to the pair"; no new prism combinatorics. -/
theorem prismOp_mem_subspaceChains {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y))
    {A : Set ↑X} {B : Set ↑Y} (hH : ∀ a ∈ A, ∀ t : unitInterval, H (a, t) ∈ B) (n : ℕ)
    {c : SingularChain X n} (hc : c ∈ subspaceChains A n) :
    prismOp H n c ∈ subspaceChains B (n + 1) := by
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d₁ d₂ h₁ h₂ => rw [map_add, map_add]; exact Submodule.add_mem _ h₁ h₂
  | single τ a =>
      rw [chainIncl_single, prismOp_single, prismBasis, Finset.smul_sum]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      refine Submodule.smul_mem _ _ ?_
      exact single_mem_subspaceChains_of_subordinate
        (range_realize_prismSimplex H hH (simplexIncl A n τ) (range_realize_simplexIncl A τ) i)

/-! ## §2. Pair homotopy invariance -/

/-- **Relative (pair) homotopy invariance** (ℤ/2): two maps of pairs `f, g : (X, A) → (Y, B)`
homotopic through maps of pairs (`H` with `H(A × I) ⊆ B`, `H(·,0) = f`, `H(·,1) = g`) induce EQUAL
maps `Hₙ₊₁(X, A; ℤ/2) → Hₙ₊₁(Y, B; ℤ/2)`. The absolute ℤ/2 chain homotopy `∂P + P∂ = g_# + f_#`
descends: on a relative cycle the `P∂` term is a `B`-chain (`prismOp_mem_subspaceChains`) and `∂P`
is a relative boundary. The pair-level engine of the moving-puncture device, mod-2. -/
theorem RelativeHomology.map_eq_of_homotopic_pair {X Y : TopCat} {A : Set ↑X} {B : Set ↑Y}
    {f g : C(↑X, ↑Y)} (H : C(↑X × unitInterval, ↑Y))
    (h0 : slice H 0 = f) (h1 : slice H 1 = g)
    (hH : ∀ a ∈ A, ∀ t : unitInterval, H (a, t) ∈ B)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (n : ℕ) :
    RelativeHomology.map g hg (n + 1) = RelativeHomology.map f hf (n + 1) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [RelativeHomology.map_mk, RelativeHomology.map_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
  -- reduce to: relMapChain g (↑z) − relMapChain f (↑z) ∈ relBoundaries B (n+1)
  have hcoe : ((relCyclesMap g hg (n + 1) z - relCyclesMap f hf (n + 1) z :
        relCycles B (n + 1)) : RelativeChain B (n + 1))
      = relMapChain g hg (n + 1) (z : RelativeChain A (n + 1))
        - relMapChain f hf (n + 1) (z : RelativeChain A (n + 1)) := by
    rw [Submodule.coe_sub, relCyclesMap_coe, relCyclesMap_coe]
  rw [hcoe]
  -- over ℤ/2 the difference is a sum
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]
  -- lift the relative cycle to an absolute chain c with ∂c an A-chain
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChain A (n + 1))
  have hzcyc : relBoundary A n (z : RelativeChain A (n + 1)) = 0 := z.2
  have hzb : chainBoundary X n c ∈ subspaceChains A n := by
    rw [← RelativeChain.mk_eq_zero_iff A n, ← relBoundary_mk]
    rw [show (Submodule.Quotient.mk c : RelativeChain A (n + 1))
      = RelativeChain.mk A (n + 1) c from rfl] at hc
    rw [hc]
    exact hzcyc
  -- the ℤ/2 prism identity, sliced to f and g
  have hkey := prism_chainHomotopy H c
  rw [endMap_eq_mapChain, endMap_eq_mapChain, h0, h1] at hkey
  refine ⟨RelativeChain.mk B (n + 1 + 1) (prismOp H (n + 1) c), ?_⟩
  have e1 : relBoundary B (n + 1) (RelativeChain.mk B (n + 1 + 1) (prismOp H (n + 1) c))
      = RelativeChain.mk B (n + 1) (chainBoundary Y (n + 1) (prismOp H (n + 1) c)) :=
    relBoundary_mk B (n + 1) _
  have e2 : RelativeChain.mk B (n + 1) (chainBoundary Y (n + 1) (prismOp H (n + 1) c))
      = RelativeChain.mk B (n + 1) (chainBoundary Y (n + 1) (prismOp H (n + 1) c)
          + prismOp H n (chainBoundary X n c)) :=
    (Submodule.Quotient.eq _).mpr (by
      have hd : chainBoundary Y (n + 1) (prismOp H (n + 1) c)
          - (chainBoundary Y (n + 1) (prismOp H (n + 1) c)
              + prismOp H n (chainBoundary X n c))
          = -(prismOp H n (chainBoundary X n c)) := by abel
      rw [hd]
      exact neg_mem (prismOp_mem_subspaceChains H hH n hzb))
  have e3 : RelativeChain.mk B (n + 1) (chainBoundary Y (n + 1) (prismOp H (n + 1) c)
        + prismOp H n (chainBoundary X n c))
      = RelativeChain.mk B (n + 1) (mapChain g (n + 1) c + mapChain f (n + 1) c) :=
    congrArg (RelativeChain.mk B (n + 1)) hkey
  have e4 : RelativeChain.mk B (n + 1) (mapChain g (n + 1) c + mapChain f (n + 1) c)
      = RelativeChain.mk B (n + 1) (mapChain g (n + 1) c)
        + RelativeChain.mk B (n + 1) (mapChain f (n + 1) c) :=
    Submodule.Quotient.mk_add _
  have e5 : RelativeChain.mk B (n + 1) (mapChain g (n + 1) c)
      = relMapChain g hg (n + 1) (z : RelativeChain A (n + 1)) := by
    rw [← hc]
    exact (relMapChain_mk g hg (n + 1) c).symm
  have e6 : RelativeChain.mk B (n + 1) (mapChain f (n + 1) c)
      = relMapChain f hf (n + 1) (z : RelativeChain A (n + 1)) := by
    rw [← hc]
    exact (relMapChain_mk f hf (n + 1) c).symm
  exact (((e1.trans e2).trans e3).trans e4).trans (by rw [e5, e6])

/-! ## §3. A pair homotopy equivalence induces an iso on relative homology -/

/-- **A pair homotopy equivalence induces an isomorphism on relative homology** (degree `≥ 1`): given
maps of pairs `f : (X, A) → (Y, B)`, `g : (Y, B) → (X, A)` with pair homotopies `g ∘ f ≃ id_{(X,A)}`
(through maps of pairs — `Hgf` keeps `A × I` inside `A`) and `f ∘ g ≃ id_{(Y,B)}` (`Hfg` keeps
`B × I` inside `B`), the induced map `Hₙ₊₁(X, A; ℤ/2) → Hₙ₊₁(Y, B; ℤ/2)` is bijective. The pair
analogue of `SingularHomotopyInvariance.Homology.map_bijective_of_homotopyEquiv`: pure functoriality
(`RelativeHomology.map_comp`, `RelativeHomology.map_id`) plus the pair homotopy invariance of §2. This
is the leg that discharges the cylinder collar-injectivity residual — `∂W ↪ Kᶜ` is a pair homotopy
equivalence through the explicit clamp retraction, so `relIncl (∂W ⊆ Kᶜ)` is an iso, hence injective. -/
theorem RelativeHomology.map_bijective_of_homotopyEquiv_pair {X Y : TopCat}
    {A : Set ↑X} {B : Set ↑Y}
    (f : C(↑X, ↑Y)) (hf : Set.MapsTo f A B) (g : C(↑Y, ↑X)) (hg : Set.MapsTo g B A)
    (Hgf : C(↑X × unitInterval, ↑X)) (hgfH : ∀ a ∈ A, ∀ t : unitInterval, Hgf (a, t) ∈ A)
    (hgf0 : slice Hgf 0 = g.comp f) (hgf1 : slice Hgf 1 = ContinuousMap.id ↑X)
    (Hfg : C(↑Y × unitInterval, ↑Y)) (hfgH : ∀ b ∈ B, ∀ t : unitInterval, Hfg (b, t) ∈ B)
    (hfg0 : slice Hfg 0 = f.comp g) (hfg1 : slice Hfg 1 = ContinuousMap.id ↑Y) (n : ℕ) :
    Function.Bijective (RelativeHomology.map f hf (n + 1)) := by
  have hgf : (RelativeHomology.map g hg (n + 1)).comp (RelativeHomology.map f hf (n + 1))
      = LinearMap.id := by
    rw [← RelativeHomology.map_comp f hf g hg (n + 1),
      ← RelativeHomology.map_eq_of_homotopic_pair Hgf hgf0 hgf1 hgfH
        (fun a ha => hg (hf ha)) (Set.mapsTo_id A) n,
      RelativeHomology.map_id]
  have hfg : (RelativeHomology.map f hf (n + 1)).comp (RelativeHomology.map g hg (n + 1))
      = LinearMap.id := by
    rw [← RelativeHomology.map_comp g hg f hf (n + 1),
      ← RelativeHomology.map_eq_of_homotopic_pair Hfg hfg0 hfg1 hfgH
        (fun b hb => hf (hg hb)) (Set.mapsTo_id B) n,
      RelativeHomology.map_id]
  have hL : Function.LeftInverse (RelativeHomology.map g hg (n + 1))
      (RelativeHomology.map f hf (n + 1)) :=
    fun x => by rw [← LinearMap.comp_apply, hgf, LinearMap.id_apply]
  have hR : Function.RightInverse (RelativeHomology.map g hg (n + 1))
      (RelativeHomology.map f hf (n + 1)) :=
    fun x => by rw [← LinearMap.comp_apply, hfg, LinearMap.id_apply]
  exact ⟨hL.injective, hR.surjective⟩

end SKEFTHawking.SingularRelativeHomotopyInvariance
