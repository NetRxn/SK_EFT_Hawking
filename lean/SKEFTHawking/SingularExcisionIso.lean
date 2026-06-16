import Mathlib
import SKEFTHawking.SingularExcision
import SKEFTHawking.SingularPairLES

/-!
# Singular excision isomorphism (ℤ/2)

The homology-level excision theorem: for sets `A B : Set X` whose interiors cover `X`, the
inclusion of pairs `(B, A ∩ B) ↪ (X, A)` induces an isomorphism
`Hₙ(B, A ∩ B; ℤ/2) ≅ Hₙ(X, A; ℤ/2)`.

This packages the relative small-chains theorem (`relative_add_singularSd_iterate_mem_relBoundaries`
and `relative_small_boundary`, both in `SingularExcision`) with the two-cover decomposition
`smallChains {A, B} = C(A) + C(B)` (`smallChains_two_eq`) and `C(A) ⊓ C(B) = C(A ∩ B)`
(`subspaceChains_inf`). The relative part of the *source* pair is `A` viewed inside `sub B`, i.e.
the preimage `Subtype.val ⁻¹' A : Set ↥B`; the chain-level inclusion is `chainIncl B`.

## Main results
* `range_toSSetObjEquiv_simplexIncl` — realization of an included simplex is the `val`-image.
* `simplexIncl_range_subset_iff` — geometric reflection: an included simplex lands in `A` iff the
  original lands in `Subtype.val ⁻¹' A`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcision SKEFTHawking.SingularSubdivision

namespace SKEFTHawking.SingularExcisionIso

variable {X : TopCat}

/-- The pullback of `A ⊆ X` to the subspace `sub B` — the relative part of the *source* pair
`(B, A ∩ B)` viewed intrinsically as a pair `(sub B, restr A B)`. -/
abbrev restr (A B : Set X) : Set (sub B) := Subtype.val ⁻¹' A

/-- The realization of an included simplex `simplexIncl B τ'` is the `Subtype.val`-image of the
realization of `τ'` (a simplex of `sub B`). Immediate from `toSSetObjEquiv_simplexIncl`, which
identifies the realization with `inclMap B` post-composed onto the `sub B`-realization. -/
theorem range_toSSetObjEquiv_simplexIncl (B : Set X) {n : ℕ}
    (τ' : (TopCat.toSSet.obj (sub B)).obj (op (SimplexCategory.mk n))) :
    Set.range ⇑(X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl B n τ')) =
      Subtype.val '' Set.range ⇑((sub B).toSSetObjEquiv (op (SimplexCategory.mk n)) τ') := by
  rw [toSSetObjEquiv_simplexIncl, ContinuousMap.coe_comp, Set.range_comp]
  rfl

/-- **Geometric reflection**: the included simplex lands in `A ⊆ X` iff the original simplex (of
`sub B`) lands in the preimage `Subtype.val ⁻¹' A`. (`Subtype.val` is injective, so image-subset
is preimage-subset.) -/
theorem simplexIncl_range_subset_iff (A B : Set X) {n : ℕ}
    (τ' : (TopCat.toSSet.obj (sub B)).obj (op (SimplexCategory.mk n))) :
    Set.range ⇑(X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl B n τ')) ⊆ A ↔
      Set.range ⇑((sub B).toSSetObjEquiv (op (SimplexCategory.mk n)) τ') ⊆ Subtype.val ⁻¹' A := by
  rw [range_toSSetObjEquiv_simplexIncl, Set.image_subset_iff]

/-- **Chain-level reflection**: `chainIncl B d` is supported in `A` iff `d` is supported in the
preimage `Subtype.val ⁻¹' A`. This makes `chainIncl B` a chain map of pairs
`(sub B, Subtype.val ⁻¹' A) → (X, A)` (and reflects subspace membership, needed for both halves of
the excision iso). -/
theorem chainIncl_mem_subspaceChains_iff (A B : Set X) {n : ℕ} (d : SingularChain (sub B) n) :
    chainIncl B n d ∈ subspaceChains A n ↔ d ∈ subspaceChains (Subtype.val ⁻¹' A) n := by
  classical
  have hd : chainIncl B n d = Finsupp.mapDomain (simplexIncl B n) d := by
    rw [chainIncl, Finsupp.lmapDomain_apply]
  constructor
  · intro h
    refine mem_subspaceChains_of_support (fun τ' hτ' => ?_)
    rw [← simplexIncl_range_subset_iff A B τ']
    refine range_of_mem_subspaceChains h ?_
    rw [Finsupp.mem_support_iff, hd, Finsupp.mapDomain_apply (simplexIncl_injective B n)]
    exact Finsupp.mem_support_iff.1 hτ'
  · intro h
    refine mem_subspaceChains_of_support (fun σ hσ => ?_)
    rw [hd] at hσ
    obtain ⟨τ', hτ', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hσ)
    rw [simplexIncl_range_subset_iff A B τ']
    exact range_of_mem_subspaceChains h hτ'

/-! ## §2. The relative-chain inclusion `C(B, A∩B) → C(X, A)` -/

/-- The pushforward of relative chains `C_n(B, A ∩ B) → C_n(X, A)` induced by `chainIncl B`
(well-defined by the `←` half of `chainIncl_mem_subspaceChains_iff`). Here the relative part of the
source is `A` pulled back into `sub B`, i.e. `Subtype.val ⁻¹' A`. -/
noncomputable def relChainIncl (A B : Set X) (n : ℕ) :
    RelativeChain (restr A B) n →ₗ[ZMod 2] RelativeChain A n :=
  Submodule.mapQ (subspaceChains (restr A B) n) (subspaceChains A n) (chainIncl B n)
    (fun d hd => Submodule.mem_comap.2 ((chainIncl_mem_subspaceChains_iff A B d).2 hd))

@[simp] theorem relChainIncl_mk (A B : Set X) (n : ℕ) (c : SingularChain (sub B) n) :
    relChainIncl A B n (RelativeChain.mk (restr A B) n c) =
      RelativeChain.mk A n (chainIncl B n c) := rfl

/-- `relChainIncl` is a chain map: it commutes with the relative boundary. -/
theorem relBoundary_relChainIncl (A B : Set X) (n : ℕ)
    (c : RelativeChain (restr A B) (n + 1)) :
    relBoundary A n (relChainIncl A B (n + 1) c) =
      relChainIncl A B n (relBoundary (restr A B) n c) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  show relBoundary A n (relChainIncl A B (n + 1) (RelativeChain.mk _ (n + 1) c)) =
    relChainIncl A B n (relBoundary (restr A B) n (RelativeChain.mk _ (n + 1) c))
  rw [relChainIncl_mk, relBoundary_mk, relBoundary_mk, relChainIncl_mk, chainIncl_chainBoundary]

/-- `relChainIncl` preserves relative cycles. -/
theorem relChainIncl_mem_relCycles (A B : Set X) (n : ℕ) (z : RelativeChain (restr A B) n)
    (hz : z ∈ relCycles (restr A B) n) : relChainIncl A B n z ∈ relCycles A n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz' : relBoundary (restr A B) m z = 0 := LinearMap.mem_ker.mp hz
    show relChainIncl A B (m + 1) z ∈ LinearMap.ker (relBoundary A m)
    rw [LinearMap.mem_ker, relBoundary_relChainIncl, hz', map_zero]

/-- `relChainIncl` preserves relative boundaries. -/
theorem relChainIncl_mem_relBoundaries (A B : Set X) (n : ℕ) (z : RelativeChain (restr A B) n)
    (hz : z ∈ relBoundaries (restr A B) n) : relChainIncl A B n z ∈ relBoundaries A n := by
  obtain ⟨d, rfl⟩ := hz
  exact ⟨relChainIncl A B (n + 1) d, relBoundary_relChainIncl A B n d⟩

/-! ## §3. The excision map on relative homology -/

/-- **The excision map** `Hₙ(B, A ∩ B) → Hₙ(X, A)` induced by `relChainIncl` (functoriality of
relative homology). The excision theorem (below) shows it is an isomorphism when `int A ∪ int B = X`. -/
noncomputable def excisionMap (A B : Set X) (n : ℕ) :
    RelativeHomology (restr A B) n →ₗ[ZMod 2] RelativeHomology A n :=
  Submodule.mapQ _ _
    (LinearMap.restrict (relChainIncl A B n) (fun z hz => relChainIncl_mem_relCycles A B n z hz))
    (fun z hz => by
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
        LinearMap.restrict_coe_apply] at hz ⊢
      exact relChainIncl_mem_relBoundaries A B n _ hz)

@[simp] theorem excisionMap_mk (A B : Set X) (n : ℕ) (z : relCycles (restr A B) n) :
    excisionMap A B n (RelativeHomology.mk (restr A B) n z)
      = RelativeHomology.mk A n ⟨relChainIncl A B n (z : RelativeChain (restr A B) n),
          relChainIncl_mem_relCycles A B n z z.2⟩ := rfl

/-! ## §4. The excision isomorphism -/

/-- Pulling `A ∩ B` back to `sub B` is the same as pulling `A` back: `Subtype.val` always lands
in `B`, so the `B`-condition is automatic. -/
theorem restr_inter (A B : Set X) : (Subtype.val ⁻¹' (A ∩ B) : Set (sub B)) = restr A B := by
  ext p
  simp only [restr, Set.mem_preimage, Set.mem_inter_iff, and_iff_left p.2]

/-- Reflection through `A ∩ B`: `chainIncl B d` lands in `C(A ∩ B)` iff `d` lands in `C(restr A B)`
(the `B`-part is automatic). The `←` direction is well-definedness; the `→` direction is the genuine
reflection used to pull excision witnesses back to `sub B`. -/
theorem chainIncl_mem_inter_iff (A B : Set X) {n : ℕ} (d : SingularChain (sub B) n) :
    chainIncl B n d ∈ subspaceChains (A ∩ B) n ↔ d ∈ subspaceChains (restr A B) n := by
  rw [chainIncl_mem_subspaceChains_iff (A ∩ B) B d, restr_inter]

/-- **Excision is injective** (positive degree): the inclusion `(B, A ∩ B) ↪ (X, A)` induces an
injection on `H_{n+1}`. Uses the injective half of the relative small-chains theorem
(`relative_small_boundary`) plus the two-cover decomposition and the reflection lemma. -/
theorem excisionMap_injective (A B : Set X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) :
    Function.Injective (excisionMap A B (n + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨c', hc'⟩ := Submodule.Quotient.mk_surjective _ (z' : RelativeChain (restr A B) (n + 1))
  replace hc' : RelativeChain.mk (restr A B) (n + 1) c' = (z' : RelativeChain (restr A B) (n + 1)) :=
    hc'
  have hz'cyc : relBoundary (restr A B) n (z' : RelativeChain (restr A B) (n + 1)) = 0 :=
    LinearMap.mem_ker.mp z'.2
  have hc'_cyc : chainBoundary (sub B) n c' ∈ subspaceChains (restr A B) n := by
    rw [← RelativeChain.mk_eq_zero_iff, ← relBoundary_mk, hc', hz'cyc]
  rw [show (Submodule.Quotient.mk z' : RelativeHomology (restr A B) (n + 1))
        = RelativeHomology.mk (restr A B) (n + 1) z' from rfl, excisionMap_mk,
      RelativeHomology.mk_eq_zero_iff] at hh
  have hval : relChainIncl A B (n + 1) (z' : RelativeChain (restr A B) (n + 1))
      = RelativeChain.mk A (n + 1) (chainIncl B (n + 1) c') := by rw [← hc', relChainIncl_mk]
  have hh2 : RelativeChain.mk A (n + 1) (chainIncl B (n + 1) c') ∈ relBoundaries A (n + 1) := by
    rw [← hval]; exact hh
  obtain ⟨wbar, hwbar⟩ := hh2
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wbar
  replace hwbar : RelativeChain.mk A (n + 1) (chainBoundary X (n + 1) w)
      = RelativeChain.mk A (n + 1) (chainIncl B (n + 1) c') := hwbar
  have hw_bound : chainIncl B (n + 1) c' + chainBoundary X (n + 1) w ∈ subspaceChains A (n + 1) := by
    have hsub := (Submodule.Quotient.eq _).1 hwbar
    rw [show chainBoundary X (n + 1) w - chainIncl B (n + 1) c'
        = chainIncl B (n + 1) c' + chainBoundary X (n + 1) w by
          rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]; abel] at hsub
    exact hsub
  have hz_small : chainIncl B (n + 1) c' ∈ smallChains ({A, B} : Set (Set X)) (n + 1) :=
    subspaceChains_le_smallChains (by simp) (n + 1) ⟨c', rfl⟩
  have hz_rcyc : chainBoundary X n (chainIncl B (n + 1) c') ∈ subspaceChains A n := by
    rw [← chainIncl_chainBoundary]
    exact (chainIncl_mem_subspaceChains_iff A B (chainBoundary (sub B) n c')).2 hc'_cyc
  obtain ⟨w', hw'_small, hw'_bound⟩ := relative_small_boundary hcov hz_small hz_rcyc hw_bound
  rw [smallChains_two_eq] at hw'_small
  obtain ⟨wA, hwA, wB, hwB, hwAB⟩ := Submodule.mem_sup.mp hw'_small
  -- `chainIncl B c' + ∂wB` lies in both `C(A)` and `C(B)`, hence in `C(A ∩ B)`.
  have hmemA : chainIncl B (n + 1) c' + chainBoundary X (n + 1) wB ∈ subspaceChains A (n + 1) := by
    have h2 : chainIncl B (n + 1) c'
        + (chainBoundary X (n + 1) wA + chainBoundary X (n + 1) wB) ∈ subspaceChains A (n + 1) := by
      rw [← map_add, hwAB]; exact hw'_bound
    have h1 : chainBoundary X (n + 1) wA ∈ subspaceChains A (n + 1) :=
      chainBoundary_mem_subspaceChains A (n + 1) wA hwA
    rw [show chainIncl B (n + 1) c' + chainBoundary X (n + 1) wB
        = (chainIncl B (n + 1) c'
            + (chainBoundary X (n + 1) wA + chainBoundary X (n + 1) wB))
          - chainBoundary X (n + 1) wA by abel]
    exact Submodule.sub_mem _ h2 h1
  have hmemB : chainIncl B (n + 1) c' + chainBoundary X (n + 1) wB ∈ subspaceChains B (n + 1) :=
    Submodule.add_mem _ ⟨c', rfl⟩ (chainBoundary_mem_subspaceChains B (n + 1) wB hwB)
  have hkey : chainIncl B (n + 1) c' + chainBoundary X (n + 1) wB ∈ subspaceChains (A ∩ B) (n + 1) := by
    rw [← subspaceChains_inf]; exact Submodule.mem_inf.2 ⟨hmemA, hmemB⟩
  -- pull `wB` back to `sub B` and reflect through `A ∩ B`
  obtain ⟨v, rfl⟩ := hwB
  rw [← chainIncl_chainBoundary, ← map_add, chainIncl_mem_inter_iff] at hkey
  -- `hkey : c' + ∂v ∈ C(restr A B)`, so `[c'] = [∂v]` is a relative boundary
  refine (RelativeHomology.mk_eq_zero_iff (restr A B) (n + 1) z').2 ?_
  refine ⟨RelativeChain.mk (restr A B) (n + 2) v, ?_⟩
  rw [relBoundary_mk, ← hc']
  show Submodule.Quotient.mk (chainBoundary (sub B) (n + 1) v) = Submodule.Quotient.mk c'
  rw [Submodule.Quotient.eq,
    show chainBoundary (sub B) (n + 1) v - c' = c' + chainBoundary (sub B) (n + 1) v by
      rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]; abel]
  exact hkey

/-- **Excision is surjective** (positive degree). Uses the surjective half of the relative
small-chains theorem (`relative_add_singularSd_iterate_mem_relBoundaries`): subdivide a relative
cycle until it is `{A, B}`-small, drop its `C(A)` part, and pull the remaining `C(B)` part back to
`sub B`. -/
theorem excisionMap_surjective (A B : Set X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) :
    Function.Surjective (excisionMap A B (n + 1)) := by
  intro h
  obtain ⟨zc, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (zc : RelativeChain A (n + 1))
  replace hz : RelativeChain.mk A (n + 1) z = (zc : RelativeChain A (n + 1)) := hz
  have hz_relcyc : RelativeChain.mk A (n + 1) z ∈ relCycles A (n + 1) := by rw [hz]; exact zc.2
  have hz_cyc : chainBoundary X n z ∈ subspaceChains A n := by
    rw [← RelativeChain.mk_eq_zero_iff, ← relBoundary_mk, hz]
    exact LinearMap.mem_ker.mp zc.2
  obtain ⟨m, hsmall⟩ := exists_iterate_smallChains hcov z
  rw [smallChains_two_eq] at hsmall
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsmall
  have hSd_eq : RelativeChain.mk A (n + 1) ((⇑(singularSd X (n + 1)))^[m] z)
      = RelativeChain.mk A (n + 1) b := by
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, show (⇑(singularSd X (n + 1)))^[m] z - b = a by rw [← hab]; abel]
    exact ha
  have hrel : RelativeChain.mk A (n + 1) z + RelativeChain.mk A (n + 1) b
      ∈ relBoundaries A (n + 1) := by
    rw [← hSd_eq]; exact relative_add_singularSd_iterate_mem_relBoundaries hz_cyc m
  have hb_cyc : RelativeChain.mk A (n + 1) b ∈ relCycles A (n + 1) := by
    have hsum : RelativeChain.mk A (n + 1) z + RelativeChain.mk A (n + 1) b ∈ relCycles A (n + 1) :=
      relBoundaries_le_relCycles A (n + 1) hrel
    rw [show RelativeChain.mk A (n + 1) b = RelativeChain.mk A (n + 1) z
          + (RelativeChain.mk A (n + 1) z + RelativeChain.mk A (n + 1) b) by
        rw [← add_assoc, ZModModule.add_self, zero_add]]
    exact Submodule.add_mem _ hz_relcyc hsum
  obtain ⟨b', rfl⟩ := hb
  have hb'_cyc : chainBoundary (sub B) n b' ∈ subspaceChains (restr A B) n := by
    rw [← chainIncl_mem_inter_iff, chainIncl_chainBoundary, ← subspaceChains_inf]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have hker : relBoundary A n (RelativeChain.mk A (n + 1) (chainIncl B (n + 1) b')) = 0 :=
        LinearMap.mem_ker.mp hb_cyc
      rwa [relBoundary_mk, RelativeChain.mk_eq_zero_iff] at hker
    · exact chainBoundary_mem_subspaceChains B n (chainIncl B (n + 1) b') ⟨b', rfl⟩
  refine ⟨RelativeHomology.mk (restr A B) (n + 1)
    ⟨RelativeChain.mk (restr A B) (n + 1) b', LinearMap.mem_ker.2 ?_⟩, ?_⟩
  · rw [relBoundary_mk, RelativeChain.mk_eq_zero_iff]; exact hb'_cyc
  · rw [excisionMap_mk]
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk zc
    rw [Submodule.Quotient.eq]
    refine Submodule.mem_comap.2 ?_
    show RelativeChain.mk A (n + 1) (chainIncl B (n + 1) b') - (zc : RelativeChain A (n + 1))
        ∈ relBoundaries A (n + 1)
    rw [← hz, show RelativeChain.mk A (n + 1) (chainIncl B (n + 1) b') - RelativeChain.mk A (n + 1) z
        = RelativeChain.mk A (n + 1) z + RelativeChain.mk A (n + 1) (chainIncl B (n + 1) b') by
      rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]; abel]
    exact hrel

/-- **The excision isomorphism** `H_{n+1}(B, A ∩ B; ℤ/2) ≅ H_{n+1}(X, A; ℤ/2)` when the interiors
of `A` and `B` cover `X`. The inclusion of pairs `(B, A ∩ B) ↪ (X, A)` induces an isomorphism on
relative ℤ/2 homology in every positive degree — singular excision, built from the relative
small-chains theorem. -/
noncomputable def excisionEquiv (A B : Set X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) :
    RelativeHomology (restr A B) (n + 1) ≃ₗ[ZMod 2] RelativeHomology A (n + 1) :=
  LinearEquiv.ofBijective (excisionMap A B (n + 1))
    ⟨excisionMap_injective A B n hcov, excisionMap_surjective A B n hcov⟩

end SKEFTHawking.SingularExcisionIso
