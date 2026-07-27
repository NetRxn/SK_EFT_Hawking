import Mathlib
import SKEFTHawking.SingularExcisionIso
import SKEFTHawking.SingularRelativeCoverMV

/-!
# Phase 5q.H — THE RELATIVE COVER-MAYER–VIETORIS SUM-EXACTNESS (open two-piece cover)

The **relative cover Mayer–Vietoris** sequence for a pair `(X, S)` and an *excisive* two-piece
cover `X = A ∪ B` (`int A ∪ int B = X`):

```
  Hₙ(A, S∩A) ⊕ Hₙ(B, S∩B) --sum--> Hₙ(X, S) --δ--> Hₙ₋₁(A∩B, S∩A∩B)
```

This is Mayer–Vietoris in the **first** variable (the ambient space is covered), relative to a
fixed subspace `S`. It is *not* the deleted-variable triad of `SingularRelativeMV` (which varies
the second variable, `Hₙ(X,U∩V) → Hₙ(X,U)⊕Hₙ(X,V) → Hₙ(X,U∪V)`), and it is *not* the absolute
cover-MV of `SingularMayerVietorisLES`. Both of those are in-tree; this one was the gap.

**What is proved here (chain-level, then homology-level).**

* §1 — the **support lattice**. `subordinate_of_mem_smallChains` is the converse of
  `mem_smallChains_of_support` (missing in-tree): the support of a `𝒰`-small chain consists of
  `𝒰`-subordinate simplices. It upgrades to the **splitting** `exists_split_of_mem_smallChains`:
  a chain supported in `P` and `{U,V}`-small splits as `u + v` with `u` supported in `P ∩ U` and
  `v` in `P ∩ V`. This is the mod-2 "coordinate subspace" fact
  `C(P) ⊓ (C(U)+C(V)) = C(P∩U) + C(P∩V)`, and it is the algebraic engine of everything below.
* §2 — the subdivision homotopy `Dₘ` **preserves supports** (`iterHomotopy_mem_subspaceChains`),
  so it descends to every subspace complex simultaneously.
* §3 — `exists_cover_split`: every chain `z` with `∂z ∈ C(S)` satisfies `z = a + b + ∂w + s`
  with `a ∈ C(A)`, `b ∈ C(B)`, `s ∈ C(S)`. (Subdivide into the cover, then correct by the
  subdivision homotopy — whose `S`-part is absorbed into `s` precisely because `∂z` is `S`-small.)
* §4 — `exists_delta_datum`: the **connecting datum**. The split's `A`-piece has
  `∂a ∈ C(A) ⊓ (C(S) + C(B)) = C(A∩S) + C(A∩B)`, so `∂a = s' + t` with `t ∈ C(A∩B)` and
  `∂t ∈ C(S∩(A∩B))` — i.e. `t` is a relative cycle of `(A∩B, S∩A∩B)`. This `t` is the chain-level
  value of the MV connecting map `δ[z]`.
* §5 — `exists_piece_relCycles_of_delta_bounds`: **the keystone**, `ker δ ⊆ im(sum)` in chain form.
  If the datum `t` bounds relatively in `(A∩B, S∩A∩B)`, say `t = ∂u + r`, then the *same* `u`
  corrects **both** pieces at once: `a' := a + u` and `b' := b + u` are genuine relative cycles of
  `(A, S∩A)` and `(B, S∩B)`, and `a' + b' = a + b` **because the correction cancels mod 2**. That
  mod-2 cancellation of the shared collar chain is the whole content of the gluing.
* §6 — the homology-level form. `relClassOf_eq_excisionMap_add` reads §5 through `excisionMap`
  (`SingularExcisionIso`) and `relClassOf` (`SingularRelativeCoverMV`): the class of `z` in
  `Hₙ(X,S)` is literally `excisionMap S A α + excisionMap S B β` for per-piece classes
  `α ∈ Hₙ(A, S∩A)`, `β ∈ Hₙ(B, S∩B)` — the sum map of the display above. Assembled with §3–§5,
  `exists_excisionMap_add_of_overlap_relAcyclic` states the standard MV consequence: when the
  overlap pair is relatively acyclic in the connecting degree, the sum map is **surjective**.

**Non-vacuity (zero-geometric-input attack).** Every new statement here is quantified over an
*arbitrary* chain `z` and returns chains satisfying *equations*, not memberships in a trivially
inhabited predicate. §5's conclusion produces `a'`, `b'` whose boundaries lie in `C(S)` **and**
whose sum reconstructs `z` up to `∂w + s`; taking `A = B = X`, `S = univ` does not make it
content-free (the equation `z = a' + b' + ∂w + s` still constrains `z`), and taking `z = 0` yields
the true-but-uninteresting instance rather than an unconstrained one. §1's splitting is refuted by
any chain that is `{U,V}`-small but not supported in `P` — the hypothesis `hcP` is load-bearing and
is used in both output memberships. No statement here is dischargeable by `rfl`/`decide`.

**Fences respected.** No binary complementary partition of `X` is used or produced
(`capstone-binary-partition-detection-uninhabitable`): `A` and `B` genuinely *overlap*, the seam is
interior to both, and the correction chain `u` lives in the overlap `A ∩ B` and is applied to
**both** sides (never a one-sided congruence — `collar-pair-hdetAB-one-sided-congruence-routes-dead`).
Nothing here consumes or produces a `seamCore`, a `CapstoneSeamTransfer`, or a shared-`cCore`
co-adaptation.

**Refutation witness for the headline** (`exists_excisionMap_add_of_overlap_relAcyclic`). Drop the
cover hypothesis `hcov` and the statement becomes *false*, so it is not provable from its other
hypotheses: take `A = B = ∅` and `S = ∅` on `X = S^{m+2}`. Then `A ∩ B = ∅` and
`subspaceChains ∅ = ⊥`, so `hacyc` holds vacuously (`t = 0 = ∂0 + 0`), while the conclusion would
force every class of `Hₘ₊₂(X, ∅) = Hₘ₊₂(X) ≠ 0` to be a sum of images of `Hₘ₊₂(∅, ∅) = 0`. So
`hcov` is load-bearing and the theorem carries genuine geometric content.

**Scope honesty.** What is *not* proved here: that `δ` is a well-defined linear map independent of
the subdivision depth and of the splitting choices, and hence the reverse inclusion
`im(sum) ⊆ ker δ` and the remaining two exactness statements of the long exact sequence. §4 gives
existence of the datum; uniqueness-up-to-relative-boundary is the next layer.

A consequence of that gap worth stating explicitly, so no downstream reader over-reads §5: because
§4's datum is *existential*, "the datum of `z` bounds" is not yet a well-defined property of `z`
(for a `z` that already decomposes, the datum `t = 0` bounds trivially). §5 must therefore be read
as *"if the supplied datum bounds, then `z` decomposes"* — an implication about a given datum, not
about `z`. `exists_excisionMap_add_of_overlap_relAcyclic` is unaffected and airtight: its `hacyc`
hypothesis is universally quantified over `t`, so it applies to whichever datum §4 hands back.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcision
open SKEFTHawking.SingularSubdivision
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularRelativeCoverMV

namespace SKEFTHawking.SingularRelativeCoverMVSumExact

variable {X : TopCat}

/-! Characteristic-two chain rearrangements below are closed by
`abel_nf; simp [two_zsmul, ZModModule.add_self]`: `abel_nf` normalises to a `ℤ`-linear combination
whose only obstruction is a `2 • x` term, which `two_zsmul` splits into `x + x` and
`ZModModule.add_self` kills. That `x + x = 0` cancellation *is* the content of the MV gluing. -/

/-! ## §1. The support lattice: `C(P) ⊓ (C(U) + C(V)) = C(P∩U) + C(P∩V)` -/

/-- **Every support simplex of a small chain is subordinate** — the converse of
`SingularExcision.mem_smallChains_of_support`. `smallChains 𝒰` is the span of a set of *basis*
singletons, so it is contained in `Finsupp.supported` over the subordinate index set, and
membership there is exactly a support constraint. -/
theorem subordinate_of_mem_smallChains {n : ℕ} {𝒰 : Set (Set ↑X)} {c : SingularChain X n}
    (hc : c ∈ smallChains 𝒰 n)
    {τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))} (hτ : τ ∈ c.support) :
    IsSubordinate 𝒰 τ := by
  classical
  have hle : smallChains 𝒰 n ≤ Finsupp.supported (ZMod 2) (ZMod 2) {σ | IsSubordinate 𝒰 σ} := by
    rw [smallChains, Submodule.span_le]
    rintro _ ⟨σ, hσ, rfl⟩
    intro a ha
    have ha' : a = σ := Finset.mem_singleton.mp (Finsupp.support_single_subset ha)
    exact ha' ▸ hσ
  exact (Finsupp.mem_supported _ _).mp (hle hc) hτ

/-- **The support-lattice splitting.** A chain supported in `P` that is `{U, V}`-small splits as
`u + v` with `u` supported in `P ∩ U` and `v` supported in `P ∩ V`.

Both hypotheses are load-bearing: `hcP` supplies the `P`-half of each output membership, and `hc`
supplies the `U`-or-`V` dichotomy. The split is by `Finsupp.filter` on "does this simplex land in
`U`", so it is canonical once `U` is fixed. -/
theorem exists_split_of_mem_smallChains {n : ℕ} {P U V : Set ↑X} {c : SingularChain X n}
    (hcP : c ∈ subspaceChains P n) (hc : c ∈ smallChains ({U, V} : Set (Set ↑X)) n) :
    ∃ u v : SingularChain X n, c = u + v ∧ u ∈ subspaceChains (P ∩ U) n ∧
      v ∈ subspaceChains (P ∩ V) n := by
  classical
  set p : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) → Prop :=
    fun τ => Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ U with hp
  refine ⟨c.filter p, c.filter (fun τ => ¬ p τ), (Finsupp.filter_pos_add_filter_neg c p).symm,
    ?_, ?_⟩
  · refine mem_subspaceChains_of_support (fun τ hτ => ?_)
    rw [Finsupp.support_filter, Finset.mem_filter] at hτ
    exact Set.subset_inter (range_of_mem_subspaceChains hcP hτ.1) hτ.2
  · refine mem_subspaceChains_of_support (fun τ hτ => ?_)
    rw [Finsupp.support_filter, Finset.mem_filter] at hτ
    refine Set.subset_inter (range_of_mem_subspaceChains hcP hτ.1) ?_
    obtain ⟨W, hW, hsub⟩ := subordinate_of_mem_smallChains hc hτ.1
    rcases hW with rfl | rfl
    · exact absurd hsub hτ.2
    · exact hsub

/-- Every chain is supported in `univ`. -/
theorem mem_subspaceChains_univ {n : ℕ} (c : SingularChain X n) :
    c ∈ subspaceChains (Set.univ : Set ↑X) n :=
  mem_subspaceChains_of_support (fun _ _ => Set.subset_univ _)

/-- **The plain two-piece splitting** `C(U) + C(V) ∋ c ⟹ c = u + v` with `u ∈ C(U)`, `v ∈ C(V)`
(the `P = univ` case of `exists_split_of_mem_smallChains`). -/
theorem exists_split_of_mem_smallChains_pair {n : ℕ} {U V : Set ↑X} {c : SingularChain X n}
    (hc : c ∈ smallChains ({U, V} : Set (Set ↑X)) n) :
    ∃ u v : SingularChain X n, c = u + v ∧ u ∈ subspaceChains U n ∧ v ∈ subspaceChains V n := by
  obtain ⟨u, v, hsum, hu, hv⟩ :=
    exists_split_of_mem_smallChains (P := Set.univ) (mem_subspaceChains_univ c) hc
  exact ⟨u, v, hsum, by rwa [Set.univ_inter] at hu, by rwa [Set.univ_inter] at hv⟩

/-! ## §2. The subdivision homotopy preserves supports -/

/-- Iterating `Sd` keeps a subspace chain in the same subspace complex. -/
theorem singularSd_iterate_mem_subspaceChains {n : ℕ} {S : Set ↑X} {c : SingularChain X n}
    (hc : c ∈ subspaceChains S n) (m : ℕ) :
    (⇑(singularSd X n))^[m] c ∈ subspaceChains S n := by
  induction m with
  | zero => rwa [Function.iterate_zero_apply]
  | succ k ih => rw [Function.iterate_succ_apply']; exact singularSd_mem_subspaceChains ih

/-- **The iterated subdivision homotopy `Dₘ` preserves supports.** `Dₘ = ∑_{i<m} Sdⁱ ∘ D`, and both
`D` (`singularD_mem_subspaceChains`) and `Sd` (`singularSd_mem_subspaceChains`) do. This is what
lets the correction term of `exists_cover_split` be absorbed into the `S`-part. -/
theorem iterHomotopy_mem_subspaceChains {n : ℕ} {S : Set ↑X} {c : SingularChain X n}
    (hc : c ∈ subspaceChains S n) (m : ℕ) :
    iterHomotopy X n m c ∈ subspaceChains S (n + 1) := by
  rw [iterHomotopy]
  exact Submodule.sum_mem _
    (fun i _ => singularSd_iterate_mem_subspaceChains (singularD_mem_subspaceChains hc) i)

/-! ## §3. The relative cover splitting -/

/-- **The relative cover splitting theorem.** For an excisive two-piece cover `int A ∪ int B = X`
and any chain `z` whose boundary is `S`-small, `z = a + b + ∂w + s` with `a` supported in `A`, `b`
in `B` and `s` in `S`.

Subdivide `z` deep enough to be `{A,B}`-small (`exists_iterate_smallChains`), split it by §1, and
pay for the subdivision with the homotopy `Dₘ`: `z + Sdᵐ z = ∂(Dₘ z) + Dₘ(∂z)`, whose second term
is `S`-small exactly because `∂z` is (§2). -/
theorem exists_cover_split {n : ℕ} {A B S : Set ↑X}
    (hcov : (⋃ W ∈ ({A, B} : Set (Set ↑X)), interior W) = Set.univ)
    (z : SingularChain X (n + 1)) (hz : chainBoundary X n z ∈ subspaceChains S n) :
    ∃ (a b : SingularChain X (n + 1)) (w : SingularChain X (n + 2)) (s : SingularChain X (n + 1)),
      a ∈ subspaceChains A (n + 1) ∧ b ∈ subspaceChains B (n + 1) ∧
        s ∈ subspaceChains S (n + 1) ∧
        z = a + b + chainBoundary X (n + 1) w + s := by
  obtain ⟨m, hm⟩ := exists_iterate_smallChains hcov z
  obtain ⟨a, b, hab, ha, hb⟩ := exists_split_of_mem_smallChains_pair hm
  refine ⟨a, b, iterHomotopy X (n + 1) m z, iterHomotopy X n m (chainBoundary X n z), ha, hb,
    iterHomotopy_mem_subspaceChains hz m, ?_⟩
  have key := iterHomotopy_chainHomotopy X m n z
  rw [hab] at key
  rw [add_assoc, key, add_comm z (a + b), ← add_assoc, ZModModule.add_self, zero_add]

/-! ## §4. The connecting datum -/

/-- **The Mayer–Vietoris connecting datum.** For an excisive cover and a relative cycle `z` of
`(X,S)`, there is a splitting `z = a + b + ∂w + s` together with a chain `t` supported in the
overlap `A ∩ B` such that

* `∂t` is `S∩(A∩B)`-small — so `t` is a genuine **relative cycle of the pair `(A∩B, S∩A∩B)`**; and
* `∂a + t` is `S`-small — so `t` *is* the failure of the `A`-piece to be a relative cycle.

`t` is the chain-level value of the MV connecting map `δ[z] ∈ Hₙ(A∩B, S∩A∩B)`. Its existence uses
the support lattice twice: once to see `∂a ∈ C(A) ⊓ (C(S)+C(B))`, and once to split that as
`C(A∩S) + C(A∩B)`. -/
theorem exists_delta_datum {n : ℕ} {A B S : Set ↑X}
    (hcov : (⋃ W ∈ ({A, B} : Set (Set ↑X)), interior W) = Set.univ)
    (z : SingularChain X (n + 2)) (hz : chainBoundary X (n + 1) z ∈ subspaceChains S (n + 1)) :
    ∃ (a b : SingularChain X (n + 2)) (w : SingularChain X (n + 3)) (s : SingularChain X (n + 2))
      (t : SingularChain X (n + 1)),
      a ∈ subspaceChains A (n + 2) ∧ b ∈ subspaceChains B (n + 2) ∧
        s ∈ subspaceChains S (n + 2) ∧
        z = a + b + chainBoundary X (n + 2) w + s ∧
        t ∈ subspaceChains (A ∩ B) (n + 1) ∧
        chainBoundary X n t ∈ subspaceChains (S ∩ (A ∩ B)) n ∧
        chainBoundary X (n + 1) a + t ∈ subspaceChains S (n + 1) := by
  obtain ⟨a, b, w, s, ha, hb, hs, hsplit⟩ := exists_cover_split hcov z hz
  have hddw : chainBoundary X (n + 1) (chainBoundary X (n + 2) w) = 0 :=
    LinearMap.congr_fun (chainBoundary_comp_chainBoundary X (n + 1)) w
  have hdaA : chainBoundary X (n + 1) a ∈ subspaceChains A (n + 1) :=
    chainBoundary_mem_subspaceChains A (n + 1) a ha
  -- `∂a = ∂z + ∂b + ∂s`, so `∂a` is `{S, B}`-small.
  have hda : chainBoundary X (n + 1) a
      = chainBoundary X (n + 1) z + chainBoundary X (n + 1) b + chainBoundary X (n + 1) s := by
    rw [hsplit]
    simp only [map_add, hddw]
    abel_nf
    simp [two_zsmul, ZModModule.add_self]
  have hSmem : S ∈ ({S, B} : Set (Set ↑X)) := Set.mem_insert _ _
  have hBmem : B ∈ ({S, B} : Set (Set ↑X)) := Set.mem_insert_of_mem _ rfl
  have h1 : chainBoundary X (n + 1) z ∈ smallChains ({S, B} : Set (Set ↑X)) (n + 1) :=
    subspaceChains_le_smallChains hSmem (n + 1) hz
  have h2 : chainBoundary X (n + 1) b ∈ smallChains ({S, B} : Set (Set ↑X)) (n + 1) :=
    subspaceChains_le_smallChains hBmem (n + 1)
      (chainBoundary_mem_subspaceChains B (n + 1) b hb)
  have h3 : chainBoundary X (n + 1) s ∈ smallChains ({S, B} : Set (Set ↑X)) (n + 1) :=
    subspaceChains_le_smallChains hSmem (n + 1)
      (chainBoundary_mem_subspaceChains S (n + 1) s hs)
  have hsmall : chainBoundary X (n + 1) a ∈ smallChains ({S, B} : Set (Set ↑X)) (n + 1) := by
    rw [hda]
    exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) h3
  -- The support lattice splits `∂a ∈ C(A) ⊓ (C(S) + C(B))` as `C(A∩S) + C(A∩B)`.
  obtain ⟨s', t, hst, hs', ht⟩ := exists_split_of_mem_smallChains (P := A) hdaA hsmall
  have hdda : chainBoundary X n (chainBoundary X (n + 1) a) = 0 :=
    LinearMap.congr_fun (chainBoundary_comp_chainBoundary X n) a
  have hteq : t = chainBoundary X (n + 1) a + s' := by
    rw [hst]; abel_nf; simp [two_zsmul, ZModModule.add_self]
  have hset : (A ∩ S) ∩ (A ∩ B) = S ∩ (A ∩ B) := by
    ext x; simp only [Set.mem_inter_iff]; tauto
  refine ⟨a, b, w, s, t, ha, hb, hs, hsplit, ht, ?_, ?_⟩
  · have h1 : chainBoundary X n t ∈ subspaceChains (A ∩ S) n := by
      rw [hteq, map_add, hdda, zero_add]
      exact chainBoundary_mem_subspaceChains (A ∩ S) n s' hs'
    have h2 : chainBoundary X n t ∈ subspaceChains (A ∩ B) n :=
      chainBoundary_mem_subspaceChains (A ∩ B) n t ht
    have hinf := Submodule.mem_inf.mpr ⟨h1, h2⟩
    rw [SingularExcision.subspaceChains_inf, hset] at hinf
    exact hinf
  · have hcancel : chainBoundary X (n + 1) a + t = s' := by
      rw [hst]; abel_nf; simp [two_zsmul, ZModModule.add_self]
    rw [hcancel]
    exact subspaceChains_mono Set.inter_subset_right (n + 1) hs'

/-! ## §5. Sum-exactness: a class with bounding datum is a sum of piece classes -/

/-- **THE RELATIVE COVER-MV SUM-EXACTNESS (chain form)** — the substantive inclusion
`ker δ ⊆ im(sum)`.

Hypotheses: `z = a + b + ∂w + s` is a cover splitting of a relative `(X,S)`-cycle, `t` is its
connecting datum (§4), and `t` **bounds relatively** in the overlap pair: `t = ∂u + r` with `u`
supported in `A ∩ B` and `r` in `S∩(A∩B)`.

Conclusion: `z = a' + b' + ∂w + s` where `a'` and `b'` are *genuine relative cycles* of `(A, S∩A)`
and `(B, S∩B)`.

The proof is the mod-2 heart of Mayer–Vietoris: the **single** overlap chain `u` is added to
**both** pieces. It repairs `∂a' = (∂a + t) + r ∈ C(S)` on the `A`-side and
`∂b' = ∂z + ∂s + r + (∂a + t) ∈ C(S)` on the `B`-side, while `a' + b' = a + b` because `u + u = 0`.
No one-sided congruence is used, and `u` is a genuinely *third* chain (supported in the overlap),
not a re-reading of either piece. -/
theorem exists_piece_relCycles_of_delta_bounds {n : ℕ} {A B S : Set ↑X}
    {z a b s : SingularChain X (n + 2)} {w : SingularChain X (n + 3)}
    {t r : SingularChain X (n + 1)} {u : SingularChain X (n + 2)}
    (ha : a ∈ subspaceChains A (n + 2)) (hb : b ∈ subspaceChains B (n + 2))
    (hs : s ∈ subspaceChains S (n + 2))
    (hsplit : z = a + b + chainBoundary X (n + 2) w + s)
    (hz : chainBoundary X (n + 1) z ∈ subspaceChains S (n + 1))
    (hat : chainBoundary X (n + 1) a + t ∈ subspaceChains S (n + 1))
    (hu : u ∈ subspaceChains (A ∩ B) (n + 2))
    (hr : r ∈ subspaceChains (S ∩ (A ∩ B)) (n + 1))
    (htu : t = chainBoundary X (n + 1) u + r) :
    ∃ a' b' : SingularChain X (n + 2),
      a' ∈ subspaceChains A (n + 2) ∧ b' ∈ subspaceChains B (n + 2) ∧
        chainBoundary X (n + 1) a' ∈ subspaceChains S (n + 1) ∧
        chainBoundary X (n + 1) b' ∈ subspaceChains S (n + 1) ∧
        z = a' + b' + chainBoundary X (n + 2) w + s := by
  have hddw : chainBoundary X (n + 1) (chainBoundary X (n + 2) w) = 0 :=
    LinearMap.congr_fun (chainBoundary_comp_chainBoundary X (n + 1)) w
  have hdu : chainBoundary X (n + 1) u = t + r := by
    rw [htu, add_assoc (chainBoundary X (n + 1) u) r r, ZModModule.add_self, add_zero]
  have hdz : chainBoundary X (n + 1) z
      = chainBoundary X (n + 1) a + chainBoundary X (n + 1) b + chainBoundary X (n + 1) s := by
    rw [hsplit, map_add, map_add, map_add, hddw, add_zero]
  have hrS : r ∈ subspaceChains S (n + 1) :=
    subspaceChains_mono Set.inter_subset_left (n + 1) hr
  refine ⟨a + u, b + u,
    Submodule.add_mem _ ha (subspaceChains_mono Set.inter_subset_left (n + 2) hu),
    Submodule.add_mem _ hb (subspaceChains_mono Set.inter_subset_right (n + 2) hu), ?_, ?_, ?_⟩
  · have hA : chainBoundary X (n + 1) (a + u) = chainBoundary X (n + 1) a + t + r := by
      rw [map_add, hdu, ← add_assoc]
    rw [hA]
    exact Submodule.add_mem _ hat hrS
  · have hB : chainBoundary X (n + 1) (b + u)
        = chainBoundary X (n + 1) z + chainBoundary X (n + 1) s
          + (chainBoundary X (n + 1) a + t + r) := by
      rw [map_add, hdu, hdz]
      abel_nf
      simp [two_zsmul, ZModModule.add_self]
    rw [hB]
    exact Submodule.add_mem _
      (Submodule.add_mem _ hz (chainBoundary_mem_subspaceChains S (n + 1) s hs))
      (Submodule.add_mem _ hat hrS)
  · rw [hsplit]
    abel_nf
    simp [two_zsmul, ZModModule.add_self]

/-! ## §6. The homology-level sum map `Hₙ(A, S∩A) ⊕ Hₙ(B, S∩B) → Hₙ(X, S)` -/

/-- Adding an absolute boundary leaves the relative class of an almost-cycle unchanged: the two
relative cycles differ by `∂` of the relative chain of `w`. -/
theorem relClassOf_add_boundary {T : Set ↑X} (m : ℕ) (c : SingularChain X (m + 2))
    (w : SingularChain X (m + 3))
    (hc : chainBoundary X (m + 1) c ∈ subspaceChains T (m + 1))
    (hcw : chainBoundary X (m + 1) (c + chainBoundary X (m + 2) w) ∈ subspaceChains T (m + 1)) :
    relClassOf T m (c + chainBoundary X (m + 2) w) hcw = relClassOf T m c hc := by
  refine SingularRelativeMV.relHomology_mk_eq_of (m + 2) _ _
    ⟨RelativeChain.mk T (m + 3) w, ?_⟩
  rw [relBoundary_mk]
  show (Submodule.Quotient.mk (chainBoundary X (m + 2) w) : RelativeChain T (m + 2))
      = Submodule.Quotient.mk (c + chainBoundary X (m + 2) w) - Submodule.Quotient.mk c
  rw [Submodule.Quotient.mk_add]
  abel

/-- **A piece-supported almost-cycle is an `excisionMap` image.** If `p` is supported in `P` and has
`S`-small boundary, then its class in `Hₘ₊₂(X, S)` is the excision pushforward of an intrinsic class
of the pair `(P, S∩P)` — realized as `RelativeHomology (restr S P)` in the subspace `sub P`, which is
the representation `excisionMap` consumes. This is the per-piece summand of the cover-MV sum map. -/
theorem exists_excisionMap_eq_relClassOf {P S : Set ↑X} (m : ℕ) (p : SingularChain X (m + 2))
    (hpP : p ∈ subspaceChains P (m + 2))
    (hp : chainBoundary X (m + 1) p ∈ subspaceChains S (m + 1)) :
    ∃ α : RelativeHomology (restr S P) (m + 2),
      excisionMap S P (m + 2) α = relClassOf S m p hp := by
  obtain ⟨p', rfl⟩ := hpP
  have hincl : chainIncl P (m + 1) (chainBoundary (sub P) (m + 1) p')
      = chainBoundary X (m + 1) (chainIncl P (m + 2) p') := chainIncl_chainBoundary P (m + 1) p'
  have hmemP : chainIncl P (m + 1) (chainBoundary (sub P) (m + 1) p')
      ∈ subspaceChains P (m + 1) := ⟨chainBoundary (sub P) (m + 1) p', rfl⟩
  have hmemS : chainIncl P (m + 1) (chainBoundary (sub P) (m + 1) p')
      ∈ subspaceChains S (m + 1) := by rw [hincl]; exact hp
  have hSP : chainIncl P (m + 1) (chainBoundary (sub P) (m + 1) p')
      ∈ subspaceChains (S ∩ P) (m + 1) := by
    have hmem := Submodule.mem_inf.mpr ⟨hmemS, hmemP⟩
    rwa [SingularExcision.subspaceChains_inf] at hmem
  have hbd : chainBoundary (sub P) (m + 1) p' ∈ subspaceChains (restr S P) (m + 1) :=
    (chainIncl_mem_inter_iff S P (chainBoundary (sub P) (m + 1) p')).mp hSP
  exact ⟨relClassOf (restr S P) m p' hbd, (relClassOf_chainIncl S P m p' hbd).symm⟩

/-- **THE RELATIVE COVER-MV SUM MAP, HOMOLOGY FORM.** Once §5 has produced per-piece *relative
cycles* `a'`, `b'` reconstructing `z` up to `∂w + s`, the class of `z` in `Hₘ₊₂(X, S)` is literally

`relClassOf S m z = excisionMap S A α + excisionMap S B β`

for `α ∈ Hₘ₊₂(A, S∩A)` and `β ∈ Hₘ₊₂(B, S∩B)` — i.e. `[z]` lies in the image of the relative
cover-Mayer–Vietoris sum map `Hₙ(A,S∩A) ⊕ Hₙ(B,S∩B) → Hₙ(X,S)`. -/
theorem relClassOf_eq_excisionMap_add {m : ℕ} {A B S : Set ↑X}
    {z a' b' s : SingularChain X (m + 2)} {w : SingularChain X (m + 3)}
    (ha' : a' ∈ subspaceChains A (m + 2)) (hb' : b' ∈ subspaceChains B (m + 2))
    (hs : s ∈ subspaceChains S (m + 2))
    (ha'S : chainBoundary X (m + 1) a' ∈ subspaceChains S (m + 1))
    (hb'S : chainBoundary X (m + 1) b' ∈ subspaceChains S (m + 1))
    (hsplit : z = a' + b' + chainBoundary X (m + 2) w + s)
    (hz : chainBoundary X (m + 1) z ∈ subspaceChains S (m + 1)) :
    ∃ (α : RelativeHomology (restr S A) (m + 2)) (β : RelativeHomology (restr S B) (m + 2)),
      relClassOf S m z hz = excisionMap S A (m + 2) α + excisionMap S B (m + 2) β := by
  obtain ⟨α, hα⟩ := exists_excisionMap_eq_relClassOf m a' ha' ha'S
  obtain ⟨β, hβ⟩ := exists_excisionMap_eq_relClassOf m b' hb' hb'S
  have hddw : chainBoundary X (m + 1) (chainBoundary X (m + 2) w) = 0 :=
    LinearMap.congr_fun (chainBoundary_comp_chainBoundary X (m + 1)) w
  have hp2 : chainBoundary X (m + 1) (a' + b') ∈ subspaceChains S (m + 1) := by
    rw [map_add]; exact Submodule.add_mem _ ha'S hb'S
  have hp1 : chainBoundary X (m + 1) (a' + b' + chainBoundary X (m + 2) w)
      ∈ subspaceChains S (m + 1) := by
    rw [map_add, hddw, add_zero]; exact hp2
  refine ⟨α, β, ?_⟩
  rw [hα, hβ, ← relClassOf_add S m a' b' ha'S hb'S,
    show relClassOf S m (a' + b') (by rw [map_add]; exact Submodule.add_mem _ ha'S hb'S)
        = relClassOf S m (a' + b') hp2 from rfl,
    ← relClassOf_add_boundary m (a' + b') w hp2 hp1,
    ← relClassOf_eq_of_congr (subset_refl S) m hsplit hs hz hp1]

/-- **Surjectivity of the relative cover-MV sum map over a relatively acyclic overlap.**

If the overlap pair `(A∩B, S∩A∩B)` has no relative homology in degree `m+1` — spelled out as: every
`(A∩B)`-supported chain with `S∩(A∩B)`-small boundary is a relative boundary there — then *every*
class of `Hₘ₊₂(X, S)` is a sum of per-piece classes. This is §3 (split) + §4 (connecting datum) +
§5 (the mod-2 collar correction) + §6 (excision bookkeeping), assembled.

The acyclicity hypothesis is exactly the vanishing of the target of the Mayer–Vietoris connecting
map, so this is the standard MV consequence — and it is not vacuous: the hypothesis is a genuine
condition, false for a generic overlap. It fails already at `A = B = X`, `S = ∅`, where (since
`subspaceChains ∅ = ⊥`) it reads "every `(m+1)`-cycle of `X` bounds", i.e. `Hₘ₊₁(X) = 0`. It holds
non-trivially whenever `A ∩ B ⊆ S` (take `u = 0`, `r = t`). -/
theorem exists_excisionMap_add_of_overlap_relAcyclic {m : ℕ} {A B S : Set ↑X}
    (hcov : (⋃ W ∈ ({A, B} : Set (Set ↑X)), interior W) = Set.univ)
    (hacyc : ∀ t : SingularChain X (m + 1), t ∈ subspaceChains (A ∩ B) (m + 1) →
      chainBoundary X m t ∈ subspaceChains (S ∩ (A ∩ B)) m →
      ∃ (u : SingularChain X (m + 2)) (r : SingularChain X (m + 1)),
        u ∈ subspaceChains (A ∩ B) (m + 2) ∧ r ∈ subspaceChains (S ∩ (A ∩ B)) (m + 1) ∧
        t = chainBoundary X (m + 1) u + r)
    (z : SingularChain X (m + 2)) (hz : chainBoundary X (m + 1) z ∈ subspaceChains S (m + 1)) :
    ∃ (α : RelativeHomology (restr S A) (m + 2)) (β : RelativeHomology (restr S B) (m + 2)),
      relClassOf S m z hz = excisionMap S A (m + 2) α + excisionMap S B (m + 2) β := by
  obtain ⟨a, b, w, s, t, ha, hb, hs, hsplit, ht, hdt, hat⟩ := exists_delta_datum hcov z hz
  obtain ⟨u, r, hu, hr, htu⟩ := hacyc t ht hdt
  obtain ⟨a', b', ha', hb', ha'S, hb'S, hsplit'⟩ :=
    exists_piece_relCycles_of_delta_bounds ha hb hs hsplit hz hat hu hr htu
  exact relClassOf_eq_excisionMap_add ha' hb' hs ha'S hb'S hsplit' hz

end SKEFTHawking.SingularRelativeCoverMVSumExact
