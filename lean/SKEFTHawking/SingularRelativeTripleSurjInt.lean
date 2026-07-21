/-
# The triple `(X, B, A)` surjectivity engine over ℤ — the relative-MV substitute

`SingularExcisionIsoInt` ships the integral excision map
`excisionMapInt A B n : Hₙ(B, A ∩ B; ℤ) → Hₙ(X, A; ℤ)` (induced by the inclusion of pairs) and
proves it an **isomorphism** when the interiors of `A` and `B` cover `X`. That hypothesis cannot be
used to split an ambient space along a cover: the pieces of a cover are never `⊆`-comparable to the
subspace one takes homology relative to.

This module supplies the missing half. For a **triple** `A ⊆ B ⊆ X` the *same* map is
**surjective** as soon as the larger relative group vanishes:

> `excisionMapInt_surjective_of_relHomologyInt_eq_zero` :
>   `A ⊆ B` and `Hₙ(X, B; ℤ) = 0`  ⟹  `Hₙ(B, A ∩ B; ℤ) ↠ Hₙ(X, A; ℤ)`

— the exactness-at-`Hₙ(X,A)` fragment of the long exact sequence of the triple, isolated and proved
directly at chain level (no zig-zag lemma, no snake, no connecting map). The argument: a relative
cycle `c` of `(X, A)` is *also* a relative cycle of `(X, B)` because `C(A) ≤ C(B)`
(`mem_relCyclesInt_mono`); vanishing of `Hₙ(X, B)` makes it a relative boundary there, so `c − ∂w` is
carried by `B` (`exists_sub_boundary_mem_subspaceChainsInt`); and the reflection lemma
`chainIncl_mem_subspaceChainsInt_iff` turns "its boundary lies in `C(A)`" into "it is a relative
cycle of `(B, A ∩ B)` read intrinsically" (`mem_relCyclesInt_restr_of_chainIncl`). Its class maps to
`[c]`, since the two representatives differ by `∂w`.

## Why this is the useful engine

Together with the banked excision **isomorphism**, this does everything a Mayer–Vietoris sequence
for pairs with a **split ambient** would do for a two-piece decomposition `X = U ∪ V` — at a
fraction of the cost (no second small-simplices theorem, no six-term diagram). Take `B := A ∪ V`;
then

* `Hₙ(B, A ∩ B) ≅ Hₙ(V, A ∩ V)` by excision (cut away the part of `A` lying off `V`), and
* `Hₙ(X, B) ≅ Hₙ(U, (A ∪ V) ∩ U)` by excision (cut away the part of `V` lying off `U`),

so `Hₙ(X, A)` is a **quotient of the one-chart group** `Hₙ(V, A ∩ V)` whenever the *other* chart's
pair group `Hₙ(U, (A ∪ V) ∩ U)` vanishes. §3 packages exactly that consequence
(`relHomologyInt_cyclic_of_triple`): cyclicity of the relative homology of a pair descends from one
piece of a two-piece decomposition. That is the shape the `b₂` residual
(`KummerPieceCollarCyclicInt.OuterECyclic`) asks for.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularRelativeMVInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt (excisionMapInt excisionMapInt_mk relChainInclInt
  relChainInclInt_mk chainIncl_mem_subspaceChainsInt_iff)
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)

namespace SKEFTHawking.SingularRelativeTripleSurjInt

noncomputable section

variable {X : TopCat}

/-! ## §1. Two degree-uniform cycle lemmas -/

/-- **Relative cycles are monotone in the subspace**: a chain that is a relative cycle of `(X, A)` is
a relative cycle of `(X, B)` whenever `A ⊆ B`, because `C(A) ≤ C(B)`. -/
theorem mem_relCyclesInt_mono {A B : Set X} (hAB : A ⊆ B) (n : ℕ) (c : SingularChainInt X n)
    (hc : RelativeChainInt.mk A n c ∈ relCyclesInt A n) :
    RelativeChainInt.mk B n c ∈ relCyclesInt B n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ k =>
    have hc' : RelativeChainInt.mk A (k + 1) c ∈ LinearMap.ker (relBoundaryInt A k) := hc
    rw [LinearMap.mem_ker, relBoundaryInt_mk, RelativeChainInt.mk_eq_zero_iff] at hc'
    show RelativeChainInt.mk B (k + 1) c ∈ LinearMap.ker (relBoundaryInt B k)
    rw [LinearMap.mem_ker, relBoundaryInt_mk, RelativeChainInt.mk_eq_zero_iff]
    exact subspaceChainsInt_mono hAB k hc'

/-- **Reflection of relative cycles into the subpair.** If the pushforward `chainIncl B d` of a
`B`-chain is a relative cycle of `(X, A)`, then `d` itself is a relative cycle of the pair
`(B, A ∩ B)` read intrinsically in `sub B`. Uses only the chain-level reflection lemma
`chainIncl_mem_subspaceChainsInt_iff`. -/
theorem mem_relCyclesInt_restr_of_chainIncl {A B : Set X} (n : ℕ) (d : SingularChainInt (sub B) n)
    (hd : RelativeChainInt.mk A n (chainIncl B n d) ∈ relCyclesInt A n) :
    RelativeChainInt.mk (restr A B) n d ∈ relCyclesInt (restr A B) n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ k =>
    have hd' : RelativeChainInt.mk A (k + 1) (chainIncl B (k + 1) d)
        ∈ LinearMap.ker (relBoundaryInt A k) := hd
    rw [LinearMap.mem_ker, relBoundaryInt_mk, RelativeChainInt.mk_eq_zero_iff,
      ← chainIncl_chainBoundary] at hd'
    show RelativeChainInt.mk (restr A B) (k + 1) d ∈ LinearMap.ker (relBoundaryInt (restr A B) k)
    rw [LinearMap.mem_ker, relBoundaryInt_mk, RelativeChainInt.mk_eq_zero_iff]
    exact (chainIncl_mem_subspaceChainsInt_iff A B (chainBoundary (sub B) k d)).mp hd'

/-! ## §2. The chain-level splitting and the triple surjectivity theorem -/

/-- **The chain-level engine.** If `Hₙ(X, B; ℤ) = 0` then every chain `c` whose class is a relative
cycle of `(X, B)` becomes a `B`-carried chain after subtracting a boundary:
`c − ∂w = chainIncl B d`. -/
theorem exists_sub_boundary_mem_subspaceChainsInt (B : Set X) (n : ℕ)
    (hzero : ∀ y : RelHomologyInt B n, y = 0) (c : SingularChainInt X n)
    (hc : RelativeChainInt.mk B n c ∈ relCyclesInt B n) :
    ∃ (w : SingularChainInt X (n + 1)) (d : SingularChainInt (sub B) n),
      c - chainBoundary X n w = chainIncl B n d := by
  have hmk : RelHomologyInt.mk B n ⟨RelativeChainInt.mk B n c, hc⟩ = 0 := hzero _
  rw [RelHomologyInt.mk_eq_zero_iff] at hmk
  obtain ⟨wbar, hwbar⟩ := hmk
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wbar
  have hw : RelativeChainInt.mk B n (chainBoundary X n w) = RelativeChainInt.mk B n c := hwbar
  have hsub : RelativeChainInt.mk B n (c - chainBoundary X n w) = 0 := by
    show (Submodule.Quotient.mk (c - chainBoundary X n w) : RelativeChainInt B n) = 0
    rw [Submodule.Quotient.mk_sub]
    show RelativeChainInt.mk B n c - RelativeChainInt.mk B n (chainBoundary X n w) = 0
    rw [hw, sub_self]
  rw [RelativeChainInt.mk_eq_zero_iff] at hsub
  obtain ⟨d, hd⟩ := hsub
  exact ⟨w, d, hd.symm⟩

/-- **The triple surjectivity theorem.** For `A ⊆ B ⊆ X`, if the larger relative group
`Hₙ(X, B; ℤ)` vanishes, then the inclusion-induced map `Hₙ(B, A ∩ B; ℤ) → Hₙ(X, A; ℤ)` is
**surjective**. This is exactness of the triple's long exact sequence at `Hₙ(X, A)`, isolated and
proved directly at chain level. -/
theorem excisionMapInt_surjective_of_relHomologyInt_eq_zero (A B : Set X) (hAB : A ⊆ B) (n : ℕ)
    (hzero : ∀ y : RelHomologyInt B n, y = 0) :
    Function.Surjective (excisionMapInt A B n) := by
  intro m
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChainInt A n)
  replace hc : RelativeChainInt.mk A n c = (z : RelativeChainInt A n) := hc
  have hcA : RelativeChainInt.mk A n c ∈ relCyclesInt A n := by rw [hc]; exact z.2
  obtain ⟨w, d, hd⟩ :=
    exists_sub_boundary_mem_subspaceChainsInt B n hzero c (mem_relCyclesInt_mono hAB n c hcA)
  -- the pushforward of `d` is `c − ∂w`, still a relative cycle of `(X, A)`
  have hbdry : RelativeChainInt.mk A n (chainBoundary X n w) ∈ relCyclesInt A n :=
    relBoundariesInt_le_relCyclesInt A n ⟨RelativeChainInt.mk A (n + 1) w, rfl⟩
  have hdA : RelativeChainInt.mk A n (chainIncl B n d) ∈ relCyclesInt A n := by
    rw [← hd]
    have hsplit : RelativeChainInt.mk A n (c - chainBoundary X n w)
        = RelativeChainInt.mk A n c - RelativeChainInt.mk A n (chainBoundary X n w) :=
      Submodule.Quotient.mk_sub _
    rw [hsplit]
    exact Submodule.sub_mem _ hcA hbdry
  have hdcyc : RelativeChainInt.mk (restr A B) n d ∈ relCyclesInt (restr A B) n :=
    mem_relCyclesInt_restr_of_chainIncl n d hdA
  refine ⟨RelHomologyInt.mk (restr A B) n ⟨RelativeChainInt.mk (restr A B) n d, hdcyc⟩, ?_⟩
  rw [excisionMapInt_mk]
  -- the two relative cycles differ by the relative boundary `∂w`
  show RelHomologyInt.mk A n
      ⟨relChainInclInt A B n (RelativeChainInt.mk (restr A B) n d), _⟩
    = RelHomologyInt.mk A n z
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
  show relChainInclInt A B n (RelativeChainInt.mk (restr A B) n d) - (z : RelativeChainInt A n)
      ∈ relBoundariesInt A n
  refine ⟨RelativeChainInt.mk A (n + 1) (-w), ?_⟩
  rw [relBoundaryInt_mk]
  show RelativeChainInt.mk A n (chainBoundary X n (-w))
      = relChainInclInt A B n (RelativeChainInt.mk (restr A B) n d) - (z : RelativeChainInt A n)
  rw [relChainInclInt_mk, ← hc, ← hd, map_neg]
  have hsplit : RelativeChainInt.mk A n (c - chainBoundary X n w)
      = RelativeChainInt.mk A n c - RelativeChainInt.mk A n (chainBoundary X n w) :=
    Submodule.Quotient.mk_sub _
  rw [hsplit]
  have hneg : RelativeChainInt.mk A n (-chainBoundary X n w)
      = -RelativeChainInt.mk A n (chainBoundary X n w) := Submodule.Quotient.mk_neg _
  rw [hneg]
  abel

/-! ## §3. The consequence used downstream: cyclicity descends -/

/-- **A surjective image of a cyclic module is cyclic** (the trivial half, isolated for
readability). Stated with `zsmul` throughout — `map_zsmul`, not `map_smul`, is what fires on a
`ℤ`-module carrier whose `•` elaborates through `SubNegMonoid.toZSMul`. -/
theorem cyclic_of_surjective {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {a : M}
    (hgen : ∀ x : M, ∃ k : ℤ, x = k • a) : ∀ y : N, ∃ k : ℤ, y = k • f a := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨k, rfl⟩ := hgen x
  exact ⟨k, map_zsmul f k a⟩

/-- **The packaged criterion.** For a triple `A ⊆ B ⊆ X`: if `Hₙ(X, B; ℤ)` vanishes and
`Hₙ(B, A ∩ B; ℤ)` is generated by a single element, then so is `Hₙ(X, A; ℤ)`.

This is the point of the module: it converts a *two-piece decomposition* of the ambient space into a
cyclicity statement about the relative homology of the pair, with the two inputs living on the two
pieces separately — the job an ambient-split relative Mayer–Vietoris sequence would do, without
building one. -/
theorem relHomologyInt_cyclic_of_triple (A B : Set X) (hAB : A ⊆ B) (n : ℕ)
    (hzero : ∀ y : RelHomologyInt B n, y = 0)
    (hcyc : ∃ a : RelHomologyInt (restr A B) n,
      ∀ x : RelHomologyInt (restr A B) n, ∃ k : ℤ, x = k • a) :
    ∃ g : RelHomologyInt A n, ∀ y : RelHomologyInt A n, ∃ k : ℤ, y = k • g := by
  obtain ⟨a, hgen⟩ := hcyc
  exact ⟨excisionMapInt A B n a,
    cyclic_of_surjective (excisionMapInt A B n)
      (excisionMapInt_surjective_of_relHomologyInt_eq_zero A B hAB n hzero) hgen⟩

end

end SKEFTHawking.SingularRelativeTripleSurjInt
