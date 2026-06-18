import Mathlib
import SKEFTHawking.SingularRelativeFunctoriality

/-!
# Relative Mayer–Vietoris: the maps `Hₙ(M|A∩B) → Hₙ(M|A) ⊕ Hₙ(M|B) → Hₙ(M|A∪B)`

Toward the fundamental class (Hatcher 3.27). With `Hₙ(M|A) := Hₙ(M, M∖A)` and opens `U = M∖A`,
`V = M∖B` of `M` (so `U∩V = M∖(A∪B)`, `U∪V = M∖(A∩B)`), the **relative** Mayer–Vietoris diagonal and
sum are the inclusion-of-pairs maps induced by `id_M` on `(M, U∩V) → (M, U)`, `(M, U) → (M, U∪V)`,
etc. (`RelativeHomology.map`). The chain-complex condition `Σ ∘ Δ = 0` holds because both inclusion
routes `(M, U∩V) → (M, U∪V)` are the single inclusion, so over `ℤ/2` the sum is `c + c = 0`. With the
connecting map (next brick) this becomes the relative MV long exact sequence — the engine of the
`Hₙ(M|A)` compactness induction giving the fundamental class `[M]`. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeFunctoriality

namespace SKEFTHawking.SingularRelativeMV

variable {M : TopCat}

/-- The inclusion-of-pairs map `Hₙ(M, S) → Hₙ(M, T)` for `S ⊆ T`, induced by `id_M` (a map of pairs
`(M, S) → (M, T)` since `id` sends `S` into `T`). -/
noncomputable def relIncl {S T : Set ↑M} (h : S ⊆ T) (n : ℕ) :
    RelativeHomology S n →ₗ[ZMod 2] RelativeHomology T n :=
  RelativeHomology.map (ContinuousMap.id ↑M) (fun _ hx => h hx) n

/-- Composing two inclusion-of-pairs maps is the inclusion over the composite subset relation
(functoriality of relative homology + `id ∘ id = id`). -/
theorem relIncl_trans {S T W : Set ↑M} (h1 : S ⊆ T) (h2 : T ⊆ W) (n : ℕ)
    (x : RelativeHomology S n) :
    relIncl h2 n (relIncl h1 n x) = relIncl (h1.trans h2) n x := by
  rw [relIncl, relIncl, relIncl, ← LinearMap.comp_apply, ← RelativeHomology.map_comp]
  rfl

/-- **Relative MV diagonal** `Hₙ(M|A∩B) → Hₙ(M|A) ⊕ Hₙ(M|B)`, the two inclusions `U∩V ↪ U`, `U∩V ↪ V`. -/
noncomputable def relMvHomDiag (U V : Set ↑M) (n : ℕ) :
    RelativeHomology (U ∩ V) n →ₗ[ZMod 2] RelativeHomology U n × RelativeHomology V n :=
  (relIncl Set.inter_subset_left n).prod (relIncl Set.inter_subset_right n)

/-- **Relative MV sum** `Hₙ(M|A) ⊕ Hₙ(M|B) → Hₙ(M|A∪B)`, the inclusions `U ↪ U∪V`, `V ↪ U∪V`
(a difference over `ℤ/2`). -/
noncomputable def relMvHomSum (U V : Set ↑M) (n : ℕ) :
    RelativeHomology U n × RelativeHomology V n →ₗ[ZMod 2] RelativeHomology (U ∪ V) n :=
  (relIncl Set.subset_union_left n).coprod (relIncl Set.subset_union_right n)

/-- **Relative MV chain-complex condition** `Σ ∘ Δ = 0`: both routes `(M, U∩V) → (M, U∪V)` equal the
single inclusion, so over `ℤ/2` the sum is `c + c = 0`. -/
theorem relMvHomSum_relMvHomDiag (U V : Set ↑M) (n : ℕ) (w : RelativeHomology (U ∩ V) n) :
    relMvHomSum U V n (relMvHomDiag U V n w) = 0 := by
  show relIncl Set.subset_union_left n (relIncl Set.inter_subset_left n w)
      + relIncl Set.subset_union_right n (relIncl Set.inter_subset_right n w) = 0
  rw [relIncl_trans, relIncl_trans]
  exact ZModModule.add_self _

end SKEFTHawking.SingularRelativeMV
