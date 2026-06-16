import Mathlib
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularMayerVietoris

/-!
# Mayer–Vietoris: the homology-level maps `Hₙ(A∩B) → Hₙ(A)⊕Hₙ(B) → Hₙ(X)`

The "easy half" of the Mayer–Vietoris long exact sequence (toward the fundamental-class gluing,
Hatcher 3.26). Built on the general homology functoriality `Homology.map` (`SingularFunctoriality`)
applied to the subspace inclusions:

* `mvHomDiag : Hₙ(A∩B) → Hₙ(A) ⊕ Hₙ(B)`, `w ↦ ((ι_{A∩B↪A})_* w, (ι_{A∩B↪B})_* w)` — the diagonal of
  the two inclusion-induced maps;
* `mvHomSum : Hₙ(A) ⊕ Hₙ(B) → Hₙ(X)`, `(u, v) ↦ (ι_{A↪X})_* u + (ι_{B↪X})_* v` — the sum (a difference
  over `ℤ/2`) of the two inclusions.

The composite property `mvHomSum ∘ mvHomDiag = 0` holds because both routes `A∩B ↪ A ↪ X` and
`A∩B ↪ B ↪ X` equal the single inclusion `A∩B ↪ X` (functoriality `Homology.map_comp`), so the sum is
`(ι_{A∩B↪X})_* w + (ι_{A∩B↪X})_* w = 0` over `ℤ/2`. This is the chain-complex condition of the MV
sequence at `Hₙ(A)⊕Hₙ(B)`; with the connecting map `δ` (next brick) it becomes the full LES.
Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularMayerVietorisLES

variable {X : TopCat}

/-- The inclusion of a subspace into the ambient space `↥S ↪ X` as a continuous map. -/
def ambIncl (S : Set ↑X) : C(↑(sub S), ↑X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion of one subspace into a larger one `↥s ↪ ↥t` (for `s ⊆ t`) as a continuous map. -/
def subIncl {s t : Set ↑X} (h : s ⊆ t) : C(↑(sub s), ↑(sub t)) :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

/-- The two routes `↥(A∩B) ↪ ↥A ↪ X` and `↥(A∩B) ↪ X` agree (both are `Subtype.val`). -/
theorem ambIncl_comp_subIncl_left (A B : Set ↑X) :
    (ambIncl A).comp (subIncl (Set.inter_subset_left (s := A) (t := B))) = ambIncl (A ∩ B) :=
  ContinuousMap.ext fun _ => rfl

theorem ambIncl_comp_subIncl_right (A B : Set ↑X) :
    (ambIncl B).comp (subIncl (Set.inter_subset_right (s := A) (t := B))) = ambIncl (A ∩ B) :=
  ContinuousMap.ext fun _ => rfl

/-- **The MV diagonal** `Hₙ(A∩B) → Hₙ(A) ⊕ Hₙ(B)`, `w ↦ ((ι_A)_* w, (ι_B)_* w)`. -/
noncomputable def mvHomDiag (A B : Set ↑X) (n : ℕ) :
    Homology (sub (A ∩ B)) n →ₗ[ZMod 2] Homology (sub A) n × Homology (sub B) n :=
  (Homology.map (subIncl (Set.inter_subset_left (s := A) (t := B))) n).prod
    (Homology.map (subIncl (Set.inter_subset_right (s := A) (t := B))) n)

/-- **The MV sum** `Hₙ(A) ⊕ Hₙ(B) → Hₙ(X)`, `(u, v) ↦ (ι_A)_* u + (ι_B)_* v` (a difference over `ℤ/2`). -/
noncomputable def mvHomSum (A B : Set ↑X) (n : ℕ) :
    Homology (sub A) n × Homology (sub B) n →ₗ[ZMod 2] Homology X n :=
  (Homology.map (ambIncl A) n).coprod (Homology.map (ambIncl B) n)

@[simp] theorem mvHomDiag_apply (A B : Set ↑X) (n : ℕ) (w : Homology (sub (A ∩ B)) n) :
    mvHomDiag A B n w
      = (Homology.map (subIncl (Set.inter_subset_left (s := A) (t := B))) n w,
         Homology.map (subIncl (Set.inter_subset_right (s := A) (t := B))) n w) := rfl

@[simp] theorem mvHomSum_apply (A B : Set ↑X) (n : ℕ)
    (p : Homology (sub A) n × Homology (sub B) n) :
    mvHomSum A B n p = Homology.map (ambIncl A) n p.1 + Homology.map (ambIncl B) n p.2 := rfl

/-- **The MV chain-complex condition** `mvHomSum ∘ mvHomDiag = 0`: both inclusion routes from `A∩B`
land in `Hₙ(X)` as the same map, so over `ℤ/2` the sum is `c + c = 0`. -/
theorem mvHomSum_mvHomDiag (A B : Set ↑X) (n : ℕ) (w : Homology (sub (A ∩ B)) n) :
    mvHomSum A B n (mvHomDiag A B n w) = 0 := by
  rw [mvHomDiag_apply, mvHomSum_apply]
  rw [show Homology.map (ambIncl A) n
          (Homology.map (subIncl (Set.inter_subset_left (s := A) (t := B))) n w)
        = Homology.map (ambIncl (A ∩ B)) n w by
        rw [← LinearMap.comp_apply, ← Homology.map_comp, ambIncl_comp_subIncl_left],
    show Homology.map (ambIncl B) n
          (Homology.map (subIncl (Set.inter_subset_right (s := A) (t := B))) n w)
        = Homology.map (ambIncl (A ∩ B)) n w by
        rw [← LinearMap.comp_apply, ← Homology.map_comp, ambIncl_comp_subIncl_right]]
  exact ZModModule.add_self _

end SKEFTHawking.SingularMayerVietorisLES
