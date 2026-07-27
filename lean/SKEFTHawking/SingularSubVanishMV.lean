/-
# The ambient-generic top-degree vanishing telescope (Mayer–Vietoris sandwich)

`KummerRP3GoodCoverTelescope` discharged `Hₘ(ℝP³;ℤ) = 0` for `m ≥ 4` with a 4-chart good-cover
Mayer–Vietoris telescope, but its vanishing vocabulary (`VanishFrom`, `vanish_union`,
`vanishFrom_union`, the disjoint-union rule) was written with the ambient space **hard-pinned** to
`RP3Etop`. Every other top-degree vanishing argument in the project — the punctured torus, the free
quotient, any open piece of a 4-manifold — needs exactly the same three lemmas over a *different*
ambient.

This module ships them once, over an arbitrary `X : TopCat`, off the banked subset-level
Mayer–Vietoris exactness `SingularSubHomologyMVInt.subHom_exact_sumInt` (which is already
ambient-generic). The content is the sandwich

    `Hₙ₊₁(U) = Hₙ₊₁(V) = 0`  and  `Hₙ(U ∩ V) = 0`   ⟹   `Hₙ₊₁(U ∪ V) = 0`

for open `U, V ⊆ X` (`vanish_union`), its degree-bookkeeping form (`vanishFrom_union`: a `k`-set
open cover whose multi-intersections are acyclic telescopes to `VanishFrom k`), and the
disjoint-union rule (`vanishFrom_union_disjoint`, using `Hₘ(∅) = 0`).

Vacuity attack: the hypothesis `Hₙ(U ∩ V) = 0` is not removable — `S¹ = U ∪ V` with two arcs has
`H₁(U) = H₁(V) = 0` but `H₁(S¹) ≅ ℤ ≠ 0`, the failure being exactly `H₀(U ∩ V) ≠ 0` for the
two-component intersection. Likewise `vanishFrom_union`'s `dI + 1 ≤ d` cannot be weakened to
`dI ≤ d`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.SingularSubHomologyMVInt
import SKEFTHawking.SingularCSCEmptyInt

namespace SKEFTHawking.SingularSubVanishMV

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSubHomologyMVInt (subHomConnectingInt subHom_exact_sumInt)
open SKEFTHawking.SingularCSCEmptyInt (homology_sub_empty_eq_zeroInt)

noncomputable section

variable {X : TopCat}

/-- `Hₘ(sub T;ℤ) = 0` for every `m ≥ d` — the top-degree vanishing predicate, ambient-generic. -/
def VanishFrom (d : ℕ) (T : Set ↑X) : Prop :=
  ∀ m, d ≤ m → ∀ x : Homology (sub T) m, x = 0

/-- Positive-degree acyclicity `Hₖ(sub T;ℤ) = 0` for `k ≥ 1` is `VanishFrom 1`. -/
theorem vanishFrom_one_of_acyclic {T : Set ↑X} (h : ∀ (k : ℕ) (x : Homology (sub T) (k + 1)), x = 0) :
    VanishFrom 1 T := by
  intro m hm x
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact h n x

/-- **The subset-level Mayer–Vietoris sandwich** (ambient-generic): if both open pieces vanish in
degree `n + 1` and their intersection vanishes in degree `n`, the union vanishes in degree `n + 1`.
The connecting map `subHomConnectingInt` sends the class into `Hₙ(U ∩ V) = 0`, so it comes from
`Hₙ₊₁(U) ⊕ Hₙ₊₁(V) = 0`. -/
theorem vanish_union {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (hUv : ∀ x : Homology (sub U) (n + 1), x = 0)
    (hVv : ∀ x : Homology (sub V) (n + 1), x = 0)
    (hIv : ∀ x : Homology (sub (U ∩ V)) n, x = 0)
    (x : Homology (sub (U ∪ V)) (n + 1)) : x = 0 := by
  have h0 : subHomConnectingInt U V hU hV n x = 0 := hIv _
  obtain ⟨p, hp⟩ := (subHom_exact_sumInt U V hU hV x).mp h0
  have hp0 : p = 0 := Prod.ext_iff.mpr ⟨hUv p.1, hVv p.2⟩
  rw [← hp, hp0, map_zero]

/-- Degree-bookkeeping form of the sandwich: the union's threshold is the max of the two pieces'
thresholds and the intersection's threshold **plus one**. -/
theorem vanishFrom_union {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V) {dU dV dI d : ℕ}
    (hUv : VanishFrom dU U) (hVv : VanishFrom dV V) (hIv : VanishFrom dI (U ∩ V))
    (hdU : dU ≤ d) (hdV : dV ≤ d) (hdI : dI + 1 ≤ d) (hd : 1 ≤ d) : VanishFrom d (U ∪ V) := by
  intro m hm x
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact vanish_union hU hV (hUv (n + 1) (by omega)) (hVv (n + 1) (by omega)) (hIv n (by omega)) x

/-- Disjoint open pieces: the threshold of a disjoint union is the max of the two thresholds (the
empty intersection has vanishing homology in every degree). -/
theorem vanishFrom_union_disjoint {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V) {dU dV d : ℕ}
    (hd : U ∩ V = ∅) (hUv : VanishFrom dU U) (hVv : VanishFrom dV V) (hdU : dU ≤ d)
    (hdV : dV ≤ d) (hd1 : 1 ≤ d) : VanishFrom d (U ∪ V) := by
  refine vanishFrom_union (dI := 0) hU hV hUv hVv ?_ hdU hdV (by omega) hd1
  intro m _ x
  revert x
  rw [hd]
  exact fun x => homology_sub_empty_eq_zeroInt m x

/-- Transport a vanishing threshold across a set equality. -/
theorem vanishFrom_congr {d : ℕ} {S T : Set ↑X} (h : S = T) (hS : VanishFrom d S) : VanishFrom d T :=
  h ▸ hS

/-- Monotonicity in the threshold. -/
theorem VanishFrom.mono {d d' : ℕ} {T : Set ↑X} (h : VanishFrom d T) (hdd : d ≤ d') :
    VanishFrom d' T := fun m hm x => h m (le_trans hdd hm) x

end

end SKEFTHawking.SingularSubVanishMV
