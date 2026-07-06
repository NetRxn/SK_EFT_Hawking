/-
# A bounded-below acyclic complex of projective ℤ-modules is contractible (reusable homological algebra)

The reusable engine behind the cohomology Mayer–Vietoris middle-exactness node `(B)` (dualising the
degreewise-split relative-homology MV chain SES): given a ℕ-graded complex `C` of **projective** ℤ-modules
with boundary `d n : C (n+1) → C n`, `d ∘ d = 0`, that is **acyclic** (`ker (d n) = range (d (n+1))`, plus
`d 0` surjective, i.e. `H₀ = 0`), there is a **contracting homotopy** `s n : C n → C (n+1)` with
  `d (n+1) ∘ s (n+1) + s n ∘ d n = id`   (for every `n`).
Dualising (`Hom(−, A)`) turns it into a cochain contraction, so **`Hom(C, A)` is acyclic in every positive
degree**: a cocycle `g : C (n+1) → A` (`g ∘ d (n+1) = 0`) is the coboundary `g = (g ∘ s n) ∘ d n`.

The construction is a self-propagating forward recursion carrying only `(sₙ, Keyₙ)` with
`Keyₙ : ∀ x, d n (sₙ (d n x)) = d n x`: from `(sₙ, Keyₙ)` the map `φ := id − sₙ ∘ d n` lands in
`ker (d n) = range (d (n+1))`, so it lifts through the projective `C (n+1)` to `s_{n+1}` with
`d (n+1) ∘ s_{n+1} = φ`, which both is the homotopy relation and regenerates `Key_{n+1}`. No
submodule-projectivity, no universal-coefficient theorem, no `HomologicalComplex` framework — matches the
project's concrete `Finsupp`-based (co)homology.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `native_decide`, no `maxHeartbeats`, no axiom.
-/
import Mathlib

namespace SKEFTHawking.AcyclicProjectiveContractionInt

/-- **Lift a map into a range through the range map** (`Module.projective_lifting_property` with
corestriction): if `g : P → B` lands in `range f` and `P` is projective, there is `t : P → A` with
`f ∘ t = g`. Stated over a general ring `R` so the `↥(range f)` module instance carries no `ℤ`-specific
diamond. -/
theorem exists_lift_of_mem_range {R : Type*} [Ring R] {A B P : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup P] [Module R P] [Module.Projective R P]
    (f : A →ₗ[R] B) (g : P →ₗ[R] B) (hg : ∀ x, g x ∈ LinearMap.range f) :
    ∃ t : P →ₗ[R] A, f.comp t = g := by
  obtain ⟨t, ht⟩ := Module.projective_lifting_property f.rangeRestrict (g.codRestrict _ hg)
    (LinearMap.surjective_rangeRestrict f)
  refine ⟨t, ?_⟩
  ext x
  have hx := congrArg (Submodule.subtype (LinearMap.range f)) (LinearMap.congr_fun ht x)
  simpa using hx

variable {C : ℕ → Type*} [∀ n, AddCommGroup (C n)] [∀ n, Module ℤ (C n)]

/-- `φ := id − sₙ ∘ dₙ` lands in `range (d (n+1))`, given the invariant `Keyₙ`. -/
theorem phi_mem_range (d : ∀ n, C (n + 1) →ₗ[ℤ] C n)
    (hex : ∀ n, LinearMap.ker (d n) = LinearMap.range (d (n + 1))) {n : ℕ}
    (sn : C n →ₗ[ℤ] C (n + 1)) (key : ∀ x : C (n + 1), d n (sn (d n x)) = d n x) :
    ∀ x, ((LinearMap.id - sn.comp (d n) : C (n + 1) →ₗ[ℤ] C (n + 1))) x
      ∈ LinearMap.range (d (n + 1)) := by
  intro x
  rw [← hex n, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply, map_sub]
  rw [key x, sub_self]

/-- The recursion state at degree `n`: a partial contraction `s` with the self-propagating invariant
`Keyₙ`. -/
structure ContrStep (d : ∀ n, C (n + 1) →ₗ[ℤ] C n) (n : ℕ) where
  s : C n →ₗ[ℤ] C (n + 1)
  key : ∀ x : C (n + 1), d n (s (d n x)) = d n x

variable [∀ n, Module.Projective ℤ (C n)]

/-- The forward recursion producing `(sₙ, Keyₙ)` for every `n`. -/
noncomputable def contrAux (d : ∀ n, C (n + 1) →ₗ[ℤ] C n)
    (hdd : ∀ n, (d n).comp (d (n + 1)) = 0)
    (hex : ∀ n, LinearMap.ker (d n) = LinearMap.range (d (n + 1)))
    (hsurj0 : Function.Surjective (d 0)) : ∀ n, ContrStep d n
  | 0 =>
    { s := (Module.projective_lifting_property (d 0) LinearMap.id hsurj0).choose
      key := by
        intro x
        have hs := (Module.projective_lifting_property (d 0) LinearMap.id hsurj0).choose_spec
        have := LinearMap.congr_fun hs (d 0 x)
        simpa using this }
  | n + 1 =>
    { s := (exists_lift_of_mem_range (d (n + 1)) (LinearMap.id - ((contrAux d hdd hex hsurj0 n).s).comp (d n))
          (phi_mem_range d hex (contrAux d hdd hex hsurj0 n).s (contrAux d hdd hex hsurj0 n).key)).choose
      key := by
        intro z
        have hs := (exists_lift_of_mem_range (d (n + 1))
          (LinearMap.id - ((contrAux d hdd hex hsurj0 n).s).comp (d n))
          (phi_mem_range d hex (contrAux d hdd hex hsurj0 n).s (contrAux d hdd hex hsurj0 n).key)).choose_spec
        have hz := LinearMap.congr_fun hs (d (n + 1) z)
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_coe, id_eq] at hz
        rw [hz]
        have hdd' : d n (d (n + 1) z) = 0 := by simpa using LinearMap.congr_fun (hdd n) z
        rw [hdd', map_zero, sub_zero] }

/-- The contracting homotopy `sₙ : C n → C (n+1)`. -/
noncomputable def contr (d : ∀ n, C (n + 1) →ₗ[ℤ] C n)
    (hdd : ∀ n, (d n).comp (d (n + 1)) = 0)
    (hex : ∀ n, LinearMap.ker (d n) = LinearMap.range (d (n + 1)))
    (hsurj0 : Function.Surjective (d 0)) (n : ℕ) : C n →ₗ[ℤ] C (n + 1) :=
  (contrAux d hdd hex hsurj0 n).s

/-- The carried invariant `Keyₙ` for the chosen `contr`. -/
theorem contr_key (d : ∀ n, C (n + 1) →ₗ[ℤ] C n)
    (hdd : ∀ n, (d n).comp (d (n + 1)) = 0)
    (hex : ∀ n, LinearMap.ker (d n) = LinearMap.range (d (n + 1)))
    (hsurj0 : Function.Surjective (d 0)) (n : ℕ) :
    ∀ x : C (n + 1), d n (contr d hdd hex hsurj0 n (d n x)) = d n x :=
  (contrAux d hdd hex hsurj0 n).key

/-- **The homotopy relation** `d (n+1) ∘ s (n+1) + s n ∘ d n = id` on `C (n+1)`. -/
theorem contr_homotopy (d : ∀ n, C (n + 1) →ₗ[ℤ] C n)
    (hdd : ∀ n, (d n).comp (d (n + 1)) = 0)
    (hex : ∀ n, LinearMap.ker (d n) = LinearMap.range (d (n + 1)))
    (hsurj0 : Function.Surjective (d 0)) (n : ℕ) :
    (d (n + 1)).comp (contr d hdd hex hsurj0 (n + 1)) + (contr d hdd hex hsurj0 n).comp (d n)
      = LinearMap.id := by
  have hs := (exists_lift_of_mem_range (d (n + 1))
      (LinearMap.id - (contr d hdd hex hsurj0 n).comp (d n))
      (phi_mem_range d hex (contr d hdd hex hsurj0 n) (contr_key d hdd hex hsurj0 n))).choose_spec
  have hce : contr d hdd hex hsurj0 (n + 1) = (exists_lift_of_mem_range (d (n + 1))
      (LinearMap.id - (contr d hdd hex hsurj0 n).comp (d n))
      (phi_mem_range d hex (contr d hdd hex hsurj0 n) (contr_key d hdd hex hsurj0 n))).choose := rfl
  rw [hce, hs]
  abel

/-- **`Hom(C, A)` is acyclic in positive degrees**: a cocycle `g : C (n+1) → A` (`g ∘ d (n+1) = 0`) is the
coboundary `g = (g ∘ s n) ∘ d n`. -/
theorem cocycle_eq_coboundary {A : Type*} [AddCommGroup A] [Module ℤ A]
    (d : ∀ n, C (n + 1) →ₗ[ℤ] C n)
    (hdd : ∀ n, (d n).comp (d (n + 1)) = 0)
    (hex : ∀ n, LinearMap.ker (d n) = LinearMap.range (d (n + 1)))
    (hsurj0 : Function.Surjective (d 0)) (n : ℕ)
    (g : C (n + 1) →ₗ[ℤ] A) (hg : g.comp (d (n + 1)) = 0) :
    g = (g.comp (contr d hdd hex hsurj0 n)).comp (d n) := by
  have h := contr_homotopy d hdd hex hsurj0 n
  have hsd : (contr d hdd hex hsurj0 n).comp (d n)
      = LinearMap.id - (d (n + 1)).comp (contr d hdd hex hsurj0 (n + 1)) := by
    rw [← h]; abel
  rw [LinearMap.comp_assoc, hsd, LinearMap.comp_sub, LinearMap.comp_id, ← LinearMap.comp_assoc, hg,
    LinearMap.zero_comp, sub_zero]

end SKEFTHawking.AcyclicProjectiveContractionInt
