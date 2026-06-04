/-
Phase 5q.B Wave B2/B1 bridge: even integer lattice → mod-2 quadratic refinement

For an even unimodular lattice with Gram matrix `M`, the spectra-free Rokhlin route works
with the finite quadratic refinement on `L/2L ≅ (ZMod 2)ⁿ`:
  q̄(x) = b(x,x)/2 mod 2,    b̄(x,y) = b(x,y) mod 2,
where `b̄` is alternating and nondegenerate (nondegeneracy ⟺ `M` unimodular) and `q̄` refines
it. The central identity `σ(L) ≡ 8·Arf(q̄) mod 16` (van der Blij / Brown) then drives B1/B3/B4.

This module builds the bridge from a symmetric even integer matrix. This increment establishes
the mod-2 reduced bilinear form `redBilin` and its symmetry; the alternating property and the
`q̄` refinement come next.

See docs/roadmaps/Phase5qB_SpectraFreeSpinBordism_Roadmap.md.
-/

import Mathlib
import SKEFTHawking.ArfInvariant

namespace SKEFTHawking.EvenLattice

variable {n : ℕ}

/-- The mod-2 reduction of the bilinear form of an integer matrix `M`:
    `b̄(x,y) = ∑_{i,j} (M i j mod 2)·xᵢ·yⱼ`. -/
def redBilin (M : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, (M i j : ZMod 2) * x i * y j

/-- Entrywise: a symmetric integer matrix has `M j i = M i j`. -/
theorem entry_symm {M : Matrix (Fin n) (Fin n) ℤ} (hM : M.transpose = M) (i j : Fin n) :
    M j i = M i j := by
  have := congrFun (congrFun hM i) j
  simpa [Matrix.transpose] using this

/-- `b̄` is symmetric when `M` is symmetric. -/
theorem redBilin_symm {M : Matrix (Fin n) (Fin n) ℤ} (hM : M.transpose = M)
    (x y : Fin n → ZMod 2) : redBilin M x y = redBilin M y x := by
  unfold redBilin
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [entry_symm hM]
  ring

/-- In `ZMod 2`, every element is idempotent: `a·a = a`. -/
theorem sq_self (a : ZMod 2) : a * a = a := by revert a; decide

/-- The mod-2 diagonal of an even matrix vanishes: `(M i i mod 2) = 0`. -/
theorem even_diag_cast_zero {M : Matrix (Fin n) (Fin n) ℤ} (heven : ∀ i, 2 ∣ M i i) (i : Fin n) :
    (M i i : ZMod 2) = 0 := by
  obtain ⟨k, hk⟩ := heven i
  rw [hk]; push_cast; rw [show (2 : ZMod 2) = 0 from by decide]; ring

/-- **`b̄` is alternating:** for a symmetric even integer matrix, `b̄(x,x) = 0`.
    (The off-diagonal terms cancel pairwise in characteristic 2 by symmetry; the diagonal
    vanishes by evenness.) This is what makes `b̄` a symplectic form on `L/2L`. -/
theorem redBilin_self_eq_zero {M : Matrix (Fin n) (Fin n) ℤ}
    (hsymm : M.transpose = M) (heven : ∀ i, 2 ∣ M i i) (x : Fin n → ZMod 2) :
    redBilin M x x = 0 := by
  unfold redBilin
  rw [← Finset.sum_product', Finset.univ_product_univ]
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _) Prod.swap_swap
  · intro p
    have hs : (M p.2 p.1 : ZMod 2) = (M p.1 p.2 : ZMod 2) := by rw [entry_symm hsymm]
    simp only [Prod.fst_swap, Prod.snd_swap, hs]
    have hcomm : (M p.1 p.2 : ZMod 2) * x p.1 * x p.2 = (M p.1 p.2 : ZMod 2) * x p.2 * x p.1 := by
      ring
    rw [hcomm]
    exact CharTwo.add_self_eq_zero _
  · intro p hp hswap
    apply hp
    have hpe : p.1 = p.2 := (Prod.ext_iff.mp hswap).2
    rw [← hpe, even_diag_cast_zero heven]
    ring

/-! ## The mod-2 quadratic refinement `q̄` -/

/-- Diagonal "half" linear part: `∑ᵢ (Mᵢᵢ/2 mod 2)·xᵢ`. -/
def hdSum (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, ((M i i / 2 : ℤ) : ZMod 2) * x i

/-- Strictly-upper quadratic part: `∑_{i<j} (Mᵢⱼ mod 2)·xᵢ·xⱼ`. -/
def upperSum (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, (if i < j then (M i j : ZMod 2) else 0) * (x i * x j)

/-- The mod-2 quadratic refinement `q̄(x) = b(x,x)/2 mod 2 = ∑ᵢ (Mᵢᵢ/2)xᵢ + ∑_{i<j} Mᵢⱼ xᵢxⱼ`. -/
def redQuad (M : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ZMod 2) : ZMod 2 :=
  hdSum M x + upperSum M x

/-- The linear part is additive. -/
theorem hdSum_add (M : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ZMod 2) :
    hdSum M (x + y) = hdSum M x + hdSum M y := by
  unfold hdSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, mul_add]

/-- The strictly-upper symmetric bilinear form `∑_{i<j} Mᵢⱼ (xᵢyⱼ + xⱼyᵢ)` — the polar form
    of `redQuad`. (Equal to `redBilin` for symmetric even `M`; bridge proved separately.) -/
def bUpper (M : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, (if i < j then (M i j : ZMod 2) else 0) * (x i * y j + x j * y i)

/-- The quadratic part expands additively with the polar `bUpper` as cross term. -/
theorem upperSum_add (M : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ZMod 2) :
    upperSum M (x + y) = upperSum M x + upperSum M y + bUpper M x y := by
  unfold upperSum bUpper
  have key : ∀ i j : Fin n,
      (if i < j then (M i j : ZMod 2) else 0) * ((x + y) i * (x + y) j)
        = (if i < j then (M i j : ZMod 2) else 0) * (x i * x j)
          + (if i < j then (M i j : ZMod 2) else 0) * (y i * y j)
          + (if i < j then (M i j : ZMod 2) else 0) * (x i * y j + x j * y i) := by
    intro i j; rw [Pi.add_apply, Pi.add_apply]; ring
  simp_rw [key, Finset.sum_add_distrib]

/-- **Refinement property:** `q̄(x+y) = q̄(x) + q̄(y) + b̄(x,y)` (with `b̄ = bUpper`).
    So `redQuad` is a quadratic refinement of the symplectic form on `L/2L`. -/
theorem redQuad_add (M : Matrix (Fin n) (Fin n) ℤ) (x y : Fin n → ZMod 2) :
    redQuad M (x + y) = redQuad M x + redQuad M y + bUpper M x y := by
  unfold redQuad
  rw [hdSum_add, upperSum_add]
  abel

/-- `q̄ 0 = 0` (the other refinement axiom). -/
theorem redQuad_zero (M : Matrix (Fin n) (Fin n) ℤ) : redQuad M (0 : Fin n → ZMod 2) = 0 := by
  unfold redQuad hdSum upperSum
  simp

/-- **Bridge:** for a symmetric even integer matrix, the strictly-upper polar `bUpper` equals the
    full mod-2 reduced bilinear form `redBilin` (the genuine symplectic form `b̄ = b mod 2`).
    (`i<j` and `i>j` regions combine by symmetry; the diagonal vanishes by evenness.) -/
theorem bUpper_eq_redBilin {M : Matrix (Fin n) (Fin n) ℤ} (hsymm : M.transpose = M)
    (heven : ∀ i, 2 ∣ M i i) (x y : Fin n → ZMod 2) :
    bUpper M x y = redBilin M x y := by
  unfold bUpper redBilin
  have hsplit : ∀ i j : Fin n,
      (if i < j then (M i j : ZMod 2) else 0) * (x i * y j + x j * y i)
        = (if i < j then (M i j : ZMod 2) else 0) * (x i * y j)
          + (if i < j then (M i j : ZMod 2) else 0) * (x j * y i) := fun i j => by ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hQ : (∑ i, ∑ j, (if i < j then (M i j : ZMod 2) else 0) * (x j * y i))
      = ∑ i, ∑ j, (if j < i then (M i j : ZMod 2) else 0) * (x i * y j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [entry_symm hsymm a b]
  rw [hQ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy i j with h | h | h
  · rw [if_pos h, if_neg (by omega)]; ring
  · subst h; simp [even_diag_cast_zero heven]
  · rw [if_neg (by omega), if_pos h]; ring

/-- **`q̄` is a quadratic refinement of the symplectic form `b̄ = b mod 2`:**
    `q̄(x+y) = q̄(x) + q̄(y) + b̄(x,y)` with `b̄ = redBilin` (alternating + symmetric).
    This is the lattice instance of the `IsRefinement` structure consumed by the Arf machinery. -/
theorem redQuad_refines_redBilin {M : Matrix (Fin n) (Fin n) ℤ} (hsymm : M.transpose = M)
    (heven : ∀ i, 2 ∣ M i i) (x y : Fin n → ZMod 2) :
    redQuad M (x + y) = redQuad M x + redQuad M y + redBilin M x y := by
  rw [redQuad_add, bUpper_eq_redBilin hsymm heven]

open Matrix in
/-- **An even symmetric integer form takes even values:** `2 ∣ wᵀ M w` for all integer `w`. The diagonal
contributes `M i i · w i²` (even since the diagonal is even); the off-diagonal terms pair up via symmetry
(`M i j · w i w j + M j i · w j w i = 2 M i j w i w j`). Formally, the mod-2 reduction of `wᵀ M w` is
`redBilin M w̄ w̄`, which vanishes (`redBilin_self_eq_zero`). This is the parity fact that lets the
hyperbolic-plane splitting adjust the partner vector to be isotropic ([E2] in the van der Blij roadmap). -/
theorem even_form_dvd {M : Matrix (Fin n) (Fin n) ℤ} (hsymm : M.transpose = M)
    (heven : ∀ i, 2 ∣ M i i) (w : Fin n → ℤ) : 2 ∣ w ⬝ᵥ M *ᵥ w := by
  have hbridge : ((w ⬝ᵥ M *ᵥ w : ℤ) : ZMod 2)
      = redBilin M (fun i => (w i : ZMod 2)) (fun i => (w i : ZMod 2)) := by
    unfold redBilin
    rw [dotProduct]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hz : ((w ⬝ᵥ M *ᵥ w : ℤ) : ZMod 2) = 0 := by
    rw [hbridge]; exact redBilin_self_eq_zero hsymm heven _
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz

end SKEFTHawking.EvenLattice
