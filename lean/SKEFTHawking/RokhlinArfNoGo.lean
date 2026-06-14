/-
# NO-GO: the lattice Arf invariant does NOT compute σ/8 mod 2

**The mod-16 factor of Rokhlin's theorem is irreducibly GEOMETRIC, not a lattice invariant.**

This module records, as kernel-pure proved theorems, the refutation of a tempting-but-FALSE bridge that
was carried as prose across two planning sessions (Phase 5q.B/5q.C) before being computed and refuted
(2026-06-13). The false claim, propagated from an internally-contradictory deep-research note
(`Lit-Search/Phase-5c/Rokhlin/…`), was:

  **(FALSE)**  `σ(L)/8 ≡ Arf(q̄) (mod 2)` for every even unimodular lattice `L`, with `q̄ = redQuad`
                the mod-2 quadratic refinement `q̄(x)=(x·x)/2 mod 2` on `L/2L`.

It is FALSE, refuted by `E₈`:
  • `σ(E₈) = 8` (E₈ positive definite), so `σ/8 = 1` (ODD); but
  • `gaussSum (redQuad E₈) = +16 = +2⁴` (`#{q̄=0}=136=2⁷+2³`, the `Arf=0` fingerprint; the 120 classes with
    `q̄=1` are exactly E₈'s 240 roots / ±pairs) ⟹ **`Arf(redQuad E₈) = 0`** (`arfOfForm E₈ = 0`).
So the bridge would read `1 ≡ 0 (mod 2)` — false (`lattice_arf_bridge_refuted`).

## Why it can never be fixed in the lattice category (the structural no-go)

1. **`arfOfForm ≡ 0` on every even unimodular lattice.** Each generator has Arf 0
   (`arfOfForm_e8lit_eq_zero`, `arfOfForm_hyp_eq_zero`, `arfOfForm_neg_e8lit_eq_zero`), and `arfOfForm`
   is additive over `⊕` (gaussSum multiplicative, all factors on the `+2^{gᵢ}` branch). So it is a
   CONSTANT (0), while `σ/8` varies — they cannot be equal.
2. **Orientation-blindness (`redQuad_neg_eq`/`arfOfForm_neg_eq`).** `redQuad(−M) = redQuad(M)` (every
   coefficient is fixed mod 2 under negation), so `arfOfForm(−M) = arfOfForm(M)`; but
   `latticeSig(−M) = −latticeSig(M)`. No `redQuad`-derived invariant can track the *sign* of `σ`.
3. **Discriminant-form ceiling.** For a *unimodular* lattice the discriminant group `L*/L` is trivial,
   so the entire finite-quadratic-form (Milgram/Brown/Arf) apparatus can certify only `σ ≡ 0 mod 8`
   (van der Blij — already proven in-repo as `eight_dvd_latticeSig`) and is BLIND to `σ mod 16`. (The
   ℤ/4 Brown refinement `(x·x) mod 4` takes only even values on an even lattice, collapsing to the same
   ±1 Arf sum.)

## What IS true (the correct statements)

- **van der Blij** is a *mod-8* theorem (`c² ≡ σ mod 8` via characteristic vectors; `0` is characteristic
  for even lattices ⟹ `8∣σ`). The project has this: `SKEFTHawking.eight_dvd_latticeSig`.
- The genuine `σ/8 ≡ Arf` relation is the **GEOMETRIC** Freedman–Kirby / Guillou–Marin congruence
  `σ(M) ≡ Σ·Σ + 8·Arf(M,Σ) mod 16`, where `Arf(M,Σ)` is the Arf invariant of the quadratic refinement on
  `H₁(Σ;ℤ/2)` of a smoothly embedded *characteristic surface* `Σ` in a spin 4-MANIFOLD — data not present
  in, and not recoverable from, the lattice. (`E₈`'s *characteristic-surface* Arf is `1`; its *lattice*
  L/2L Arf is `0` — these are different invariants, and conflating them is the original error.)
- Hence `16∣σ` for smooth spin 4-manifolds carries exactly ONE irreducible topological input, by
  mathematical necessity (E₈ is the even-unimodular counterexample with σ=8). The project carries it as
  the tracked hypothesis `SmoothSpinManifold4.topo : 2∣σ/8` (ADR-003). It CANNOT be re-expressed as a
  lattice-algebraic `Arf=0`; the only honest `Arf=0` form is the geometric one (ADR-003 Phase-2 frontier).

The `redQuad`/`gaussSum` machinery in `EvenLatticeForm.lean`/`ArfInvariant.lean` is itself correct and
reusable — it correctly proves `gaussSum(redQuad M) = 2^g·(−1)^{Arf}` and `arfOfForm ≡ 0`; it simply does
NOT drive a `σ mod 16` bridge.

See: ADR-003 (irreducible-topological-residue posture), `docs/roadmaps/Phase5qC_ArfBridge_Roadmap.md`
(retired premise), `docs/audits/` no-go register. Kernel-pure (`propext`/`Classical.choice`/`Quot.sound`
only); no `native_decide`, no `sorry`, no `maxHeartbeats`.
-/

import Mathlib
import SKEFTHawking.ArfInvariant
import SKEFTHawking.EvenLatticeForm
import SKEFTHawking.E8Literal
import SKEFTHawking.E8Signature
import SKEFTHawking.LatticeSignature
import SKEFTHawking.GeneratorNondeg

namespace SKEFTHawking.RokhlinArfNoGo

open SKEFTHawking SKEFTHawking.EvenLattice Matrix

/-- The candidate **algebraic Arf invariant** of an even unimodular lattice: the Arf invariant of the
mod-2 quadratic refinement `redQuad M`, read off the sign of its genus-`g` Gauss sum
(`gaussSum (redQuad M) = 2^g·(−1)^{Arf}`, so a positive Gauss sum ↔ `Arf = 0`). This is the exact object
the (false) Phase-5q.C roadmap bridge proposed as a replacement for the tracked topological input
`SmoothSpinManifold4.topo : 2 ∣ σ/8`. It is well-defined and kernel-pure, but — as the theorems below
show — it is **identically `0`** on even unimodular lattices and does NOT equal `σ/8 mod 2`. -/
noncomputable def arfOfForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : ZMod 2 :=
  if 0 < Arf.gaussSum (redQuad M) then 0 else 1

set_option maxRecDepth 4000 in
/-- **Witness (kernel `decide`, `native_decide`-free):** `gaussSum (redQuad E₈) = +16 = +2⁴`, the
`Arf = 0` branch. (Independent cross-check: `#{x : redQuad E₈ x = 0} = 136 = 2⁷+2³`, and the 120 classes
with `q̄ = 1` are exactly E₈'s 240 roots in ±pairs.) -/
theorem gaussSum_redQuad_e8lit_eq : Arf.gaussSum (redQuad E8lit) = 16 := by decide

/-- **`arfOfForm E₈ = 0`** — NOT `1`, contradicting the roadmap's Wave-C.2 assertion `arfOfForm E₈ = 1`. -/
theorem arfOfForm_e8lit_eq_zero : arfOfForm E8lit = 0 := by
  unfold arfOfForm; rw [gaussSum_redQuad_e8lit_eq]; norm_num

/-- `gaussSum (redQuad H) = +2 = +2¹` (the hyperbolic plane, `Arf 0`). -/
theorem gaussSum_redQuad_hyp_eq : Arf.gaussSum (redQuad Hyp) = 2 := by decide

/-- **`arfOfForm H = 0`.** -/
theorem arfOfForm_hyp_eq_zero : arfOfForm Hyp = 0 := by
  unfold arfOfForm; rw [gaussSum_redQuad_hyp_eq]; norm_num

/-- **Orientation-blindness of `redQuad`:** `redQuad(−M) = redQuad(M)` for even `M`. Every coefficient of
`redQuad` is fixed mod 2 under negation (`-a ≡ a (mod 2)`, and `-(2k)/2 = -k ≡ k (mod 2)` for the even
diagonal). This is the structural reason no `redQuad`-derived invariant can see the *sign* of the
signature. -/
theorem redQuad_neg_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (heven : ∀ i, 2 ∣ M i i) :
    redQuad (-M) = redQuad M := by
  funext x
  unfold redQuad hdSum upperSum
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := heven i
    simp only [Matrix.neg_apply, hk]
    rw [show (-(2 * k)) / 2 = -k from by omega, show (2 * k) / 2 = k from by omega,
      Int.cast_neg, CharTwo.neg_eq]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.neg_apply]
    by_cases h : i < j <;> simp only [h, if_true, if_false, Int.cast_neg, CharTwo.neg_eq]

/-- **`arfOfForm(−M) = arfOfForm(M)`** for even `M` — `arfOfForm` is orientation-blind, whereas
`latticeSig(−M) = −latticeSig(M)` (`latticeSig_neg`). -/
theorem arfOfForm_neg_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (heven : ∀ i, 2 ∣ M i i) :
    arfOfForm (-M) = arfOfForm M := by
  unfold arfOfForm; rw [redQuad_neg_eq M heven]

/-- **`arfOfForm(−E₈) = 0`** (= `arfOfForm E₈`), while `σ(−E₈) = −8 ≠ 8 = σ(E₈)`: a concrete instance of
the orientation-blindness obstruction. -/
theorem arfOfForm_neg_e8lit_eq_zero : arfOfForm (-E8lit) = 0 := by
  rw [arfOfForm_neg_eq E8lit e8lit_even, arfOfForm_e8lit_eq_zero]

/-- **THE NO-GO.** The proposed bridge `σ/8 ≡ arfOfForm M (mod 2)` for even unimodular `M` is FALSE,
refuted by `E₈`: an even unimodular lattice with `σ/8 = 1` (odd) but `arfOfForm = 0`. Equivalently, the
mod-16 factor of Rokhlin's theorem is irreducibly geometric and cannot be carried by any lattice Arf
invariant (the lattice `L/2L` Arf is identically `0`). The honest carrier remains
`SmoothSpinManifold4.topo : 2 ∣ σ/8` (ADR-003); van der Blij gives only `8 ∣ σ`
(`SKEFTHawking.eight_dvd_latticeSig`). -/
theorem lattice_arf_bridge_refuted :
    ¬ (∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ), IsEvenUnimodular M →
        ((latticeSig M / 8 : ℤ) : ZMod 2) = arfOfForm M) := by
  intro h
  have hE8 := h E8lit e8lit_even_unimodular
  rw [e8lit_latticeSig, arfOfForm_e8lit_eq_zero] at hE8
  norm_num at hE8

end SKEFTHawking.RokhlinArfNoGo
