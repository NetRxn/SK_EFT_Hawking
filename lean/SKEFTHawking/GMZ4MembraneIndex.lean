/-
# Phase 5q.H — the Guillou–Marin ℤ/4 membrane index (the coefficient split, PINNED)

`KernelNoGos` fork `fk-mod2-membrane-index-cannot-reach-nonorientable-stratum` established that the
**mod-2** membrane index `D·F + 𝒪(D) + d(C)` cannot reach a nonorientable characteristic surface:
any `μ` with `μ(x+y) = μ x + μ y + B x y` forces `B v v = 0` (put `x = y = v`; `μ v + μ v = 0` in
`ZMod 2`), refuted concretely at `stdQuadratic 1` — the ℝP² half of the `(ℝP⁴, ℝP²)` generator, where
`B 1 1 = 1` (`MembraneIndex.no_mod2_index_on_rp2`). That fork recorded that the repair needs the
Guillou–Marin **ℤ/4-resolution** index and that its coefficient split must NOT be guessed.

## The split, from the primary source

Read directly (lead, 2026-07-28) from **M. R. Klug, "A relative version of Rochlin's theorem",
arXiv:2011.12418v3, §6 p. 18**, which follows Matsumoto [Mat86] and Guillou–Marin [GM77]. For a
characteristic (not necessarily orientable) surface `F` in an oriented `X⁴`, and `x ∈ H₁(F;ℤ/2)`
represented by a curve `C ⊆ F` bounding an immersed orientable membrane `D` in `X`:

    e_F(x)  =  n(D) + 2(D · F) + 2 d(C)   (mod 4)

* `n(D)` — the **framing** of `D`: the number of right-handed **HALF**-twists of the line subbundle
  `ν(C ⊆ F) ⊆ ν(D)|_∂D`, under the orientation convention that `(r_D, C, e₁, e₂)` agrees with the
  ambient orientation of `X`. Half-twists are needed exactly because `F` need not be oriented — this
  is the whole point, and it is the term that carries the escape below.
* `D · F` — the number of intersection points of `D` with `F`.
* `d(C)` — the number of double points of `C`.

Klug states the resulting identity as `e_S(x+y) = e_S(x) + e_S(y) + 2(x·y)` (p. 14), and the
orientable comparison as `n(D) = 2𝒪(D)`, whence `e_F = 2 q_F` and `β(F) = 4 Arf(F)` (p. 18).
The congruence itself (Theorem 5, p. 19, Guillou–Marin) is `σ(X) = F·F + 2β(F) (mod 16)` — which is
exactly the in-tree `GuillouMarinBridge.GMrelation`, so the algebra layer already matches the source.

## What this file adds

§1 packages the three geometric counts with the additivity laws Klug proves, and derives the
`Z4Quadratic` refinement identity from them — so the split above is encoded as a *construction*,
not asserted. §2 is the sharp statement of **why** ℤ/4 escapes where mod-2 dies, with the ℝP²
contrast pair. §3 closes the loop: assuming the *orientable* comparison `n = 2𝒪` re-derives the
mod-2 obstruction, so the escape is powered by the half-twists and by nothing else.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.MembraneIndex

namespace SKEFTHawking.GMZ4MembraneIndex

open SKEFTHawking.Brown
open SKEFTHawking.Brown.Z4Quadratic (stdQuadratic)

/-- Every element of an `ι → ZMod 2` is its own additive inverse — the step that makes the
polarizations below *evaluations at `0`*. -/
theorem self_add_self {ι : Type*} (v : ι → ZMod 2) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = a
  revert a
  decide

/-- Pure `ZMod` arithmetic: `2 a = 2 b` in `ZMod 4` pins `a mod 2 = b`. -/
theorem castHom_of_two_mul_eq_embed2 {a : ZMod 4} {b : ZMod 2} (h : 2 * a = embed2 b) :
    (ZMod.castHom (show (2 : ℕ) ∣ 4 by norm_num) (ZMod 2)) a = b := by
  revert h
  revert a b
  decide

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1. The three counts, and the index they assemble -/

/-- **The Guillou–Marin ℤ/4 membrane data** (Klug §6 p. 18 / Matsumoto / Guillou–Marin). One value
per class `x ∈ H₁(F;ℤ/2)`, together with the additivity laws that hold for the geometric counts:
`n` and `D·F` are additive under taking the union of representing curves, while the double-point
count picks up the intersection number, `d(C_x ∪ C_y) = d(C_x) + d(C_y) + x·y` (Klug p. 14).

⚠ `framing` is `ZMod 4`-valued because `n(D)` counts **half**-twists. Making it `ZMod 2`-valued (a
whole-twist count `𝒪(D)`) is exactly the mod-2 index, which §3 shows is obstructed. -/
structure Z4MembraneData (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- `n(D)` — the framing of the membrane, in right-handed HALF-twists. -/
  framing : (ι → ZMod 2) → ZMod 4
  /-- `D · F` — the membrane/surface intersection count. -/
  meets : (ι → ZMod 2) → ZMod 2
  /-- `d(C)` — the double-point count of the representing curve. -/
  doubles : (ι → ZMod 2) → ZMod 2
  /-- The surface's own mod-2 intersection form on `H₁(F;ℤ/2)`. -/
  B : (ι → ZMod 2) → (ι → ZMod 2) → ZMod 2
  /-- The framing is additive under union of membranes. -/
  framing_add : ∀ x y, framing (x + y) = framing x + framing y
  /-- The intersection count is additive under union of membranes. -/
  meets_add : ∀ x y, meets (x + y) = meets x + meets y
  /-- `d(C_x ∪ C_y) = d(C_x) + d(C_y) + x·y` — the union creates `x·y` new double points. -/
  doubles_add : ∀ x y, doubles (x + y) = doubles x + doubles y + B x y
  /-- The intersection form is additive in its left argument. -/
  B_add_left : ∀ x y z, B (x + y) z = B x z + B y z
  /-- The intersection form is symmetric. -/
  B_symm : ∀ x y, B x y = B y x

namespace Z4MembraneData

variable (M : Z4MembraneData ι)

/-- **THE INDEX: `n(D) + 2(D·F) + 2d(C)`** — Klug §6 p. 18, verbatim in the coefficients. -/
def index (x : ι → ZMod 2) : ZMod 4 :=
  M.framing x + embed2 (M.meets x) + embed2 (M.doubles x)

/-- **The index refines the intersection form**, `e(x+y) = e x + e y + 2(x·y)` — derived from the
three additivity laws, not assumed. The `2` on `B x y` comes from `d`'s defect passing through the
`embed2` on the double-point term; the framing and intersection terms contribute nothing to it. -/
theorem index_refine (x y : ι → ZMod 2) :
    M.index (x + y) = M.index x + M.index y + embed2 (M.B x y) := by
  simp only [index, M.framing_add, M.meets_add, M.doubles_add, embed2_add]
  ring

/-- Packaged as a `Z4Quadratic` once the polar form is known to be nondegenerate — the shape
`GuillouMarinBridge.GMrelation` consumes. -/
def toZ4Quadratic (nondeg : ∀ x, (∀ y, M.B x y = 0) → x = 0) : Z4Quadratic ι where
  q := M.index
  B := M.B
  refine' := M.index_refine
  B_add_left := M.B_add_left
  B_symm := M.B_symm
  nondeg := nondeg

/-- `B 0 y = 0`, from left additivity. -/
theorem B_zero_left (y : ι → ZMod 2) : M.B 0 y = 0 := by
  have h := M.B_add_left 0 0 y
  rw [add_zero] at h
  simpa using h.symm

/-- The three counts all vanish on `0`, hence so does the index. -/
theorem index_zero : M.index 0 = 0 := by
  have hf : M.framing 0 = 0 := by
    have h := M.framing_add 0 0
    rw [add_zero] at h
    simpa using h.symm
  have hm : M.meets 0 = 0 := by
    have h := M.meets_add 0 0
    rw [add_zero] at h
    simpa using h.symm
  have hd : M.doubles 0 = 0 := by
    have h := M.doubles_add 0 0
    rw [add_zero, M.B_zero_left] at h
    simpa using h.symm
  simp [index, hf, hm, hd, embed2]

end Z4MembraneData

/-! ## §2. WHY ℤ/4 ESCAPES — the polarization, run in both coefficient rings

Polarizing at `x = y = v` uses `v + v = 0`:

* **mod 2:** `0 = μ v + μ v + B v v = B v v`, because `μ v + μ v = 0`. The index term *dies* and the
  obstruction is unavoidable — this is `MembraneIndex.refines_forces_alternating`.
* **mod 4:** `0 = e v + e v + 2·(B v v)`, i.e. `2·(B v v) = 2·e v`. The index term *survives* as
  `2 e v` and absorbs the defect; nothing forces `B v v = 0`. What is forced instead is the
  compatibility that the index reduces mod 2 to the self-intersection. -/

/-- **THE ℤ/4 POLARIZATION.** `2·q v = 2·(B v v)` in `ZMod 4` — the index term survives rather than
dying, which is the entire difference from the mod-2 case. -/
theorem two_mul_q_self (Q : Z4Quadratic ι) (v : ι → ZMod 2) :
    2 * Q.q v = embed2 (Q.B v v) := by
  have hvv : v + v = 0 := self_add_self v
  have h := Q.refine' v v
  rw [hvv, Q.q_zero] at h
  generalize Q.q v = a at h ⊢
  generalize Q.B v v = b at h ⊢
  revert h
  revert a b
  decide

/-- **The forced content is a CONGRUENCE, not a vanishing:** the ℤ/4 index reduces mod 2 to the
self-intersection. This is the honest replacement for `B v v = 0`; on an orientable surface every
`B v v = 0` and one recovers `q v ∈ {0, 2}`, i.e. Klug's `e_F = 2 q_F`. -/
theorem q_self_reduce (Q : Z4Quadratic ι) (v : ι → ZMod 2) :
    (ZMod.castHom (show (2 : ℕ) ∣ 4 by norm_num) (ZMod 2)) (Q.q v) = Q.B v v :=
  castHom_of_two_mul_eq_embed2 (two_mul_q_self Q v)

/-- **THE CONTRAST, ON THE ℝP² FORM.** `stdQuadratic 1` is the rank-1 odd form `B 1 1 = 1` carried by
the ℝP² half of the `(ℝP⁴, ℝP²)` generator — the exact place the mod-2 index was refuted. No mod-2
index exists there; a ℤ/4 index does, and the form's own `q` is one. So the ℤ/4-resolution route is
open at precisely the point that closed the mod-2 route. -/
theorem z4_index_exists_on_rp2 :
    ∃ e : (Fin 1 → ZMod 2) → ZMod 4,
      ∀ x y, e (x + y) = e x + e y + embed2 ((stdQuadratic 1).B x y) :=
  ⟨(stdQuadratic 1).q, (stdQuadratic 1).refine'⟩

/-- **The contrast as one statement** — mod-2 impossible AND ℤ/4 possible, on the same form. Neither
conjunct implies the other and the pair is the content: it is what turns
`fk-mod2-membrane-index-cannot-reach-nonorientable-stratum` from a dead end into a *routing*
decision. -/
theorem mod2_refuted_but_z4_realized_on_rp2 :
    (¬ ∃ μ : (Fin 1 → ZMod 2) → ZMod 2,
        ∀ x y, μ (x + y) = μ x + μ y + (stdQuadratic 1).B x y)
    ∧ (∃ e : (Fin 1 → ZMod 2) → ZMod 4,
        ∀ x y, e (x + y) = e x + e y + embed2 ((stdQuadratic 1).B x y)) :=
  ⟨MembraneIndex.no_mod2_index_on_rp2, z4_index_exists_on_rp2⟩

/-- **The surviving term is genuinely nonzero on ℝP².** `2 · q(1) ≠ 0` in `ZMod 4` for the standard
rank-1 form, so the escape in `two_mul_q_self` is not vacuous bookkeeping — there really is a term
there that the mod-2 reduction would have destroyed. -/
theorem two_mul_q_ne_zero_on_rp2 : 2 * (stdQuadratic 1).q 1 ≠ 0 := by
  rw [two_mul_q_self]
  decide

/-! ## §3. The orientable comparison RE-DERIVES the obstruction

Klug p. 18: if `F` is orientable then `n(D) = 2𝒪(D)`, hence `e_F = 2 q_F` and `β(F) = 4 Arf(F)`.
Read contrapositively, that comparison is exactly the hypothesis under which the ℤ/4 index collapses
back onto a mod-2 one — so a `Z4MembraneData` whose framing is a whole-twist count inherits the
mod-2 no-go verbatim. This is the check that §1's `framing : … → ZMod 4` is load-bearing and not
decoration. -/

/-- **A whole-twist framing forces the alternating obstruction back.** If `n = 2𝒪` for an additive
mod-2 twist count `𝒪` — Klug's orientable comparison — then `B v v = 0` for every `v`, i.e. the data
can only describe an *orientable* characteristic surface. Contrapositive: on the nonorientable
stratum the framing must carry a genuine half-twist, which is precisely why the index is `ZMod 4`. -/
theorem orientable_framing_forces_alternating (M : Z4MembraneData ι)
    (o : (ι → ZMod 2) → ZMod 2) (ho : ∀ x, M.framing x = embed2 (o x))
    (v : ι → ZMod 2) : M.B v v = 0 := by
  -- Polarize the index at `x = y = v`, using `v + v = 0`.
  have hvv : v + v = 0 := self_add_self v
  have h := M.index_refine v v
  rw [hvv, M.index_zero] at h
  -- With a whole-twist framing the index is `embed2` of a mod-2 quantity, so `2 * index v = 0`.
  have hind : M.index v = embed2 (o v + M.meets v + M.doubles v) := by
    simp only [Z4MembraneData.index, ho, embed2_add]
  have hkill : M.index v + M.index v = 0 := by
    rw [hind]
    generalize o v + M.meets v + M.doubles v = c
    revert c
    decide
  -- Hence `embed2 (B v v) = 0`, and `embed2` is injective.
  have hz : embed2 (M.B v v) = 0 := by
    have : M.index v + M.index v + embed2 (M.B v v) = 0 := h.symm
    rw [hkill, zero_add] at this
    exact this
  revert hz
  generalize M.B v v = b
  revert b
  decide
