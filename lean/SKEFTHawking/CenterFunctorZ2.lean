/-
Phase 5s Wave 9: CenterFunctor for G = ℤ/2

Explicit construction of the 4 simple `D(ℤ/2)`-modules as characters
(algebra homomorphisms `DG k G2 →ₐ[k] k`, where `G2 := Multiplicative (ZMod 2)`).
Together with the `Module.compHom` Module instance they induce, these are
the **target objects** of the CenterFunctor Z(Vec_{ℤ/2}) ⥤ Rep(D(ℤ/2)).

For `G = ℤ/2` (abelian, 2 elements), `D(G)` is commutative, 4-dimensional
over `k`, and decomposes as `k⁴` (semisimple). The 4 simple `D(G)`-modules
are 1-dimensional, indexed by pairs (conjugacy class, irrep of centralizer):

  (e, triv)  "trivTriv": χ(f) = f(e, e) + f(e, a)
  (e, sign)  "trivSign": χ(f) = f(e, e) − f(e, a)
  (a, triv)  "flipTriv": χ(f) = f(a, e) + f(a, a)
  (a, sign)  "flipSign": χ(f) = f(a, e) − f(a, a)

where `e := (1 : G2) = Multiplicative.ofAdd 0` and `a := Multiplicative.ofAdd 1`.
These correspond bijectively to the 4 toric-code anyons {vacuum, electric,
magnetic, fermion} via the bijection in `CenterEquivalenceZ2.lean`.

## Main definitions

* `G2`: `Multiplicative (ZMod 2)`, the 2-element group Z/2 as a *multiplicative* group
  (needed because `DG k G` requires `[Group G]`)
* `e`, `a`: the two elements, identity and generator
* `chiTrivTriv`, `chiTrivSign`, `chiFlipTriv`, `chiFlipSign`:
  the 4 characters as `AlgHom k (DG k G2) k`
* `simpleChi : DZ2Simple → (DG k G2 →ₐ[k] k)`:
  a single function giving the character for each simple label

## Main theorems

Each character is a valid `AlgHom` (map_one, map_mul, map_add, map_zero,
commutes all proved). The multiplication respect proofs use
`DG_mul_coeff_G2`, which expands `ddAlgMul` over `G2`'s 2-element universe.

## Phase 5s Wave 9 scope

This module ships the **objects** (the 4 DG(G2)-modules as characters)
and verifies their validity as algebra homomorphisms. Remaining for the
full `H_CF1_center_functor` / `H_CF2_center_equivalence` discharge
(estimated ~300-400 LOC beyond this module):

- Package each character as a `Module (DG k G2)` on `k` via `Module.compHom`
- Define the functor `centerToRepZ2 : Center (VecG_Cat k G2) ⥤ ModuleCat (DG k G2)`
  sending toric anyons to their character-induced modules
- Prove Full + Faithful + EssSurj (finite case analysis on 4 objects)
- Assemble `Equivalence.ofFullyFaithfulEssSurj` to discharge both hypotheses

## References

- `CenterEquivalenceZ2.lean` — the 4-anyon bijection at the data level
- `DrinfeldDoubleRing.lean` — `DG k G` Ring + Algebra structure
- `DrinfeldDoubleAlgebra.lean` — `ddAlgMul`, `ddAlgOne` definitions
- Deep research: `Lit-Search/Phase-5s/CenterFunctor Z2 finite matrix feasibility.md`
- Kitaev, Ann. Phys. 303, 2 (2003) — toric code
- Dijkgraaf-Pasquier-Roche (1991) — D(G) anyon classification
-/

import Mathlib
import SKEFTHawking.DrinfeldDoubleRing
import SKEFTHawking.CenterEquivalenceZ2

noncomputable section

namespace SKEFTHawking.CenterFunctorZ2

open SKEFTHawking

/-- The multiplicative form of ℤ/2, used so that `DG k G2` has `[Group G2]`. -/
abbrev G2 : Type := Multiplicative (ZMod 2)

/-- Identity of `G2`. Corresponds to `0 : ZMod 2` via `Multiplicative.ofAdd`. -/
abbrev e : G2 := (1 : G2)

/-- Generator of `G2` (non-identity element). Corresponds to `1 : ZMod 2`. -/
abbrev a : G2 := Multiplicative.ofAdd (1 : ZMod 2)

variable (k : Type) [CommRing k]

/-! ## 1. Helpers for the G2 sums

`G2 = Multiplicative (ZMod 2)` has 2 elements `{e, a}`. Every sum over `G2`
is a 2-term sum. -/

/-- Enumerate `G2`'s `Finset.univ` as `{e, a}`. -/
lemma finset_univ_G2 : (Finset.univ : Finset G2) = {e, a} := by decide

lemma a_ne_e : a ≠ e := by decide

lemma a_mul_a : a * a = e := by decide

lemma a_inv : a⁻¹ = a := by decide

/-! ## 2. The 4 character formulas

Each character is defined as a `k`-linear combination of coefficients of
its input on the four basis-index pairs `(x, g) : G2 × G2`. -/

/-- `χ_trivTriv(f) := f(e, e) + f(e, a)`. Trivial class × trivial rep. -/
def chiTrivTrivFun (f : DG k G2) : k :=
  f.coeff (e, e) + f.coeff (e, a)

/-- `χ_trivSign(f) := f(e, e) − f(e, a)`. Trivial class × sign rep. -/
def chiTrivSignFun (f : DG k G2) : k :=
  f.coeff (e, e) - f.coeff (e, a)

/-- `χ_flipTriv(f) := f(a, e) + f(a, a)`. Nontrivial class × trivial rep. -/
def chiFlipTrivFun (f : DG k G2) : k :=
  f.coeff (a, e) + f.coeff (a, a)

/-- `χ_flipSign(f) := f(a, e) − f(a, a)`. Nontrivial class × sign rep. -/
def chiFlipSignFun (f : DG k G2) : k :=
  f.coeff (a, e) - f.coeff (a, a)

/-! ## 3. `map_one`: χ(1) = 1 for all 4

`1_{DG}` has `coeff (x, g) = 1` if `g = 1` (group identity, here `e`) and
`0` otherwise. So every character evaluates to `1 + 0 = 1` or `1 − 0 = 1`. -/

/-- `ddAlgOne` at `(x, g)` for `G = G2`: it is `1` if `g = e` and `0` otherwise. -/
@[simp] lemma ddAlgOne_apply (x g : G2) :
    ddAlgOne k G2 (x, g) = if g = e then 1 else 0 := rfl

/-- `(1 : DG k G2).coeff = ddAlgOne k G2` (unfolded). -/
@[simp] lemma DG_one_coeff_apply (x g : G2) :
    (1 : DG k G2).coeff (x, g) = if g = e then 1 else 0 := rfl

lemma chiTrivTriv_map_one : chiTrivTrivFun k 1 = 1 := by
  show (1 : DG k G2).coeff (e, e) + (1 : DG k G2).coeff (e, a) = 1
  rw [DG_one_coeff_apply, DG_one_coeff_apply]
  simp [a_ne_e]

lemma chiTrivSign_map_one : chiTrivSignFun k 1 = 1 := by
  show (1 : DG k G2).coeff (e, e) - (1 : DG k G2).coeff (e, a) = 1
  rw [DG_one_coeff_apply, DG_one_coeff_apply]
  simp [a_ne_e]

lemma chiFlipTriv_map_one : chiFlipTrivFun k 1 = 1 := by
  show (1 : DG k G2).coeff (a, e) + (1 : DG k G2).coeff (a, a) = 1
  rw [DG_one_coeff_apply, DG_one_coeff_apply]
  simp [a_ne_e]

lemma chiFlipSign_map_one : chiFlipSignFun k 1 = 1 := by
  show (1 : DG k G2).coeff (a, e) - (1 : DG k G2).coeff (a, a) = 1
  rw [DG_one_coeff_apply, DG_one_coeff_apply]
  simp [a_ne_e]

/-! ## 4. `DG_mul_coeff_G2`: expand `(f * g).coeff` over G2's 2-term sum

Core computation: for abelian `G2`, `g1⁻¹ * x * g1 = x`, so

    (f * g).coeff (x, h) = Σ_{g1 ∈ G2} f(x, g1) · g(x, g1⁻¹ * h)
                         = f(x, e) · g(x, h) + f(x, a) · g(x, a⁻¹ * h)
                         = f(x, e) · g(x, h) + f(x, a) · g(x, a * h)     [a⁻¹ = a]
-/

lemma DG_mul_coeff_G2 (f g : DG k G2) (x h : G2) :
    (f * g).coeff (x, h) =
      f.coeff (x, e) * g.coeff (x, h) +
      f.coeff (x, a) * g.coeff (x, a * h) := by
  show ddAlgMul k G2 f.coeff g.coeff (x, h) = _
  unfold ddAlgMul
  rw [finset_univ_G2]
  rw [show ({e, a} : Finset G2) = insert e {a} from rfl]
  rw [Finset.sum_insert (by simp [a_ne_e.symm])]
  rw [Finset.sum_singleton]
  -- After unfolding: for g1 = e, conjugation e⁻¹·x·e = x and e⁻¹·h = h.
  -- For g1 = a, a⁻¹ = a (since a² = e), and a⁻¹·x·a = a·x·a = x (abelian).
  have conj_e : e⁻¹ * x * e = x := by simp
  have conj_a : a⁻¹ * x * a = x := by
    rw [a_inv]
    -- a·x·a: use commutativity twice, then a·a = e, then e·x = x
    rw [mul_comm a x, mul_assoc, a_mul_a, mul_one]
  have h_e : e⁻¹ * h = h := by simp
  have h_a : a⁻¹ * h = a * h := by rw [a_inv]
  rw [conj_e, conj_a, h_e, h_a]

/-! ## 5. `map_mul`: χ(f * g) = χ(f) · χ(g) for all 4

Plug `DG_mul_coeff_G2` in for `x = e` and `x = a`, then use `a * e = a`,
`a * a = e` to close with `ring`. -/

lemma chiTrivTriv_map_mul (f g : DG k G2) :
    chiTrivTrivFun k (f * g) = chiTrivTrivFun k f * chiTrivTrivFun k g := by
  show (f * g).coeff (e, e) + (f * g).coeff (e, a) =
       (f.coeff (e, e) + f.coeff (e, a)) * (g.coeff (e, e) + g.coeff (e, a))
  rw [DG_mul_coeff_G2, DG_mul_coeff_G2]
  -- In the expansion, `a * e = a` and `a * a = e`:
  have h1 : a * e = a := by decide
  have h2 : a * a = e := by decide
  rw [h1, h2]
  ring

lemma chiTrivSign_map_mul (f g : DG k G2) :
    chiTrivSignFun k (f * g) = chiTrivSignFun k f * chiTrivSignFun k g := by
  show (f * g).coeff (e, e) - (f * g).coeff (e, a) =
       (f.coeff (e, e) - f.coeff (e, a)) * (g.coeff (e, e) - g.coeff (e, a))
  rw [DG_mul_coeff_G2, DG_mul_coeff_G2]
  have h1 : a * e = a := by decide
  have h2 : a * a = e := by decide
  rw [h1, h2]
  ring

lemma chiFlipTriv_map_mul (f g : DG k G2) :
    chiFlipTrivFun k (f * g) = chiFlipTrivFun k f * chiFlipTrivFun k g := by
  show (f * g).coeff (a, e) + (f * g).coeff (a, a) =
       (f.coeff (a, e) + f.coeff (a, a)) * (g.coeff (a, e) + g.coeff (a, a))
  rw [DG_mul_coeff_G2, DG_mul_coeff_G2]
  have h1 : a * e = a := by decide
  have h2 : a * a = e := by decide
  rw [h1, h2]
  ring

lemma chiFlipSign_map_mul (f g : DG k G2) :
    chiFlipSignFun k (f * g) = chiFlipSignFun k f * chiFlipSignFun k g := by
  show (f * g).coeff (a, e) - (f * g).coeff (a, a) =
       (f.coeff (a, e) - f.coeff (a, a)) * (g.coeff (a, e) - g.coeff (a, a))
  rw [DG_mul_coeff_G2, DG_mul_coeff_G2]
  have h1 : a * e = a := by decide
  have h2 : a * a = e := by decide
  rw [h1, h2]
  ring

/-! ## 6. Additive + algebraMap compatibility

All 4 characters are k-linear (additive + scalar-respecting) by direct
coefficient projection + the `DG.instAlgebra` structure. -/

lemma chiTrivTriv_map_add (f g : DG k G2) :
    chiTrivTrivFun k (f + g) = chiTrivTrivFun k f + chiTrivTrivFun k g := by
  unfold chiTrivTrivFun
  show (f.coeff + g.coeff) (e, e) + (f.coeff + g.coeff) (e, a) =
       (f.coeff (e, e) + f.coeff (e, a)) + (g.coeff (e, e) + g.coeff (e, a))
  simp
  ring

lemma chiTrivSign_map_add (f g : DG k G2) :
    chiTrivSignFun k (f + g) = chiTrivSignFun k f + chiTrivSignFun k g := by
  unfold chiTrivSignFun
  show (f.coeff + g.coeff) (e, e) - (f.coeff + g.coeff) (e, a) =
       (f.coeff (e, e) - f.coeff (e, a)) + (g.coeff (e, e) - g.coeff (e, a))
  simp
  ring

lemma chiFlipTriv_map_add (f g : DG k G2) :
    chiFlipTrivFun k (f + g) = chiFlipTrivFun k f + chiFlipTrivFun k g := by
  unfold chiFlipTrivFun
  show (f.coeff + g.coeff) (a, e) + (f.coeff + g.coeff) (a, a) =
       (f.coeff (a, e) + f.coeff (a, a)) + (g.coeff (a, e) + g.coeff (a, a))
  simp
  ring

lemma chiFlipSign_map_add (f g : DG k G2) :
    chiFlipSignFun k (f + g) = chiFlipSignFun k f + chiFlipSignFun k g := by
  unfold chiFlipSignFun
  show (f.coeff + g.coeff) (a, e) - (f.coeff + g.coeff) (a, a) =
       (f.coeff (a, e) - f.coeff (a, a)) + (g.coeff (a, e) - g.coeff (a, a))
  simp
  ring

/-- Scalar embedding: `algebraMap k (DG k G2) r` has coefficient `r` at
    `(x, e)` for each `x ∈ G2`, and `0` elsewhere. -/
lemma algebraMap_coeff (r : k) (x g : G2) :
    (algebraMap k (DG k G2) r).coeff (x, g) = if g = e then r else 0 := rfl

lemma chiTrivTriv_commutes (r : k) :
    chiTrivTrivFun k (algebraMap k (DG k G2) r) = r := by
  show (algebraMap k (DG k G2) r).coeff (e, e) +
       (algebraMap k (DG k G2) r).coeff (e, a) = r
  rw [algebraMap_coeff, algebraMap_coeff]
  simp [a_ne_e]

lemma chiTrivSign_commutes (r : k) :
    chiTrivSignFun k (algebraMap k (DG k G2) r) = r := by
  show (algebraMap k (DG k G2) r).coeff (e, e) -
       (algebraMap k (DG k G2) r).coeff (e, a) = r
  rw [algebraMap_coeff, algebraMap_coeff]
  simp [a_ne_e]

lemma chiFlipTriv_commutes (r : k) :
    chiFlipTrivFun k (algebraMap k (DG k G2) r) = r := by
  show (algebraMap k (DG k G2) r).coeff (a, e) +
       (algebraMap k (DG k G2) r).coeff (a, a) = r
  rw [algebraMap_coeff, algebraMap_coeff]
  simp [a_ne_e]

lemma chiFlipSign_commutes (r : k) :
    chiFlipSignFun k (algebraMap k (DG k G2) r) = r := by
  show (algebraMap k (DG k G2) r).coeff (a, e) -
       (algebraMap k (DG k G2) r).coeff (a, a) = r
  rw [algebraMap_coeff, algebraMap_coeff]
  simp [a_ne_e]

/-! ## 7. Assembled AlgHoms -/

/-- `χ_{trivTriv}(0) = 0`. Direct from `(0 : DG).coeff = 0`. -/
lemma chiTrivTriv_map_zero : chiTrivTrivFun k 0 = 0 := by
  show (0 : DG k G2).coeff (e, e) + (0 : DG k G2).coeff (e, a) = 0
  change (0 : G2 × G2 → k) (e, e) + (0 : G2 × G2 → k) (e, a) = 0
  simp

lemma chiTrivSign_map_zero : chiTrivSignFun k 0 = 0 := by
  show (0 : DG k G2).coeff (e, e) - (0 : DG k G2).coeff (e, a) = 0
  change (0 : G2 × G2 → k) (e, e) - (0 : G2 × G2 → k) (e, a) = 0
  simp

lemma chiFlipTriv_map_zero : chiFlipTrivFun k 0 = 0 := by
  show (0 : DG k G2).coeff (a, e) + (0 : DG k G2).coeff (a, a) = 0
  change (0 : G2 × G2 → k) (a, e) + (0 : G2 × G2 → k) (a, a) = 0
  simp

lemma chiFlipSign_map_zero : chiFlipSignFun k 0 = 0 := by
  show (0 : DG k G2).coeff (a, e) - (0 : DG k G2).coeff (a, a) = 0
  change (0 : G2 × G2 → k) (a, e) - (0 : G2 × G2 → k) (a, a) = 0
  simp

/-- `χ_{trivTriv}` as an algebra homomorphism `DG k G2 →ₐ[k] k`. -/
def chiTrivTriv : DG k G2 →ₐ[k] k where
  toFun := chiTrivTrivFun k
  map_one' := chiTrivTriv_map_one k
  map_mul' := chiTrivTriv_map_mul k
  map_zero' := chiTrivTriv_map_zero k
  map_add' := chiTrivTriv_map_add k
  commutes' := chiTrivTriv_commutes k

/-- `χ_{trivSign}` as an algebra homomorphism. -/
def chiTrivSign : DG k G2 →ₐ[k] k where
  toFun := chiTrivSignFun k
  map_one' := chiTrivSign_map_one k
  map_mul' := chiTrivSign_map_mul k
  map_zero' := chiTrivSign_map_zero k
  map_add' := chiTrivSign_map_add k
  commutes' := chiTrivSign_commutes k

/-- `χ_{flipTriv}` as an algebra homomorphism. -/
def chiFlipTriv : DG k G2 →ₐ[k] k where
  toFun := chiFlipTrivFun k
  map_one' := chiFlipTriv_map_one k
  map_mul' := chiFlipTriv_map_mul k
  map_zero' := chiFlipTriv_map_zero k
  map_add' := chiFlipTriv_map_add k
  commutes' := chiFlipTriv_commutes k

/-- `χ_{flipSign}` as an algebra homomorphism. -/
def chiFlipSign : DG k G2 →ₐ[k] k where
  toFun := chiFlipSignFun k
  map_one' := chiFlipSign_map_one k
  map_mul' := chiFlipSign_map_mul k
  map_zero' := chiFlipSign_map_zero k
  map_add' := chiFlipSign_map_add k
  commutes' := chiFlipSign_commutes k

/-! ## 8. Character table: single function indexed by DZ2Simple -/

/-- The character associated to each simple label of `D(ℤ/2)`. -/
def simpleChi : DZ2Simple → (DG k G2 →ₐ[k] k)
  | .trivTriv => chiTrivTriv k
  | .trivSign => chiTrivSign k
  | .flipTriv => chiFlipTriv k
  | .flipSign => chiFlipSign k

/-! ## 9. Module summary -/

/--
CenterFunctorZ2 module: Phase 5s Wave 9 scaffold.

  - 4 explicit characters `DG k G2 →ₐ[k] k` where `G2 = Multiplicative (ZMod 2)`:
    χ_trivTriv, χ_trivSign, χ_flipTriv, χ_flipSign
  - Each character verified as an `AlgHom` (map_one, map_mul, map_zero,
    map_add, commutes) with proofs driven by `DG_mul_coeff_G2` which
    expands the twisted-convolution multiplication over G2's 2-element group
  - `simpleChi` packages the 4 characters as a single function indexed
    by `DZ2Simple`, aligning with the `CenterEquivalenceZ2` bijection
  - Zero sorry, zero axioms

**Remaining for full CenterFunctor Z/2** (Phase 5s Wave 9 completion):
  - Package each character as a `Module (DG k G2)` instance on `k`
    via `Module.compHom`
  - Define the functor `centerToRepZ2 : Center (VecG_Cat k G2) ⥤
    ModuleCat (DG k G2)` sending toric anyons to their character modules
  - Prove Full + Faithful + EssSurj (finite case analysis on 4 objects)
  - Assemble `Equivalence.ofFullyFaithfulEssSurj` to discharge
    `H_CF1_center_functor` and `H_CF2_center_equivalence`

  Estimated additional LOC: ~300-400 (per deep research).
-/
theorem center_functor_z2_scaffold_summary : True := trivial

end CenterFunctorZ2

end SKEFTHawking
