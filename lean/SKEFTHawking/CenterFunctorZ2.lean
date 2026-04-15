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

/-! ## 9. The simple DG(G2)-modules via `Module.compHom`

Each character `χ : DG k G2 →ₐ[k] k` gives a `Module (DG k G2)` structure
on `k` by `Module.compHom`. To keep the 4 module structures distinct as
Lean types (so typeclass inference doesn't collapse them), we use a
wrapper structure parameterized by the character. -/

/-- The 1-dimensional simple `D(G2)`-module associated to a character `χ`.
    Underlying type is `k`; the `D(G2)`-action is via `χ`.

    `k` is implicit so that instance declarations can write `SimpleModule χ`
    without having to re-thread `k` through each instance header. -/
@[ext] structure SimpleModule {k : Type} [CommRing k] (_χ : DG k G2 →ₐ[k] k) where
  /-- The underlying `k`-valued coordinate. -/
  val : k

namespace SimpleModule

variable {k : Type} [CommRing k]
variable (χ : DG k G2 →ₐ[k] k)

instance : Zero (SimpleModule χ) := ⟨⟨0⟩⟩
instance : Add (SimpleModule χ) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance : Neg (SimpleModule χ) := ⟨fun x => ⟨-x.val⟩⟩
instance : Sub (SimpleModule χ) := ⟨fun x y => ⟨x.val - y.val⟩⟩

@[simp] lemma val_zero : (0 : SimpleModule χ).val = 0 := rfl
@[simp] lemma val_add (x y : SimpleModule χ) : (x + y).val = x.val + y.val := rfl
@[simp] lemma val_neg (x : SimpleModule χ) : (-x).val = -x.val := rfl
@[simp] lemma val_sub (x y : SimpleModule χ) : (x - y).val = x.val - y.val := rfl

instance : AddCommGroup (SimpleModule χ) where
  add_assoc a b c := by ext; simp [add_assoc]
  zero_add a := by ext; simp
  add_zero a := by ext; simp
  add_comm a b := by ext; simp [add_comm]
  neg_add_cancel a := by ext; simp
  sub_eq_add_neg a b := by ext; simp [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- `k`-module structure on `SimpleModule χ`: scalar multiplication by `r : k`. -/
instance : SMul k (SimpleModule χ) := ⟨fun r x => ⟨r * x.val⟩⟩

@[simp] lemma val_smul (r : k) (x : SimpleModule χ) : (r • x).val = r * x.val := rfl

instance : Module k (SimpleModule χ) where
  smul_add r a b := by ext; simp [mul_add]
  smul_zero r := by ext; simp
  add_smul r s a := by ext; simp [add_mul]
  zero_smul a := by ext; simp
  one_smul a := by ext; simp
  mul_smul r s a := by ext; simp [mul_assoc]

/-- The `D(G2)`-module structure on `SimpleModule χ`, with `d · x := χ(d) · x`.
    Derived via `Module.compHom` from the `k`-module structure and the
    underlying `RingHom` of the algebra map `χ`. -/
noncomputable instance : Module (DG k G2) (SimpleModule χ) :=
  Module.compHom (SimpleModule χ) (χ : DG k G2 →+* k)

end SimpleModule

/-! ## 10. Package the 4 simples + verify distinct DG-actions -/

/-- The 4 simple `D(G2)`-modules, indexed by `DZ2Simple` labels.

    Returns the zero element of the corresponding module — enough to
    identify the underlying type; the content of the simple is in its
    module structure, not in any specific value. -/
def simpleMod : (s : DZ2Simple) → SimpleModule (simpleChi k s) := fun _ => ⟨0⟩

/-- Each simple module's DG action on the distinguished unit `⟨1⟩` recovers
    the character value: `d · ⟨1⟩ = ⟨χ(d)⟩`. This confirms the four module
    structures are genuinely different (one per character). -/
lemma basis_smul_one {χ : DG k G2 →ₐ[k] k} (d : DG k G2) :
    (d • (⟨1⟩ : SimpleModule χ)).val = χ d := by
  -- The DG-module structure on SimpleModule χ is via Module.compHom,
  -- which makes d • x = (χ d : k) • x. Then (r : k) • ⟨v⟩ = ⟨r * v⟩.
  show ((((χ : DG k G2 →+* k) d) • (⟨1⟩ : SimpleModule χ)) : SimpleModule χ).val = χ d
  simp

/-! ## 11. Character distinctness: `simpleChi` is injective

When the base ring `k` satisfies `(1 : k) ≠ -1` (i.e., `char k ≠ 2`),
the four characters are pairwise distinct. This is a prerequisite for
the Faithful/EssSurj proofs of the full CenterFunctor: the 4 simple
objects on the target side really are distinct objects. -/

/-- Character values on the basis element `DG.basis (a, g)` simplify to
    indicator-weighted constants. For a character `χ(f) = c_00 f(e,e) +
    c_01 f(e,a) + c_10 f(a,e) + c_11 f(a,a)` (only some coefficients
    nonzero), evaluating on `basis a' g'` picks out the single matching
    coefficient. We verify this for the four specific characters. -/
lemma chiTrivTriv_on_basis_ee :
    chiTrivTrivFun k (DG.basis k G2 e e) = 1 := by
  unfold chiTrivTrivFun
  show (DG.basis k G2 e e).coeff (e, e) + (DG.basis k G2 e e).coeff (e, a) = 1
  show ddBasis k G2 e e (e, e) + ddBasis k G2 e e (e, a) = 1
  unfold ddBasis
  simp [a_ne_e]

lemma chiTrivTriv_on_basis_ea :
    chiTrivTrivFun k (DG.basis k G2 e a) = 1 := by
  show ddBasis k G2 e a (e, e) + ddBasis k G2 e a (e, a) = 1
  unfold ddBasis; simp [a_ne_e, a_ne_e.symm]

lemma chiTrivSign_on_basis_ea :
    chiTrivSignFun k (DG.basis k G2 e a) = -1 := by
  show ddBasis k G2 e a (e, e) - ddBasis k G2 e a (e, a) = -1
  unfold ddBasis; simp [a_ne_e.symm]

lemma chiFlipTriv_on_basis_ae :
    chiFlipTrivFun k (DG.basis k G2 a e) = 1 := by
  show ddBasis k G2 a e (a, e) + ddBasis k G2 a e (a, a) = 1
  unfold ddBasis; simp [a_ne_e]

lemma chiFlipSign_on_basis_aa :
    chiFlipSignFun k (DG.basis k G2 a a) = -1 := by
  show ddBasis k G2 a a (a, e) - ddBasis k G2 a a (a, a) = -1
  unfold ddBasis; simp [a_ne_e.symm]

/-- The three "cross-class" characters (not involving index (e, a) or (a, a))
    vanish on `DG.basis e e`. -/
lemma chiTrivSign_on_basis_ee : chiTrivSignFun k (DG.basis k G2 e e) = 1 := by
  show ddBasis k G2 e e (e, e) - ddBasis k G2 e e (e, a) = 1
  unfold ddBasis; simp [a_ne_e]

lemma chiFlipTriv_on_basis_ee : chiFlipTrivFun k (DG.basis k G2 e e) = 0 := by
  show ddBasis k G2 e e (a, e) + ddBasis k G2 e e (a, a) = 0
  unfold ddBasis; simp [a_ne_e.symm]

lemma chiFlipSign_on_basis_ee : chiFlipSignFun k (DG.basis k G2 e e) = 0 := by
  show ddBasis k G2 e e (a, e) - ddBasis k G2 e e (a, a) = 0
  unfold ddBasis; simp [a_ne_e.symm]

/-! ### Pairwise distinctness lemmas

Each lemma picks a specific `DG.basis` probe that separates the two
characters via a concrete value difference. The hypothesis `h : (1 : k) ≠ 0`
(nontriviality) or `h2 : (1 : k) ≠ -1` (char ≠ 2) is supplied per-pair. -/

/-- `chiTrivTriv ≠ chiFlipTriv` when `(1 : k) ≠ 0`. Probe: `basis e e` (gives 1 vs 0). -/
lemma chiTrivTriv_ne_chiFlipTriv (h : (1 : k) ≠ 0) :
    chiTrivTriv k ≠ chiFlipTriv k := by
  intro heq
  apply h
  have := congrArg (· (DG.basis k G2 e e)) heq
  simpa [chiTrivTriv, chiFlipTriv, chiTrivTriv_on_basis_ee,
         chiFlipTriv_on_basis_ee] using this

/-- `chiTrivTriv ≠ chiFlipSign` when `(1 : k) ≠ 0`. -/
lemma chiTrivTriv_ne_chiFlipSign (h : (1 : k) ≠ 0) :
    chiTrivTriv k ≠ chiFlipSign k := by
  intro heq
  apply h
  have := congrArg (· (DG.basis k G2 e e)) heq
  simpa [chiTrivTriv, chiFlipSign, chiTrivTriv_on_basis_ee,
         chiFlipSign_on_basis_ee] using this

/-- `chiTrivSign ≠ chiFlipTriv` when `(1 : k) ≠ 0`. -/
lemma chiTrivSign_ne_chiFlipTriv (h : (1 : k) ≠ 0) :
    chiTrivSign k ≠ chiFlipTriv k := by
  intro heq
  apply h
  have := congrArg (· (DG.basis k G2 e e)) heq
  simpa [chiTrivSign, chiFlipTriv, chiTrivSign_on_basis_ee,
         chiFlipTriv_on_basis_ee] using this

/-- `chiTrivSign ≠ chiFlipSign` when `(1 : k) ≠ 0`. -/
lemma chiTrivSign_ne_chiFlipSign (h : (1 : k) ≠ 0) :
    chiTrivSign k ≠ chiFlipSign k := by
  intro heq
  apply h
  have := congrArg (· (DG.basis k G2 e e)) heq
  simpa [chiTrivSign, chiFlipSign, chiTrivSign_on_basis_ee,
         chiFlipSign_on_basis_ee] using this

/-- `chiTrivTriv ≠ chiTrivSign` when `(1 : k) ≠ -1`. Probe: `basis e a` (gives 1 vs -1). -/
lemma chiTrivTriv_ne_chiTrivSign (h : (1 : k) ≠ -1) :
    chiTrivTriv k ≠ chiTrivSign k := by
  intro heq
  apply h
  have := congrArg (· (DG.basis k G2 e a)) heq
  simpa [chiTrivTriv, chiTrivSign, chiTrivTriv_on_basis_ea,
         chiTrivSign_on_basis_ea] using this

/-- `chiFlipTriv ≠ chiFlipSign` when `(1 : k) ≠ -1`. Probe: `basis a a` (gives 1 vs -1). -/
lemma chiFlipTriv_ne_chiFlipSign (h : (1 : k) ≠ -1) :
    chiFlipTriv k ≠ chiFlipSign k := by
  intro heq
  apply h
  have h_ft : chiFlipTrivFun k (DG.basis k G2 a a) = 1 := by
    show ddBasis k G2 a a (a, e) + ddBasis k G2 a a (a, a) = 1
    unfold ddBasis; simp [a_ne_e.symm]
  have := congrArg (· (DG.basis k G2 a a)) heq
  simpa [chiFlipTriv, chiFlipSign, h_ft, chiFlipSign_on_basis_aa] using this

/-- The 4 characters `chiTrivTriv`, `chiTrivSign`, `chiFlipTriv`, `chiFlipSign`
    are pairwise distinct whenever `(1 : k) ≠ 0` and `(1 : k) ≠ -1` (i.e.,
    `k` is nontrivial with characteristic ≠ 2).

    Assembled via the 6 pairwise-distinctness lemmas above. -/
theorem simpleChi_injective (h1 : (1 : k) ≠ 0) (h2 : (1 : k) ≠ -1) :
    Function.Injective (simpleChi k) := by
  intro s t hst
  rcases s with _ | _ | _ | _ <;> rcases t with _ | _ | _ | _ <;>
    simp only [simpleChi] at hst <;>
    first
    | rfl
    | exact absurd hst (chiTrivTriv_ne_chiTrivSign k h2)
    | exact absurd hst (chiTrivTriv_ne_chiTrivSign k h2).symm
    | exact absurd hst (chiTrivTriv_ne_chiFlipTriv k h1)
    | exact absurd hst (chiTrivTriv_ne_chiFlipTriv k h1).symm
    | exact absurd hst (chiTrivTriv_ne_chiFlipSign k h1)
    | exact absurd hst (chiTrivTriv_ne_chiFlipSign k h1).symm
    | exact absurd hst (chiTrivSign_ne_chiFlipTriv k h1)
    | exact absurd hst (chiTrivSign_ne_chiFlipTriv k h1).symm
    | exact absurd hst (chiTrivSign_ne_chiFlipSign k h1)
    | exact absurd hst (chiTrivSign_ne_chiFlipSign k h1).symm
    | exact absurd hst (chiFlipTriv_ne_chiFlipSign k h2)
    | exact absurd hst (chiFlipTriv_ne_chiFlipSign k h2).symm

/-! ## 12. Bundling the 4 simples as `ModuleCat (DG k G2)` objects

Each `SimpleModule χ` has its full typeclass stack in place. We can bundle
each as a `ModuleCat (DG k G2)` object via `ModuleCat.of`. The resulting
`simpleRepModule : DZ2Simple → ModuleCat (DG k G2)` is the object-part of
the would-be functor `Center (VecG_Cat k G2) ⥤ ModuleCat (DG k G2)`
(after composing with the toric-anyon ↔ DZ2Simple bijection). -/

/-- The 4 simple `Rep(D(G2))` objects bundled as `ModuleCat (DG k G2)`,
    indexed by the `DZ2Simple` label corresponding to each toric anyon.

    Pattern-matches on the label (rather than composing a helper
    function) so that Lean can directly unify each branch's `SimpleModule`
    type with the expected `ModuleCat (DG k G2)` carrier. -/
noncomputable def simpleRepModule : DZ2Simple → ModuleCat (DG k G2)
  | .trivTriv => ModuleCat.of (DG k G2) (SimpleModule (chiTrivTriv k))
  | .trivSign => ModuleCat.of (DG k G2) (SimpleModule (chiTrivSign k))
  | .flipTriv => ModuleCat.of (DG k G2) (SimpleModule (chiFlipTriv k))
  | .flipSign => ModuleCat.of (DG k G2) (SimpleModule (chiFlipSign k))

/-! ## 13. Key observation for H_CF1 discharge

The `CenterFunctor.H_CF1_center_functor` hypothesis is `Nonempty
(Center (VecG_Cat k G) ⥤ ModuleCat (DG k G))`. As stated this is
trivially discharge-able by ANY functor (e.g., the constant functor
at an arbitrary object). This reveals the hypothesis as stated is
weaker than its intended meaning ("the *canonical* functor exists").

The correct strengthening, if desired, is to specify the canonical
functor's action explicitly — which requires the full 300+ LOC
construction described in the Wave 9 roadmap entry. We do NOT
discharge H_CF1 trivially here, because doing so would paper over
the hypothesis's imprecision rather than address it. -/

/-! ## 14. Module summary -/

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
