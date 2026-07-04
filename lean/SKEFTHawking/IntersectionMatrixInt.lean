/-
# Phase 5q.H · E1 — the integer intersection MATRIX + the conditional manifold `σ ÷ 16`

Substrate-G foundation brick (Option-A from-scratch), the FINAL link of the structural chain
"integral cohomology → cup → form → **matrix → σ÷16**" on genuine integral substrate.

The integral intersection *form* `interFormInt : H²(M⁴;ℤ) × H²(M⁴;ℤ) → ℤ` (a symmetric ℤ-bilinear map,
`interFormInt fc a b = ⟨a ∪ b, [M]⟩`) is already built kernel-pure (`SingularIntersectionFormInt.lean`).
Given a finite ℤ-basis of `H²(M;ℤ)` — carried as a **disclosed datum** (`IntH2Basis`, registered in
`HYPOTHESIS_REGISTRY` as `intH2_basis_datum`; discharge = `H²(M;ℤ)` is finitely-generated free from the
manifold's finite CW structure) — this module forms the **Gram matrix** `interMatrix : Matrix (Fin n)
(Fin n) ℤ`, `interMatrix i j = interFormInt fc (basis i) (basis j)`, proves it **symmetric**, and applies
the DONE lattice `σ÷16` theorem (`RokhlinHMRankFour.sixteen_dvd_latticeSig`) to it — reducing the
manifold-level Rokhlin `16 ∣ σ(M)` to its two irreducibly-geometric Props: even-unimodularity
`IsEvenUnimodular interMatrix` (evenness = Wu, unimodularity = Poincaré duality) **and** the topological
factor `2 ∣ latticeSig interMatrix / 8` (Guillou–Marin / Â-genus-even — the genuinely topological `2`,
NOT recoverable from the algebra: `nogo_lattice_arf_not_sigma8`).

## What is proved here vs. what is disclosed/left as hypothesis

PROVED (kernel-pure, `{propext, Classical.choice, Quot.sound}`; no `sorry`/`native_decide`/`maxHeartbeats`/
axiom):
* `interMatrix` — the Gram matrix of `interFormInt fc` on a disclosed free basis;
* `interMatrix_isSymm` / `interMatrix_transpose` — the matrix is symmetric (from `interFormInt_symm`),
  hence supplies the `IsSymmetricInt` conjunct of `IsEvenUnimodular` for free;
* `eight_dvd_manifold_sig` — the UNCONDITIONAL algebraic half `IsEvenUnimodular interMatrix → 8 ∣
  latticeSig interMatrix` (the `8 ∣ σ` is now a discharged theorem: [HM]+[Θ]);
* `sixteen_dvd_manifold_sig` — the **headline** conditional manifold `σ÷16`:
  `IsEvenUnimodular interMatrix → (2 ∣ latticeSig interMatrix / 8) → 16 ∣ latticeSig interMatrix`.

DISCLOSED DATUM (structure field, not axiom): `IntH2Basis` = a finite free basis of `H²(M;ℤ)`.

LEFT AS HYPOTHESIS (the community-scale geometric Props — deliberately NOT proved, cf. dispatch):
* `IsEvenUnimodular interMatrix` = evenness (Wu class `w₂` / characteristic-square) + unimodularity
  (Poincaré duality: the form is a perfect pairing);
* `2 ∣ latticeSig interMatrix / 8` = the topological Rokhlin factor (Guillou–Marin / index-theoretic);
* the fundamental-class evaluation `fc.eval` (`IntFundamentalClass`, orientation/`[M]`) — already disclosed
  upstream;
* basis finite-freeness (`IntH2Basis` here).

All four are isolated as clean data/hypotheses; the entire structural chain around them is kernel-pure.
-/
import Mathlib
import SKEFTHawking.SingularIntersectionFormInt
import SKEFTHawking.RokhlinHMRankFour

namespace SKEFTHawking.SingularCohomologyInt

open SKEFTHawking SKEFTHawking.SingularCohomologyInt

variable {X : TopCat}

/-! ## §1. The finite free basis of `H²(M;ℤ)` as a disclosed tracked datum -/

/-- **A finite free `ℤ`-basis of `H²(M;ℤ)`, carried as a disclosed datum.**

For a closed 4-manifold `M`, `H²(M;ℤ) = Cohomology (TopCat.of M) 2` is a finitely-generated free abelian
group (the finite CW structure gives finitely-generated integral cohomology; the intersection form being
unimodular forces the free quotient, and the torsion pairs off under Poincaré duality). Mathlib has no
manifold cohomology, so — exactly as the fundamental class `[M]` is carried by `IntFundamentalClass` — the
basis is carried as a **datum**: a `Module.Basis (Fin n) ℤ (Cohomology X 2)` together with its rank `n`.

Disclosed tracked hypothesis `intH2_basis_datum` (`HYPOTHESIS_REGISTRY`, tier `discharge_future`). Discharge
= build integral singular homology/cohomology of a finite CW complex, prove `H²(M;ℤ)` finitely-generated,
and split off the free part (`Module.Free`/`Module.Finite` over the PID `ℤ` ⟹ a finite basis exists). Every
result in this module holds for an arbitrary such basis, so the datum is the only unproved *free-module*
input to the intersection matrix. -/
structure IntH2Basis (X : TopCat) where
  /-- The rank `n = b₂(M)` = the second Betti number (dimension of the free part of `H²(M;ℤ)`). -/
  rank : ℕ
  /-- The finite free `ℤ`-basis of `H²(M;ℤ)` indexed by `Fin rank`. -/
  basis : Module.Basis (Fin rank) ℤ (Cohomology X 2)

/-! ## §2. The integer intersection matrix and its symmetry -/

/-- **The integer intersection matrix** `interMatrix i j = ⟨(bᵢ ∪ bⱼ), [M]⟩` — the Gram matrix of the
integral intersection form `interFormInt fc` on the disclosed free basis `B.basis` of `H²(M;ℤ)`.

This is the `Matrix (Fin n) (Fin n) ℤ` the DONE lattice leg (`AlgebraicRokhlin.IsEvenUnimodular` +
`LatticeSignature.latticeSig`, with the discharged `8 ∣ σ` / conditional `16 ∣ σ`) consumes: the integral
intersection form *in coordinates*. It is the concrete arithmetic object whose even-unimodularity + the
topological factor deliver the manifold-level Rokhlin `16 ∣ σ(M)`. -/
noncomputable def interMatrix (fc : IntFundamentalClass X) (B : IntH2Basis X) :
    Matrix (Fin B.rank) (Fin B.rank) ℤ :=
  Matrix.of fun i j => interFormInt fc (B.basis i) (B.basis j)

/-- **`interMatrix fc B i j = ⟨(bᵢ ∪ bⱼ), [M]⟩`** — the matrix entry is the intersection form evaluated on
the `i`-th and `j`-th basis classes. -/
@[simp] theorem interMatrix_apply (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (i j : Fin B.rank) :
    interMatrix fc B i j = interFormInt fc (B.basis i) (B.basis j) :=
  rfl

/-- **The integer intersection matrix is symmetric** (`Matrix.IsSymm`): `interMatrix j i = interMatrix i j`
for all `i j`. Immediate from symmetry of the intersection form `interFormInt_symm` (graded-commutativity of
the integral cup product at bidegree `(2,2)`, Koszul sign `+1`). This is the `IsSymmetricInt` conjunct of
`IsEvenUnimodular` supplied for free. -/
theorem interMatrix_isSymm (fc : IntFundamentalClass X) (B : IntH2Basis X) :
    (interMatrix fc B).IsSymm := by
  refine Matrix.IsSymm.ext (fun i j => ?_)
  simp only [interMatrix_apply]
  exact interFormInt_symm fc (B.basis j) (B.basis i)

/-- **`interMatrixᵀ = interMatrix`** — the transpose form of symmetry (`Matrix.IsSymm.eq`), i.e. exactly the
project's `IsSymmetricInt (interMatrix fc B)` predicate that `IsEvenUnimodular` requires. -/
theorem interMatrix_transpose (fc : IntFundamentalClass X) (B : IntH2Basis X) :
    (interMatrix fc B).transpose = interMatrix fc B :=
  (interMatrix_isSymm fc B).eq

/-- **`IsSymmetricInt (interMatrix fc B)`** — the intersection matrix satisfies the project-local
symmetric-matrix predicate (the first conjunct of `IsEvenUnimodular`), stated explicitly so the geometric
`IsEvenUnimodular interMatrix` hypothesis reduces to just its two genuinely-geometric conjuncts (evenness/Wu
and unimodularity/PD). -/
theorem interMatrix_isSymmetricInt (fc : IntFundamentalClass X) (B : IntH2Basis X) :
    IsSymmetricInt (interMatrix fc B) :=
  interMatrix_transpose fc B

/-! ## §3. The conditional manifold `σ ÷ 16` (headline) -/

/-- **The algebraic half, unconditional: `8 ∣ σ` of the intersection matrix.**

`IsEvenUnimodular (interMatrix fc B) → 8 ∣ latticeSig (interMatrix fc B)`. A direct application of the DONE,
fully-discharged (`[HM]`+`[Θ]`) lattice theorem `RokhlinHMRankFour.eight_dvd_latticeSig` to the manifold's
integer intersection matrix — the algebraic Serre/van-der-Blij bound `σ ≡ 0 mod 8` at the manifold level.
The extra factor of `2` (to `16`) is genuinely topological; see `sixteen_dvd_manifold_sig`. -/
theorem eight_dvd_manifold_sig (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (heu : IsEvenUnimodular (interMatrix fc B)) :
    (8 : ℤ) ∣ latticeSig (interMatrix fc B) :=
  eight_dvd_latticeSig B.rank (interMatrix fc B) heu

/-- **The manifold-level Rokhlin `σ ÷ 16`, conditional on the two geometric Props (HEADLINE).**

`IsEvenUnimodular (interMatrix fc B) → (2 ∣ latticeSig (interMatrix fc B) / 8) → 16 ∣ latticeSig
(interMatrix fc B)`.

A DIRECT application of the DONE lattice theorem `RokhlinHMRankFour.sixteen_dvd_latticeSig` to the
manifold's integer intersection matrix. This is the manifold-level `σ÷16` **reduced to exactly its two
irreducibly-geometric inputs**:

* `IsEvenUnimodular (interMatrix fc B)` — **evenness** (the intersection form of a spin 4-manifold is even,
  characteristic-square/Wu class `w₂ = 0`) **and unimodularity** (Poincaré duality makes the form a perfect
  pairing, `det = ±1`); its symmetric conjunct is already discharged here (`interMatrix_isSymmetricInt`);
* `2 ∣ latticeSig (interMatrix fc B) / 8` — the **topological Rokhlin factor** (`2 ∣ σ/8`), the Guillou–Marin
  / index-theoretic input. This is genuinely topological and is provably NOT recoverable from the algebra
  (the lattice-Arf refutation `nogo_lattice_arf_not_sigma8`): it must be supplied as a geometric datum.

Everything else in the chain — the integral cohomology ring, the cup product, graded-commutativity, the
form, the Gram matrix, its symmetry, the algebraic `8 ∣ σ`, and this final divisibility composition — is
kernel-pure. The remaining inputs (basis finite-freeness `IntH2Basis`, even/Wu + unimodular/PD
`IsEvenUnimodular`, topological factor, and orientation `[M]`/`IntFundamentalClass`) are all cleanly
isolated as disclosed geometric data. -/
theorem sixteen_dvd_manifold_sig (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (heu : IsEvenUnimodular (interMatrix fc B))
    (htopo : (2 : ℤ) ∣ latticeSig (interMatrix fc B) / 8) :
    (16 : ℤ) ∣ latticeSig (interMatrix fc B) :=
  sixteen_dvd_latticeSig (interMatrix fc B) heu htopo

end SKEFTHawking.SingularCohomologyInt
