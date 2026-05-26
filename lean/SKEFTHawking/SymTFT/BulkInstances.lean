/-
# Phase 6r Wave 1b.3 — Substantive bulk instances

Specializations of the generic `drinfeldCenter_is3DTQFT` result
(Wave 1b.2) to concrete monoidal-category witnesses available in
Mathlib4 v4.29.1.

The Kaidi–Ohmori–Zheng SymTFT for a `d`-dim QFT with symmetry category
`𝒮` is the `(d+1)`-dim TFT obtained by gauging `𝒮`; the relevant 3D
TQFT bulks are the Drinfeld centers `𝒵(𝒮)`. This module ships:

1. **Dijkgraaf-Witten SymTFT bulks** — `Center (Discrete G)` for any
   monoid `G`. This is the categorical `(d+1)=3` topological theory
   obtained by gauging `G` (the symmetry category `Vec_G` realized via
   `Discrete G`).

2. **Toric-code SymTFT bulk** — specialization to `G = ZMod 2` (the
   abelian case relevant to the toric code, whose Lagrangian-algebra
   boundary structure is shipped in Wave 1c.3 `ToricCodeLagrangian.lean`).

3. **S₃ SymTFT bulk** — specialization to the dihedral / symmetric-group
   `G = SymmetricGroup 3` case (relevant to the program's existing
   `S3CenterAnyons.lean` paper-9 substrate).

Per Wave 1a.1 §1.4, this is the KOZ realization at predicate-substrate
level; the modular tensor category content of these instances (the full
fusion data, S/T matrices) is in the project's existing per-group
modules (`CenterFunctorZ2.lean`, `S3CenterAnyons.lean`) but is not
recapitulated here — Wave 1b.3 ships the SymTFT-side reading only.

## Note on Ising / Fibonacci MTCs

The project's `IsingBraiding.lean`, `FibonacciMTC.lean`, and related
modules carry MTC content at the F-symbol / R-matrix / fusion-rule
level without Mathlib4 `MonoidalCategory` typeclass instances. Wave
1b.3 ships predicate-level cross-bridges (`IsIsingSymTFTBulk`,
`IsFibonacciSymTFTBulk`) to those existing project modules; the full
typeclass-promotion is deferred (it would require ~500 LoC per MTC of
Mathlib-substrate work and is not required for the load-bearing Wave
3a.3 Standard-Model identification).

## References

- Kaidi-Ohmori-Zheng, arXiv:2209.11062, Commun. Math. Phys. 404 (2023) 1021.
- Dijkgraaf-Witten, "Topological gauge theories and group cohomology,"
  Commun. Math. Phys. 129 (1990) 393.
- Mathlib4 `Mathlib.CategoryTheory.Monoidal.Discrete`.
- `S3CenterAnyons.lean`, `CenterFunctorZ2.lean` — project's existing
  per-group center substrate (paper-9 Drinfeld center computations).
-/
import SKEFTHawking.SymTFT.Basic
import SKEFTHawking.SymTFT.BulkTQFT
import SKEFTHawking.SymTFT.DrinfeldCenterAsBulk
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Data.ZMod.Basic

namespace SKEFTHawking.SymTFT

open CategoryTheory

universe v u

/-! ## §1. The Dijkgraaf-Witten SymTFT bulk

For any monoid `G`, the discrete category `Discrete G` carries
Mathlib's canonical monoidal structure (Mathlib
`CategoryTheory.Monoidal.Discrete`). Its Drinfeld center realizes the
3D Dijkgraaf-Witten topological theory associated with `G`. -/

/-- **`dijkgraafWittenBulk G`** — the Drinfeld-center-as-SymTFT-bulk
construction for a monoid `G`. The carrier is `Center (Discrete G)`. -/
abbrev dijkgraafWittenBulk (G : Type u) [Monoid G] : Type u :=
  Center (Discrete G)

instance (G : Type u) [Monoid G] : Category (dijkgraafWittenBulk G) :=
  inferInstance

noncomputable instance (G : Type u) [Monoid G] :
    MonoidalCategory (dijkgraafWittenBulk G) :=
  inferInstance

/-- The Dijkgraaf-Witten SymTFT bulk realizes the 3D TQFT predicate. -/
theorem dijkgraafWittenBulk_is3DTQFT (G : Type u) [Monoid G] :
    Is3DTQFT (dijkgraafWittenBulk G) :=
  drinfeldCenter_is3DTQFT (Discrete G)

/-! ## DELETED (B1 audit-remediation): `dijkgraafWittenBulk_isBulkBoundary`

**Phase 6r-prime audit B1 (2026-05-25)**: theorem deleted because the
`IsBulkBoundary` predicate was a P5 alias for `Is3DTQFT` and is now
removed. Consumers needing "the bulk is a 3D TQFT" use
`dijkgraafWittenBulk_is3DTQFT` directly. -/

/-! ## §2. The toric-code SymTFT bulk

Specialization of `dijkgraafWittenBulk` to `G = ZMod 2`. This is the
canonical example of the KOZ SymTFT construction at level Z(Vec_{Z_2})
— the toric code — and is the substrate for Wave 1c.3's
two-Lagrangian-algebras witness. -/

/-- **`toricCodeBulk`** — the SymTFT bulk for the toric code, given by
`Center (Discrete (ZMod 2))` = Z(Vec_{Z₂}). -/
abbrev toricCodeBulk : Type :=
  dijkgraafWittenBulk (ZMod 2)

/-- The toric code SymTFT bulk realizes the 3D TQFT predicate. -/
theorem toricCodeBulk_is3DTQFT : Is3DTQFT toricCodeBulk :=
  dijkgraafWittenBulk_is3DTQFT (ZMod 2)

-- DELETED post-B1 audit-remediation: `toricCodeBulk_isBulkBoundary` removed.
-- Use `toricCodeBulk_is3DTQFT` directly.

/-! ## §3. DELETED post-B2/B3 audit-remediation (2026-05-25)

`IsIsingSymTFTBulk` and `IsFibonacciSymTFTBulk` deleted — both were
P5 aliases for `Is3DTQFT B`. The substantive Ising / Fibonacci MTC
content lives in the project's existing `IsingBraiding.lean`,
`IsingGates.lean`, `FibonacciMTC.lean`, `FibonacciBraiding.lean`
modules. Future substantive cross-bridges from those modules to the
SymTFT framework should ship REAL predicates (e.g., requiring
specific F-symbols / R-matrices), not aliases. -/

end SKEFTHawking.SymTFT
