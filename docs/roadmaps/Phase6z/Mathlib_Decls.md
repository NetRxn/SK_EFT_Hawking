# Phase 6z — Mathlib4 declarations + gotchas (verified at pin `8850ed93`, Lean v4.29.1)

*Progressive-disclosure detail doc for `Phase6z_Roadmap.md`. Source: DR2 (`Lit-Search/Phase-6y/Phase 6y :
SK_EFT_Hawking Irrational-Angle Seed for Density of ⟨H, S, CNOT, CCZ⟩ in SU(8).md`), which verified each
decl against the pin. **Re-confirm with `lean_hover_info`/`lean_declaration_file`/`lean_local_search`
before use** — renames happen.*

## (a) Irrational ⇒ density on the circle
| Need | Decl | Module |
|---|---|---|
| Dense-or-cyclic dichotomy | `AddSubgroup.dense_or_cyclic` | `Mathlib.Topology.Algebra.Order.Archimedean` |
| Exclusive form | `AddSubgroup.dense_xor'_cyclic` | same |
| Irrational predicate | `Irrational` | `Mathlib.Data.Real.Irrational` |
| Circle group | `AddCircle` (namespace) | `Mathlib.Topology.Instances.AddCircle.Defs` |
| Finite-order ↔ rational | `AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder`, `AddCircle.addOrderOf_div_of_gcd_eq_one` | same |

New local lemma (~25 LoC): `irrational_dense_on_circle (T) (hT:0<T) (a) (h:Irrational (a/T)) :
Dense (Set.range (fun n:ℤ ↦ ((n:ℝ)•a : AddCircle T)))` — assemble from `dense_or_cyclic` on
`AddSubgroup.zmultiples a` through the quotient `ℝ → AddCircle T`, cyclic branch killed by `Irrational (a/T)`.

## (b) Algebraic-integer / root-of-unity machinery
| Need | Decl | Module |
|---|---|---|
| `IsIntegral` | `IsIntegral` | `Mathlib.RingTheory.IntegralClosure.Basic` |
| Sum/product preserve | `IsIntegral.add`, `IsIntegral.mul` | `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` |
| Primitive root | `IsPrimitiveRoot` | `Mathlib.RingTheory.RootsOfUnity.Basic` |
| `exp(2πi·i/n)` primitive | `Complex.isPrimitiveRoot_exp_of_isCoprime` | `Mathlib.RingTheory.RootsOfUnity.Complex` |
| Cyclotomic = minpoly | `Polynomial.cyclotomic_eq_minpoly` | `Mathlib.RingTheory.Polynomial.Cyclotomic.Roots` |
| Cyclotomic irreducible | `Polynomial.cyclotomic.irreducible` | same |
| Char-0 root ↔ primitive | `isRoot_cyclotomic_iff` | same |
| Primitive root is integral | `IsPrimitiveRoot.isIntegral` | `Mathlib.RingTheory.RootsOfUnity.Minpoly` |

New local lemma (~70 LoC, the highest-leverage 6z artifact):
`not_rootOfUnity_of_minpoly_not_int {α:ℂ} (hα : ∀ p:ℤ[X], p.Monic → ¬ p.aeval α = 0) : ∀ n, 0<n → α^n ≠ 1`
— contrapositive via `IsPrimitiveRoot.isIntegral` + `cyclotomic_eq_minpoly`. Decompose into ≤12-term sub-lemmas.

## (c) Accumulation → one-parameter subgroup
| Need | Status |
|---|---|
| `Subgroup.topologicalClosure`, `Subgroup.isClosed_topologicalClosure` | ✓ `Mathlib.Topology.Algebra.Group.Basic` |
| 1-D Kronecker / irrational-rotation dense | ✗ build (≤200 raw LoC) via (a) |
| **Multi-D Kronecker–Weyl on `𝕋^d`** | ✗ **ABSENT** — but **not needed for the first flow** (1-D suffices on the 2-D eigenblock). Defer (6z.D). |
| Monothetic group structure | ✗ ABSENT |

## (d) Spectral log → traceless skew-Hermitian generator
| Need | Decl | Module |
|---|---|---|
| Spectral theorem (Hermitian) | `Matrix.IsHermitian.spectral_theorem` | `Mathlib.Analysis.Matrix.Spectrum` (moved 2024 from `Mathlib.LinearAlgebra.Matrix.Spectrum`; both aliased at pin — import the new path) |
| Eigenvector unitary | `Matrix.IsHermitian.eigenvectorUnitary` | same |
| Eigenvalues | `Matrix.IsHermitian.eigenvalues` | same |
| Matrix exponential | `NormedSpace.exp 𝕂 A` | `Mathlib.Analysis.Normed.Algebra.MatrixExponential` |
| `exp` of diagonal | `Matrix.exp_diagonal` | same |
| `exp` of conjTranspose | `Matrix.exp_conjTranspose` | same |
| Unit conjugation | `NormedSpace.exp_units_conj`, `exp_units_conj'` | `Mathlib.Analysis.Normed.Algebra.Exponential` |

## ⚠️ Gotchas (from DR2 — do not relearn the hard way)
1. **Niven's theorem is ABSENT** (`Mathlib.Analysis.SpecialFunctions.Trigonometric.*` /
   `Mathlib.NumberTheory.*` — no `Niven`, no `cos_rat_pi`). **Not needed** — the algebraic-integer route
   (b) is strictly cleaner. (Building Niven = ~200–400 LoC via Chebyshev; AVOID.)
2. **`Matrix.exp_conj` does NOT exist.** Use `NormedSpace.exp_units_conj` (+ `'`) via `Matrix.GeneralLinearGroup`
   unit-wrapping. (The project's `Matrix.exp_conj` usages elsewhere are project-local lemmas, not Mathlib.)
3. **The spectral theorem is `IsHermitian`-only, but `g₀` is UNITARY.** Diagonalize via
   `g₀ = U·diag(e^{iθⱼ})·U†` → `A := U·diag(θⱼ)·U†`. Either build `IsUnitary.spectral_theorem` locally
   (~150 LoC, apply Hermitian theorem to `(g₀+g₀†)/2` and `(g₀−g₀†)/(2i)` simultaneously) or reuse any
   unitary-diagonalization wrapper in `FKLW/SU2BCHBracketClosure.lean`.
4. **`NormedSpace.exp` junk-value = `1`** if no `ℚ`-algebra instance; present for `Matrix (Fin 8) (Fin 8) ℂ`
   but discharge the instance explicitly in proof obligations (existing project usage handles it).
5. **`AddSubgroup.dense_or_cyclic` is in `Mathlib.Topology.Algebra.Order.Archimedean`** — import explicitly.
   (2025 refactor: typeclass is `IsOrderedAddMonoid` + `Archimedean`, NOT `LinearOrderedAddCommGroup`.)
6. 2025 renames seen project-wide: `IsTopologicalGroup`/`IsTopologicalRing` (not `Topological*`);
   `NormedSpace.exp` (not root `exp`); `eigenvectorUnitary` (not `eigenvectorMatrix`).
