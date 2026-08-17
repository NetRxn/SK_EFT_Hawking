/-
Phase 5q.T Wave T3: EXACTNESS of the A(1) minimal free resolution — kernel-pure

`A1Resolution.lean` certifies that `d1 … d5` form a chain complex (`dᵢ·dᵢ₊₁ = 0`) and
records rank data. What it did NOT contain is a proof that the complex is **exact** — that
it is a *resolution* rather than merely a complex. The nearest thing,

```
theorem exactness_rank_nullity : 1 + 7 = 8 ∧ 7 + 9 = 16 ∧ … := by omega
```

is the same failure mode as the retired `ext_dim_n : 24/8 = 3` proxies: a closed arithmetic
identity carrying a structural name. It states that the *documented* ranks are consistent
with exactness; it does not state, and cannot state, that `ker dₙ = range dₙ₊₁`.

This module proves the real thing, and proves it **kernel-purely**.

**Method — a contracting homotopy, not rank counting.** Over F₂ every exact complex of
vector spaces is contractible, so exactness is equivalent to the existence of maps
`s₋₁, s₀ … s₄` satisfying

```
ε·s₋₁ = 1,   d₁·s₀ + s₋₁·ε = 1,   dₙ₊₁·sₙ + sₙ₋₁·dₙ = 1   (n = 1 … 4)
```

Each is a concrete F₂-matrix identity, hence `decide +kernel`, hence adds no axiom. Python
solves for the `sₙ` (`scripts/generate_a1_homotopy.py`); Lean VERIFIES them — the same
certificate discipline as the existing RREF witnesses. If any entry of any `sₙ` is wrong the
proof fails to compile.

**Why this route and not the kernel cardinalities.** `d1_kernel_card`, `d2_kernel_card` and
`d3_kernel_card` are the three surviving `native_decide` theorems in the development (2^16
vector enumerations). Routing exactness through them would make every downstream `Ext`
theorem carry `Lean.ofReduceBool`. The homotopy route depends on none of them: the axiom set
of `resolution_is_exact` is `{propext, Classical.choice, Quot.sound}`.

**What this unlocks.** Exactness is a statement about the underlying sets of the kernel and
range, so the F₂-linear statements below are simultaneously the A(1)-module statements: an
A(1)-linear map has the same kernel and image whether read over A(1) or over F₂. This is the
`quasiIso` content that Mathlib's `ProjectiveResolution` requires (Wave T3 sub-task (c)).

Roadmap: docs/roadmaps/Phase5qT_ExtSubstantiation_Roadmap.md (Wave T3).
-/

import SKEFTHawking.A1Resolution

namespace SKEFTHawking.A1

open Matrix

/-! ## 1. The augmentation and the contracting homotopy -/

/-- The augmentation `ε : P₀ → F₂`, as a 1×8 matrix: the coefficient of the unit `e₀`.
    This is the map the resolution resolves; `P₀ = A(1)` and `ε` kills the augmentation
    ideal (cf. `A1Algebra.aug`). -/
def epsM : Matrix (Fin 1) (Fin 8) F2 := Matrix.of fun _ i => if i.val = 0 then 1 else 0

/-- `s₋₁ : F₂ → P₀`, the unit section of the augmentation. -/
def sneg : Matrix (Fin 8) (Fin 1) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 0 => 1
  | _, _ => 0

/-- `s0 : P0 → P1`, a contracting-homotopy component. Python-solved, Lean-verified. -/
def s0 : Matrix (Fin 16) (Fin 8) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 2, 4 => 1 | 3, 5 => 1 | 6, 7 => 1
  | 8, 2 => 1 | 9, 3 => 1 | 9, 4 => 1 | 12, 6 => 1
  | _, _ => 0

/-- `s1 : P1 → P2`, a contracting-homotopy component. Python-solved, Lean-verified. -/
def s1 : Matrix (Fin 16) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 2, 4 => 1 | 3, 5 => 1 | 6, 7 => 1
  | 6, 14 => 1 | 8, 10 => 1 | 9, 11 => 1 | 10, 13 => 1
  | 12, 14 => 1 | 13, 15 => 1
  | _, _ => 0

/-- `s2 : P2 → P3`, a contracting-homotopy component. Python-solved, Lean-verified. -/
def s2 : Matrix (Fin 16) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 2, 4 => 1 | 3, 5 => 1 | 6, 7 => 1
  | 8, 11 => 1 | 10, 14 => 1 | 11, 15 => 1
  | _, _ => 0

/-- `s3 : P3 → P4`, a contracting-homotopy component. Python-solved, Lean-verified. -/
def s3 : Matrix (Fin 24) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 2, 4 => 1 | 3, 5 => 1 | 6, 7 => 1
  | 8, 9 => 1 | 10, 12 => 1 | 11, 13 => 1 | 14, 15 => 1
  | 16, 14 => 1
  | _, _ => 0

/-- `s4 : P4 → P5`, a contracting-homotopy component. Python-solved, Lean-verified. -/
def s4 : Matrix (Fin 32) (Fin 24) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 2, 4 => 1 | 3, 5 => 1 | 6, 7 => 1
  | 8, 9 => 1 | 10, 12 => 1 | 11, 13 => 1 | 14, 15 => 1
  | 16, 17 => 1 | 18, 20 => 1 | 19, 21 => 1 | 22, 23 => 1
  | 24, 18 => 1 | 25, 19 => 1 | 25, 20 => 1 | 28, 22 => 1
  | _, _ => 0

/-! ## 2. The homotopy identities (kernel-pure `decide +kernel`) -/

/-- `ε·s₋₁ = 1`: the augmentation is split, hence surjective. -/
theorem homotopy_aug : epsM * sneg = 1 := by decide +kernel

/-- `d₁·s₀ + s₋₁·ε = 1` on `P₀`. -/
theorem homotopy_0 : d1 * s0 + sneg * epsM = 1 := by decide +kernel

/-- `d2·s1 + s0·d1 = 1` on `P1`. -/
theorem homotopy_1 : d2 * s1 + s0 * d1 = 1 := by decide +kernel

/-- `d3·s2 + s1·d2 = 1` on `P2`. -/
theorem homotopy_2 : d3 * s2 + s1 * d2 = 1 := by decide +kernel

/-- `d4·s3 + s2·d3 = 1` on `P3`. -/
theorem homotopy_3 : d4 * s3 + s2 * d3 = 1 := by decide +kernel

/-- `d5·s4 + s3·d4 = 1` on `P4`. -/
theorem homotopy_4 : d5 * s4 + s3 * d4 = 1 := by decide +kernel

/-- `ε·d₁ = 0` — minimality of `d₁` (its row 0 vanishes), i.e. `im d₁ ⊆ ker ε`. -/
theorem eps_d1_zero : epsM * d1 = 0 := by decide +kernel

/-! ## 3. Exactness

The one-line homological argument, stated once and applied five times: if `D·E = 0` and
`E·S + T·D = 1`, then `D x = 0` forces `x = E (S x)`, so `ker D = range E`. -/

/-- **A contracting homotopy certifies exactness.** `D : Pₙ → Pₙ₋₁`, `E : Pₙ₊₁ → Pₙ`,
    `S = sₙ`, `T = sₙ₋₁`. -/
theorem exact_of_homotopy {m n p : ℕ}
    (D : Matrix (Fin m) (Fin n) F2) (E : Matrix (Fin n) (Fin p) F2)
    (S : Matrix (Fin p) (Fin n) F2) (T : Matrix (Fin n) (Fin m) F2)
    (hDE : D * E = 0) (h : E * S + T * D = 1) :
    LinearMap.ker (Matrix.mulVecLin D) = LinearMap.range (Matrix.mulVecLin E) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
    refine ⟨S.mulVec x, ?_⟩
    have hTD : (T * D).mulVec x = 0 := by
      rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    have hone : ((E * S) + (T * D)).mulVec x = x := by rw [h, Matrix.one_mulVec]
    rw [Matrix.add_mulVec, hTD, add_zero, ← Matrix.mulVec_mulVec] at hone
    exact hone
  · rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hDE, Matrix.zero_mulVec]

/-- **Exact at `P₀`:** `ker ε = im d₁`. -/
theorem exact_at_P0 :
    LinearMap.ker (Matrix.mulVecLin epsM) = LinearMap.range (Matrix.mulVecLin d1) :=
  exact_of_homotopy epsM d1 s0 sneg eps_d1_zero homotopy_0

/-- **Exact at `P1`:** `ker d1 = im d2`. -/
theorem exact_at_P1 :
    LinearMap.ker (Matrix.mulVecLin d1) = LinearMap.range (Matrix.mulVecLin d2) :=
  exact_of_homotopy d1 d2 s1 s0 d1_d2_zero homotopy_1

/-- **Exact at `P2`:** `ker d2 = im d3`. -/
theorem exact_at_P2 :
    LinearMap.ker (Matrix.mulVecLin d2) = LinearMap.range (Matrix.mulVecLin d3) :=
  exact_of_homotopy d2 d3 s2 s1 d2_d3_zero homotopy_2

/-- **Exact at `P3`:** `ker d3 = im d4`. -/
theorem exact_at_P3 :
    LinearMap.ker (Matrix.mulVecLin d3) = LinearMap.range (Matrix.mulVecLin d4) :=
  exact_of_homotopy d3 d4 s3 s2 d3_d4_zero homotopy_3

/-- **Exact at `P4`:** `ker d4 = im d5`. -/
theorem exact_at_P4 :
    LinearMap.ker (Matrix.mulVecLin d4) = LinearMap.range (Matrix.mulVecLin d5) :=
  exact_of_homotopy d4 d5 s4 s3 d4_d5_zero homotopy_4

/-- The augmentation is surjective — the resolution really does cover `F₂`. -/
theorem aug_surjective : Function.Surjective (Matrix.mulVecLin epsM) := by
  intro y
  refine ⟨sneg.mulVec y, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, homotopy_aug, Matrix.one_mulVec]

/-- **Master theorem: the minimal free resolution of F₂ over A(1) is EXACT.**

    `F₂ ←ε— P₀ ←d₁— P₁ ←d₂— P₂ ←d₃— P₃ ←d₄— P₄ ←d₅— P₅` is exact at `F₂` (surjectivity of
    `ε`) and at `P₀ … P₄`. Together with `A1Resolution.resolution_is_a1_linear` — which says
    every differential commutes with the A(1)-action — this is the statement that `P•` is a
    resolution of `F₂` by free A(1)-modules through degree 5, and it is the `quasiIso`
    content Mathlib's `ProjectiveResolution` demands.

    Kernel-pure: `{propext, Classical.choice, Quot.sound}`. In particular it does NOT depend
    on `d1_kernel_card`/`d2_kernel_card`/`d3_kernel_card`, the development's three remaining
    `native_decide` theorems.

    Exactness at `P₅` is NOT claimed and does not follow from the data here: it requires
    `d₆`, which this development does not construct. -/
theorem resolution_is_exact :
    Function.Surjective (Matrix.mulVecLin epsM)
    ∧ LinearMap.ker (Matrix.mulVecLin epsM) = LinearMap.range (Matrix.mulVecLin d1)
    ∧ LinearMap.ker (Matrix.mulVecLin d1) = LinearMap.range (Matrix.mulVecLin d2)
    ∧ LinearMap.ker (Matrix.mulVecLin d2) = LinearMap.range (Matrix.mulVecLin d3)
    ∧ LinearMap.ker (Matrix.mulVecLin d3) = LinearMap.range (Matrix.mulVecLin d4)
    ∧ LinearMap.ker (Matrix.mulVecLin d4) = LinearMap.range (Matrix.mulVecLin d5) :=
  ⟨aug_surjective, exact_at_P0, exact_at_P1, exact_at_P2, exact_at_P3, exact_at_P4⟩

end SKEFTHawking.A1
