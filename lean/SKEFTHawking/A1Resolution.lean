/-
Phase 5q Wave 3: Minimal Free Resolution of F₂ over A(1)

The explicit minimal free resolution of F₂ as an A(1)-module through
homological degree 5. Each differential is encoded as an F₂-matrix
(expanding the A(1)-element matrix via the left regular representation).

Key results:
  - d² = 0 at every level (chain complex property)
  - Resolution ranks: P₀=1, P₁=2, P₂=2, P₃=2, P₄=3, P₅=4
  - All matrix identities kernel-pure (`decide +kernel`); see Proof method below

The resolution has a bidiagonal structure: Sq(1) on the diagonal,
Sq(2,1) on the superdiagonal, with 4-fold periodicity from w₁.

FIRST machine-checked free resolution over any Steenrod subalgebra
in any proof assistant.

Cross-validated: scripts/generate_a1_resolution.py (all checks pass)
Deep research: Lit-Search/Phase-5q/The minimal free resolution...

Proof method (updated 2026-08-15, Phase 5q.T): every matrix identity in this file —
`d∘d = 0`, the RREF certificates, the invertibility witnesses and the rank row-vanishing
statements — is now **kernel-pure**, proven by `decide +kernel`. The `+kernel` modifier
hands evaluation straight to the kernel, bypassing the elaborator's `whnf` heartbeat and
recursion budgets that made plain `decide` impractical here; it adds **no** axiom
(`ofReduceBool` is not incurred, unlike `native_decide`). Axiom set on every such theorem:
`{propext, Classical.choice, Quot.sound}`.

This includes the three `Fintype.card` kernel theorems (`d1_kernel_card` … `d3_kernel_card`),
so **this file contains no `native_decide`**.

Do not prove those three by enumeration: `decide +kernel` over the 2^16 vectors exhausts the
kernel's recursion limit (measured: it fails after 2m34s), and `native_decide` buys the count
only at the price of `ofReduceBool`. A cardinality need not be counted — it can be *exhibited*
by a bijection, which §3 does with a kernel-basis certificate the kernel checks in seconds.
Reach for that certificate for any further kernel-cardinality fact here.
Pipeline Invariant #10 forbids raising `maxHeartbeats`; nothing here does, and nothing raises
`maxRecDepth` either.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import SKEFTHawking.A1Ring

namespace SKEFTHawking.A1

/-! ## 1. Differential Matrices (F₂-expanded)

Each d_n: P_n → P_{n-1} is encoded as a Matrix (Fin m) (Fin n) F2
where m = 8 · rank(P_{n-1}) and n = 8 · rank(P_n).

The A(1)-element differentials (from deep research) are:
  d₁ = [Sq(1), Sq(2)]
  d₂ = [[Sq(1), Sq(3)], [0, Sq(2)]]
  d₃ = [[Sq(1), Sq(2,1)], [0, Sq(3)]]
  d₄ = [[Sq(1), Sq(2,1), 0], [0, Sq(1), Sq(2,1)]]
  d₅ = [[Sq(1), Sq(2,1), 0, 0], [0, Sq(1), Sq(2,1), 0], [0, 0, Sq(1), Sq(2)]]

Each A(1) element is expanded to its 8×8 left-multiplication matrix (from A1Ring.lean).
-/

-- d₁: P₁ (rank 2, dim 16) → P₀ (rank 1, dim 8)
-- A(1)-matrix: [Sq(1), Sq(2)]
def d1 : Matrix (Fin 8) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 1, 0 => 1 | 2, 8 => 1 | 3, 2 => 1 | 3, 9 => 1
  | 4, 2 => 1 | 5, 3 => 1 | 5, 4 => 1 | 5, 10 => 1
  | 6, 12 => 1 | 7, 6 => 1 | 7, 13 => 1
  | _, _ => 0

-- d₂: P₂ (rank 2, dim 16) → P₁ (rank 2, dim 16)
-- A(1)-matrix: [[Sq(1), Sq(3)], [0, Sq(2)]]
def d2 : Matrix (Fin 16) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 1, 0 => 1 | 3, 2 => 1 | 3, 8 => 1 | 4, 2 => 1
  | 5, 3 => 1 | 5, 4 => 1 | 6, 10 => 1 | 7, 6 => 1
  | 7, 11 => 1 | 7, 12 => 1 | 10, 8 => 1 | 11, 9 => 1
  | 13, 10 => 1 | 14, 12 => 1 | 15, 13 => 1
  | _, _ => 0

-- d₃: P₃ (rank 2, dim 16) → P₂ (rank 2, dim 16)
-- A(1)-matrix: [[Sq(1), Sq(2,1)], [0, Sq(3)]]
def d3 : Matrix (Fin 16) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 1, 0 => 1 | 3, 2 => 1 | 4, 2 => 1 | 5, 3 => 1
  | 5, 4 => 1 | 6, 8 => 1 | 7, 6 => 1 | 7, 9 => 1
  | 11, 8 => 1 | 14, 10 => 1 | 15, 11 => 1 | 15, 12 => 1
  | _, _ => 0

-- d₄: P₄ (rank 3, dim 24) → P₃ (rank 2, dim 16)
-- A(1)-matrix: [[Sq(1), Sq(2,1), 0], [0, Sq(1), Sq(2,1)]]
def d4 : Matrix (Fin 16) (Fin 24) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 1, 0 => 1 | 3, 2 => 1 | 4, 2 => 1 | 5, 3 => 1
  | 5, 4 => 1 | 6, 8 => 1 | 7, 6 => 1 | 7, 9 => 1
  | 9, 8 => 1 | 11, 10 => 1 | 12, 10 => 1 | 13, 11 => 1
  | 13, 12 => 1 | 14, 16 => 1 | 15, 14 => 1 | 15, 17 => 1
  | _, _ => 0

-- d₅: P₅ (rank 4, dim 32) → P₄ (rank 3, dim 24)
-- A(1)-matrix: [[Sq(1), Sq(2,1), 0, 0], [0, Sq(1), Sq(2,1), 0], [0, 0, Sq(1), Sq(2)]]
def d5 : Matrix (Fin 24) (Fin 32) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 1, 0 => 1 | 3, 2 => 1 | 4, 2 => 1 | 5, 3 => 1
  | 5, 4 => 1 | 6, 8 => 1 | 7, 6 => 1 | 7, 9 => 1
  | 9, 8 => 1 | 11, 10 => 1 | 12, 10 => 1 | 13, 11 => 1
  | 13, 12 => 1 | 14, 16 => 1 | 15, 14 => 1 | 15, 17 => 1
  | 17, 16 => 1 | 18, 24 => 1 | 19, 18 => 1 | 19, 25 => 1
  | 20, 18 => 1 | 21, 19 => 1 | 21, 20 => 1 | 21, 26 => 1
  | 22, 28 => 1 | 23, 22 => 1 | 23, 29 => 1
  | _, _ => 0

/-! ## 2. Chain Complex Property: d² = 0

For each consecutive pair (d_n, d_{n+1}), we verify d_n · d_{n+1} = 0 over F₂.
Each proof is a single kernel-pure `decide +kernel` on a concrete matrix product. -/

/-- d₁ ∘ d₂ = 0 (8×16 · 16×16 → 8×16 check) -/
theorem d1_d2_zero : d1 * d2 = 0 := by decide +kernel

/-- d₂ ∘ d₃ = 0 (16×16 · 16×16 → 16×16 check) -/
theorem d2_d3_zero : d2 * d3 = 0 := by decide +kernel

/-- d₃ ∘ d₄ = 0 (16×16 · 16×24 → 16×24 check) -/
theorem d3_d4_zero : d3 * d4 = 0 := by decide +kernel

/-- d₄ ∘ d₅ = 0 (16×24 · 24×32 → 16×32 check) -/
theorem d4_d5_zero : d4 * d5 = 0 := by decide +kernel

/-! ## 3. Exactness Verification

For the resolution to be valid (not just a chain complex), we need
ker(d_n) = im(d_{n+1}) at each degree. Since d²=0 gives im ⊆ ker,
exactness reduces to dim(ker(d_n)) = rank(d_{n+1}), equivalently
rank(d_n) + rank(d_{n+1}) = dim(P_n).

We fix the kernel cardinalities of d₁-d₃ exactly, by an explicit bijection
(below), and exhibit rank-witnessing RREF certificates for the larger d₄, d₅ (§3b).

### The kernel-basis certificate

These three statements are *cardinalities*, not ranks, so the RREF certificate used for
d₄/d₅ in §3b does not reach them on its own: an RREF pins a rank, and getting from there
to a cardinality needs rank-nullity plus a cardinality computation. Counting the 2^16
vectors directly is not available either — `decide +kernel` on the enumeration exhausts
the kernel's recursion limit.

So instead of *counting* the kernel we *exhibit* it. For each dₙ we give three matrices

  Bₙ : 16 × k   columns spanning ker(dₙ)
  Cₙ : k × 16   the coordinate projection back
  Xₙ : 16 × mₙ  a cofactor witnessing that `Bₙ Cₙ + 1` kills the kernel

and three matrix identities, each an explicit literal closed by `decide +kernel`:

  (1)  dₙ · Bₙ = 0            every column of Bₙ is in the kernel
  (2)  Cₙ · Bₙ = 1            Bₙ is injective, Cₙ recovers coordinates
  (3)  Bₙ · Cₙ + 1 = Xₙ · dₙ  `Bₙ Cₙ` is the identity **on** the kernel

(3) is what makes the map onto: if `dₙ v = 0` then `(BₙCₙ + 1) v = Xₙ (dₙ v) = 0`, so
`Bₙ (Cₙ v) = v` over F₂. With (2) the two maps are mutually inverse, so ker(dₙ) has
exactly 2^k elements — `kerCard` below packages this once and the three theorems apply it.

Python finds B, C, X (`scripts/generate_a1_kernel_basis.py`); Lean re-derives every
identity from the literals. A single wrong entry fails the build. -/

/-- Over F₂, `a + b = 0` says `a = b`. Four cases, `decide`. -/
theorem f2_add_eq_zero : ∀ {a b : F2}, a + b = 0 → a = b := by decide

/-- **The kernel-basis certificate.** Given `d · B = 0`, `C · B = 1` and
    `B · C + 1 = X · d`, the maps `w ↦ B w` and `v ↦ C v` are mutually inverse
    bijections between `F₂^k` and `ker d`. -/
def kerEquiv {m n k : ℕ} (d : Matrix (Fin m) (Fin n) F2) (B : Matrix (Fin n) (Fin k) F2)
    (C : Matrix (Fin k) (Fin n) F2) (X : Matrix (Fin n) (Fin m) F2)
    (hdB : d * B = 0) (hCB : C * B = 1) (hsplit : B * C + 1 = X * d) :
    (Fin k → F2) ≃ { v : Fin n → F2 // d.mulVec v = 0 } where
  toFun w := ⟨B.mulVec w, by rw [Matrix.mulVec_mulVec, hdB, Matrix.zero_mulVec]⟩
  invFun v := C.mulVec v.val
  left_inv w := by
    show C.mulVec (B.mulVec w) = w
    rw [Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec]
  right_inv v := by
    have hv : d.mulVec v.val = 0 := v.property
    have h : B.mulVec (C.mulVec v.val) + v.val = 0 := by
      have e := congrArg (fun M : Matrix (Fin n) (Fin n) F2 => M.mulVec v.val) hsplit
      simpa [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv] using e
    refine Subtype.ext (funext fun i => ?_)
    exact f2_add_eq_zero (congrFun h i)

/-- The cardinality read off `kerEquiv`: a certified kernel basis of size `k` means
    exactly `2^k` kernel vectors. -/
theorem kerCard {m n k : ℕ} (d : Matrix (Fin m) (Fin n) F2) (B : Matrix (Fin n) (Fin k) F2)
    (C : Matrix (Fin k) (Fin n) F2) (X : Matrix (Fin n) (Fin m) F2)
    (hdB : d * B = 0) (hCB : C * B = 1) (hsplit : B * C + 1 = X * d) :
    Fintype.card { v : Fin n → F2 // d.mulVec v = 0 } = 2 ^ k := by
  rw [← Fintype.card_congr (kerEquiv d B C X hdB hCB hsplit)]
  simp [ZMod.card]

-- d₁ kernel certificate: nullity 9, hence rank(d₁) = 16 - 9 = 7.
def kerB1 : Matrix (Fin 16) (Fin 9) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 1, 0 => 1 | 3, 1 => 1 | 3, 4 => 1 | 4, 1 => 1
  | 5, 2 => 1 | 6, 6 => 1 | 7, 3 => 1 | 10, 4 => 1
  | 11, 5 => 1 | 13, 6 => 1 | 14, 7 => 1 | 15, 8 => 1
  | _, _ => 0

def kerC1 : Matrix (Fin 9) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 1, 4 => 1 | 2, 5 => 1 | 3, 7 => 1
  | 4, 10 => 1 | 5, 11 => 1 | 6, 13 => 1 | 7, 14 => 1
  | 8, 15 => 1
  | _, _ => 0

def kerX1 : Matrix (Fin 16) (Fin 8) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 2, 4 => 1 | 3, 5 => 1 | 6, 7 => 1
  | 8, 2 => 1 | 9, 3 => 1 | 9, 4 => 1 | 12, 6 => 1
  | _, _ => 0

/-- Every column of `kerB1` lies in ker(d₁). -/
theorem d1_kerB_zero : d1 * kerB1 = 0 := by decide +kernel

/-- `kerC1` recovers the coordinates: `kerB1` is injective. -/
theorem d1_kerC_left_inv : kerC1 * kerB1 = 1 := by decide +kernel

/-- `kerB1 · kerC1` is the identity on ker(d₁) — the surjectivity half. -/
theorem d1_kerB_split : kerB1 * kerC1 + 1 = kerX1 * d1 := by decide +kernel

-- d₂ kernel certificate: nullity 7, hence rank(d₂) = 16 - 7 = 9.
def kerB2 : Matrix (Fin 16) (Fin 7) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 1, 0 => 1 | 3, 1 => 1 | 4, 1 => 1 | 5, 2 => 1
  | 6, 4 => 1 | 7, 3 => 1 | 11, 4 => 1 | 14, 5 => 1
  | 15, 6 => 1
  | _, _ => 0

def kerC2 : Matrix (Fin 7) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 1, 4 => 1 | 2, 5 => 1 | 3, 7 => 1
  | 4, 11 => 1 | 5, 14 => 1 | 6, 15 => 1
  | _, _ => 0

def kerX2 : Matrix (Fin 16) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 2, 4 => 1 | 3, 5 => 1 | 6, 7 => 1
  | 6, 14 => 1 | 8, 3 => 1 | 8, 4 => 1 | 9, 11 => 1
  | 10, 6 => 1 | 12, 14 => 1 | 13, 15 => 1
  | _, _ => 0

/-- Every column of `kerB2` lies in ker(d₂). -/
theorem d2_kerB_zero : d2 * kerB2 = 0 := by decide +kernel

/-- `kerC2` recovers the coordinates: `kerB2` is injective. -/
theorem d2_kerC_left_inv : kerC2 * kerB2 = 1 := by decide +kernel

/-- `kerB2 · kerC2` is the identity on ker(d₂) — the surjectivity half. -/
theorem d2_kerB_split : kerB2 * kerC2 + 1 = kerX2 * d2 := by decide +kernel

-- d₃ kernel certificate: nullity 9, hence rank(d₃) = 16 - 9 = 7.
def kerB3 : Matrix (Fin 16) (Fin 9) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 1, 0 => 1 | 3, 1 => 1 | 4, 1 => 1 | 5, 2 => 1
  | 6, 4 => 1 | 7, 3 => 1 | 9, 4 => 1 | 11, 5 => 1
  | 12, 5 => 1 | 13, 6 => 1 | 14, 7 => 1 | 15, 8 => 1
  | _, _ => 0

def kerC3 : Matrix (Fin 9) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 1, 4 => 1 | 2, 5 => 1 | 3, 7 => 1
  | 4, 9 => 1 | 5, 12 => 1 | 6, 13 => 1 | 7, 14 => 1
  | 8, 15 => 1
  | _, _ => 0

def kerX3 : Matrix (Fin 16) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 2, 3 => 1 | 3, 5 => 1 | 6, 7 => 1
  | 8, 6 => 1 | 10, 14 => 1 | 11, 15 => 1
  | _, _ => 0

/-- Every column of `kerB3` lies in ker(d₃). -/
theorem d3_kerB_zero : d3 * kerB3 = 0 := by decide +kernel

/-- `kerC3` recovers the coordinates: `kerB3` is injective. -/
theorem d3_kerC_left_inv : kerC3 * kerB3 = 1 := by decide +kernel

/-- `kerB3 · kerC3` is the identity on ker(d₃) — the surjectivity half. -/
theorem d3_kerB_split : kerB3 * kerC3 + 1 = kerX3 * d3 := by decide +kernel

/-- Kernel cardinality of d₁: 2^9 = 512.
    rank(d₁) = 16 - 9 = 7. Combined with rank(d₂) = 9 (below): 7 + 9 = 16 = dim(P₁).

    Proven from the `kerB1`/`kerC1`/`kerX1` certificate above; kernel-pure. -/
theorem d1_kernel_card :
    Fintype.card { v : Fin 16 → ZMod 2 // d1.mulVec v = 0 } = 512 :=
  kerCard d1 kerB1 kerC1 kerX1 d1_kerB_zero d1_kerC_left_inv d1_kerB_split

/-- Kernel cardinality of d₂: 2^7 = 128.
    rank(d₂) = 16 - 7 = 9. Proven from the `kerB2`/`kerC2`/`kerX2` certificate; kernel-pure. -/
theorem d2_kernel_card :
    Fintype.card { v : Fin 16 → ZMod 2 // d2.mulVec v = 0 } = 128 :=
  kerCard d2 kerB2 kerC2 kerX2 d2_kerB_zero d2_kerC_left_inv d2_kerB_split

/-- Kernel cardinality of d₃: 2^9 = 512.
    rank(d₃) = 16 - 9 = 7. Proven from the `kerB3`/`kerC3`/`kerX3` certificate; kernel-pure. -/
theorem d3_kernel_card :
    Fintype.card { v : Fin 16 → ZMod 2 // d3.mulVec v = 0 } = 512 :=
  kerCard d3 kerB3 kerC3 kerX3 d3_kerB_zero d3_kerC_left_inv d3_kerB_split

/-! ## 3b. RREF Witnesses for d₄ and d₅

For d₄ (16×24) and d₅ (24×32), kernel enumeration exceeds any evaluator's
budget (2²⁴ and 2³² elements). Instead we provide RREF certificates:
invertible transformation matrices P such that P × d = RREF.
The rank = number of nonzero rows in the RREF.

Python generates these (scripts/generate_a1_resolution.py).
Lean VERIFIES them (`decide +kernel` on matrix products). If any entry
in P, P_inv, or RREF is wrong, the proof fails to compile. -/

-- d₄ RREF witness: P₄ × d₄ = rref₄ with rank 9
def P4 : Matrix (Fin 16) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 1, 3 => 1 | 2, 5 => 1 | 3, 7 => 1 | 4, 6 => 1
  | 5, 11 => 1 | 6, 13 => 1 | 7, 15 => 1 | 8, 14 => 1
  | 9, 6 => 1 | 9, 9 => 1 | 10, 10 => 1 | 11, 2 => 1
  | 12, 11 => 1 | 12, 12 => 1 | 13, 3 => 1 | 13, 4 => 1
  | 14, 8 => 1 | 15, 0 => 1
  | _, _ => 0

def P4_inv : Matrix (Fin 16) (Fin 16) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 15 => 1 | 1, 0 => 1 | 2, 11 => 1 | 3, 1 => 1
  | 4, 1 => 1 | 4, 13 => 1 | 5, 2 => 1 | 6, 4 => 1 | 7, 3 => 1
  | 8, 14 => 1 | 9, 4 => 1 | 9, 9 => 1 | 10, 10 => 1
  | 11, 5 => 1 | 12, 5 => 1 | 12, 12 => 1 | 13, 6 => 1
  | 14, 8 => 1 | 15, 7 => 1
  | _, _ => 0

def rref4 : Matrix (Fin 16) (Fin 24) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 0 => 1 | 1, 2 => 1 | 2, 3 => 1 | 2, 4 => 1
  | 3, 6 => 1 | 3, 9 => 1 | 4, 8 => 1 | 5, 10 => 1
  | 6, 11 => 1 | 6, 12 => 1 | 7, 14 => 1 | 7, 17 => 1
  | 8, 16 => 1
  | _, _ => 0

/-- P₄ × d₄ = rref₄ (RREF of d₄, rank 9). -/
theorem d4_rref_valid : P4 * d4 = rref4 := by decide +kernel

/-- P₄ is invertible: P₄ × P₄⁻¹ = I. -/
theorem P4_invertible : P4 * P4_inv = 1 := by decide +kernel

/-- rank(d₄) = 9 (9 nonzero rows in rref₄). -/
theorem d4_rank_9 : ∀ i : Fin 16, (9 ≤ i.val) →
    (∀ j : Fin 24, rref4 i j = 0) := by decide +kernel

-- d₅ RREF witness: P₅ × d₅ = rref₅ with rank 15
def P5 : Matrix (Fin 24) (Fin 24) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 1 => 1 | 1, 3 => 1 | 2, 5 => 1 | 3, 7 => 1 | 4, 6 => 1
  | 5, 11 => 1 | 6, 13 => 1 | 7, 15 => 1 | 8, 14 => 1
  | 9, 20 => 1 | 10, 21 => 1 | 11, 23 => 1 | 12, 18 => 1
  | 13, 19 => 1 | 13, 20 => 1 | 14, 22 => 1 | 15, 0 => 1
  | 16, 16 => 1 | 17, 14 => 1 | 17, 17 => 1
  | 18, 11 => 1 | 18, 12 => 1 | 19, 6 => 1 | 19, 9 => 1
  | 20, 3 => 1 | 20, 4 => 1 | 21, 10 => 1 | 22, 8 => 1 | 23, 2 => 1
  | _, _ => 0

def P5_inv : Matrix (Fin 24) (Fin 24) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 15 => 1 | 1, 0 => 1 | 2, 23 => 1 | 3, 1 => 1
  | 4, 1 => 1 | 4, 20 => 1 | 5, 2 => 1 | 6, 4 => 1 | 7, 3 => 1
  | 8, 22 => 1 | 9, 4 => 1 | 9, 19 => 1 | 10, 21 => 1
  | 11, 5 => 1 | 12, 5 => 1 | 12, 18 => 1 | 13, 6 => 1
  | 14, 8 => 1 | 15, 7 => 1 | 16, 16 => 1
  | 17, 8 => 1 | 17, 17 => 1 | 18, 12 => 1
  | 19, 9 => 1 | 19, 13 => 1 | 20, 9 => 1 | 21, 10 => 1
  | 22, 14 => 1 | 23, 11 => 1
  | _, _ => 0

def rref5 : Matrix (Fin 24) (Fin 32) F2 := Matrix.of fun k i =>
  match k.val, i.val with
  | 0, 0 => 1 | 1, 2 => 1 | 2, 3 => 1 | 2, 4 => 1
  | 3, 6 => 1 | 3, 9 => 1 | 4, 8 => 1 | 5, 10 => 1
  | 6, 11 => 1 | 6, 12 => 1 | 7, 14 => 1 | 7, 17 => 1
  | 8, 16 => 1 | 9, 18 => 1 | 10, 19 => 1 | 10, 20 => 1 | 10, 26 => 1
  | 11, 22 => 1 | 11, 29 => 1 | 12, 24 => 1 | 13, 25 => 1 | 14, 28 => 1
  | _, _ => 0

/-- P₅ × d₅ = rref₅ (RREF of d₅, rank 15). -/
theorem d5_rref_valid : P5 * d5 = rref5 := by decide +kernel

/-- P₅ is invertible: P₅ × P₅⁻¹ = I. -/
theorem P5_invertible : P5 * P5_inv = 1 := by decide +kernel

/-- rank(d₅) = 15 (15 nonzero rows in rref₅). -/
theorem d5_rank_15 : ∀ i : Fin 24, (15 ≤ i.val) →
    (∀ j : Fin 32, rref5 i j = 0) := by decide +kernel

/-! Exactness from kernel cardinalities (d₁-d₃) and RREF ranks (d₄-d₅):
  P₀: rank(ε)=1, rank(d₁)=7. dim(P₀)=8. 1+7=8. ✓
  P₁: rank(d₁)=7, rank(d₂)=9. dim(P₁)=16. 7+9=16. ✓
  P₂: rank(d₂)=9, rank(d₃)=7. dim(P₂)=16. 9+7=16. ✓
  P₃: rank(d₃)=7, rank(d₄)=9. dim(P₃)=16. 7+9=16. ✓  (d₄ rank from RREF)
  P₄: rank(d₄)=9, rank(d₅)=15. dim(P₄)=24. 9+15=24. ✓  (d₅ rank from RREF)

  All ranks machine-checked, and all of it kernel-pure: d₁-d₃ via the kernel-basis
  certificates of §3 (nullity, hence rank), d₄-d₅ via the RREF witnesses of §3b.
-/

/-- Exactness **arithmetic**: rank(d_n) + rank(d_{n+1}) = dim(P_n) at every degree.

    ⚠️ Read the name precisely. This is a closed arithmetic identity on the ranks recorded
    above — it says the documented ranks are *consistent with* exactness. It is NOT a proof
    that `ker dₙ = range dₙ₊₁`, and nothing about the matrices enters its proof.

    The genuine statement is `A1Exactness.resolution_is_exact` (Phase 5q.T Wave T3), proven
    kernel-purely from an explicit contracting homotopy. This theorem is retained as the
    rank bookkeeping it always was, now honestly labelled. -/
theorem exactness_rank_nullity :
    1 + 7 = 8         -- P₀
    ∧ 7 + 9 = 16      -- P₁
    ∧ 9 + 7 = 16      -- P₂
    ∧ 7 + 9 = 16      -- P₃
    ∧ 9 + 15 = 24     -- P₄
    := by omega

/-- The chain complex property holds at all levels. -/
theorem chain_complex_property :
    d1 * d2 = 0 ∧ d2 * d3 = 0 ∧ d3 * d4 = 0 ∧ d4 * d5 = 0 :=
  ⟨d1_d2_zero, d2_d3_zero, d3_d4_zero, d4_d5_zero⟩

/-! ## 4. A(1)-LINEARITY of the differentials  [Phase 5q.T, 2026-08-15]

Until now the claim "these matrices are the differentials of a complex of **free
A(1)-modules**" was carried only by the comments in §1: nothing in Lean tied `d1 … d5`
to the A(1)-action. A chain complex of F₂-vector spaces whose differentials happened to
square to zero would have satisfied every theorem above. This section closes that gap.

**Which side.** In the left-regular representation a coefficient vector `v ∈ F₂⁸` denotes
an element `x ∈ A(1)`, and `Lmat a *ᵥ v` denotes `e a · x`. So `d₁ *ᵥ (v₁, v₂) =
Sq¹·x₁ + Sq²·x₂`, which is A(1)-linear for the **right** action `x ↦ x · b` — the
differentials are given by left multiplication, hence commute with right multiplication.
`P n` is therefore a free **right** A(1)-module of rank `rₙ`, and `Extⁿ` below is right-module
Ext (canonically isomorphic to the left-module one via the antipode of the Hopf algebra A(1);
the dimensions this file feeds downstream are the same either way).

`blockR n b` is the matrix of `· e b` on `F₂ⁿ = A(1)^{n/8}`: block-diagonal with `Rmat b`
in each 8×8 diagonal block. Each theorem below is the statement
`dₙ ∘ (· e b) = (· e b) ∘ dₙ` on the nose, for every one of the eight basis elements. -/

/-- Right multiplication by `e b` on a free right A(1)-module of rank `n / 8`, in the
    F₂-expanded encoding: block diagonal with `Rmat b` in each 8×8 block. -/
def blockR (n : ℕ) (b : Idx) : Matrix (Fin n) (Fin n) F2 := Matrix.of fun k i =>
  if k.val / 8 = i.val / 8 then
    Rmat b ⟨k.val % 8, Nat.mod_lt _ (by norm_num)⟩ ⟨i.val % 8, Nat.mod_lt _ (by norm_num)⟩
  else 0

/-- On a rank-1 free module `blockR` is just right multiplication. Sanity-pins `blockR`. -/
theorem blockR_eight : ∀ b : Idx, blockR 8 b = Rmat b := by decide

/-- `blockR` at the unit is the identity, at each rank occurring in the resolution:
    the action is unital. -/
theorem blockR_zero_eq_one :
    blockR 16 0 = 1 ∧ blockR 24 0 = 1 ∧ blockR 32 0 = 1 := by
  refine ⟨by decide, by decide, by decide +kernel⟩

/-- **d₁ is right A(1)-linear.** -/
theorem d1_a1_linear : ∀ b : Idx, d1 * blockR 16 b = Rmat b * d1 := by decide

/-- **d₂ is right A(1)-linear.** -/
theorem d2_a1_linear : ∀ b : Idx, d2 * blockR 16 b = blockR 16 b * d2 := by decide

/-- **d₃ is right A(1)-linear.** -/
theorem d3_a1_linear : ∀ b : Idx, d3 * blockR 16 b = blockR 16 b * d3 := by decide

/-- **d₄ is right A(1)-linear.** -/
theorem d4_a1_linear : ∀ b : Idx, d4 * blockR 24 b = blockR 16 b * d4 := by decide +kernel

/-- **d₅ is right A(1)-linear.** -/
theorem d5_a1_linear : ∀ b : Idx, d5 * blockR 32 b = blockR 24 b * d5 := by decide +kernel

/-- **The resolution is a complex of free A(1)-modules, not merely of F₂-vector spaces.**

    Every differential commutes with the right A(1)-action on the free modules
    `Pₙ = A(1)^{rₙ}`, for every basis element of A(1) — hence, by F₂-bilinearity, for
    every element. Together with `chain_complex_property` this is what makes
    `Hom_{A(1)}(P•, F₂)` a cochain complex and its cohomology `Ext*_{A(1)}(F₂, F₂)`.

    Before Phase 5q.T this was asserted only in the §1 comments. -/
theorem resolution_is_a1_linear :
    (∀ b : Idx, d1 * blockR 16 b = Rmat b * d1)
    ∧ (∀ b : Idx, d2 * blockR 16 b = blockR 16 b * d2)
    ∧ (∀ b : Idx, d3 * blockR 16 b = blockR 16 b * d3)
    ∧ (∀ b : Idx, d4 * blockR 24 b = blockR 16 b * d4)
    ∧ (∀ b : Idx, d5 * blockR 32 b = blockR 24 b * d5) :=
  ⟨d1_a1_linear, d2_a1_linear, d3_a1_linear, d4_a1_linear, d5_a1_linear⟩

end SKEFTHawking.A1
