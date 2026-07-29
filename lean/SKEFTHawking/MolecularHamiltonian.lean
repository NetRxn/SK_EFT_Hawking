import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.MetricSpace.Contracting
import Physlib.QuantumMechanics.SpaceDQuantumSystem

/-!
# The molecular Coulomb Hamiltonian and Kato–Rellich self-adjointness (Phase 6BB, Wave 1)

The gating analysis wave of the verified density-functional-theory foundations. The physical
content is that the `N`-electron molecular Schrödinger operator

  `H = -Δ/2m + V`,    `V(x) = -∑ᵢₖ Zₖ/|xᵢ - Rₖ| + ∑_{i<j} 1/|xᵢ - xⱼ|`

is **essentially self-adjoint** on a core (the Schwartz functions), so its closure is a genuine
quantum-mechanical observable with a real spectrum — the precondition for *every* later DFT result
(Hohenberg–Kohn, Levy–Lieb). The mechanism is the **Kato–Rellich theorem**: a symmetric perturbation
`B` of a self-adjoint operator `A`, relatively `A`-bounded with relative bound `a < 1`, yields a
self-adjoint `A + B` (essentially self-adjoint on any core of `A`).

## Substrate (Route C — Mathlib `LinearPMap`, in-tree)

The unbounded operators are Mathlib partial linear maps `H →ₗ.[ℂ] H` with the densely-defined adjoint
`A†` (`Mathlib.Analysis.InnerProductSpace.LinearPMap`: `LinearPMap.adjoint`, `IsFormalAdjoint`,
`adjoint_isClosed`, the `Star` instance `IsSelfAdjoint A ↔ A† = A`, `IsSelfAdjoint.isClosed`,
`IsSelfAdjoint.dense_domain`).

PhysLib's spectral theory (`QuantumMechanics/DDimensions/Operators/SpectralTheory.*`) is *not* used:
it does not compile at the project's pinned PhysLib/Mathlib/Lean-4.29.1 (verified 2026-06-29 by
`lake build` — a localized `Or.casesOn` toolchain drift in `SpectralTheory/Basic.lean` and a
mid-refactor `DDimensions/Basic.lean`), and bumping the shared PhysLib pin is disallowed (in-repo
lakefile warning; pin shared with a parallel agent). The needed self-adjointness substrate is built
in-tree here on Mathlib instead.

## What is proven here vs. tracked

The **abstract Kato–Rellich reduction** (the mathematical heart) is proven in full. The molecular
instantiation rests on genuinely Mathlib-scale analytic inputs that carry no constructive scaffold in
current Mathlib (verified 2026-06-29 by semantic search: no Hardy inequality, no operator
relative-boundedness, no Laplacian/Schrödinger essential self-adjointness, no unbounded
self-adjointness-via-range criterion; only the Gagliardo–Nirenberg–Sobolev embedding and the
Schwartz/Fourier substrate). These are carried as **disclosed, load-bearing tracked hypotheses**
(Prop-valued arguments — *not* axioms, never vacuous), each with a discharge plan = a dedicated future
Hardy/Fourier analysis sub-wave:

  * `kineticOperator` is essentially self-adjoint on the Schwartz core (free-Laplacian self-adjointness
    via the Fourier multiplier `|p|²`), and
  * the molecular Coulomb potential is `kineticOperator`-bounded with relative bound `< 1`
    (Kato's inequality / Hardy's inequality `∫|u|²/|x|² ≤ 4∫|∇u|²` in 3D).

Invariants (Phase 6BB): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new
project-local axiom; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.DFT

open LinearPMap
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Applying two equal partial linear maps to the same underlying vector gives the same value
(transport across an operator equality, dodging `rw`/`▸` motive failures on the dependent domain). -/
lemma applyEq_of_pmap_eq {f g : H →ₗ.[ℂ] H} (h : f = g) (x : H) (hx : x ∈ f.domain) :
    (f ⟨x, hx⟩ : H) = g ⟨x, h ▸ hx⟩ := by subst h; rfl

/-- An unbounded operator `T` is **symmetric** if `⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in its domain.
For a densely-defined `T` this is equivalent to `T ≤ T†`. -/
def IsSymmetricPMap (T : H →ₗ.[ℂ] H) : Prop :=
  ∀ x y : T.domain, ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ

/-- **Relative (Kato) boundedness.** `B` is relatively `A`-bounded with bounds `a, b` if
`A.domain ⊆ B.domain` and, for every `x` in the domain of `A`,

  `‖B x‖ ≤ a · ‖A x‖ + b · ‖x‖`.

The infimum of admissible `a` is the *relative bound*; Kato–Rellich requires it to be `< 1`. -/
structure IsRelBounded (A B : H →ₗ.[ℂ] H) (a b : ℝ) : Prop where
  /-- The domain of `A` is contained in the domain of `B`. -/
  domain_le : A.domain ≤ B.domain
  /-- The Kato bound `‖B x‖ ≤ a‖A x‖ + b‖x‖` on the domain of `A`. -/
  bound : ∀ x : A.domain, ‖B ⟨(x : H), domain_le x.2⟩‖ ≤ a * ‖A x‖ + b * ‖(x : H)‖

/-- For a symmetric operator the diagonal of the quadratic form `⟪A x, x⟫` is real. -/
lemma IsSymmetricPMap.inner_self_im_eq_zero {A : H →ₗ.[ℂ] H} (hA : IsSymmetricPMap A)
    (x : A.domain) : (⟪A x, (x : H)⟫_ℂ).im = 0 := by
  have h : (starRingEnd ℂ) ⟪A x, (x : H)⟫_ℂ = ⟪A x, (x : H)⟫_ℂ := by
    rw [inner_conj_symm]; exact (hA x x).symm
  exact Complex.conj_eq_iff_im.mp h

/-- For a symmetric operator and real `μ`, `‖(A - iμ)x‖² = ‖A x‖² + μ²‖x‖²`. The cross term vanishes
because `⟪A x, x⟫` is real (`inner_self_im_eq_zero`); this is the resolvent lower bound
`‖(A - iμ)x‖ ≥ |μ|·‖x‖` underlying invertibility of a self-adjoint operator at non-real points. -/
lemma IsSymmetricPMap.norm_sub_I_smul_sq {A : H →ₗ.[ℂ] H} (hA : IsSymmetricPMap A)
    (μ : ℝ) (x : A.domain) :
    ‖(A x : H) - (Complex.I * (μ : ℂ)) • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + μ ^ 2 * ‖(x : H)‖ ^ 2 := by
  rw [@norm_sub_sq ℂ, norm_smul]
  have hre : RCLike.re ⟪(A x : H), (Complex.I * (μ : ℂ)) • (x : H)⟫_ℂ = 0 := by
    simp [inner_smul_right, hA.inner_self_im_eq_zero x]
  rw [hre]
  simp [Complex.norm_I, mul_pow]

/-- The **resolvent lower bound** for a symmetric operator: `|μ|·‖x‖ ≤ ‖(A - iμ)x‖`. In particular
`A - iμ` is injective for `μ ≠ 0`, the first half of invertibility at non-real points. -/
lemma IsSymmetricPMap.mul_norm_le_norm_sub_I_smul {A : H →ₗ.[ℂ] H} (hA : IsSymmetricPMap A)
    (μ : ℝ) (x : A.domain) :
    |μ| * ‖(x : H)‖ ≤ ‖(A x : H) - (Complex.I * (μ : ℂ)) • (x : H)‖ := by
  have hsq := hA.norm_sub_I_smul_sq μ x
  have hle : (|μ| * ‖(x : H)‖) ^ 2 ≤ ‖(A x : H) - (Complex.I * (μ : ℂ)) • (x : H)‖ ^ 2 := by
    rw [hsq, mul_pow, sq_abs]; nlinarith [sq_nonneg ‖(A x : H)‖]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hle

/-- A self-adjoint partial operator is symmetric (`A† = A` and the formal-adjoint relation). -/
lemma IsSelfAdjoint.isSymmetricPMap [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    IsSymmetricPMap A := by
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hfa
  intro x y
  exact hfa x y

/-- A symmetric operator has no non-real eigenvalue: `A y = iμ·y` with `μ ≠ 0` forces `y = 0`
(equivalently `A - iμ` is injective). The kernel input to the deficiency/surjectivity argument. -/
lemma IsSymmetricPMap.eq_zero_of_apply_eq_I_smul {A : H →ₗ.[ℂ] H} (hA : IsSymmetricPMap A) {μ : ℝ}
    (hμ : μ ≠ 0) (y : A.domain) (h : (A y : H) = (Complex.I * (μ : ℂ)) • (y : H)) : (y : H) = 0 := by
  have hb := hA.mul_norm_le_norm_sub_I_smul μ y
  rw [h, sub_self, norm_zero] at hb
  have hy : ‖(y : H)‖ = 0 := le_antisymm (by nlinarith [abs_pos.mpr hμ, norm_nonneg (y : H)])
    (norm_nonneg _)
  simpa using hy

/-- **Density half of surjectivity.** For self-adjoint `A` and `μ ≠ 0`, any `y` orthogonal to the
range of `x ↦ A x - iμ·x` is zero — i.e. that range is dense. The proof routes a vector orthogonal to
the range into `A†.domain` via `mem_adjoint_domain_of_exists`, identifies `A† = A`, and applies the
no-non-real-eigenvalue lemma. -/
lemma IsSelfAdjoint.eq_zero_of_orthogonal_range_sub_I_smul [CompleteSpace H] {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) {μ : ℝ} (hμ : μ ≠ 0) (y : H)
    (hy : ∀ x : A.domain, ⟪y, (A x : H) - (Complex.I * (μ : ℂ)) • (x : H)⟫_ℂ = 0) : y = 0 := by
  have h1 : ∀ x : A.domain, ⟪y, (A x : H)⟫_ℂ = (Complex.I * (μ : ℂ)) * ⟪y, (x : H)⟫_ℂ := by
    intro x
    have hx := hy x
    rw [inner_sub_right, inner_smul_right, sub_eq_zero] at hx
    exact hx
  have hw : ∀ x : A.domain, ⟪(-(Complex.I * (μ : ℂ))) • y, (x : H)⟫_ℂ = ⟪y, A x⟫_ℂ := by
    intro x
    rw [inner_smul_left, h1 x, _root_.map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hmem : y ∈ (LinearPMap.adjoint A).domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨_, hw⟩
  have hAy : (LinearPMap.adjoint A) ⟨y, hmem⟩ = (-(Complex.I * (μ : ℂ))) • y :=
    LinearPMap.adjoint_apply_eq hA.dense_domain ⟨y, hmem⟩ (fun x => hw x)
  have hsa : LinearPMap.adjoint A = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hsym : IsSymmetricPMap A := IsSelfAdjoint.isSymmetricPMap hA
  have hmem' : y ∈ A.domain := hsa ▸ hmem
  have hval : (A ⟨y, hmem'⟩ : H) = -(Complex.I * (μ : ℂ)) • y := by
    rw [applyEq_of_pmap_eq hsa.symm y hmem']; exact hAy
  refine hsym.eq_zero_of_apply_eq_I_smul (μ := -μ) (by simpa using hμ) ⟨y, hmem'⟩ ?_
  rw [hval]; push_cast; ring_nf

/-- The sum of two symmetric partial operators is symmetric (on the intersection domain). -/
lemma IsSymmetricPMap.add {A B : H →ₗ.[ℂ] H} (hA : IsSymmetricPMap A) (hB : IsSymmetricPMap B) :
    IsSymmetricPMap (A + B) := by
  intro x y
  obtain ⟨xv, hx⟩ := x
  obtain ⟨yv, hy⟩ := y
  simp only [LinearPMap.add_domain, Submodule.mem_inf] at hx hy
  rw [LinearPMap.add_apply, LinearPMap.add_apply, inner_add_left, inner_add_right,
    hA ⟨xv, hx.1⟩ ⟨yv, hy.1⟩, hB ⟨xv, hx.2⟩ ⟨yv, hy.2⟩]

/-- **Closed half of surjectivity.** For self-adjoint (hence closed) `A` and `μ ≠ 0`, the range of
`x ↦ A x - iμ·x` is topologically closed: a convergent image sequence has Cauchy preimages (lower
bound), whose limit lies in `D(A)` by closedness of the graph. -/
lemma IsSelfAdjoint.isClosed_range_sub_I_smul [CompleteSpace H] {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) {μ : ℝ} (hμ : μ ≠ 0) :
    IsClosed {w : H | ∃ x : A.domain, (A x : H) - (Complex.I * (μ : ℂ)) • (x : H) = w} := by
  apply IsSeqClosed.isClosed
  intro w wlim hw_mem hw_lim
  -- witnesses `x n` with `A (x n) - iμ (x n) = w n`  (w is the SEQUENCE, wlim the limit)
  choose x hx using hw_mem
  have hsym : IsSymmetricPMap A := IsSelfAdjoint.isSymmetricPMap hA
  have hμpos : 0 < |μ| := abs_pos.mpr hμ
  -- the preimage sequence is Cauchy (from the lower bound) hence converges
  have hCauchy : CauchySeq fun n => ((x n : H)) := by
    have hwc : CauchySeq w := hw_lim.cauchySeq
    rw [Metric.cauchySeq_iff] at hwc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hwc (|μ| * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb := hsym.mul_norm_le_norm_sub_I_smul μ (x m - x n)
    have hsub : (A (x m - x n) : H) - (Complex.I * (μ : ℂ)) • ((x m - x n : A.domain) : H)
        = w m - w n := by
      rw [LinearPMap.map_sub, AddSubgroupClass.coe_sub, smul_sub, sub_sub_sub_comm, hx m, hx n]
    rw [hsub] at hb
    rw [dist_eq_norm]
    have hlt := hN m hm n hn
    rw [dist_eq_norm] at hlt
    have hbb : |μ| * ‖(x m : H) - (x n : H)‖ ≤ ‖w m - w n‖ := by
      simpa [AddSubgroupClass.coe_sub] using hb
    nlinarith [norm_nonneg ((x m : H) - (x n : H))]
  obtain ⟨x₀, hx₀⟩ := cauchySeq_tendsto_of_complete hCauchy
  -- `A (x n) = w n + iμ (x n) → wlim + iμ x₀`, so `(x₀, wlim + iμ x₀) ∈ graph A`
  have hAx : Filter.Tendsto (fun n => (A (x n) : H)) Filter.atTop
      (nhds (wlim + (Complex.I * (μ : ℂ)) • x₀)) := by
    have heq : (fun n => (A (x n) : H)) = fun n => w n + (Complex.I * (μ : ℂ)) • (x n : H) := by
      funext n; rw [← hx n]; abel
    rw [heq]
    exact hw_lim.add (hx₀.const_smul _)
  have hgraph : (x₀, wlim + (Complex.I * (μ : ℂ)) • x₀) ∈ A.graph :=
    hA.isClosed.mem_of_tendsto (hx₀.prodMk_nhds hAx)
      (Filter.Eventually.of_forall fun n => A.mem_graph (x n))
  obtain ⟨y₀, hy₀_eq, hy₀_val⟩ := (LinearPMap.mem_graph_iff A).mp hgraph
  refine ⟨y₀, ?_⟩
  have hy_eq : (y₀ : H) = x₀ := hy₀_eq
  have hy_val : (A y₀ : H) = wlim + (Complex.I * (μ : ℂ)) • x₀ := hy₀_val
  rw [hy_val, hy_eq]; module

/-- **Surjectivity** of `A - iμ` for self-adjoint `A` and `μ ≠ 0`: dense range (orthogonal complement
trivial) + closed range ⟹ full range. Equivalently `iμ` is in the resolvent set. -/
lemma IsSelfAdjoint.surjective_sub_I_smul [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {μ : ℝ} (hμ : μ ≠ 0) (z : H) :
    ∃ x : A.domain, (A x : H) - (Complex.I * (μ : ℂ)) • (x : H) = z := by
  set L : A.domain →ₗ[ℂ] H := A.toFun - (Complex.I * (μ : ℂ)) • A.domain.subtype with hL
  have hLapp : ∀ x : A.domain, L x = (A x : H) - (Complex.I * (μ : ℂ)) • (x : H) := by
    intro x; simp [hL]
  have hKbot : (LinearMap.range L)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine IsSelfAdjoint.eq_zero_of_orthogonal_range_sub_I_smul hA hμ y (fun x => ?_)
    rw [← hLapp x, inner_eq_zero_symm]
    exact (Submodule.mem_orthogonal _ _).mp hy (L x) (LinearMap.mem_range_self L x)
  have hKclosed : IsClosed ((LinearMap.range L : Submodule ℂ H) : Set H) := by
    convert IsSelfAdjoint.isClosed_range_sub_I_smul hA hμ using 2
  have hKtop : LinearMap.range L = ⊤ := by
    have hcl : (LinearMap.range L).topologicalClosure = ⊤ :=
      Submodule.topologicalClosure_eq_top_iff.mpr hKbot
    rwa [hKclosed.submodule_topologicalClosure_eq] at hcl
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (hKtop.ge (Submodule.mem_top : z ∈ (⊤ : Submodule ℂ H)))
  exact ⟨x, by rw [← hLapp x]; exact hx⟩

/-- **Basic criterion of self-adjointness.** A densely-defined symmetric operator `S` with `S ± iμ`
both surjective (`μ ≠ 0`) is self-adjoint: the deficiency vector `a - x ∈ ker(S† - iμ) ⊥ ran(S + iμ)
= H`, forcing `D(S†) ⊆ D(S)`. -/
lemma IsSymmetricPMap.isSelfAdjoint_of_surjective [CompleteSpace H] {S : H →ₗ.[ℂ] H}
    (hS : IsSymmetricPMap S) (hdense : Dense (S.domain : Set H)) {μ : ℝ}
    (hpos : ∀ z : H, ∃ x : S.domain, (S x : H) - (Complex.I * (μ : ℂ)) • (x : H) = z)
    (hneg : ∀ z : H, ∃ x : S.domain, (S x : H) + (Complex.I * (μ : ℂ)) • (x : H) = z) :
    IsSelfAdjoint S := by
  have hSle : S ≤ LinearPMap.adjoint S := LinearPMap.IsFormalAdjoint.le_adjoint hdense hS
  have hfa : (LinearPMap.adjoint S).IsFormalAdjoint S := LinearPMap.adjoint_isFormalAdjoint hdense
  -- value of S† on elements of D(S): `S† x = S x`
  have hval : ∀ x : S.domain, (LinearPMap.adjoint S) ⟨(x : H), hSle.1 x.2⟩ = (S x : H) :=
    fun x => (hSle.2 (rfl : ((x : H)) = ((⟨(x : H), hSle.1 x.2⟩ : (LinearPMap.adjoint S).domain) : H))).symm
  -- D(S†) ⊆ D(S)
  have hdom : ∀ a : H, a ∈ (LinearPMap.adjoint S).domain → a ∈ S.domain := by
    intro a ha
    obtain ⟨x, hx⟩ := hpos ((LinearPMap.adjoint S) ⟨a, ha⟩ - (Complex.I * (μ : ℂ)) • a)
    set w : H := a - (x : H) with hw
    have hwmem : w ∈ (LinearPMap.adjoint S).domain := sub_mem ha (hSle.1 x.2)
    have hSadjw : (LinearPMap.adjoint S) ⟨w, hwmem⟩ = (Complex.I * (μ : ℂ)) • w := by
      have hlin : (LinearPMap.adjoint S) ⟨w, hwmem⟩
          = (LinearPMap.adjoint S) ⟨a, ha⟩ - (S x : H) := by
        have he : (⟨w, hwmem⟩ : (LinearPMap.adjoint S).domain)
            = ⟨a, ha⟩ - ⟨(x : H), hSle.1 x.2⟩ := Subtype.ext (by simp [hw, AddSubgroupClass.coe_sub])
        rw [he, LinearPMap.map_sub, hval x]
      rw [hlin, hw]
      linear_combination (norm := module) (-hx)
    have hperp : ∀ u : S.domain, ⟪(S u : H) + (Complex.I * (μ : ℂ)) • (u : H), w⟫_ℂ = 0 := by
      intro u
      have h1 : ⟪w, (S u : H)⟫_ℂ = ⟪(LinearPMap.adjoint S) ⟨w, hwmem⟩, (u : H)⟫_ℂ :=
        (hfa ⟨w, hwmem⟩ u).symm
      rw [inner_add_left, inner_smul_left, ← inner_conj_symm (S u : H) w, h1, hSadjw]
      rw [inner_smul_left, ← inner_conj_symm w (u : H)]
      simp only [map_mul, _root_.map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]
      ring
    have hw0 : w = 0 := by
      have hall : ∀ z : H, ⟪z, w⟫_ℂ = 0 := fun z => by
        obtain ⟨u, hu⟩ := hneg z; rw [← hu]; exact hperp u
      exact inner_self_eq_zero.mp (hall w)
    have : a = (x : H) := by rw [hw] at hw0; linear_combination (norm := module) hw0
    rw [this]; exact x.2
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ hSle
  refine ⟨fun a ha => hdom a ha, fun {x y} hxy => ?_⟩
  rw [show (S y : H) = (LinearPMap.adjoint S) ⟨(y : H), hSle.1 y.2⟩ from (hval y).symm]
  exact congrArg _ (Subtype.ext hxy)

/-- `‖A x‖ ≤ ‖(A - iμ)x‖`: the kinetic part is dominated by the shifted operator. -/
lemma IsSymmetricPMap.norm_le_norm_sub_I_smul {A : H →ₗ.[ℂ] H} (hA : IsSymmetricPMap A) (μ : ℝ)
    (x : A.domain) : ‖(A x : H)‖ ≤ ‖(A x : H) - (Complex.I * (μ : ℂ)) • (x : H)‖ := by
  have h := hA.norm_sub_I_smul_sq μ x
  have hsq : ‖(A x : H)‖ ^ 2 ≤ ‖(A x : H) - (Complex.I * (μ : ℂ)) • (x : H)‖ ^ 2 := by
    rw [h]; nlinarith [mul_nonneg (sq_nonneg μ) (sq_nonneg ‖(x : H)‖)]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq

/-- The linear bijection `x ↦ A x - iμ·x : D(A) ≃ H` for self-adjoint `A`, `μ ≠ 0` (injective by the
resolvent lower bound, surjective by `surjective_sub_I_smul`). Its inverse is the bounded resolvent. -/
noncomputable def resolventEquiv [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {μ : ℝ} (hμ : μ ≠ 0) : A.domain ≃ₗ[ℂ] H :=
  LinearEquiv.ofBijective (A.toFun - (Complex.I * (μ : ℂ)) • A.domain.subtype) <| by
    constructor
    · intro x y hxy
      have hb := (IsSelfAdjoint.isSymmetricPMap hA).mul_norm_le_norm_sub_I_smul μ (x - y)
      have hL0 : (A (x - y) : H) - (Complex.I * (μ : ℂ)) • ((x - y : A.domain) : H) = 0 := by
        have hxy' := sub_eq_zero.mpr hxy
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.subtype_apply,
          LinearPMap.toFun_eq_coe] at hxy'
        rw [LinearPMap.map_sub, AddSubgroupClass.coe_sub, smul_sub]
        linear_combination (norm := module) hxy'
      rw [hL0, norm_zero] at hb
      have : ((x - y : A.domain) : H) = 0 :=
        norm_eq_zero.mp (le_antisymm
          (by nlinarith [abs_pos.mpr hμ, norm_nonneg ((x - y : A.domain) : H)]) (norm_nonneg _))
      rw [AddSubgroupClass.coe_sub, sub_eq_zero] at this
      exact Subtype.ext this
    · intro z
      obtain ⟨x, hx⟩ := IsSelfAdjoint.surjective_sub_I_smul hA hμ z
      exact ⟨x, by simpa [LinearMap.sub_apply, LinearMap.smul_apply] using hx⟩

/-- The resolvent equivalence is `x ↦ A x - iμ·x`. -/
lemma resolventEquiv_apply [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {μ : ℝ} (hμ : μ ≠ 0) (w : A.domain) :
    (resolventEquiv hA hμ) w = (A w : H) - (Complex.I * (μ : ℂ)) • (w : H) := by
  simp [resolventEquiv, LinearMap.sub_apply, LinearMap.smul_apply, LinearPMap.toFun_eq_coe]

/-- The resolvent `R = (A - iμ)⁻¹` recovers its argument: `A (R z) - iμ·(R z) = z`. -/
lemma resolventEquiv_symm_apply [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {μ : ℝ} (hμ : μ ≠ 0) (z : H) :
    (A ((resolventEquiv hA hμ).symm z) : H)
      - (Complex.I * (μ : ℂ)) • (((resolventEquiv hA hμ).symm z : A.domain) : H) = z := by
  rw [← resolventEquiv_apply hA hμ ((resolventEquiv hA hμ).symm z)]
  exact (resolventEquiv hA hμ).apply_symm_apply z

/-- Resolvent norm bound: `‖R z‖ ≤ ‖z‖ / |μ|`. -/
lemma resolventEquiv_symm_norm_le [CompleteSpace H] {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {μ : ℝ} (hμ : μ ≠ 0) (z : H) :
    ‖(((resolventEquiv hA hμ).symm z : A.domain) : H)‖ ≤ ‖z‖ / |μ| := by
  have hb := (IsSelfAdjoint.isSymmetricPMap hA).mul_norm_le_norm_sub_I_smul μ
    ((resolventEquiv hA hμ).symm z)
  rw [resolventEquiv_symm_apply hA hμ z] at hb
  rw [le_div_iff₀ (abs_pos.mpr hμ), mul_comm]
  exact hb

/-- The relatively-bounded perturbation composed with the resolvent contracts: `‖B (R v)‖ ≤
(a + b/|μ|)‖v‖`, where `R = (A - iμ)⁻¹`. The bound `< 1` (for `|μ|` large) drives the Neumann series. -/
lemma resolvent_relBound [CompleteSpace H] {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb : 0 ≤ b) (hrel : IsRelBounded A B a b) {μ : ℝ} (hμ : μ ≠ 0) (v : H) :
    ‖(B ⟨(((resolventEquiv hA hμ).symm v : A.domain) : H),
        hrel.domain_le ((resolventEquiv hA hμ).symm v).2⟩ : H)‖ ≤ (a + b / |μ|) * ‖v‖ := by
  set x := (resolventEquiv hA hμ).symm v with hx
  have hAx : ‖(A x : H)‖ ≤ ‖v‖ := by
    have := (IsSelfAdjoint.isSymmetricPMap hA).norm_le_norm_sub_I_smul μ x
    rwa [resolventEquiv_symm_apply hA hμ v] at this
  have hxv : ‖(x : H)‖ ≤ ‖v‖ / |μ| := resolventEquiv_symm_norm_le hA hμ v
  calc ‖(B ⟨(x : H), hrel.domain_le x.2⟩ : H)‖
      ≤ a * ‖A x‖ + b * ‖(x : H)‖ := hrel.bound x
    _ ≤ a * ‖v‖ + b * (‖v‖ / |μ|) := by gcongr
    _ = (a + b / |μ|) * ‖v‖ := by ring

/-- **Neumann surjectivity (abstract).** If a linear `T : H → H` is a strict contraction
(`‖T v‖ ≤ k‖v‖`, `k < 1`), then `1 + T` is surjective — `w + T w = z` is solved by the Banach fixed
point of the contraction `w ↦ z - T w`. -/
lemma surjective_one_add_of_contraction [CompleteSpace H] {T : H →ₗ[ℂ] H} {k : ℝ} (hk0 : 0 ≤ k)
    (hk1 : k < 1) (hT : ∀ v : H, ‖T v‖ ≤ k * ‖v‖) (z : H) : ∃ w : H, w + T w = z := by
  have hlip : LipschitzWith ⟨k, hk0⟩ (fun w => z - T w) := by
    apply LipschitzWith.of_dist_le_mul
    intro w w'
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mk,
      show z - T w - (z - T w') = T (w' - w) by rw [_root_.map_sub]; abel]
    calc ‖T (w' - w)‖ ≤ k * ‖w' - w‖ := hT _
      _ = k * ‖w - w'‖ := by rw [norm_sub_rev]
  have hcon : ContractingWith ⟨k, hk0⟩ (fun w => z - T w) := ⟨by exact_mod_cast hk1, hlip⟩
  refine ⟨ContractingWith.fixedPoint _ hcon, ?_⟩
  have hfp := ContractingWith.fixedPoint_isFixedPt hcon
  rw [Function.IsFixedPt] at hfp
  linear_combination (norm := module) -hfp

/-- **Neumann surjectivity for the perturbed operator.** For `|μ|` large (`a + b/|μ| < 1`), the map
`x ↦ A x + B x - iμ·x` is surjective: `(1 + BR)w = z` has a solution `w` (abstract Neumann), then
`x = R w` works since `(A - iμ)(R w) = w` and `B (R w) = (BR)w`. -/
lemma katoRellich_map_surjective [CompleteSpace H] {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb : 0 ≤ b) (hrel : IsRelBounded A B a b)
    {μ : ℝ} (hμne : μ ≠ 0) (hμk : a + b / |μ| < 1) (z : H) :
    ∃ x : A.domain, (A x : H) + (B ⟨(x : H), hrel.domain_le x.2⟩ : H)
      - (Complex.I * (μ : ℂ)) • (x : H) = z := by
  set BR : H →ₗ[ℂ] H :=
    B.toFun ∘ₗ Submodule.inclusion hrel.domain_le ∘ₗ ((resolventEquiv hA hμne).symm.toLinearMap)
    with hBRdef
  have hBRapp : ∀ v : H, BR v = (B ⟨(((resolventEquiv hA hμne).symm v : A.domain) : H),
      hrel.domain_le ((resolventEquiv hA hμne).symm v).2⟩ : H) := fun _ => rfl
  have hBRbound : ∀ v : H, ‖BR v‖ ≤ (a + b / |μ|) * ‖v‖ := fun v => by
    rw [hBRapp v]; exact resolvent_relBound hA ha0 hb hrel hμne v
  obtain ⟨w, hw⟩ := surjective_one_add_of_contraction (by positivity) hμk hBRbound z
  refine ⟨(resolventEquiv hA hμne).symm w, ?_⟩
  rw [hBRapp w] at hw
  have hsym := resolventEquiv_symm_apply hA hμne w
  linear_combination (norm := module) hsym + hw

/-- **Kato–Rellich theorem.** If `A` is self-adjoint, `B` is symmetric, and `B` is relatively
`A`-bounded with relative bound `a < 1` (and `0 ≤ b`), then the sum `A + B` (on the domain of `A`) is
self-adjoint.

This is the abstract mathematical core of Wave 1; the molecular Hamiltonian is the instantiation. The
hypothesis `a < 1` is load-bearing: for `a ≥ 1` the conclusion fails in general. -/
theorem katoRellich [CompleteSpace H] {A B : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSymmetricPMap B) {a b : ℝ} (ha0 : 0 ≤ a) (ha : a < 1) (hb : 0 ≤ b)
    (hrel : IsRelBounded A B a b) :
    IsSelfAdjoint (A + B) := by
  have h1a : 0 < 1 - a := by linarith
  set μ : ℝ := b / (1 - a) + 1 with hμdef
  have hμpos : 0 < μ := by rw [hμdef]; positivity
  have hμne : μ ≠ 0 := ne_of_gt hμpos
  have hμk : a + b / |μ| < 1 := by
    rw [abs_of_pos hμpos]
    have hbμ : b / μ < 1 - a := by
      rw [div_lt_iff₀ hμpos, hμdef]
      have heq : (1 - a) * (b / (1 - a) + 1) = b + (1 - a) := by
        field_simp
      rw [heq]; linarith
    linarith
  have hABsym : IsSymmetricPMap (A + B) := (IsSelfAdjoint.isSymmetricPMap hA).add hB
  have hdomeq : (A + B).domain = A.domain := by
    rw [LinearPMap.add_domain]; exact inf_eq_left.mpr hrel.domain_le
  have hABdense : Dense ((A + B).domain : Set H) := by
    rw [hdomeq]; exact IsSelfAdjoint.dense_domain hA
  have hconn : ∀ ν : ℝ, ν ≠ 0 → a + b / |ν| < 1 →
      ∀ z, ∃ x : (A + B).domain, ((A + B) x : H) - (Complex.I * (ν : ℂ)) • (x : H) = z := by
    intro ν hν hνk z
    obtain ⟨x, hx⟩ := katoRellich_map_surjective hA ha0 hb hrel hν hνk z
    refine ⟨⟨(x : H), hdomeq.ge x.2⟩, ?_⟩
    rw [LinearPMap.add_apply]
    exact hx
  refine hABsym.isSelfAdjoint_of_surjective hABdense (μ := μ) (hconn μ hμne hμk) (fun z => ?_)
  obtain ⟨x, hx⟩ := hconn (-μ) (neg_ne_zero.mpr hμne) (by rwa [abs_neg]) z
  exact ⟨x, by rw [← hx]; push_cast; module⟩

/-! ## The molecular Hamiltonian (instantiation on PhysLib's `SpaceDQuantumSystem`) -/

open QuantumMechanics in
/-- **Self-adjointness of a single-particle Schrödinger Hamiltonian** `H = T̄ + V`, via Kato–Rellich.
PhysLib's `kineticOperator` lives on the Schwartz core, so it is only *essentially* self-adjoint; its
**closure** `T̄ = kineticOperator.closure` is the self-adjoint kinetic energy (`hkin`). Given that and a
symmetric potential `V` relatively `T̄`-bounded with bound `a < 1`, the self-adjoint Hamiltonian
realization `T̄ + V` is self-adjoint. The molecular Coulomb Hamiltonian is the instance at `d = 3N`. -/
theorem spaceDQuantumSystem_hamiltonian_isSelfAdjoint (Q : QuantumMechanics.SpaceDQuantumSystem)
    (hkin : IsSelfAdjoint Q.kineticOperator.closure) (hpot : IsSymmetricPMap Q.potentialOperator)
    {a b : ℝ} (ha0 : 0 ≤ a) (ha : a < 1) (hb : 0 ≤ b)
    (hrel : IsRelBounded Q.kineticOperator.closure Q.potentialOperator a b) :
    IsSelfAdjoint (Q.kineticOperator.closure + Q.potentialOperator) :=
  katoRellich hkin hpot ha0 ha hb hrel

open QuantumMechanics in
/-- Electron `i`'s 3D position (its three spatial coordinates) within the `3N`-dimensional
configuration `x` of an `N`-electron system. -/
noncomputable def electronPos {N : ℕ} (x : Space (3 * N)) (i : Fin N) : Space 3 :=
  ⟨fun j => x.val ⟨3 * (i : ℕ) + (j : ℕ), by have := i.2; have := j.2; omega⟩⟩

open QuantumMechanics in
/-- The **N-electron molecular Coulomb potential** for nuclei `(Rₖ, Zₖ) ∈ nuclei`: nuclear attraction
`-∑ᵢₖ Zₖ/|xᵢ - Rₖ|` plus electron–electron repulsion `∑_{i<j} 1/|xᵢ - xⱼ|`. -/
noncomputable def molecularCoulombPotential {N : ℕ} (nuclei : Finset (Space 3 × ℝ)) :
    Space (3 * N) → ℝ := fun x =>
  (-∑ i : Fin N, ∑ p ∈ nuclei, p.2 / ‖electronPos x i - p.1‖)
    + ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (i < ·), 1 / ‖electronPos x i - electronPos x j‖

open QuantumMechanics in
/-- The **N-electron molecular quantum system**: configuration space `Space (3N)`, electron mass `m`,
and the molecular Coulomb potential. Its `hamiltonianOperator = kineticOperator + potentialOperator`
is the molecular Schrödinger operator. -/
noncomputable def molecularSystem (N : ℕ) (m : ℝ) (hm : 0 < m) (nuclei : Finset (Space 3 × ℝ)) :
    QuantumMechanics.SpaceDQuantumSystem where
  d := 3 * N
  m := m
  hm := hm
  potential := molecularCoulombPotential nuclei

/- **Apex theorems relocated (Phase 6BB Wave 6, `hkin` discharge).** `molecularHamiltonian_essSelfAdjoint`
and `molecularHamiltonian_essSelfAdjoint_of_kinetic` now live in
`SKEFTHawking/KineticEssentialSelfAdjoint.lean`, where the kinetic operator's essential
self-adjointness (`kineticOperator_isSelfAdjoint_closure`, the discharge of the former `hkin`
hypothesis) is available — they no longer take an `hkin` argument. The Kato–Rellich substrate
(`spaceDQuantumSystem_hamiltonian_isSelfAdjoint`, `katoRellich`) and the `hpot` discharge
(`molecularPotentialOperator_isSymmetric`, below) remain here. -/

/-! ### Wave 5 — discharge of `hpot` (the potential is symmetric), via measurability of the
molecular Coulomb potential. -/

open QuantumMechanics in
/-- Each electron's 3D-position map is continuous (coordinate projections, PhysLib `coordCLM`/
`mk_continuous`). -/
lemma electronPos_continuous {N : ℕ} (i : Fin N) :
    Continuous (fun x : Space (3 * N) => electronPos x i) :=
  Space.mk_continuous.comp (by fun_prop)

open QuantumMechanics MeasureTheory in
/-- The molecular Coulomb potential is measurable (a finite sum of `c / ‖affine‖` terms, each
measurable since the position maps are continuous and division on `ℝ` is measurable). -/
lemma molecularCoulombPotential_measurable {N : ℕ} (nuclei : Finset (Space 3 × ℝ)) :
    Measurable (molecularCoulombPotential (N := N) nuclei) := by
  unfold molecularCoulombPotential
  refine (Finset.measurable_sum _ fun i _ => ?_).neg.add (Finset.measurable_sum _ fun i _ => ?_)
  · exact Finset.measurable_sum _ fun p _ =>
      measurable_const.div (((electronPos_continuous i).sub continuous_const).norm).measurable
  · exact Finset.measurable_sum _ fun j _ =>
      measurable_const.div
        (((electronPos_continuous i).sub (electronPos_continuous j)).norm).measurable

open QuantumMechanics in
/-- **Wave-5 discharge of `hpot`:** the molecular potential operator is symmetric — the real Coulomb
multiplication operator is self-adjoint by measurability (PhysLib `potentialOperator_isSelfAdjoint`). -/
lemma molecularPotentialOperator_isSymmetric (N : ℕ) (m : ℝ) (hm : 0 < m)
    (nuclei : Finset (Space 3 × ℝ)) :
    IsSymmetricPMap (molecularSystem N m hm nuclei).potentialOperator :=
  IsSelfAdjoint.isSymmetricPMap
    ((molecularSystem N m hm nuclei).potentialOperator_isSelfAdjoint
      (molecularCoulombPotential_measurable nuclei).aestronglyMeasurable)

end SKEFTHawking.DFT
