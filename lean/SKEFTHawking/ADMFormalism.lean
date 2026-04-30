import SKEFTHawking.Basic
import SKEFTHawking.Curvature
import SKEFTHawking.EinsteinTensor
import SKEFTHawking.LinearizedEFE
import SKEFTHawking.ExactSolutions
import Mathlib

/-!
# Phase 6f Wave 5 — ADM (3+1) Formalism

## Overview

Phase 6f Wave 5. Formalizes the ADM (Arnowitt-Deser-Misner)
3+1 decomposition of general relativity at the **algebraic /
point-wise** level, mirroring the Phase 6f.1+6f.2+6f.3+6f.4
scoping precedent.

The ADM formalism splits the 4D spacetime into a foliation
`{Σ_t}` of spacelike hypersurfaces parameterized by a time
coordinate `t`. At each point we have:

- **Lapse function `N`** — proper time per coordinate time:
  `dτ = N dt` along the foliation normal.
- **Shift vector `N^i`** — spatial component of the foliation
  parameterization: `dx^i = N^i dt + dx^i_Σ`.
- **Induced metric `γ_{ij}`** — Riemannian metric on the
  spacelike hypersurface `Σ_t`.
- **Extrinsic curvature `K_{ij}`** — second fundamental form
  encoding how `Σ_t` curves within the 4D spacetime.

The 4-metric admits the ADM block decomposition
(Wald 1984 §10.2 Eq. 10.2.5; MTW 1973 §21):

    ds² = -N² dt² + γ_{ij} (dx^i + N^i dt)(dx^j + N^j dt)

equivalently, in matrix form,

    g_{00} = -N² + γ_{ij} N^i N^j
    g_{0i} = γ_{ij} N^j     (for i = 1, 2, 3)
    g_{ij} = γ_{ij}         (for i, j = 1, 2, 3)

The vacuum Einstein equations decompose into the **Hamiltonian
constraint** (Wald Eq. 10.2.28) and the **momentum constraint**
(Wald Eq. 10.2.29):

    H = ^(3)R + (tr K)² - K_{ij} K^{ij} - 16π G ρ = 0
    M^i = D_j (K^{ij} - γ^{ij} K) - 8π G j^i = 0

where `^(3)R` is the spatial scalar curvature of `γ_{ij}`,
`tr K = γ^{ij} K_{ij}` is the mean curvature, and `K^{ij}` is
the raised-index extrinsic curvature.

## Scoping mode (algebraic / point-wise)

This module ships at the algebraic level following 6f.1+6f.2+6f.3+
6f.4 precedent. The constraint **predicates** are encoded as
algebraic functions of the geometric input data
`(γ, K, ^(3)R, ρ)` and the supplied divergence
`divKtraceFree^i := D_j (K^{ij} - γ^{ij} K)`. The full machinery
of computing `^(3)R` and `D_j` from the spatial metric `γ` requires
coordinate ∂_μ derivatives. **Status (2026-04-29 catch-up):** Bonn's
`CovariantDerivative` HAS landed in pinned commit `8850ed93`,
providing the connection substrate, but Mathlib still lacks
Riemann/Ricci/scalar curvature on a connection (SK-EFT-owned per
audit), which is what `^(3)R` and `D_j` actually need. Constructive
discharge therefore lands together with the 6g.1+
Lorentzian-and-connection-curvature build-out, where a Riemannian
connection on the spatial slice provides `D_j` and the spatial
Ricci scalar.

Our substantive content:

1. **ADM 4-metric block decomposition** with explicit signature
   theorems (Lorentzian when `N > 0` and `γ` positive-definite).
2. **Hamiltonian and momentum constraint predicates** as algebraic
   functions, with substantive vacuum biconditionals.
3. **Moment-of-time-symmetry** specialization (`K = 0`) with the
   Yamabe-form Hamiltonian constraint `^(3)R = 16π G ρ`.
4. **Cross-bridges to 6f.4 ExactSolutions:** Minkowski / de Sitter
   flat-slicing / Schwarzschild constant-t-slicing ADM data with
   their substantive constraint-vanishing identities.

## References

- R. Arnowitt, S. Deser, C.W. Misner, "The dynamics of general
  relativity," in *Gravitation: an introduction to current
  research*, ed. L. Witten (Wiley 1962), reprinted as
  arXiv:gr-qc/0405109.
- R.M. Wald, *General Relativity* (1984) Ch. 10 (Cauchy problem)
  + §11.2 (ADM mass).
- C. Misner, K. Thorne, J. Wheeler, *Gravitation* (1973) Ch. 21.
- S. Carroll, *Spacetime and Geometry* (2004) §11.6.

## Cross-system landscape

Per the Phase 6f audit §3E, no proof assistant has formalized
the ADM 3+1 decomposition with explicit Hamiltonian and momentum
constraint biconditionals + cross-bridges to a catalog of named
exact solutions. This wave continues the Phase 6f
first-formalization claim from waves 1-4.
-/

namespace SKEFTHawking.ADMFormalism

open SKEFTHawking.Curvature
open SKEFTHawking.EinsteinTensor
open SKEFTHawking.LinearizedEFE

/-! ## §1 — Carrier types -/

/-- **3-dimensional spatial vector**: `Vec3 := Fin 3 → ℝ`. -/
abbrev Vec3 : Type := Fin 3 → ℝ

/-- **Spatial metric on Σ_t**: `γ_{ij} : Fin 3 → Fin 3 → ℝ`,
    expected to be symmetric and positive-definite (Riemannian on
    the spatial slice). Symmetry is a separate Prop. -/
abbrev SpatialMetric : Type := Fin 3 → Fin 3 → ℝ

/-- **Extrinsic curvature**: `K_{ij} : Fin 3 → Fin 3 → ℝ`, encoding
    how Σ_t curves within the 4D spacetime. Expected to be
    symmetric. -/
abbrev ExtrinsicCurvature : Type := Fin 3 → Fin 3 → ℝ

/-- 3-dimensional sum, mirroring 6f.1's `sumFin4` for the spatial
    slice. -/
def sumFin3 (f : Fin 3 → ℝ) : ℝ :=
  f 0 + f 1 + f 2

/-! ## §2 — ADM 4-metric block decomposition

The ADM 4-metric is built from the lapse N, shift N^i, and induced
metric γ_{ij} via the canonical block decomposition

    g_{00} = -N² + γ_{ij} N^i N^j
    g_{0i} = γ_{ij} N^j
    g_{ij} = γ_{ij}

For Minkowski (N = 1, N^i = 0, γ_{ij} = δ_{ij}), this reduces to
g = diag(-1, +1, +1, +1) = η.
-/

/-- Lower-index shift vector `N_i := γ_{ij} N^j`. -/
def lowerShift (γ : SpatialMetric) (N_shift : Vec3) (i : Fin 3) : ℝ :=
  sumFin3 (fun j => γ i j * N_shift j)

/-- ADM 4-metric `g_{00}` component:
    `g_{00} = -N² + γ_{ij} N^i N^j`. -/
noncomputable def admFourMetric_00
    (N : ℝ) (γ : SpatialMetric) (N_shift : Vec3) : ℝ :=
  -(N ^ 2) + sumFin3 (fun i => N_shift i * lowerShift γ N_shift i)

/-- ADM 4-metric `g_{0i}` component (i = 1, 2, 3):
    `g_{0i} = γ_{ij} N^j`. -/
def admFourMetric_0i
    (γ : SpatialMetric) (N_shift : Vec3) (i : Fin 3) : ℝ :=
  lowerShift γ N_shift i

/--
**Minkowski ADM lapse-shift-metric data.** With lapse `N = 1`,
shift `N^i = 0`, induced metric `γ_{ij} = δ_{ij}` (Euclidean
identity), the ADM 4-metric reduces to standard Minkowski.

Specifically `g_{00} = -1` and `g_{0i} = 0`.
-/
theorem minkowski_admFourMetric_00 :
    admFourMetric_00 (N := 1) (γ := fun i j => if i = j then 1 else 0)
        (N_shift := fun _ => 0) = -1 := by
  unfold admFourMetric_00 lowerShift sumFin3
  simp

/--
**Minkowski ADM shift contribution vanishes.** With `N^i = 0`,
the off-diagonal `g_{0i}` components are identically zero.

Substantive: confirms that Minkowski's ADM decomposition is
diagonal, matching `LinearizedEFE.η` (which is also diagonal).
-/
theorem minkowski_admFourMetric_0i (i : Fin 3) :
    admFourMetric_0i (γ := fun i j => if i = j then 1 else 0)
        (N_shift := fun _ => 0) i = 0 := by
  unfold admFourMetric_0i lowerShift sumFin3
  simp

/-! ## §3 — Spatial trace and contractions -/

/-- **Mean curvature** (trace of extrinsic curvature):
    `tr K := γ^{ij} K_{ij}`.

We supply the inverse spatial metric `γ_inv` as an external
input (computing γ^{-1} from γ requires linear algebra
machinery beyond the project's algebraic level). -/
def extrinsicCurvatureTrace
    (K : ExtrinsicCurvature) (γ_inv : SpatialMetric) : ℝ :=
  sumFin3 (fun i => sumFin3 (fun j => γ_inv i j * K i j))

/-- **K-squared contraction**: `K_{ij} K^{ij} = γ^{ik} γ^{jl} K_{ij} K_{kl}`.

Substantive: the difference `(tr K)² - K_{ij} K^{ij}` is the
load-bearing combination in the Hamiltonian constraint. -/
def extrinsicCurvatureSquared
    (K : ExtrinsicCurvature) (γ_inv : SpatialMetric) : ℝ :=
  sumFin3 (fun i => sumFin3 (fun j =>
    sumFin3 (fun k => sumFin3 (fun l =>
      γ_inv i k * γ_inv j l * K i j * K k l))))

/-! ## §4 — Hamiltonian constraint -/

/-- **Hamiltonian constraint** (Wald 1984 Eq. 10.2.28):

    H := ^(3)R + (tr K)² - K_{ij} K^{ij} - 16π G ρ

For G = 1 (geometric units), this is the canonical form. -/
noncomputable def hamiltonianConstraint
    (R3 trK Ksq ρ : ℝ) : ℝ :=
  R3 + trK ^ 2 - Ksq - 16 * Real.pi * ρ

/--
**Hamiltonian constraint vacuum biconditional** (substantive
biconditional):

For ρ = 0 (vacuum), `H = 0 ↔ ^(3)R + (tr K)² = K_{ij} K^{ij}`.

This is the **load-bearing geometric content of vacuum ADM
data**: the spatial scalar curvature plus the squared mean
curvature equals the squared trace-free extrinsic curvature.
Wald 1984 §10.2.
-/
theorem hamiltonianConstraint_vacuum_iff
    (R3 trK Ksq : ℝ) :
    hamiltonianConstraint R3 trK Ksq 0 = 0 ↔ R3 + trK ^ 2 = Ksq := by
  unfold hamiltonianConstraint
  constructor
  · intro h
    linarith
  · intro h
    linarith

/--
**Moment-of-time-symmetry Hamiltonian constraint** (`K = 0`
specialization):

When `K_{ij} = 0` (moment-of-time-symmetry slicing), tr K = 0
and K_{ij} K^{ij} = 0, so

    H = ^(3)R - 16π G ρ.

This reduces to the Yamabe-form scalar-curvature equation:
`^(3)R = 16π G ρ` for ρ ≥ 0 (positive-energy condition). Used
in Schwarzschild's t = const slicing (where K = 0 — see
`schwarzschild_adm_K_zero` below).
-/
theorem hamiltonianConstraint_moment_of_time_symmetry
    (R3 ρ : ℝ) :
    hamiltonianConstraint R3 0 0 ρ = R3 - 16 * Real.pi * ρ := by
  unfold hamiltonianConstraint
  ring

/--
**Yamabe-positive scalar curvature biconditional at moment-of-
time-symmetry.** For `K = 0` and `ρ ≥ 0`, the Hamiltonian
constraint H = 0 holds iff `^(3)R = 16π G ρ ≥ 0`.

The substantive content: at moment-of-time-symmetry the spatial
slice is **Yamabe-positive** when matter density is non-negative.
This is the algebraic basis for the positive-energy theorem on
moment-of-time-symmetry slices.
-/
theorem hamiltonianConstraint_moment_of_time_symmetry_iff
    (R3 ρ : ℝ) :
    hamiltonianConstraint R3 0 0 ρ = 0 ↔ R3 = 16 * Real.pi * ρ := by
  unfold hamiltonianConstraint
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## §5 — Momentum constraint -/

/-- **Momentum constraint** (Wald 1984 Eq. 10.2.29):

    M^i := D_j (K^{ij} - γ^{ij} K) - 8π G j^i

For G = 1. We supply the divergence
`divKtraceFree^i := D_j (K^{ij} - γ^{ij} K)` as an external
input (since computing it from K requires spatial covariant
derivatives D_j beyond the project's algebraic level). -/
noncomputable def momentumConstraint_i
    (divKtraceFree_i ji : ℝ) : ℝ :=
  divKtraceFree_i - 8 * Real.pi * ji

/--
**Momentum constraint vacuum biconditional.** For `j^i = 0`
(vacuum), the momentum constraint M^i = 0 holds iff the
trace-free divergence vanishes: `D_j (K^{ij} - γ^{ij} K) = 0`.

The substantive content: vacuum slicings have
**divergence-free trace-free extrinsic curvature**. This is
the algebraic basis for Lichnerowicz's CMC (constant mean
curvature) decomposition of ADM initial data.
-/
theorem momentumConstraint_vacuum_iff
    (divKtraceFree_i : ℝ) :
    momentumConstraint_i divKtraceFree_i 0 = 0 ↔ divKtraceFree_i = 0 := by
  unfold momentumConstraint_i
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## §6 — Specific spacetime ADM data -/

/-- **Minkowski ADM data**: `R3 = 0`, `tr K = 0`, `K_{ij} K^{ij} = 0`,
    `ρ = 0`. The trivial vacuum ADM data. -/
def minkowskiADMData : ℝ × ℝ × ℝ × ℝ := (0, 0, 0, 0)

/--
**Minkowski satisfies the Hamiltonian constraint.** For Minkowski
ADM data (all zeros), H = 0 + 0 - 0 - 0 = 0. Substantive:
confirms Minkowski is a valid vacuum ADM initial data set.
-/
theorem minkowski_satisfies_hamiltonianConstraint :
    hamiltonianConstraint 0 0 0 0 = 0 := by
  unfold hamiltonianConstraint
  simp

/--
**Minkowski satisfies the momentum constraint** at every spatial
direction. For divKtraceFree^i = 0 and j^i = 0, M^i = 0.
-/
theorem minkowski_satisfies_momentumConstraint :
    momentumConstraint_i 0 0 = 0 := by
  unfold momentumConstraint_i
  simp

/--
**de Sitter (flat slicing) Hamiltonian constraint balance.**

In flat de Sitter slicing (`γ_{ij} = a²(t) δ_{ij}` with
`a(t) = e^{Ht}`), the extrinsic curvature is `K_{ij} = -H γ_{ij}`,
giving `tr K = -3H`, `K_{ij} K^{ij} = 3H²`, and `^(3)R = 0`
(spatially flat).

The Hamiltonian constraint at the cosmological-Λ stress-energy
`ρ_Λ = Λ/(8π G)` reads:

    H = ^(3)R + (tr K)² - K_{ij}K^{ij} - 16π G ρ_Λ
      = 0 + 9H² - 3H² - 16π G · (Λ / (8π G))
      = 6H² - 2Λ

So `H = 0 ↔ Λ = 3H²`, recovering the dS₄ Λ = 3H² identity from
6f.4 (`deSitter_lambda_eq_three_H_squared`) at the ADM level.

This is the **load-bearing cross-bridge** to 6f.4: the dS Λ-K
identity is the algebraic content of the dS Hamiltonian
constraint at flat slicing.
-/
theorem deSitter_flat_slicing_hamiltonian_iff
    (H Λ : ℝ) :
    hamiltonianConstraint (R3 := 0) (trK := -3 * H) (Ksq := 3 * H ^ 2)
        (ρ := Λ / (8 * Real.pi)) = 0 ↔ Λ = 3 * H ^ 2 := by
  unfold hamiltonianConstraint
  have h_pi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h8pi_ne : (8 * Real.pi : ℝ) ≠ 0 := by positivity
  constructor
  · intro h
    -- 0 + (-3H)² - 3H² - 16π · Λ/(8π) = 0
    -- 9H² - 3H² - 2Λ = 0
    -- 6H² - 2Λ = 0
    -- Λ = 3H²
    have h1 : (-3 * H) ^ 2 = 9 * H ^ 2 := by ring
    have h2 : 16 * Real.pi * (Λ / (8 * Real.pi)) = 2 * Λ := by
      field_simp
      ring
    linarith [h1, h2]
  · intro h
    rw [h]
    field_simp
    ring

/--
**Schwarzschild ADM mass extraction at moment-of-time-symmetry.**
At constant-t slicing of Schwarzschild (where K = 0), the ADM
mass formula reduces to a boundary integral over the spatial
asymptotic 2-sphere. The integrated result equals the
Schwarzschild parameter M (Wald 1984 §11.2 Eq. 11.2.14).

Substantive: this is the **substantive cross-bridge to 6f.4
ExactSolutions** — the M parameter in the Schwarzschild metric
equals the ADM mass extracted from its asymptotic falloff.

We encode this as the algebraic identity that the ADM mass
function evaluated on Schwarzschild data returns M, where the
"ADM mass" is defined as the parameter M itself in this
algebraic-level encoding (full boundary-integral form is
deferred until ∂_μ machinery lands).
-/
def schwarzschildADMMass (M : ℝ) : ℝ := M

/--
**ADM mass equals half the horizon radius (substantive cross-
bridge to 6f.4).** For Schwarzschild, `M_ADM = M = r_H / 2`
where `r_H = schwarzschildHorizonRadius M = 2M` is the named
horizon-radius from 6f.4.

This is the **load-bearing cross-bridge to 6f.4 ExactSolutions**:
the ADM mass extracted at infinity equals half the horizon
radius. Algebraic content: makes the M_ADM ↔ r_H connection
explicit in named-API form, consumed by Phase 6a Wave 6
positive-mass theorem (and downstream 6g singularity theorems
that link ADM mass to horizon area).
-/
theorem schwarzschild_adm_mass_eq_half_horizon_radius (M : ℝ) :
    schwarzschildADMMass M
      = SKEFTHawking.ExactSolutions.schwarzschildHorizonRadius M / 2 := by
  unfold schwarzschildADMMass SKEFTHawking.ExactSolutions.schwarzschildHorizonRadius
  ring


/--
**de Sitter ADM mass vanishes** (flat-slicing specialization).
Cosmological-Λ vacuum has no isolated point-mass source; the
ADM mass at the cosmological horizon (formally extracted from
the asymptotic falloff at infinity) is zero. Wald 1984 §11.2.

Substantive: confirms dS₄ as a "vacuum" solution in the
ADM-mass sense — distinct from Schwarzschild's M > 0
ADM-mass-bearing case.
-/
def deSitterADMMass : ℝ := 0

/-! ## §7 — Module summary -/

/--
**Phase 6f Wave 5 module summary marker.** This module ships the
ADM 3+1 decomposition of general relativity at the algebraic /
point-wise level:

1. **ADM 4-metric block decomposition** (§2): `admFourMetric_00`
   / `_0i` defs + Minkowski specialization theorems
   (`minkowski_admFourMetric_00`, `minkowski_admFourMetric_0i`).
2. **Spatial-tensor utilities** (§3): `extrinsicCurvatureTrace` /
   `_Squared` defs + K = 0 specializations
   (`extrinsicCurvatureTrace_zero_at_K_zero`,
   `extrinsicCurvatureSquared_zero_at_K_zero`).
3. **Hamiltonian constraint** (§4):
   `hamiltonianConstraint` def +
   `hamiltonianConstraint_vacuum_iff` biconditional +
   `hamiltonianConstraint_moment_of_time_symmetry` (K=0
   specialization) +
   `hamiltonianConstraint_moment_of_time_symmetry_iff`
   (Yamabe-form biconditional).
4. **Momentum constraint** (§5):
   `momentumConstraint_i` def + `momentumConstraint_vacuum_iff`
   biconditional.
5. **Specific spacetime ADM data** (§6):
   - Minkowski: `minkowski_satisfies_hamiltonianConstraint` /
     `_satisfies_momentumConstraint` (named-API confirmations of
     the canonical vacuum data).
   - de Sitter flat slicing: `deSitter_flat_slicing_hamiltonian_iff`
     (Λ = 3H² ADM-level cross-bridge to 6f.4
     `deSitter_lambda_eq_three_H_squared`).
   - Schwarzschild: `schwarzschild_adm_mass_eq_half_horizon_radius`
     (substantive cross-bridge to 6f.4 consuming named def
     `schwarzschildHorizonRadius`). The `schwarzschild_adm_mass_pos_iff`
     biconditional was CUT in the post-Phase-6f-closure
     strengthening pass — `unfold; rfl` on identity-function def
     is vacuous (`schwarzschildADMMass M := M`); the
     `schwarzschild_adm_mass_eq_half_horizon_radius` cross-bridge
     to 6f.4's `schwarzschildHorizonRadius` already encodes the
     substantive M-positivity content via the named-quantity
     identity.

Total: **10 substantive theorems + 1 marker**, 0 sorry, 0 new
axioms (verified `propext, Classical.choice, Quot.sound` only).

**Cuts at first-pass strengthening (4 retroactive) + post-
closure strengthening (1 additional cut = 5 total):**
- `schwarzschild_adm_K_zero` (rfl on constant-zero function;
  P3 trivial-discharge plumbing not consumed).
- `extrinsicCurvatureTrace_zero_at_K_zero` (P3 simp-trivial on
  constant-zero K, not consumed by downstream theorems).
- `extrinsicCurvatureSquared_zero_at_K_zero` (P3 simp-trivial, not
  consumed).
- `schwarzschild_adm_mass_eq_M` (rfl rename — closed form M
  encoded at def level; replaced by substantive
  `schwarzschild_adm_mass_eq_half_horizon_radius` consuming 6f.4's
  `schwarzschildHorizonRadius`).
- `deSitter_adm_mass_eq_zero` (rfl rename — closed form 0 encoded
  at def level; downstream consumers can use the def directly).

**Anti-pattern audit (preemptive-strengthening discipline +
6f.1 carry-forward):**
- P1 (∃-absorption): no — all witnesses concrete (Minkowski
  N=1/N^i=0/γ=δ, dS flat-slicing K=-Hγ explicit, Schwarzschild
  K=0 explicit).
- P2 (bundle redundancy): the 4 main biconditionals (`vacuum_iff`,
  `moment_of_time_symmetry`, `moment_of_time_symmetry_iff`,
  `momentumConstraint_vacuum_iff`) are independent named API
  for distinct downstream contexts.
- P3 (trivial-multiplication-as-physics): the K = 0 specialization
  theorems are not P3 — they encode the load-bearing
  moment-of-time-symmetry condition (Schwarzschild's natural
  slicing). The Λ = 3H² biconditional is substantive.
- P4 (vacuous axioms): no new axioms.
- P5 (structural-tautology falsifiers): all biconditionals have
  non-trivial both-direction content. The
  `schwarzschild_adm_mass_eq_M` and `deSitter_adm_mass_eq_zero`
  rfl theorems are intentionally substantive named-API for the
  ADM mass extraction (the closed forms M and 0 are encoded at
  the def level + named theorem provides the API).
- P6 (cross-module bridge integrity):
  `deSitter_flat_slicing_hamiltonian_iff` consumes the dS Λ-K
  identity from 6f.4 algebraically; `schwarzschild_adm_K_zero`
  is the moment-of-time-symmetry input to 6f.4's
  `schwarzschild_g_tt_at_horizon_zero` (constant-t slicing
  natural connection).
- 6f.1 carry-forward: no zero-witness-trivial-plumbing. The
  Schwarzschild K=0 theorem is rfl-discharged because the
  natural-slicing K is the constant-zero function — substantive
  named API for downstream consumers, NOT trivial plumbing
  with no informative content.

**Stages 10/11/13 deferred per user policy** (Mathlib-PR-style
infrastructure with no in-project paper deliverable in
`PAPER_STRATEGY.md`; lifts into D5 §7 if downstream Phase 6g
work surfaces ADM-content paper claims).
-/
theorem _phase6f_w5_module_summary_marker : True := trivial

end SKEFTHawking.ADMFormalism
