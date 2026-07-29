import SKEFTHawking.BlochBundle

/-!
# Honeycomb tight-binding and the Dirac points (Phase 6ED, Wave 1)

The repo formalizes graphene as a *Dirac fluid* (Phase 5w: analog metric, Hawking spectrum, noise
PSD) and formalizes *abstract* two-band Chern machinery (Phase 6CA: `blochPauli` d·σ models, FHS
lattice Chern number). What both sides implicitly cite — and neither builds — is graphene's actual
electronic structure. This wave supplies it: the nearest-neighbour honeycomb Bloch Hamiltonian as
a `blochPauli` instance, its band energies, and the **exact** zero set of the structure factor,
which is the pair of inequivalent Dirac points.

## Coordinates: Bloch phases, not a coordinate choice

The structure factor is written as a function of the two **Bloch phases**
`θ = (θ₁, θ₂) = (⟨k, a₁⟩, ⟨k, a₂⟩)`:

    f(θ) = 1 + exp(i·θ₁) + exp(i·θ₂)

rather than of a momentum `k` against a fixed pair of lattice vectors. This is deliberate and is a
*strengthening*: every theorem below then holds for **any** primitive-vector choice, and the
lattice geometry enters only where a consumer supplies it. Identifying `θᵢ = ⟨k, aᵢ⟩` for a
particular sample's lattice is the consumer's declared hypothesis, in the same two-layer style
`BlochBundle` uses for `d(k)`.

## The zero set, and why it is stated without `mod 2π`

The roadmap's AC asked for `f k = 0 ↔ (k ≡ K ∨ k ≡ K')` modulo the reciprocal lattice. What ships
is the equivalent **quotient-free** characterization

    f(θ) = 0  ↔  cos θ₁ = −1/2  ∧  cos θ₂ = −1/2  ∧  sin θ₁ + sin θ₂ = 0

(`structureFactor_eq_zero_iff`). It is *exactly* the same set — periodicity is automatic in `cos`
and `sin`, so no `mod` bookkeeping is needed and none is smuggled — and it is strictly easier for a
consumer to discharge, since it is three real equations rather than a statement about a quotient by
the reciprocal lattice. The `K`/`K'` reading is recovered by
`structureFactor_eq_zero_iff_dirac_branch`: the two solutions of the phase constraints are exactly
`sin θ₁ = +√3/2` (the `K` branch) and `sin θ₁ = −√3/2` (the `K'` branch).

## Layout

* **Definitions** — `structureFactor`, `honeycombD` (the `blochPauli` d-vector), `diracK`/`diracK'`,
  and the high-symmetry points `gammaPoint`/`mPoint`.
* **Real/imaginary parts** — `structureFactor_re`/`_im`, the computational core everything else
  reduces to.
* **Band structure** — `dNormSq_honeycombD` (`‖d‖² = |f|²`) and `honeycomb_energy_eq`
  (bands `±|f|`), both routed through `BlochBundle`'s spectral core rather than re-deriving 2×2
  algebra.
* **The Dirac points** — the zero-set characterization, its two-branch form, gaplessness at `K`/`K'`
  and `honeycomb_gapped_away` off the zero set (via `blochPauli_gap_pos`).
* **Witnesses** — `norm_num`-backed evaluations at Γ (`|f| = 3`) and M (`|f| = 1`).

**⚠ Guardrail (inherited).** Every statement is about the *stated* nearest-neighbour honeycomb
tight-binding model. Identifying its parameters with a physical sample (hopping energies, measured
`v_F`, gap sizes) is consumer-side. No claim about devices, transport, or fabrication.

**Publication target:** bundle **D11** — *Kernel-Verified Topological Band Theory & Metamaterial
Substrate* (this phase's thread; its `6E*` siblings route to D12).
-/

namespace SKEFTHawking.GrapheneBand

open Complex Real SKEFTHawking.Topological

/-! ## Definitions -/

/-- **The nearest-neighbour honeycomb structure factor**, in Bloch-phase coordinates:

    f(θ) = 1 + exp(i·θ₁) + exp(i·θ₂),   θᵢ = ⟨k, aᵢ⟩.

The three terms are the three nearest-neighbour hoppings from an A site to its B neighbours (one
within the cell, two across the primitive vectors). Writing it in the phases rather than in `k`
makes every theorem below independent of the primitive-vector choice. -/
noncomputable def structureFactor (θ : ℝ × ℝ) : ℂ :=
  1 + Complex.exp (θ.1 * Complex.I) + Complex.exp (θ.2 * Complex.I)

/-- **The honeycomb `d`-vector**, `d(θ) = (Re f, −Im f, 0)`.

The third component vanishes: nearest-neighbour honeycomb hopping is **sublattice-off-diagonal**,
which is exactly the chiral symmetry that pins the bands symmetrically at `±|f|` and permits the
gapless Dirac points. A nonzero `d₃` is the *mass* term, which Wave 2 adds. -/
noncomputable def honeycombD (θ : ℝ × ℝ) : Fin 3 → ℝ :=
  ![(structureFactor θ).re, -(structureFactor θ).im, 0]

/-- The honeycomb Bloch Hamiltonian as a `blochPauli` instance — so the whole 2×2 spectral core
(`blochPauli_sq`, `blochPauli_secular_det`, `blochPauli_gap_pos`) applies without re-derivation. -/
noncomputable def honeycombBloch (θ : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  blochPauli (honeycombD θ)

/-- The `K` Dirac point in phase coordinates: `θ = (2π/3, 4π/3)`. -/
noncomputable def diracK : ℝ × ℝ := (2 * π / 3, 4 * π / 3)

/-- The inequivalent `K'` Dirac point: the coordinate swap of `K`. -/
noncomputable def diracK' : ℝ × ℝ := (4 * π / 3, 2 * π / 3)

/-- The Brillouin-zone centre Γ, `θ = (0, 0)`. -/
def gammaPoint : ℝ × ℝ := (0, 0)

/-- An `M` point (edge midpoint), `θ = (π, 0)`. -/
noncomputable def mPoint : ℝ × ℝ := (π, 0)

/-! ## Real and imaginary parts — the computational core -/

/-- `Re f(θ) = 1 + cos θ₁ + cos θ₂`. -/
theorem structureFactor_re (θ : ℝ × ℝ) :
    (structureFactor θ).re = 1 + Real.cos θ.1 + Real.cos θ.2 := by
  unfold structureFactor
  simp [Complex.exp_mul_I, Complex.add_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- `Im f(θ) = sin θ₁ + sin θ₂`. -/
theorem structureFactor_im (θ : ℝ × ℝ) :
    (structureFactor θ).im = Real.sin θ.1 + Real.sin θ.2 := by
  unfold structureFactor
  simp [Complex.exp_mul_I, Complex.add_im, Complex.sin_ofReal_re]

/-! ## Band structure — routed through `BlochBundle` -/

/-- **`‖d‖² = |f|²`.** The honeycomb `d`-vector's squared norm is exactly the squared modulus of
the structure factor — the identity that turns `BlochBundle`'s abstract `±‖d‖` bands into the
honeycomb bands `±|f|`. -/
theorem dNormSq_honeycombD (θ : ℝ × ℝ) :
    dNormSq (honeycombD θ) = Complex.normSq (structureFactor θ) := by
  unfold dNormSq honeycombD Complex.normSq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  ring

/-- **The honeycomb bands are `±|f(θ)|`.** The half-gap `‖d‖` of the abstract two-band model
evaluates to the modulus of the structure factor. Everything downstream (gaplessness at the Dirac
points, the gap away from them) is a statement about `|f|`. -/
theorem honeycomb_energy_eq (θ : ℝ × ℝ) :
    Real.sqrt (dNormSq (honeycombD θ)) = ‖structureFactor θ‖ := by
  rw [Complex.norm_def, dNormSq_honeycombD]

/-- **The honeycomb Hamiltonian is Hermitian** — inherited from `BlochBundle`, so the instance is
load-bearing rather than a name: the physical requirement (real band energies) is discharged by
the `blochPauli` core, not re-argued. -/
theorem honeycombBloch_isHermitian (θ : ℝ × ℝ) : (honeycombBloch θ).IsHermitian :=
  blochPauli_isHermitian (honeycombD θ)

/-- **The honeycomb Pauli identity** `H(θ)² = |f(θ)|²·I` — `blochPauli_sq` with the honeycomb
`‖d‖²` evaluated. This is the algebraic fact that *forces* the bands to `±|f|`, and it is the
second place the `blochPauli` instantiation does real work. -/
theorem honeycombBloch_sq (θ : ℝ × ℝ) :
    honeycombBloch θ * honeycombBloch θ
      = (Complex.normSq (structureFactor θ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold honeycombBloch
  rw [blochPauli_sq, dNormSq_honeycombD]

/-! ## The Dirac points -/

/-- **The exact zero set of the structure factor**, quotient-free.

    f(θ) = 0  ↔  cos θ₁ = −1/2  ∧  cos θ₂ = −1/2  ∧  sin θ₁ + sin θ₂ = 0

The forward direction is the delicate step: vanishing of `Re f` and `Im f` gives
`1 + cos θ₁ + cos θ₂ = 0` and `sin θ₂ = −sin θ₁`, and squaring the latter with
`sin² + cos² = 1` forces `cos²θ₂ = cos²θ₁`. The branch `cos θ₂ = −cos θ₁` contradicts the first
equation (it would need `1 = 0`), so `cos θ₂ = cos θ₁` and both equal `−1/2`.

No `mod 2π` bookkeeping appears because none is needed — `cos` and `sin` are already periodic, so
this characterizes the full reciprocal-lattice orbit of `K` and `K'` at once. -/
theorem structureFactor_eq_zero_iff (θ : ℝ × ℝ) :
    structureFactor θ = 0 ↔
      Real.cos θ.1 = -(1/2) ∧ Real.cos θ.2 = -(1/2) ∧ Real.sin θ.1 + Real.sin θ.2 = 0 := by
  rw [Complex.ext_iff, Complex.zero_re, Complex.zero_im, structureFactor_re, structureFactor_im]
  constructor
  · rintro ⟨hre, him⟩
    have hp1 := Real.sin_sq_add_cos_sq θ.1
    have hp2 := Real.sin_sq_add_cos_sq θ.2
    -- `sin θ₂ = −sin θ₁`, so the two `sin²` agree, hence so do the two `cos²`.
    have hsneg : Real.sin θ.2 = -Real.sin θ.1 := by linarith
    have hs2 : Real.sin θ.2 ^ 2 = Real.sin θ.1 ^ 2 := by rw [hsneg]; ring
    have hfac : (Real.cos θ.1 - Real.cos θ.2) * (Real.cos θ.1 + Real.cos θ.2) = 0 := by
      nlinarith [hp1, hp2, hs2]
    -- the `cos θ₁ = −cos θ₂` branch would force `1 = 0` in `hre`, so the sum branch is dead
    have hcos : Real.cos θ.1 = Real.cos θ.2 := by
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · linarith
    refine ⟨by linarith, by linarith, him⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rw [h1, h2]; ring, h3⟩

/-- **The two Dirac branches.** The phase constraints of `structureFactor_eq_zero_iff` have exactly
two solution branches, distinguished by the sign of `sin θ₁`: the `K` branch
(`sin θ₁ = +√3/2`, `sin θ₂ = −√3/2`) and the `K'` branch (the reverse). This is the `K`/`K'`
reading the AC's `mod`-quotient phrasing was after, recovered without the quotient. -/
theorem structureFactor_eq_zero_iff_dirac_branch (θ : ℝ × ℝ) :
    structureFactor θ = 0 ↔
      Real.cos θ.1 = -(1/2) ∧ Real.cos θ.2 = -(1/2) ∧
        ((Real.sin θ.1 = Real.sqrt 3 / 2 ∧ Real.sin θ.2 = -(Real.sqrt 3 / 2)) ∨
         (Real.sin θ.1 = -(Real.sqrt 3 / 2) ∧ Real.sin θ.2 = Real.sqrt 3 / 2)) := by
  rw [structureFactor_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hp1 := Real.sin_sq_add_cos_sq θ.1
    have hsq : Real.sin θ.1 ^ 2 = (Real.sqrt 3 / 2) ^ 2 := by
      rw [div_pow, hs3]; nlinarith [hp1, h1]
    refine ⟨h1, h2, ?_⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact Or.inl ⟨h, by linarith⟩
    · exact Or.inr ⟨h, by linarith⟩
  · rintro ⟨h1, h2, h | h⟩
    · exact ⟨h1, h2, by rw [h.1, h.2]; ring⟩
    · exact ⟨h1, h2, by rw [h.1, h.2]; ring⟩

/-- **The model is gapless exactly on the Dirac set.** At `K` the structure factor vanishes, so the
two bands touch at zero energy. -/
theorem honeycomb_gapless_at_diracK : structureFactor diracK = 0 := by
  rw [structureFactor_eq_zero_iff]
  refine ⟨?_, ?_, ?_⟩
  · show Real.cos (2 * π / 3) = -(1/2)
    rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  · show Real.cos (4 * π / 3) = -(1/2)
    rw [show (4 * π / 3 : ℝ) = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three]
  · show Real.sin (2 * π / 3) + Real.sin (4 * π / 3) = 0
    rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, show (4 * π / 3 : ℝ) = π / 3 + π by ring,
      Real.sin_pi_sub, Real.sin_add_pi]
    ring

/-- `K'` is likewise a Dirac point — the two are inequivalent as phase pairs (they are the two
branches of `structureFactor_eq_zero_iff_dirac_branch`), which is why graphene has *two* cones. -/
theorem honeycomb_gapless_at_diracK' : structureFactor diracK' = 0 := by
  rw [structureFactor_eq_zero_iff]
  refine ⟨?_, ?_, ?_⟩
  · show Real.cos (4 * π / 3) = -(1/2)
    rw [show (4 * π / 3 : ℝ) = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three]
  · show Real.cos (2 * π / 3) = -(1/2)
    rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  · show Real.sin (4 * π / 3) + Real.sin (2 * π / 3) = 0
    rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, show (4 * π / 3 : ℝ) = π / 3 + π by ring,
      Real.sin_pi_sub, Real.sin_add_pi]
    ring

/-- **The model is gapped away from the Dirac set** — via `BlochBundle`'s `blochPauli_gap_pos`,
not a fresh argument. Off the zero set of `f` the half-gap `‖d‖` is strictly positive. -/
theorem honeycomb_gapped_away {θ : ℝ × ℝ} (h : structureFactor θ ≠ 0) :
    0 < Real.sqrt (dNormSq (honeycombD θ)) := by
  refine blochPauli_gap_pos _ ?_
  intro hd
  apply h
  have hre : (structureFactor θ).re = 0 := by
    have := congrFun hd 0
    simpa [honeycombD] using this
  have him : (structureFactor θ).im = 0 := by
    have := congrFun hd 1
    simpa [honeycombD] using this
  exact Complex.ext hre him

/-! ## High-symmetry witnesses -/

/-- **Γ point: `|f| = 3`.** All three hoppings add in phase — the band extremum. A `norm_num`-level
number, so the abstract band formula is pinned to an arithmetic fact at a named point. -/
theorem structureFactor_gamma : structureFactor gammaPoint = 3 := by
  unfold structureFactor gammaPoint
  norm_num

/-- The Γ-point band energy is `3` (in units of the hopping `t`). -/
theorem honeycomb_energy_gamma : Real.sqrt (dNormSq (honeycombD gammaPoint)) = 3 := by
  rw [honeycomb_energy_eq, structureFactor_gamma]
  norm_num

/-- **M point: `|f| = 1`.** One hopping cancels against another, leaving a single unit — the
saddle-point value between Γ and the Dirac points. -/
theorem structureFactor_mPoint : structureFactor mPoint = 1 := by
  unfold structureFactor mPoint
  simp [Complex.exp_mul_I]

/-- The M-point band energy is `1`. Together with `honeycomb_energy_gamma` (`3`) and gaplessness at
`K` (`0`), the three named points give the band's full range as checkable numbers. -/
theorem honeycomb_energy_mPoint : Real.sqrt (dNormSq (honeycombD mPoint)) = 1 := by
  rw [honeycomb_energy_eq, structureFactor_mPoint]
  norm_num

/-- **The three high-symmetry values are distinct** — so the band is genuinely dispersive, not a
flat band the formulas would also permit. The non-vacuity witness for the whole wave. -/
theorem honeycomb_band_dispersive :
    Real.sqrt (dNormSq (honeycombD gammaPoint)) ≠ Real.sqrt (dNormSq (honeycombD mPoint)) ∧
      Real.sqrt (dNormSq (honeycombD mPoint)) ≠ Real.sqrt (dNormSq (honeycombD diracK)) := by
  refine ⟨?_, ?_⟩
  · rw [honeycomb_energy_gamma, honeycomb_energy_mPoint]; norm_num
  · rw [honeycomb_energy_mPoint, honeycomb_energy_eq, honeycomb_gapless_at_diracK]
    norm_num

end SKEFTHawking.GrapheneBand
