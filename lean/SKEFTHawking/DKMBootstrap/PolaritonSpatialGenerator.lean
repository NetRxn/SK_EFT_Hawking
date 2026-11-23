import SKEFTHawking.KineticEssentialSelfAdjoint
import SKEFTHawking.DKMBootstrap.PolaritonPortBath
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Closed spatial polariton generator at total particle number one

Two actual planar L² fields and the full vector-valued positive-frequency port bath
form a finite Hilbert product. The angular generator is `K = H / ℏ`: the two independent
physical masses multiply the native momentum-square closure by `(2 m ℏ)⁻¹`.
Bounded measurable spatial potentials, complex Rabi multiplication and a bounded
photon-to-bath map are added with their true Hilbert adjoints. The graph domain is
unchanged by this bounded perturbation. No photon-sector invariance, external drive,
Markov loss, detector identification or group differentiability is asserted here.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate

namespace SKEFTHawking.DKMBootstrap.PolaritonSpatialGenerator

/-! ## Finite Hilbert diagonal, with actual coordinate resolvents -/

section FiniteDiagonal

variable {ι : Type*} [Fintype ι] {F : ι → Type*}
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]

/-- No extra summability condition occurs in a finite Hilbert product. -/
def diagonalDomain (A : ∀ i, F i →ₗ.[ℂ] F i) : Submodule ℂ (PiLp 2 F) where
  carrier := {x | ∀ i, x i ∈ (A i).domain}
  zero_mem' := fun i ↦ (A i).domain.zero_mem
  add_mem' := fun hx hy i ↦ (A i).domain.add_mem (hx i) (hy i)
  smul_mem' := fun c _ hx i ↦ (A i).domain.smul_mem c (hx i)

/-- The free partial map applies each native block on its own native domain. -/
def diagonal (A : ∀ i, F i →ₗ.[ℂ] F i) : PiLp 2 F →ₗ.[ℂ] PiLp 2 F where
  domain := diagonalDomain A
  toFun :=
    { toFun := fun x ↦ WithLp.toLp 2 (fun i ↦ A i ⟨x.val i, x.property i⟩)
      map_add' := by
        intro x y
        apply PiLp.ext
        intro i
        exact (A i).map_add ⟨x.val i, x.property i⟩ ⟨y.val i, y.property i⟩
      map_smul' := by
        intro c x
        apply PiLp.ext
        intro i
        exact (A i).map_smul c ⟨x.val i, x.property i⟩ }

omit [Fintype ι] in
@[simp] theorem diagonal_apply (A : ∀ i, F i →ₗ.[ℂ] F i)
    (x : (diagonal A).domain) (i : ι) :
    diagonal A x i = A i ⟨x.val i, x.property i⟩ := rfl

theorem diagonal_symmetric (A : ∀ i, F i →ₗ.[ℂ] F i)
    (hA : ∀ i, DFT.IsSymmetricPMap (A i)) : DFT.IsSymmetricPMap (diagonal A) := by
  intro x y
  simp only [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun i _ ↦ hA i ⟨x.val i, x.property i⟩
    ⟨y.val i, y.property i⟩

variable [∀ i, CompleteSpace (F i)]

omit [Fintype ι] in
/-- Coordinate resolvents produce a genuine preimage in the full product graph. -/
theorem diagonal_shift_surjective (A : ∀ i, F i →ₗ.[ℂ] F i)
    (hA : ∀ i, IsSelfAdjoint (A i)) (μ : ℝ) (hμ : μ ≠ 0) (z : PiLp 2 F) :
    ∃ x : (diagonal A).domain,
      diagonal A x - (Complex.I * (μ : ℂ)) • x.val = z := by
  choose x hx using fun i ↦ DFT.IsSelfAdjoint.surjective_sub_I_smul (hA i) hμ (z i)
  refine ⟨⟨WithLp.toLp 2 (fun i ↦ (x i).val), fun i ↦ (x i).property⟩, ?_⟩
  exact PiLp.ext hx

/-- Density is proved on this graph, using its actual shifted preimages. -/
theorem diagonal_dense (A : ∀ i, F i →ₗ.[ℂ] F i)
    (hA : ∀ i, IsSelfAdjoint (A i)) : Dense ((diagonal A).domain : Set (PiLp 2 F)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨x, hx⟩ := diagonal_shift_surjective A hA 1 one_ne_zero y
  have hxy : ⟪x.val, y⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp hy x.val x.property
  have hs := diagonal_symmetric A (fun i ↦ DFT.IsSelfAdjoint.isSymmetricPMap (hA i))
  have him : (⟪x.val, diagonal A x⟫_ℂ).im = 0 := by
    rw [← hs x x]
    exact hs.inner_self_im_eq_zero x
  rw [← hx, inner_sub_right, inner_smul_right] at hxy
  have hnorm : ‖x.val‖ ^ 2 = 0 := by
    have hi := congrArg Complex.im hxy
    simp only [Complex.ofReal_one, mul_one, Complex.sub_im, Complex.I_mul_im,
      Complex.zero_im, him] at hi
    have hre : (⟪x.val, x.val⟫_ℂ).re = ‖x.val‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) x.val
    linarith
  have hx0 : x.val = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hAx0 : diagonal A x = 0 := by
    rw [show x = 0 from Subtype.ext hx0, LinearPMap.map_zero]
  rw [hAx0, hx0, smul_zero, sub_zero] at hx
  exact hx.symm

theorem diagonal_selfAdjoint (A : ∀ i, F i →ₗ.[ℂ] F i)
    (hA : ∀ i, IsSelfAdjoint (A i)) : IsSelfAdjoint (diagonal A) := by
  apply DFT.IsSymmetricPMap.isSelfAdjoint_of_surjective
    (diagonal_symmetric A (fun i ↦ DFT.IsSelfAdjoint.isSymmetricPMap (hA i)))
    (diagonal_dense A hA) (μ := 1)
  · exact diagonal_shift_surjective A hA 1 one_ne_zero
  · intro z
    obtain ⟨x, hx⟩ := diagonal_shift_surjective A hA (-1) (by norm_num) z
    exact ⟨x, by simpa using hx⟩

end FiniteDiagonal

/-! ## Physical planar kinetics and bounded measurable profiles -/

abbrev Spatial := QuantumMechanics.SpaceDHilbertSpace 2
abbrev Profile := Lp ℂ ⊤ (volume : Measure (Space 2))

/-- Angular kinetic coefficient; native momentum already includes ℏ. -/
def kineticCoefficient (m : ℝ) : ℝ := (2 * m * (Constants.ℏ : ℝ))⁻¹

def kinetic (m : ℝ) : Spatial →ₗ.[ℂ] Spatial :=
  (kineticCoefficient m : ℂ) • (QuantumMechanics.momentumSqOperator (d := 2)).closure

theorem kineticCoefficient_pos {m : ℝ} (hm : 0 < m) : 0 < kineticCoefficient m := by
  exact inv_pos.mpr (mul_pos (mul_pos (by norm_num) hm) Constants.ℏ_pos)

theorem kinetic_selfAdjoint {m : ℝ} (hm : 0 < m) : IsSelfAdjoint (kinetic m) :=
  LinearPMap.IsSelfAdjoint.smul (DFT.momentumSqOperator_isSelfAdjoint_closure (d := 2))
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (kineticCoefficient_pos hm)))
    (Complex.conj_ofReal _)

/-- Scaling retains the full momentum-square closure domain, not only Schwartz tests. -/
theorem kinetic_domain (m : ℝ) :
    (kinetic m).domain = (QuantumMechanics.momentumSqOperator (d := 2)).closure.domain := rfl

/-- Genuine L∞ × L² multiplication on the physical plane. -/
def multiplier (v : Profile) : Spatial →L[ℂ] Spatial :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2 v

theorem multiplier_ae (v : Profile) (u : Spatial) :
    (multiplier v u : Space 2 → ℂ) =ᵐ[volume] fun x ↦ v x * u x :=
  (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder v u (r := 2)

/-- Reality is required only almost everywhere, appropriate to L∞ classes. -/
def RealProfile (v : Profile) : Prop := ∀ᵐ x ∂volume, conj (v x) = v x

theorem multiplier_symmetric (v : Profile) (hv : RealProfile v) (u w : Spatial) :
    ⟪multiplier v u, w⟫_ℂ = ⟪u, multiplier v w⟫_ℂ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplier_ae v u, multiplier_ae v w, hv] with x hu hw hx
  rw [hu, hw]
  simp only [RCLike.inner_apply, map_mul, hx]
  ring

/-- Complex spatial multiplication has exactly conjugate-profile Hilbert adjoint. -/
theorem multiplier_adjoint (v : Profile) : (multiplier v).adjoint = multiplier (star v) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplier_ae v w, multiplier_ae (star v) u, Lp.coeFn_star v]
    with x hw hu hv
  rw [hw, hu, hv]
  simp only [RCLike.inner_apply, Pi.star_apply, Complex.star_def, map_mul, Complex.conj_conj]
  ring

open QuantumMechanics QuantumMechanics.SpaceDHilbertSpace in
/-- Actual Schwartz inputs belong to the closed angular kinetic graph. -/
theorem schwartz_mem_kinetic (m : ℝ) (f : SchwartzMap (Space 2) ℂ) :
    (schwartzEquiv volume f : Spatial) ∈ (kinetic m).domain := by
  apply (momentumSqOperator (d := 2)).le_closure.1
  rw [momentumSqOperator_domain_eq]
  exact (schwartzEquiv volume f).property

open QuantumMechanics QuantumMechanics.SpaceDHilbertSpace in
/-- The closed operator agrees with native differential momentum-square on Schwartz inputs. -/
theorem kinetic_schwartz (m : ℝ) (f : SchwartzMap (Space 2) ℂ) :
    kinetic m ⟨(schwartzEquiv volume f : Spatial), schwartz_mem_kinetic m f⟩ =
      (kineticCoefficient m : ℂ) • schwartzIncl volume
        (∑ i : Fin 2, momentumCLM i (momentumCLM i f)) := by
  have hf : (schwartzEquiv volume f : Spatial) ∈ momentumSqOperator.domain := by
    rw [momentumSqOperator_domain_eq]
    exact (schwartzEquiv volume f).property
  change (kineticCoefficient m : ℂ) • momentumSqOperator.closure
    ⟨_, schwartz_mem_kinetic m f⟩ = _
  congr 1
  calc
    momentumSqOperator.closure ⟨_, schwartz_mem_kinetic m f⟩ =
        momentumSqOperator ⟨_, hf⟩ := (momentumSqOperator.le_closure.2 rfl).symm
    _ = _ := DFT.momentumSqOperator_apply_eq f hf

/-- The angular kinetic coefficient is −ℏ/(2m) after the two native momenta act. -/
theorem angular_kinetic_coefficient {m : ℝ} (hm : 0 < m) :
    (kineticCoefficient m : ℂ) * (-Complex.I * (Constants.ℏ : ℂ)) ^ 2 =
      -((Constants.ℏ : ℂ) / (2 * (m : ℂ))) := by
  have hm0 : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hm)
  have hh0 : (Constants.ℏ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt Constants.ℏ_pos)
  simp only [kineticCoefficient, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  field_simp
  simp [Complex.I_sq]

open QuantumMechanics QuantumMechanics.SpaceDHilbertSpace in
/-- On actual planar Schwartz inputs the angular generator has differential coefficient
`−ℏ/(2m)`, with the two Cartesian second directional derivatives. -/
theorem kinetic_schwartz_laplacian {m : ℝ} (hm : 0 < m)
    (f : SchwartzMap (Space 2) ℂ) :
    kinetic m ⟨(schwartzEquiv volume f : Spatial), schwartz_mem_kinetic m f⟩ =
      -((Constants.ℏ : ℂ) / (2 * (m : ℂ))) • schwartzIncl volume
        (∑ i : Fin 2, LineDeriv.lineDerivOp (Space.basis i)
          (LineDeriv.lineDerivOp (Space.basis i) f)) := by
  rw [kinetic_schwartz]
  have hi (i : Fin 2) : momentumCLM i (momentumCLM i f) =
      (-Complex.I * (Constants.ℏ : ℂ)) ^ 2 •
        LineDeriv.lineDerivOp (Space.basis i) (LineDeriv.lineDerivOp (Space.basis i) f) := by
    rw [DFT.momentumCLM_eq_smul_lineDeriv, DFT.momentumCLM_eq_smul_lineDeriv,
      LineDeriv.lineDerivOp_smul, smul_smul, pow_two]
  simp_rw [hi]
  rw [← Finset.smul_sum, map_smul, smul_smul, angular_kinetic_coefficient hm]

/-! ## Actual photon–exciton–port Hilbert product -/

inductive Species
  | photon | exciton | port
  deriving DecidableEq, Fintype

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The two planar fields and the untruncated vector-valued port carrier. -/
abbrev Fiber : Species → Type _
  | .photon => Spatial
  | .exciton => Spatial
  | .port => PolaritonPortBath.Bath E

instance fiberNorm : (s : Species) → NormedAddCommGroup (Fiber E s)
  | .photon => inferInstanceAs (NormedAddCommGroup Spatial)
  | .exciton => inferInstanceAs (NormedAddCommGroup Spatial)
  | .port => inferInstanceAs (NormedAddCommGroup (PolaritonPortBath.Bath E))

instance fiberInner : (s : Species) → InnerProductSpace ℂ (Fiber E s)
  | .photon => inferInstanceAs (InnerProductSpace ℂ Spatial)
  | .exciton => inferInstanceAs (InnerProductSpace ℂ Spatial)
  | .port => inferInstanceAs (InnerProductSpace ℂ (PolaritonPortBath.Bath E))

instance fiberComplete [CompleteSpace E] : (s : Species) → CompleteSpace (Fiber E s)
  | .photon => inferInstanceAs (CompleteSpace Spatial)
  | .exciton => inferInstanceAs (CompleteSpace Spatial)
  | .port => inferInstanceAs (CompleteSpace (PolaritonPortBath.Bath E))

abbrev State := PiLp 2 (Fiber E)

/-- Actual coordinate projection. -/
def projection (s : Species) : State E →L[ℂ] Fiber E s := PiLp.proj 2 (Fiber E) s

/-- Actual supported coordinate injection, continuous in the Hilbert product norm. -/
def injection (s : Species) : Fiber E s →L[ℂ] State E :=
  (PiLp.continuousLinearEquiv 2 ℂ (Fiber E)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (Fiber E) s

@[simp] theorem injection_apply (s : Species) (u : Fiber E s) :
    injection E s u = PiLp.single 2 s u := rfl

@[simp] theorem projection_apply (s : Species) (u : State E) : projection E s u = u s := rfl

@[simp] theorem projection_injection_same (s : Species) (u : Fiber E s) :
    projection E s (injection E s u) = u := by simp

@[simp] theorem projection_injection_ne {s t : Species} (h : t ≠ s) (u : Fiber E s) :
    projection E t (injection E s u) = 0 := by simp [h]

@[simp] theorem injection_coordinate_same (s : Species) (u : Fiber E s) :
    (injection E s u) s = u := PiLp.single_eq_same 2 s u

@[simp] theorem injection_coordinate_ne {s t : Species} (h : t ≠ s) (u : Fiber E s) :
    (injection E s u) t = 0 := PiLp.single_eq_of_ne 2 h u

theorem inner_injection_left (s : Species) (u : Fiber E s) (v : State E) :
    ⟪injection E s u, v⟫_ℂ = ⟪u, projection E s v⟫_ℂ := by
  rw [injection_apply, PiLp.inner_apply, Finset.sum_eq_single s]
  · simp
  · intro t _ h
    simp [h]
  · simp

theorem inner_injection_right (s : Species) (u : State E) (v : Fiber E s) :
    ⟪u, injection E s v⟫_ℂ = ⟪projection E s u, v⟫_ℂ := by
  rw [← inner_conj_symm, inner_injection_left, inner_conj_symm]

/-- The injections and projections are a true adjoint pair. -/
theorem injection_adjoint [CompleteSpace E] (s : Species) :
    (injection E s).adjoint = projection E s := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left, inner_injection_right]

/-- Native free blocks; the physical photon and exciton masses are independent. -/
def freeBlock (mC mX : ℝ) : ∀ s, Fiber E s →ₗ.[ℂ] Fiber E s
  | .photon => kinetic mC
  | .exciton => kinetic mX
  | .port => PolaritonPortBath.omega

def free (mC mX : ℝ) : State E →ₗ.[ℂ] State E := diagonal (freeBlock E mC mX)

variable {E}

theorem freeBlock_selfAdjoint [CompleteSpace E] {mC mX : ℝ}
    (hC : 0 < mC) (hX : 0 < mX) (s : Species) :
    IsSelfAdjoint (freeBlock E mC mX s) := by
  cases s
  · exact kinetic_selfAdjoint hC
  · exact kinetic_selfAdjoint hX
  · exact PolaritonPortBath.omega_selfAdjoint

/-- Actual free graph: both closed kinetic domains and the maximal bath domain. -/
theorem free_mem_domain (mC mX : ℝ) (u : State E) :
    u ∈ (free E mC mX).domain ↔
      u .photon ∈ (QuantumMechanics.momentumSqOperator (d := 2)).closure.domain ∧
      u .exciton ∈ (QuantumMechanics.momentumSqOperator (d := 2)).closure.domain ∧
      MemLp (fun ω : ℝ ↦ (ω : ℂ) • u .port ω) 2
        PolaritonPortBath.frequencyMeasure := by
  change (∀ s, u s ∈ (freeBlock E mC mX s).domain) ↔ _
  constructor
  · intro h
    exact ⟨h .photon, h .exciton, h .port⟩
  · rintro ⟨hC, hX, hB⟩ s
    cases s
    · exact hC
    · exact hX
    · exact hB

theorem free_symmetric {mC mX : ℝ} [CompleteSpace E]
    (hC : 0 < mC) (hX : 0 < mX) : DFT.IsSymmetricPMap (free E mC mX) :=
  diagonal_symmetric _ (fun s ↦ DFT.IsSelfAdjoint.isSymmetricPMap
    (freeBlock_selfAdjoint hC hX s))

theorem free_shift_surjective [CompleteSpace E] {mC mX : ℝ}
    (hC : 0 < mC) (hX : 0 < mX) (μ : ℝ) (hμ : μ ≠ 0) (z : State E) :
    ∃ x : (free E mC mX).domain,
      free E mC mX x - (Complex.I * (μ : ℂ)) • x.val = z :=
  diagonal_shift_surjective _ (freeBlock_selfAdjoint hC hX) μ hμ z

theorem free_dense [CompleteSpace E] {mC mX : ℝ} (hC : 0 < mC) (hX : 0 < mX) :
    Dense ((free E mC mX).domain : Set (State E)) :=
  diagonal_dense _ (freeBlock_selfAdjoint hC hX)

theorem free_selfAdjoint [CompleteSpace E] {mC mX : ℝ} (hC : 0 < mC) (hX : 0 < mX) :
    IsSelfAdjoint (free E mC mX) := diagonal_selfAdjoint _ (freeBlock_selfAdjoint hC hX)

/-! ## Bounded physical couplings and the closed generator -/

variable (E)

/-- Closed N=1 angular-frequency data. The offsets and profiles are in angular units;
`mPhoton` and `mExciton` are physical masses. The port map has no bath-domain constraint. -/
structure Model [CompleteSpace E] where
  mPhoton : ℝ
  mExciton : ℝ
  mPhoton_pos : 0 < mPhoton
  mExciton_pos : 0 < mExciton
  photonOffset : ℝ
  excitonOffset : ℝ
  photonPotential : Profile
  excitonPotential : Profile
  photonPotential_real : RealProfile photonPotential
  excitonPotential_real : RealProfile excitonPotential
  rabi : Profile
  portCoupling : Spatial →L[ℂ] PolaritonPortBath.Bath E

variable {E} [CompleteSpace E]

/-- Offset plus a genuine a.e. real, essentially bounded planar multiplier. -/
def spatialDiagonal (ω : ℝ) (v : Profile) : Spatial →L[ℂ] Spatial :=
  (ω : ℂ) • ContinuousLinearMap.id ℂ Spatial + multiplier v

theorem spatialDiagonal_symmetric (ω : ℝ) (v : Profile) (hv : RealProfile v)
    (u w : Spatial) : ⟪spatialDiagonal ω v u, w⟫_ℂ =
      ⟪u, spatialDiagonal ω v w⟫_ℂ := by
  simp only [spatialDiagonal, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, multiplier_symmetric v hv]

/-- A block uses the actual Hilbert coordinate maps. -/
def liftBlock (i j : Species) (T : Fiber E j →L[ℂ] Fiber E i) : State E →L[ℂ] State E :=
  injection E i ∘L T ∘L projection E j

omit [CompleteSpace E] in
theorem liftBlock_inner_left (i j : Species) (T : Fiber E j →L[ℂ] Fiber E i)
    (u v : State E) : ⟪liftBlock i j T u, v⟫_ℂ =
      ⟪T (projection E j u), projection E i v⟫_ℂ := by
  exact inner_injection_left E i _ _

omit [CompleteSpace E] in
theorem liftBlock_inner_right (i j : Species) (T : Fiber E j →L[ℂ] Fiber E i)
    (u v : State E) : ⟪u, liftBlock i j T v⟫_ℂ =
      ⟪projection E i u, T (projection E j v)⟫_ℂ := by
  exact inner_injection_right E i _ _

/-- Off-diagonal exchange and its true Hilbert adjoint. -/
def exchange (i j : Species) (T : Fiber E j →L[ℂ] Fiber E i) : State E →L[ℂ] State E :=
  liftBlock i j T + liftBlock j i T.adjoint

theorem exchange_symmetric (i j : Species) (T : Fiber E j →L[ℂ] Fiber E i)
    (u v : State E) : ⟪exchange i j T u, v⟫_ℂ = ⟪u, exchange i j T v⟫_ℂ := by
  simp only [exchange, add_apply, inner_add_left, inner_add_right,
    liftBlock_inner_left, liftBlock_inner_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  exact add_comm _ _

/-- Full bounded matrix: two real diagonals, complex spatial Rabi and photon-port exchange. -/
def boundedPart (p : Model E) : State E →L[ℂ] State E :=
  liftBlock .photon .photon (spatialDiagonal p.photonOffset p.photonPotential) +
  liftBlock .exciton .exciton (spatialDiagonal p.excitonOffset p.excitonPotential) +
  exchange .photon .exciton (multiplier p.rabi) +
  exchange .port .photon p.portCoupling

theorem boundedPart_symmetric (p : Model E) (u v : State E) :
    ⟪boundedPart p u, v⟫_ℂ = ⟪u, boundedPart p v⟫_ℂ := by
  simp only [boundedPart, add_apply, inner_add_left, inner_add_right,
    exchange_symmetric, liftBlock_inner_left, liftBlock_inner_right,
    spatialDiagonal_symmetric _ _ p.photonPotential_real,
    spatialDiagonal_symmetric _ _ p.excitonPotential_real]

/-- Photon row, including both actual off-diagonal gains. -/
theorem boundedPart_photon (p : Model E) (u : State E) :
    boundedPart p u .photon =
      spatialDiagonal p.photonOffset p.photonPotential (u .photon) +
      multiplier p.rabi (u .exciton) + p.portCoupling.adjoint (u .port) := by
  simp [boundedPart, exchange, liftBlock, projection, injection]

theorem boundedPart_exciton (p : Model E) (u : State E) :
    boundedPart p u .exciton =
      spatialDiagonal p.excitonOffset p.excitonPotential (u .exciton) +
      (multiplier p.rabi).adjoint (u .photon) := by
  simp [boundedPart, exchange, liftBlock, projection, injection]

theorem boundedPart_port (p : Model E) (u : State E) :
    boundedPart p u .port = p.portCoupling (u .photon) := by
  simp [boundedPart, exchange, liftBlock, projection, injection]

/-- Top-domain partial map for the bounded perturbation. -/
def boundedOperator (p : Model E) : State E →ₗ.[ℂ] State E :=
  (boundedPart p).toLinearMap.toPMap ⊤

@[simp] theorem boundedOperator_apply (p : Model E) (u : (boundedOperator p).domain) :
    boundedOperator p u = boundedPart p u.val := rfl

/-- The autonomous, closed total-N=1 angular generator. -/
def generator (p : Model E) : State E →ₗ.[ℂ] State E :=
  free E p.mPhoton p.mExciton + boundedOperator p

/-- Relative bound zero requires no range regularity from Rabi or the port coupling. -/
theorem boundedOperator_relBound (p : Model E) :
    DFT.IsRelBounded (free E p.mPhoton p.mExciton) (boundedOperator p) 0 ‖boundedPart p‖ := by
  refine ⟨le_top, fun x ↦ ?_⟩
  simpa only [zero_mul, zero_add, boundedOperator_apply] using (boundedPart p).le_opNorm x.val

theorem generator_domain (p : Model E) :
    (generator p).domain = (free E p.mPhoton p.mExciton).domain := by
  rw [generator, LinearPMap.add_domain]
  exact inf_top_eq _

/-- The exact closed domain is exposed independently of the bounded coupling data. -/
theorem generator_mem_domain (p : Model E) (u : State E) :
    u ∈ (generator p).domain ↔
      u .photon ∈ (QuantumMechanics.momentumSqOperator (d := 2)).closure.domain ∧
      u .exciton ∈ (QuantumMechanics.momentumSqOperator (d := 2)).closure.domain ∧
      MemLp (fun ω : ℝ ↦ (ω : ℂ) • u .port ω) 2
        PolaritonPortBath.frequencyMeasure := by
  rw [generator_domain, free_mem_domain]

theorem generator_dense (p : Model E) : Dense ((generator p).domain : Set (State E)) := by
  rw [generator_domain]
  exact free_dense p.mPhoton_pos p.mExciton_pos

/-- Self-adjointness of the actual coupled generator by relative-zero Kato–Rellich. -/
theorem generator_selfAdjoint (p : Model E) : IsSelfAdjoint (generator p) := by
  have hA : IsSelfAdjoint (free E p.mPhoton p.mExciton) :=
    free_selfAdjoint p.mPhoton_pos p.mExciton_pos
  have hB : DFT.IsSymmetricPMap (boundedOperator p) := by
    intro x y
    rw [boundedOperator_apply, boundedOperator_apply]
    exact boundedPart_symmetric p x.val y.val
  exact DFT.katoRellich hA hB (a := 0) (b := ‖boundedPart p‖)
    (by norm_num) (by norm_num) (norm_nonneg (boundedPart p)) (boundedOperator_relBound p)

/-- The graph is closed on the stated maximal product domain. -/
theorem generator_closed (p : Model E) : (generator p).IsClosed :=
  LinearPMap.IsSelfAdjoint.isClosed (generator_selfAdjoint p)

/-- Same input, viewed in the free graph; no assumption on bounded-output regularity. -/
def freeInput (p : Model E) (u : (generator p).domain) :
    (free E p.mPhoton p.mExciton).domain := ⟨u.val, (generator_domain p).le u.property⟩

theorem generator_apply (p : Model E) (u : (generator p).domain) :
    generator p u = free E p.mPhoton p.mExciton (freeInput p u) + boundedPart p u.val := by
  change (free E p.mPhoton p.mExciton + boundedOperator p) u = _
  rw [LinearPMap.add_apply, boundedOperator_apply]
  rfl

/-- Exact photon block action on the full coupled graph. -/
theorem generator_photon (p : Model E) (u : (generator p).domain) :
    generator p u .photon =
      kinetic p.mPhoton ⟨u.val .photon, (freeInput p u).property .photon⟩ +
      spatialDiagonal p.photonOffset p.photonPotential (u.val .photon) +
      multiplier p.rabi (u.val .exciton) + p.portCoupling.adjoint (u.val .port) := by
  rw [generator_apply, PiLp.add_apply, boundedPart_photon]
  have hfree : free E p.mPhoton p.mExciton (freeInput p u) .photon =
      kinetic p.mPhoton ⟨u.val .photon, (freeInput p u).property .photon⟩ := rfl
  rw [hfree]
  abel

/-- Exact exciton block action, with the true adjoint Rabi map. -/
theorem generator_exciton (p : Model E) (u : (generator p).domain) :
    generator p u .exciton =
      kinetic p.mExciton ⟨u.val .exciton, (freeInput p u).property .exciton⟩ +
      spatialDiagonal p.excitonOffset p.excitonPotential (u.val .exciton) +
      (multiplier p.rabi).adjoint (u.val .photon) := by
  rw [generator_apply, PiLp.add_apply, boundedPart_exciton]
  have hfree : free E p.mPhoton p.mExciton (freeInput p u) .exciton =
      kinetic p.mExciton ⟨u.val .exciton, (freeInput p u).property .exciton⟩ := rfl
  rw [hfree]
  abel

/-- Exact full vector-valued positive-frequency bath row. -/
theorem generator_port (p : Model E) (u : (generator p).domain) :
    generator p u .port =
      PolaritonPortBath.omega ⟨u.val .port, (freeInput p u).property .port⟩ +
      p.portCoupling (u.val .photon) := by
  rw [generator_apply, PiLp.add_apply, boundedPart_port]
  rfl

/-- Supported photon inputs retain exactly their closed spatial kinetic domain. -/
def photonInput (p : Model E) (u : Spatial) (hu : u ∈ (kinetic p.mPhoton).domain) :
    (generator p).domain := by
  refine ⟨injection E .photon u, ?_⟩
  rw [generator_domain]
  change ∀ s, (injection E .photon u) s ∈ (freeBlock E p.mPhoton p.mExciton s).domain
  intro s
  cases s
  · simpa [injection, freeBlock] using hu
  · simp [injection, freeBlock]
  · simp [injection, freeBlock]

/-- Supported photon states are in the coupled graph exactly on the native kinetic domain. -/
theorem photon_injection_mem_domain_iff (p : Model E) (u : Spatial) :
    injection E .photon u ∈ (generator p).domain ↔ u ∈ (kinetic p.mPhoton).domain := by
  constructor
  · intro hu
    have h := ((generator_domain p).le hu :
      injection E .photon u ∈ (free E p.mPhoton p.mExciton).domain)
    have hC := h .photon
    simpa [injection, freeBlock] using hC
  · intro hu
    exact (photonInput p u hu).property

/-- Compression identifies the photon diagonal without claiming an invariant photon sector. -/
theorem photon_compression (p : Model E) (u : Spatial)
    (hu : u ∈ (kinetic p.mPhoton).domain) :
    projection E .photon (generator p (photonInput p u hu)) =
      kinetic p.mPhoton ⟨u, hu⟩ + spatialDiagonal p.photonOffset p.photonPotential u := by
  rw [projection_apply, generator_photon]
  simp [photonInput, injection]

/-- Rabi coupling sends a supported photon input into the actual exciton coordinate. -/
theorem photon_exciton_gain (p : Model E) (u : Spatial)
    (hu : u ∈ (kinetic p.mPhoton).domain) :
    projection E .exciton (generator p (photonInput p u hu)) =
      (multiplier p.rabi).adjoint u := by
  rw [projection_apply, generator_exciton]
  simp [photonInput, injection]
  exact (kinetic p.mExciton).map_zero

/-- Photon-port gain remains present on the full continuum bath. -/
theorem photon_port_gain (p : Model E) (u : Spatial)
    (hu : u ∈ (kinetic p.mPhoton).domain) :
    projection E .port (generator p (photonInput p u hu)) = p.portCoupling u := by
  rw [projection_apply, generator_port]
  simp [photonInput, injection]
  exact (PolaritonPortBath.omega (E := E)).map_zero

/-- A nonzero actual port gain prevents the photon output from lying in the photon sector. -/
theorem photon_not_invariant_of_port_gain (p : Model E) (u : Spatial)
    (hu : u ∈ (kinetic p.mPhoton).domain) (hW : p.portCoupling u ≠ 0) (v : Spatial) :
    generator p (photonInput p u hu) ≠ injection E .photon v := by
  intro h
  have hp := congrArg (projection E .port) h
  rw [photon_port_gain] at hp
  have hz : projection E .port (injection E .photon v) = 0 := by
    simp [projection, injection]
  exact hW (hp.trans hz)

end SKEFTHawking.DKMBootstrap.PolaritonSpatialGenerator
