import SKEFTHawking.QuantumNetwork.FiniteAdaptiveProcessRobustness
import SKEFTHawking.QuantumNetwork.NegativityGeneral

/-! Summed branch-state bounds for actual finite intervention maps. Branches retain
unnormalized mass, including impossible outcomes; the environment is explicit.

The local premise is uniform over every density on this fixed finite system and
retained environment, including correlations. The actual paired-tree telescope
bounds both full-history variation and the terminal quantum state after history
is forgotten. Independently mixed evolution/instrument fields retain cross terms.
The exact multiplicative survival law is specific to the realized noisy-feedback
family, with m feedback layers after one root measurement. No extra-ancilla
diamond certification, postselection, sampling estimate, positive-quotient
stability, physical-time identification, or publication readiness is asserted. -/
namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveMapPerturbation
open Matrix FiniteInterventionProcess
open scoped BigOperators ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem traceNorm_sub_le (A B : Matrix ι ι ℂ) :
    traceNorm (A-B) ≤ traceNorm A + traceNorm B := by
  simpa only [sub_eq_add_neg, traceNorm_neg] using traceNorm_triangle A (-B)

/-- Jordan decomposition applies before every positive branch; total trace is
preserved only after summing the whole family. -/
theorem summed_jordan (F : κ → Matrix ι ι ℂ → Matrix ι ι ℂ)
    (hsub : ∀ k X Y, F k (X-Y)=F k X-F k Y)
    (hpos : ∀ k X, X.PosSemidef → (F k X).PosSemidef)
    (htrace : ∀ X, ∑ k, (F k X).trace=X.trace)
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    ∑ k, traceNorm (F k A) ≤ traceNorm A := by
  have hs k : F k A=F k (posPart hA)-F k (negPart hA) := by
    conv_lhs => rw [self_eq_posPart_sub_negPart hA]
    exact hsub k _ _
  calc
    _ ≤ ∑ k, ((F k (posPart hA)).trace.re+(F k (negPart hA)).trace.re) := by
      apply Finset.sum_le_sum
      intro k _
      rw [hs]
      simpa only [traceNorm_posSemidef (hpos k _ (posPart_posSemidef hA)),
        traceNorm_posSemidef (hpos k _ (negPart_posSemidef hA))] using
        traceNorm_sub_le (F k (posPart hA)) (F k (negPart hA))
    _ = traceNorm A := by
      rw [Finset.sum_add_distrib, ← Complex.re_sum, ← Complex.re_sum,
        htrace, htrace, traceNorm_hermitian_eq_pos_add_neg hA]

theorem instrument_contraction {o : ℕ} (D : FiniteInstrument ι o)
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    ∑ a, traceNorm (D.branch a A) ≤ traceNorm A :=
  summed_jordan D.branch (fun _ X Y => krausMap_sub _ X Y)
    (fun a _ h => D.branch_posSemidef a h) D.sum_trace hA

variable (S E : Type*) [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E] (o : ℕ)

theorem branch_sub (D : Step S E o) (a : Fin o) (X Y : Matrix (S × E) (S × E) ℂ) :
    D.branch S E o a (X-Y)=D.branch S E o a X-D.branch S E o a Y := by
  simp only [Step.branch, FiniteInstrument.branch, krausMap_sub]

theorem branch_hermitian (D : Step S E o) (a : Fin o)
    {A : Matrix (S × E) (S × E) ℂ} (hA : A.IsHermitian) :
    (D.branch S E o a A).IsHermitian :=
  krausMap_isHermitian _ (krausMap_isHermitian _ hA)

theorem step_contraction (D : Step S E o)
    {A : Matrix (S × E) (S × E) ℂ} (hA : A.IsHermitian) :
    ∑ a, traceNorm (D.branch S E o a A) ≤ traceNorm A :=
  summed_jordan (D.branch S E o) (branch_sub S E o D)
    (fun a _ h => D.branch_posSemidef S E o a h) (D.sum_trace S E o) hA

theorem run_sub {n : ℕ} (T : Tree S E o n) (h : History o n)
    (X Y : Matrix (S × E) (S × E) ℂ) :
    run S E o T h (X-Y)=run S E o T h X-run S E o T h Y := by
  induction T generalizing X Y with
  | done => rfl
  | node D F ih =>
    rcases h with ⟨a,h⟩
    simp only [run, branch_sub, ih]

theorem run_hermitian {n : ℕ} (T : Tree S E o n) (h : History o n)
    {A : Matrix (S × E) (S × E) ℂ} (hA : A.IsHermitian) :
    (run S E o T h A).IsHermitian := by
  induction T generalizing A with
  | done => exact hA
  | node D F ih => exact ih h.1 h.2 (branch_hermitian S E o D h.1 hA)

theorem tree_contraction {n : ℕ} (T : Tree S E o n)
    {A : Matrix (S × E) (S × E) ℂ} (hA : A.IsHermitian) :
    ∑ h, traceNorm (run S E o T h A) ≤ traceNorm A :=
  summed_jordan (run S E o T) (run_sub S E o T)
    (fun h _ hX => run_posSemidef S E o T h hX) (sum_trace S E o T) hA


noncomputable def outputDistance {n : ℕ} (T U : Tree S E o n)
    (X Y : Matrix (S × E) (S × E) ℂ) : ℝ :=
  (∑ h, traceNorm (run S E o T h X-run S E o U h Y))/2

noncomputable def stepDistance (D D' : Step S E o)
    (X : Matrix (S × E) (S × E) ℂ) : ℝ :=
  (∑ a, traceNorm (D.branch S E o a X-D'.branch S E o a X))/2

/-- Uniform on every density of the full fixed system and retained environment. -/
def LocalError (D D' : Step S E o) (ε : ℝ) : Prop :=
  0≤ε ∧ ∀ Z, IsDensityOperator Z → stepDistance S E o D D' Z≤ε

theorem stepDistance_nonneg (D D' : Step S E o) (Z : Matrix (S × E) (S × E) ℂ) :
    0≤stepDistance S E o D D' Z :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => traceNorm_nonneg _)) (by norm_num)

theorem stepDistance_mass (D D' : Step S E o)
    {Z : Matrix (S × E) (S × E) ℂ} (hZ : Z.PosSemidef) :
    stepDistance S E o D D' Z ≤ Z.trace.re := by
  have hb : (∑ a, traceNorm (D.branch S E o a Z-D'.branch S E o a Z)) ≤
      Z.trace.re+Z.trace.re := by
    calc
      _ ≤ ∑ a, ((D.branch S E o a Z).trace.re+(D'.branch S E o a Z).trace.re) := by
        apply Finset.sum_le_sum
        intro a _
        simpa only [traceNorm_posSemidef (D.branch_posSemidef S E o a hZ),
          traceNorm_posSemidef (D'.branch_posSemidef S E o a hZ)] using
          traceNorm_sub_le (D.branch S E o a Z) (D'.branch S E o a Z)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Complex.re_sum, ← Complex.re_sum,
          D.sum_trace S E o, D'.sum_trace S E o]
  unfold stepDistance
  linarith

theorem stepDistance_zero_trace (D D' : Step S E o)
    {Z : Matrix (S × E) (S × E) ℂ} (hZ : Z.PosSemidef) (ht : Z.trace.re=0) :
    stepDistance S E o D D' Z=0 :=
  le_antisymm ((stepDistance_mass S E o D D' hZ).trans_eq ht)
    (stepDistance_nonneg S E o D D' Z)

theorem stepDistance_smul (D D' : Step S E o) (Z : Matrix (S × E) (S × E) ℂ)
    {c : ℝ} (hc : 0≤c) :
    stepDistance S E o D D' ((c:ℂ) • Z)=c*stepDistance S E o D D' Z := by
  simp only [stepDistance, Step.branch_smul, ← smul_sub, traceNorm_smul_nonneg hc]
  rw [← Finset.mul_sum]
  ring

/-- Only positive mass is normalized. The zero-mass case uses the unconditional
summed positive-output estimate and retains every branch. -/
theorem localError_positive (D D' : Step S E o) {ε : ℝ} (hε : LocalError S E o D D' ε)
    {Z : Matrix (S × E) (S × E) ℂ} (hZ : Z.PosSemidef) :
    stepDistance S E o D D' Z ≤ ε*Z.trace.re := by
  have ht : 0≤Z.trace.re := (Complex.le_def.mp hZ.trace_nonneg).1
  by_cases hz : Z.trace.re=0
  · rw [stepDistance_zero_trace S E o D D' hZ hz,hz,mul_zero]
  · have hp : 0<Z.trace.re := lt_of_le_of_ne ht (Ne.symm hz)
    have he : Z.trace=(Z.trace.re:ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using (Complex.le_def.mp hZ.trace_nonneg).2.symm
    let W := (((Z.trace.re)⁻¹:ℝ):ℂ) • Z
    have hW : IsDensityOperator W := by
      refine ⟨hZ.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr ht)),?_⟩
      dsimp only [W]
      rw [Matrix.trace_smul,smul_eq_mul,he]
      norm_cast
      exact inv_mul_cancel₀ hz
    have hs : Z=(Z.trace.re:ℂ) • W := by
      dsimp only [W]
      rw [smul_smul]
      norm_cast
      rw [mul_inv_cancel₀ hz,one_smul]
    have hb := mul_le_mul_of_nonneg_left (hε.2 W hW) hp.le
    conv_lhs => rw [hs,stepDistance_smul S E o D D' W ht]
    simpa only [mul_comm] using hb

theorem outputDistance_done (X Y : Matrix (S × E) (S × E) ℂ) :
    outputDistance S E o .done .done X Y=traceDist X Y := by
  simp [outputDistance,run,traceDist,history_card,div_eq_mul_inv,mul_comm]

theorem outputDistance_one (D D' : Step S E o) (Z : Matrix (S × E) (S × E) ℂ) :
    outputDistance S E o (.node D (fun _ => .done)) (.node D' (fun _ => .done)) Z Z=
      stepDistance S E o D D' Z := by
  change (∑ h : Fin o × Unit, traceNorm (D.branch S E o h.1 Z-D'.branch S E o h.1 Z))/2 = _
  simp [stepDistance,Fintype.sum_prod_type]

theorem outputDistance_common {n : ℕ} (T : Tree S E o n)
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    outputDistance S E o T T X Y≤traceDist X Y := by
  unfold outputDistance traceDist
  simp only [← run_sub]
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using
    div_le_div_of_nonneg_right (tree_contraction S E o T (hX.sub hY)) (by norm_num : 0≤(2:ℝ))

theorem outputDistance_zero {n : ℕ} (T U : Tree S E o n) :
    outputDistance S E o T U 0 0=0 := by
  simp [outputDistance,FiniteInterventionProcess.run_zero]

theorem stepDistance_zero (D D' : Step S E o) : stepDistance S E o D D' 0=0 := by
  simp [stepDistance,Step.branch_zero]


/-- Different trees have different complete laws; this definition keeps both. -/
noncomputable def historyVariation {n : ℕ} (T U : Tree S E o n)
    (X Y : Matrix (S × E) (S × E) ℂ) : ℝ :=
  (∑ h, |weight S E o T h X-weight S E o U h Y|)/2

theorem historyVariation_done {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    historyVariation S E o .done .done X Y=0 := by
  simp [historyVariation,weight,run,hX.2,hY.2]

theorem localError_refl (D : Step S E o) : LocalError S E o D D 0 := by
  refine ⟨le_rfl,fun Z _ => ?_⟩
  simp [stepDistance]

theorem localError_one (D D' : Step S E o) : LocalError S E o D D' 1 := by
  refine ⟨by norm_num,fun Z hZ => ?_⟩
  simpa only [hZ.2,Complex.one_re] using stepDistance_mass S E o D D' hZ.1

theorem outputDistance_one_positive (D D' : Step S E o) {ε : ℝ}
    (hε : LocalError S E o D D' ε) {Z : Matrix (S × E) (S × E) ℂ}
    (hZ : Z.PosSemidef) :
    outputDistance S E o (.node D (fun _ => .done)) (.node D' (fun _ => .done)) Z Z
      ≤ ε*Z.trace.re := by
  rw [outputDistance_one]
  exact localError_positive S E o D D' hε hZ


/-- Concatenation permits unrelated internal Kraus counts. -/
noncomputable def mixKraus {k l : ℕ} (K : Fin k → Matrix ι ι ℂ)
    (L : Fin l → Matrix ι ι ℂ) (p : ℝ) : Fin (k+l) → Matrix ι ι ℂ :=
  Fin.addCases (fun i => Real.sqrt (1-p) • K i) (fun j => Real.sqrt p • L j)

theorem sqrt_action (t : ℝ) (ht : 0≤t) (A X : Matrix ι ι ℂ) :
    (Real.sqrt t • A)*X*(Real.sqrt t • A)ᴴ=t • (A*X*Aᴴ) := by
  simp [Matrix.conjTranspose_smul,smul_smul,mul_assoc,Real.mul_self_sqrt ht]

theorem sqrt_normalization (t : ℝ) (ht : 0≤t) (A : Matrix ι ι ℂ) :
    (Real.sqrt t • A)ᴴ*(Real.sqrt t • A)=t • (Aᴴ*A) := by
  simp [Matrix.conjTranspose_smul,smul_smul,Real.mul_self_sqrt ht]

theorem mixKraus_action {k l : ℕ} (K : Fin k → Matrix ι ι ℂ)
    (L : Fin l → Matrix ι ι ℂ) {p : ℝ} (hp : 0≤p) (hp1 : p≤1)
    (X : Matrix ι ι ℂ) :
    krausMap (mixKraus K L p) X=(1-p) • krausMap K X+p • krausMap L X := by
  simp only [krausMap, mixKraus, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    sqrt_action _ (sub_nonneg.mpr hp1), sqrt_action _ hp, Finset.smul_sum]

theorem mixKraus_normalization {k l : ℕ} (K : Fin k → Matrix ι ι ℂ)
    (L : Fin l → Matrix ι ι ℂ) {p : ℝ} (hp : 0≤p) (hp1 : p≤1) :
    (∑ i, (mixKraus K L p i)ᴴ*mixKraus K L p i)=
      (1-p) • (∑ i, (K i)ᴴ*K i)+p • (∑ j, (L j)ᴴ*L j) := by
  simp only [mixKraus, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    sqrt_normalization _ (sub_nonneg.mpr hp1), sqrt_normalization _ hp, Finset.smul_sum]

theorem mixKraus_channel {k l : ℕ} {K : Fin k → Matrix ι ι ℂ}
    {L : Fin l → Matrix ι ι ℂ} (hK : IsKrausChannel K) (hL : IsKrausChannel L)
    {p : ℝ} (hp : 0≤p) (hp1 : p≤1) : IsKrausChannel (mixKraus K L p) := by
  rw [IsKrausChannel, mixKraus_normalization K L hp hp1, hK, hL, ← add_smul]
  simp

noncomputable def mixInstrument {a : ℕ} (D D' : FiniteInstrument ι a)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) : FiniteInstrument ι a where
  count := D.count+D'.count
  operators b := mixKraus (D.operators b) (D'.operators b) p
  normalized := by
    simp only [mixKraus_normalization _ _ hp hp1, Finset.sum_add_distrib,
      ← Finset.smul_sum,D.normalized,D'.normalized,← add_smul]
    simp

theorem mixInstrument_branch {a : ℕ} (D D' : FiniteInstrument ι a)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (b : Fin a) (X : Matrix ι ι ℂ) :
    (mixInstrument D D' p hp hp1).branch b X=(1-p) • D.branch b X+p • D'.branch b X :=
  mixKraus_action _ _ hp hp1 X


open scoped Kronecker

omit [Fintype ι] [DecidableEq ι] [Fintype E] in
theorem mixKraus_lift {k l : ℕ} (K : Fin k → Matrix ι ι ℂ)
    (L : Fin l → Matrix ι ι ℂ) (p : ℝ) :
    (fun i => mixKraus K L p i ⊗ₖ (1 : Matrix E E ℂ))=
      mixKraus (fun i => K i ⊗ₖ (1 : Matrix E E ℂ))
        (fun j => L j ⊗ₖ (1 : Matrix E E ℂ)) p := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [mixKraus,Matrix.smul_kronecker]

/-- Operator equality on every joint matrix, without a product-state premise. -/
theorem mixInstrument_lift_branch (D D' : FiniteInstrument S o)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (a : Fin o) (Z : Matrix (S × E) (S × E) ℂ) :
    ((mixInstrument D D' p hp hp1).lift E).branch a Z=
      (1-p) • (D.lift E).branch a Z+p • (D'.lift E).branch a Z := by
  change krausMap (fun i => mixKraus (D.operators a) (D'.operators a) p i ⊗ₖ 1) Z= _
  rw [mixKraus_lift E,mixKraus_action _ _ hp hp1]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem mixture_difference (p : ℝ) (A B : Matrix ι ι ℂ) :
    (1-p) • A+p • B-A=(p:ℂ) • (B-A) := by
  ext i j
  simp [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,Complex.real_smul]
  ring

theorem instrument_mass_bound {a : ℕ} (D D' : FiniteInstrument ι a)
    {Z : Matrix ι ι ℂ} (hZ : Z.PosSemidef) :
    (∑ b,traceNorm (D.branch b Z-D'.branch b Z))/2≤Z.trace.re := by
  have hb : (∑ b,traceNorm (D.branch b Z-D'.branch b Z))≤Z.trace.re+Z.trace.re := by
    calc
      _ ≤ ∑ b,((D.branch b Z).trace.re+(D'.branch b Z).trace.re) := by
        apply Finset.sum_le_sum
        intro b _
        simpa only [traceNorm_posSemidef (D.branch_posSemidef b hZ),
          traceNorm_posSemidef (D'.branch_posSemidef b hZ)] using
          traceNorm_sub_le (D.branch b Z) (D'.branch b Z)
      _ = _ := by
        rw [Finset.sum_add_distrib,← Complex.re_sum,← Complex.re_sum,D.sum_trace,D'.sum_trace]
  linarith

theorem mixture_instrument_bound (D D' : FiniteInstrument S o)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) {Z : Matrix (S × E) (S × E) ℂ}
    (hZ : IsDensityOperator Z) :
    (∑ a,traceNorm (((mixInstrument D D' p hp hp1).lift E).branch a Z-
      (D.lift E).branch a Z))/2≤p := by
  simp only [mixInstrument_lift_branch,mixture_difference,traceNorm_smul_nonneg hp]
  rw [← Finset.mul_sum,mul_div_assoc]
  have hb := instrument_mass_bound (D'.lift E) (D.lift E) hZ.1
  rw [hZ.2,Complex.one_re] at hb
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hp

theorem mixture_channel_bound {k l : ℕ} {K : Fin k → Matrix ι ι ℂ}
    {L : Fin l → Matrix ι ι ℂ} (hK : IsKrausChannel K) (hL : IsKrausChannel L)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) {Z : Matrix ι ι ℂ} (hZ : IsDensityOperator Z) :
    traceDist (krausMap (mixKraus K L p) Z) (krausMap K Z)≤p := by
  unfold traceDist
  rw [mixKraus_action K L hp hp1,mixture_difference,traceNorm_smul_nonneg hp]
  have hb := (traceDist_mem_Icc (krausMap_isDensityOperator hL hZ)
    (krausMap_isDensityOperator hK hZ)).2
  unfold traceDist at hb
  nlinarith


noncomputable def realizedStep {k : ℕ} (K : Fin k → Matrix (S × E) (S × E) ℂ)
    (hK : IsKrausChannel K) (D : FiniteInstrument S o) : Step S E o where
  count := k
  evolution := K
  normalized := hK
  instrument := D

theorem stepDistance_triangle (D F G : Step S E o) (Z : Matrix (S × E) (S × E) ℂ) :
    stepDistance S E o D G Z≤stepDistance S E o D F Z+stepDistance S E o F G Z := by
  have hb : (∑ a,traceNorm (D.branch S E o a Z-G.branch S E o a Z))≤
      ∑ a,(traceNorm (D.branch S E o a Z-F.branch S E o a Z)+
        traceNorm (F.branch S E o a Z-G.branch S E o a Z)) := by
    apply Finset.sum_le_sum
    intro a _
    have he : D.branch S E o a Z-G.branch S E o a Z=
      (D.branch S E o a Z-F.branch S E o a Z)+(F.branch S E o a Z-G.branch S E o a Z) := by abel
    rw [he]
    exact traceNorm_triangle _ _
  rw [Finset.sum_add_distrib] at hb
  unfold stepDistance
  linarith

theorem localError_trans (D F G : Step S E o) {η θ : ℝ}
    (hη : LocalError S E o D F η) (hθ : LocalError S E o F G θ) :
    LocalError S E o D G (η+θ) := by
  refine ⟨add_nonneg hη.1 hθ.1,fun Z hZ => ?_⟩
  exact (stepDistance_triangle S E o D F G Z).trans (add_le_add (hη.2 Z hZ) (hθ.2 Z hZ))

theorem evolution_localError {k l : ℕ} (K : Fin k → Matrix (S × E) (S × E) ℂ)
    (L : Fin l → Matrix (S × E) (S × E) ℂ) (hK : IsKrausChannel K) (hL : IsKrausChannel L)
    (D : FiniteInstrument S o) {η : ℝ} (hη : 0≤η)
    (hb : ∀ Z, IsDensityOperator Z → traceDist (krausMap K Z) (krausMap L Z)≤η) :
    LocalError S E o (realizedStep S E o K hK D) (realizedStep S E o L hL D) η := by
  refine ⟨hη,fun Z hZ => ?_⟩
  have hc := instrument_contraction (D.lift E)
    ((krausMap_isHermitian K hZ.1.isHermitian).sub (krausMap_isHermitian L hZ.1.isHermitian))
  have hd := hb Z hZ
  simp only [FiniteInstrument.branch,krausMap_sub] at hc
  change (∑ a,traceNorm (krausMap ((D.lift E).operators a) (krausMap K Z)-
    krausMap ((D.lift E).operators a) (krausMap L Z)))/2≤η
  unfold traceDist at hd
  linarith

theorem instrument_localError {k : ℕ} (K : Fin k → Matrix (S × E) (S × E) ℂ)
    (hK : IsKrausChannel K) (D D' : FiniteInstrument S o) {θ : ℝ} (hθ : 0≤θ)
    (hb : ∀ Z, IsDensityOperator Z →
      (∑ a,traceNorm ((D.lift E).branch a Z-(D'.lift E).branch a Z))/2≤θ) :
    LocalError S E o (realizedStep S E o K hK D) (realizedStep S E o K hK D') θ := by
  exact ⟨hθ,fun Z hZ => hb _ (krausMap_isDensityOperator hK hZ)⟩

/-- Changing both fields uses an actual intermediate step; no two-component
whole-step mixture is asserted for independently mixed fields. -/
theorem both_fields_localError {k l : ℕ} (K : Fin k → Matrix (S × E) (S × E) ℂ)
    (L : Fin l → Matrix (S × E) (S × E) ℂ) (hK : IsKrausChannel K) (hL : IsKrausChannel L)
    (D D' : FiniteInstrument S o) {η θ : ℝ} (hη : 0≤η) (hθ : 0≤θ)
    (he : ∀ Z, IsDensityOperator Z → traceDist (krausMap K Z) (krausMap L Z)≤η)
    (hi : ∀ Z, IsDensityOperator Z →
      (∑ a,traceNorm ((D.lift E).branch a Z-(D'.lift E).branch a Z))/2≤θ) :
    LocalError S E o (realizedStep S E o K hK D) (realizedStep S E o L hL D') (η+θ) :=
  localError_trans S E o _ (realizedStep S E o L hL D) _
    (evolution_localError S E o K L hK hL D hη he)
    (instrument_localError S E o L hL D D' hθ hi)

theorem mixed_evolution_localError {k l : ℕ} (K : Fin k → Matrix (S × E) (S × E) ℂ)
    (L : Fin l → Matrix (S × E) (S × E) ℂ) (hK : IsKrausChannel K) (hL : IsKrausChannel L)
    (D : FiniteInstrument S o) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    LocalError S E o
      (realizedStep S E o (mixKraus K L p) (mixKraus_channel hK hL hp hp1) D)
      (realizedStep S E o K hK D) p :=
  evolution_localError S E o _ _ (mixKraus_channel hK hL hp hp1) hK D hp
    (fun _ hZ => mixture_channel_bound hK hL p hp hp1 hZ)

theorem mixed_instrument_localError {k : ℕ} (K : Fin k → Matrix (S × E) (S × E) ℂ)
    (hK : IsKrausChannel K) (D D' : FiniteInstrument S o)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    LocalError S E o (realizedStep S E o K hK (mixInstrument D D' p hp hp1))
      (realizedStep S E o K hK D) p :=
  instrument_localError S E o K hK _ _ hp (fun _ hZ => mixture_instrument_bound S E o D D' p hp hp1 hZ)


open FiniteMemoryProcess

noncomputable def memoryInput : Matrix Joint Joint ℂ := basisState 1 ⊗ₖ basisState 0
noncomputable def swapPrepare : Step Qubit Qubit 2 :=
  realizedStep Qubit Qubit 2 swapKraus swapKraus_normalized (FiniteInstrument.prepare 0)
noncomputable def identityPrepare : Step Qubit Qubit 2 :=
  localStep Qubit Qubit 2 (FiniteInstrument.prepare 0)
noncomputable def memorySwapTree : Tree Qubit Qubit 2 1 := .node swapPrepare (fun _ => .done)
noncomputable def memoryIdentityTree : Tree Qubit Qubit 2 1 := .node identityPrepare (fun _ => .done)

theorem memoryInput_density : IsDensityOperator memoryInput := basisJoint_density 1 0

theorem lifted_prepare_zero_reset (X : Matrix Joint Joint ℂ) :
    ((FiniteInstrument.prepare 0).lift Qubit).branch 0 X=resetSystem X := by
  have hk : (FiniteInstrument.prepare 0).operators 0=resetKraus := by
    funext k
    ext i j
    simp [FiniteInstrument.prepare,resetKraus,Matrix.single,eq_comm]
  change krausMap (fun k => (FiniteInstrument.prepare 0).operators 0 k ⊗ₖ 1) X= _
  rw [hk]
  rfl

/-- SWAP stores the original system bit in E before the system is prepared as zero. -/
theorem memory_swap_branch (a : Qubit) :
    swapPrepare.branch Qubit Qubit 2 a memoryInput=
      if a=0 then basisState 0 ⊗ₖ basisState 1 else 0 := by
  by_cases ha : a=0
  · subst a
    change ((FiniteInstrument.prepare 0).lift Qubit).branch 0 (swapJoint memoryInput)= _
    rw [lifted_prepare_zero_reset]
    simp only [memoryInput,swapJoint_basis,resetSystem_basis,ite_true]
  · change ((FiniteInstrument.prepare 0).lift Qubit).branch a (swapJoint memoryInput)= _
    rw [FiniteInstrument.lift_prepare_other Qubit 0 a ha,if_neg ha]

theorem memory_identity_branch (a : Qubit) :
    identityPrepare.branch Qubit Qubit 2 a memoryInput=
      if a=0 then basisState 0 ⊗ₖ basisState 0 else 0 := by
  rw [identityPrepare,localStep_branch]
  by_cases ha : a=0
  · subst a
    rw [lifted_prepare_zero_reset]
    simp only [memoryInput,resetSystem_basis,ite_true]
  · rw [FiniteInstrument.lift_prepare_other Qubit 0 a ha,if_neg ha]

theorem memory_swap_run (a : Qubit) :
    run Qubit Qubit 2 memorySwapTree (a,()) memoryInput=
      if a=0 then basisState 0 ⊗ₖ basisState 1 else 0 := memory_swap_branch a

theorem memory_identity_run (a : Qubit) :
    run Qubit Qubit 2 memoryIdentityTree (a,()) memoryInput=
      if a=0 then basisState 0 ⊗ₖ basisState 0 else 0 := memory_identity_branch a

theorem memory_weights (a : Qubit) :
    weight Qubit Qubit 2 memorySwapTree (a,()) memoryInput=(if a=0 then 1 else 0) ∧
    weight Qubit Qubit 2 memoryIdentityTree (a,()) memoryInput=(if a=0 then 1 else 0) := by
  simp only [weight,memory_swap_run,memory_identity_run]
  split_ifs <;> simp [(basisJoint_density 0 1).2,(basisJoint_density 0 0).2]

theorem memory_historyVariation_zero :
    historyVariation Qubit Qubit 2 memorySwapTree memoryIdentityTree memoryInput memoryInput=0 := by
  have he : ∀ h : History 2 1, weight Qubit Qubit 2 memorySwapTree h memoryInput=
      weight Qubit Qubit 2 memoryIdentityTree h memoryInput := by
    rintro ⟨a,u⟩
    cases u
    exact (memory_weights a).1.trans (memory_weights a).2.symm
  simp only [historyVariation,he,sub_self,abs_zero,Finset.sum_const_zero,zero_div]

theorem basis_one_zero_distance : traceDist (basisState 1) (basisState 0)=1 := by
  have h1 : basisState 1=binaryDiagonalState 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [basisState,binaryDiagonalState]
  have h0 : basisState 0=binaryDiagonalState 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [basisState,binaryDiagonalState]
  rw [h1,h0,binaryDiagonalState_traceDist]
  norm_num

theorem memory_outputDistance_one :
    outputDistance Qubit Qubit 2 memorySwapTree memoryIdentityTree memoryInput memoryInput=1 := by
  rw [memorySwapTree,memoryIdentityTree,outputDistance_one]
  unfold stepDistance
  simp only [memory_swap_branch,memory_identity_branch,Fin.sum_univ_two]
  norm_num only [ite_true,Fin.one_eq_zero_iff,OfNat.ofNat_ne_zero,ite_false,
    sub_zero,sub_self,traceNorm_zero,add_zero]
  have hd := FiniteAdaptiveProcessRobustness.traceDist_tensor_left (basisState_density 0)
    (basisState 1) (basisState 0)
  rw [basis_one_zero_distance] at hd
  unfold traceDist at hd
  linarith

theorem memory_local_bound_attained :
    LocalError Qubit Qubit 2 swapPrepare identityPrepare 1 ∧
      stepDistance Qubit Qubit 2 swapPrepare identityPrepare memoryInput=1 := by
  refine ⟨localError_one Qubit Qubit 2 _ _,?_⟩
  simpa only [memorySwapTree,memoryIdentityTree,outputDistance_one] using memory_outputDistance_one


/-- Independent evolution and instrument noise is bounded through the actual
intermediate step, including the cross terms in their composite action. -/
theorem mixed_both_localError {k l : ℕ} (K : Fin k → Matrix (S × E) (S × E) ℂ)
    (L : Fin l → Matrix (S × E) (S × E) ℂ) (hK : IsKrausChannel K) (hL : IsKrausChannel L)
    (D D' : FiniteInstrument S o) (p q : ℝ) (hp : 0≤p) (hp1 : p≤1)
    (hq : 0≤q) (hq1 : q≤1) :
    LocalError S E o
      (realizedStep S E o (mixKraus K L p) (mixKraus_channel hK hL hp hp1)
        (mixInstrument D D' q hq hq1))
      (realizedStep S E o K hK D) (p+q) :=
  both_fields_localError S E o _ K (mixKraus_channel hK hL hp hp1) hK
    (mixInstrument D D' q hq hq1) D hp hq
    (fun _ hZ => mixture_channel_bound hK hL p hp hp1 hZ)
    (fun _ hZ => mixture_instrument_bound S E o D D' q hq hq1 hZ)

/-- Each depth has one bound, required at every pair of actual continuations. -/
inductive PairedErrors : {n : ℕ} → Tree S E o n → Tree S E o n → List ℝ → Prop
  | done : PairedErrors .done .done []
  | node {n : ℕ} {D D' : Step S E o} {F G : Fin o → Tree S E o n}
      {ε : ℝ} {es : List ℝ} (hl : LocalError S E o D D' ε)
      (length : es.length = n) (next : ∀ a, PairedErrors (F a) (G a) es) :
      PairedErrors (.node D F) (.node D' G) (ε :: es)

theorem pairedErrors_length {n : ℕ} {T U : Tree S E o n} {es : List ℝ}
    (h : PairedErrors S E o T U es) : es.length=n := by
  cases h with
  | done => rfl
  | node hl hlen hn => simpa using congrArg Nat.succ hlen

theorem outputDistance_triangle {n : ℕ} (T U V : Tree S E o n)
    (X Y Z : Matrix (S × E) (S × E) ℂ) :
    outputDistance S E o T V X Z ≤
      outputDistance S E o T U X Y + outputDistance S E o U V Y Z := by
  unfold outputDistance
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro h _
  convert traceNorm_triangle (run S E o T h X-run S E o U h Y)
    (run S E o U h Y-run S E o V h Z) using 1 <;> (congr 1 <;> abel)

theorem outputDistance_node {n : ℕ} (D D' : Step S E o)
    (F G : Fin o → Tree S E o n) (X Y : Matrix (S × E) (S × E) ℂ) :
    outputDistance S E o (.node D F) (.node D' G) X Y =
      ∑ a, outputDistance S E o (F a) (G a) (D.branch S E o a X) (D'.branch S E o a Y) := by
  change (∑ h : Fin o × History o n, _) / 2 = _
  simp only [run, Fintype.sum_prod_type, outputDistance, Finset.sum_div]

theorem pairedErrors_positive {n : ℕ} {T U : Tree S E o n} {es : List ℝ}
    (h : PairedErrors S E o T U es) {Z : Matrix (S × E) (S × E) ℂ}
    (hZ : Z.PosSemidef) : outputDistance S E o T U Z Z ≤ es.sum*Z.trace.re := by
  induction h generalizing Z with
  | done => simp [outputDistance_done,traceDist_self]
  | @node n D D' F G ε es hl hlen hn ih =>
    rw [outputDistance_node]
    calc
      _ ≤ ∑ a, (es.sum*(D.branch S E o a Z).trace.re +
          traceDist (D.branch S E o a Z) (D'.branch S E o a Z)) := by
        apply Finset.sum_le_sum
        intro a _
        exact (outputDistance_triangle S E o (F a) (G a) (G a) _ _ _).trans
          (add_le_add (ih a (D.branch_posSemidef S E o a hZ))
            (outputDistance_common S E o (G a)
              (D.branch_posSemidef S E o a hZ).isHermitian
              (D'.branch_posSemidef S E o a hZ).isHermitian))
      _ = es.sum*Z.trace.re + stepDistance S E o D D' Z := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.re_sum, D.sum_trace S E o]
        simp only [stepDistance,traceDist, ← Finset.mul_sum]
        ring
      _ ≤ _ := by
        have hb := localError_positive S E o D D' hl hZ
        simp only [List.sum_cons]
        nlinarith

theorem outputDistance_mass {n : ℕ} (T U : Tree S E o n)
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    outputDistance S E o T U X Y ≤ (X.trace.re+Y.trace.re)/2 := by
  unfold outputDistance
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ h, ((run S E o T h X).trace.re + (run S E o U h Y).trace.re) := by
      apply Finset.sum_le_sum
      intro h _
      simpa only [traceNorm_posSemidef (run_posSemidef S E o T h hX),
        traceNorm_posSemidef (run_posSemidef S E o U h hY)] using
        traceNorm_sub_le (run S E o T h X) (run S E o U h Y)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Complex.re_sum, ← Complex.re_sum, sum_trace, sum_trace]

theorem pairedErrors_changed_input {n : ℕ} {T U : Tree S E o n} {es : List ℝ}
    (h : PairedErrors S E o T U es) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance S E o T U X Y ≤ traceDist X Y + es.sum := by
  have hp := pairedErrors_positive S E o h hX.1
  rw [hX.2, Complex.one_re, mul_one] at hp
  exact (outputDistance_triangle S E o T U U X X Y).trans
    (by simpa only [add_comm] using (add_le_add hp
      (outputDistance_common S E o U hX.1.isHermitian hY.1.isHermitian)))

theorem pairedErrors_capped {n : ℕ} {T U : Tree S E o n} {es : List ℝ}
    (h : PairedErrors S E o T U es) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance S E o T U X Y ≤ min 1 (traceDist X Y + es.sum) := by
  refine le_min ?_ (pairedErrors_changed_input S E o h hX hY)
  simpa [hX.2,hY.2] using outputDistance_mass S E o T U hX.1 hY.1

theorem historyVariation_le_outputDistance {n : ℕ} (T U : Tree S E o n)
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    historyVariation S E o T U X Y ≤ outputDistance S E o T U X Y := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro h _
  simpa only [weight,Matrix.trace_sub,Complex.sub_re] using
    traceNorm_ge_abs_re_trace ((run_hermitian S E o T h hX).sub (run_hermitian S E o U h hY))

/-- A spectator identity acts on the actual tensor branch, not on a marginal. -/
theorem lift_branch_tensor (D : FiniteInstrument ι o) (a : Fin o)
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) [DecidableEq κ] :
    (D.lift κ).branch a (X ⊗ₖ Y) = D.branch a X ⊗ₖ Y := by
  simp only [FiniteInstrument.branch,FiniteInstrument.lift,krausMap,
    Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]
  ext ⟨i,e⟩ ⟨j,f⟩
  simp only [Matrix.sum_apply,Matrix.kronecker_apply,Finset.sum_mul]
  rfl

theorem prepare_basis (b a c : Qubit) :
    (FiniteInstrument.prepare b).branch a (basisState c) =
      if a=b then basisState b else 0 := by
  simp only [FiniteInstrument.branch,FiniteInstrument.prepare]
  fin_cases b <;> fin_cases a <;> fin_cases c <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [FiniteInstrument.branch,FiniteInstrument.prepare,krausMap,basisState,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.single,Fin.sum_univ_two]

theorem computational_basis (a c : Qubit) :
    FiniteInstrument.computational.branch a (basisState c) =
      if a=c then basisState c else 0 := by
  simp only [FiniteInstrument.branch,FiniteInstrument.computational]
  fin_cases a <;> fin_cases c <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [FiniteInstrument.branch,FiniteInstrument.computational,krausMap,basisState,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]

noncomputable def correlatedInput : Matrix Joint Joint ℂ :=
  (1/2:ℂ) • (basisState 0 ⊗ₖ basisState 0) + (1/2:ℂ) • (basisState 1 ⊗ₖ basisState 1)

theorem correlatedInput_density : IsDensityOperator correlatedInput := by
  refine ⟨((basisJoint_density 0 0).1.smul (by norm_num [Complex.le_def] : (0:ℂ)≤1/2)).add
    ((basisJoint_density 1 1).1.smul (by norm_num [Complex.le_def] : (0:ℂ)≤1/2)),?_⟩
  simp only [correlatedInput,Matrix.trace_add,Matrix.trace_smul,
    (basisJoint_density 0 0).2,(basisJoint_density 1 1).2,smul_eq_mul]
  norm_num

noncomputable def readStep : Step Qubit Qubit 2 := localStep Qubit Qubit 2 FiniteInstrument.computational
noncomputable def idealStep (a : Qubit) : Step Qubit Qubit 2 :=
  localStep Qubit Qubit 2 (FiniteInstrument.prepare a)
noncomputable def noisyStep (a : Qubit) : Step Qubit Qubit 2 :=
  localStep Qubit Qubit 2 (mixInstrument (FiniteInstrument.prepare a)
    (FiniteInstrument.prepare (1-a)) (1/4) (by norm_num) (by norm_num))
noncomputable def idealTwo : Tree Qubit Qubit 2 3 :=
  .node readStep (fun a => .node (idealStep a) (fun b => .node (idealStep b) (fun _ => .done)))
noncomputable def noisyTwo : Tree Qubit Qubit 2 3 :=
  .node readStep (fun a => .node (noisyStep a) (fun b => .node (noisyStep b) (fun _ => .done)))

theorem readStep_correlated (a : Qubit) :
    readStep.branch Qubit Qubit 2 a correlatedInput = (1/2:ℂ) • (basisState a ⊗ₖ basisState a) := by
  rw [readStep,correlatedInput,Step.branch_add,Step.branch_smul,Step.branch_smul]
  simp only [localStep_branch,lift_branch_tensor,computational_basis]
  fin_cases a <;> simp

theorem idealStep_basis (a b c e : Qubit) :
    (idealStep a).branch Qubit Qubit 2 b (basisState c ⊗ₖ basisState e) =
      if b=a then basisState b ⊗ₖ basisState e else 0 := by
  simp only [idealStep,localStep_branch,lift_branch_tensor,prepare_basis]
  split_ifs with h
  · subst b; rfl
  · simp

theorem noisyStep_basis (a b c e : Qubit) :
    (noisyStep a).branch Qubit Qubit 2 b (basisState c ⊗ₖ basisState e) =
      (if b=a then (3/4:ℂ) else (1/4:ℂ)) • (basisState b ⊗ₖ basisState e) := by
  rw [noisyStep,localStep_branch,mixInstrument_lift_branch]
  simp only [lift_branch_tensor,prepare_basis]
  fin_cases a <;> fin_cases b <;> norm_num <;> ext i j <;> norm_num [Complex.real_smul]

/-- The terminal system is the last observed bit; the environment retains the first. -/
theorem noisyTwo_run (a b c : Qubit) :
    run Qubit Qubit 2 noisyTwo (a,b,c,()) correlatedInput =
      ((1/2:ℂ)*(if b=a then 3/4 else 1/4)*(if c=b then 3/4 else 1/4)) •
        (basisState c ⊗ₖ basisState a) := by
  simp only [noisyTwo,run,readStep_correlated,Step.branch_smul,noisyStep_basis,smul_smul]

theorem idealTwo_run (a b c : Qubit) :
    run Qubit Qubit 2 idealTwo (a,b,c,()) correlatedInput =
      if b=a ∧ c=b then (1/2:ℂ) • (basisState c ⊗ₖ basisState a) else 0 := by
  simp only [idealTwo,run,readStep_correlated,Step.branch_smul,idealStep_basis]
  by_cases hb : b=a <;> by_cases hc : c=b <;>
    simp [hb,hc,Step.branch_zero,idealStep_basis]

noncomputable def tableWeight (a b c : Qubit) : ℝ :=
  if b=a then (if c=b then 9/32 else 3/32) else (if c=b then 3/32 else 1/32)

theorem noisyTwo_matrix_table (a b c : Qubit) :
    run Qubit Qubit 2 noisyTwo (a,b,c,()) correlatedInput =
      (tableWeight a b c:ℂ) • (basisState c ⊗ₖ basisState a) := by
  rw [noisyTwo_run]
  unfold tableWeight
  split_ifs <;> norm_num

theorem noisyTwo_weight_table (a b c : Qubit) :
    weight Qubit Qubit 2 noisyTwo (a,b,c,()) correlatedInput = tableWeight a b c := by
  simp only [weight,noisyTwo_matrix_table,Matrix.trace_smul,(basisJoint_density c a).2,
    smul_eq_mul,mul_one,Complex.ofReal_re]

theorem idealTwo_weight_table (a b c : Qubit) :
    weight Qubit Qubit 2 idealTwo (a,b,c,()) correlatedInput = if b=a ∧ c=b then 1/2 else 0 := by
  simp only [weight,idealTwo_run]
  split_ifs <;> simp [Matrix.trace_smul,(basisJoint_density c a).2]

theorem noisyTwo_every_history_positive (a b c : Qubit) :
    0 < weight Qubit Qubit 2 noisyTwo (a,b,c,()) correlatedInput := by
  rw [noisyTwo_weight_table]
  unfold tableWeight
  split_ifs <;> norm_num

theorem noisyStep_localError (a : Qubit) :
    LocalError Qubit Qubit 2 (noisyStep a) (idealStep a) (1/4) := by
  exact mixed_instrument_localError Qubit Qubit 2 (fun _ : Fin 1 => 1)
    (by simp [IsKrausChannel]) (FiniteInstrument.prepare a) (FiniteInstrument.prepare (1-a))
    (1/4) (by norm_num) (by norm_num)

theorem noisyTwo_pairedErrors :
    PairedErrors Qubit Qubit 2 noisyTwo idealTwo [0,1/4,1/4] := by
  refine .node (localError_refl Qubit Qubit 2 readStep) rfl (fun a => ?_)
  refine .node (noisyStep_localError a) rfl (fun b => ?_)
  exact .node (noisyStep_localError b) rfl (fun _ => .done)

theorem density_ray_norm {A : Matrix ι ι ℂ} (hA : IsDensityOperator A) (r : ℝ) :
    traceNorm ((r:ℂ) • A) = |r| := by
  have hn : traceNorm A=1 := by rw [traceNorm_posSemidef hA.1,hA.2]; rfl
  by_cases hr : 0≤r
  · rw [traceNorm_smul_nonneg hr,hn,mul_one,abs_of_nonneg hr]
  · have hnr : 0≤-r := by linarith
    have he : (r:ℂ) • A = - ((-r:ℝ):ℂ) • A := by simp
    rw [he,neg_smul,traceNorm_neg,traceNorm_smul_nonneg hnr,hn,mul_one,abs_of_neg (lt_of_not_ge hr)]

theorem noisyTwo_branch_norm (a b c : Qubit) :
    traceNorm (run Qubit Qubit 2 noisyTwo (a,b,c,()) correlatedInput -
      run Qubit Qubit 2 idealTwo (a,b,c,()) correlatedInput) =
      |tableWeight a b c - (if b=a ∧ c=b then 1/2 else 0)| := by
  rw [noisyTwo_matrix_table,idealTwo_run]
  split_ifs with h
  · rw [← sub_smul]
    convert density_ray_norm (basisJoint_density c a) (tableWeight a b c - 1/2) using 1
    push_cast
    rfl
  · simp only [sub_zero]
    exact density_ray_norm (basisJoint_density c a) (tableWeight a b c)

theorem noisyTwo_outputDistance :
    outputDistance Qubit Qubit 2 noisyTwo idealTwo correlatedInput correlatedInput = 7/16 := by
  have hh : ∀ h : History 2 3,
      traceNorm (run Qubit Qubit 2 noisyTwo h correlatedInput -
        run Qubit Qubit 2 idealTwo h correlatedInput) =
        |tableWeight h.1 h.2.1 h.2.2.1 - (if h.2.1=h.1 ∧ h.2.2.1=h.2.1 then 1/2 else 0)| := by
    rintro ⟨a,b,c,u⟩
    cases u
    exact noisyTwo_branch_norm a b c
  simp only [outputDistance,hh]
  change (∑ h : Qubit × Qubit × Qubit × Unit, _) / 2 = _
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_two,Fintype.sum_unique,tableWeight]

theorem noisyTwo_historyVariation :
    historyVariation Qubit Qubit 2 noisyTwo idealTwo correlatedInput correlatedInput = 7/16 := by
  have hh : ∀ h : History 2 3,
      |weight Qubit Qubit 2 noisyTwo h correlatedInput -
        weight Qubit Qubit 2 idealTwo h correlatedInput| =
        |tableWeight h.1 h.2.1 h.2.2.1 - (if h.2.1=h.1 ∧ h.2.2.1=h.2.1 then 1/2 else 0)| := by
    rintro ⟨a,b,c,u⟩
    cases u
    rw [noisyTwo_weight_table,idealTwo_weight_table]
  simp only [historyVariation,hh]
  change (∑ h : Qubit × Qubit × Qubit × Unit, _) / 2 = _
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_two,Fintype.sum_unique,tableWeight]

theorem noisyTwo_exceeds_one_step :
    (1/4:ℝ) < historyVariation Qubit Qubit 2 noisyTwo idealTwo correlatedInput correlatedInput := by
  rw [noisyTwo_historyVariation]
  norm_num

theorem noisyTwo_telescope_consumer :
    outputDistance Qubit Qubit 2 noisyTwo idealTwo correlatedInput correlatedInput ≤ 1/2 := by
  have h := pairedErrors_capped Qubit Qubit 2 noisyTwo_pairedErrors
    correlatedInput_density correlatedInput_density
  norm_num [traceDist_self] at h ⊢
  exact h

/-- Lexicographic order 000,001,010,011,100,101,110,111; all eight actual histories. -/
theorem noisyTwo_full_weight_table :
    [weight Qubit Qubit 2 noisyTwo (0,0,0,()) correlatedInput,
     weight Qubit Qubit 2 noisyTwo (0,0,1,()) correlatedInput,
     weight Qubit Qubit 2 noisyTwo (0,1,0,()) correlatedInput,
     weight Qubit Qubit 2 noisyTwo (0,1,1,()) correlatedInput,
     weight Qubit Qubit 2 noisyTwo (1,0,0,()) correlatedInput,
     weight Qubit Qubit 2 noisyTwo (1,0,1,()) correlatedInput,
     weight Qubit Qubit 2 noisyTwo (1,1,0,()) correlatedInput,
     weight Qubit Qubit 2 noisyTwo (1,1,1,()) correlatedInput] =
    [9/32,3/32,1/32,3/32,3/32,1/32,3/32,9/32] := by
  norm_num [noisyTwo_weight_table,tableWeight]

theorem idealTwo_impossible (a b c : Qubit) (h : ¬ (b=a ∧ c=b)) :
    run Qubit Qubit 2 idealTwo (a,b,c,()) correlatedInput=0 ∧
      0 < weight Qubit Qubit 2 noisyTwo (a,b,c,()) correlatedInput := by
  exact ⟨by rw [idealTwo_run,if_neg h],noisyTwo_every_history_positive a b c⟩

theorem noisyTwo_first_marginal (a : Qubit) :
    (∑ b : Qubit, ∑ c : Qubit,
      weight Qubit Qubit 2 noisyTwo (a,b,c,()) correlatedInput)=1/2 := by
  simp only [noisyTwo_weight_table]
  fin_cases a <;> norm_num [Fin.sum_univ_two,tableWeight]

/-- Forget only the classical history, retaining the full terminal quantum state. -/
noncomputable def terminalState {n : ℕ} (T : Tree S E o n)
    (X : Matrix (S × E) (S × E) ℂ) := ∑ h, run S E o T h X

theorem terminalState_density {n : ℕ} (T : Tree S E o n)
    {X : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) :
    IsDensityOperator (terminalState S E o T X) := by
  refine ⟨Matrix.posSemidef_sum _ (fun h _ => run_posSemidef S E o T h hX.1),?_⟩
  simpa only [terminalState,Matrix.trace_sum,sum_trace] using hX.2

theorem terminalState_distance {n : ℕ} (T U : Tree S E o n)
    (X Y : Matrix (S × E) (S × E) ℂ) :
    traceDist (terminalState S E o T X) (terminalState S E o U Y) ≤
      outputDistance S E o T U X Y := by
  unfold terminalState traceDist outputDistance
  rw [← Finset.sum_sub_distrib]
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using
    mul_le_mul_of_nonneg_left (traceNorm_sum_le Finset.univ
      (fun h => run S E o T h X-run S E o U h Y)) (by norm_num : (0:ℝ)≤1/2)

theorem pairedErrors_history_capped {n : ℕ} {T U : Tree S E o n} {es : List ℝ}
    (h : PairedErrors S E o T U es) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    historyVariation S E o T U X Y ≤ min 1 (traceDist X Y+es.sum) :=
  (historyVariation_le_outputDistance S E o T U hX.1.isHermitian hY.1.isHermitian).trans
    (pairedErrors_capped S E o h hX hY)

theorem pairedErrors_terminal_capped {n : ℕ} {T U : Tree S E o n} {es : List ℝ}
    (h : PairedErrors S E o T U es) {X Y : Matrix (S × E) (S × E) ℂ}
    (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    traceDist (terminalState S E o T X) (terminalState S E o U Y) ≤
      min 1 (traceDist X Y+es.sum) :=
  (terminalState_distance S E o T U X Y).trans (pairedErrors_capped S E o h hX hY)

noncomputable def noisyStepAt (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (a : Qubit) : Step Qubit Qubit 2 :=
  localStep Qubit Qubit 2 (mixInstrument (FiniteInstrument.prepare a)
    (FiniteInstrument.prepare (1-a)) p hp hp1)

noncomputable def noisySuffix (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    (m : ℕ) → Qubit → Tree Qubit Qubit 2 m
  | 0, _ => .done
  | m+1, a => .node (noisyStepAt p hp hp1 a) (fun b => noisySuffix p hp hp1 m b)

noncomputable def idealSuffix : (m : ℕ) → Qubit → Tree Qubit Qubit 2 m
  | 0, _ => .done
  | m+1, a => .node (idealStep a) (fun b => idealSuffix m b)

noncomputable def noisyFeedback (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    Tree Qubit Qubit 2 (m+1) := .node readStep (noisySuffix p hp hp1 m)
noncomputable def idealFeedback (m : ℕ) : Tree Qubit Qubit 2 (m+1) :=
  .node readStep (idealSuffix m)

noncomputable def transition (p : ℝ) (a b : Qubit) : ℝ := if b=a then 1-p else p
noncomputable def pathWeight (p : ℝ) : {m : ℕ} → Qubit → History 2 m → ℝ
  | 0, _, _ => 1
  | _+1, a, (b,h) => transition p a b * pathWeight p b h

def lastBit : {m : ℕ} → Qubit → History 2 m → Qubit
  | 0, a, _ => a
  | _+1, _, (b,h) => lastBit b h

def constantHistory (a : Qubit) : (m : ℕ) → History 2 m
  | 0 => ()
  | m+1 => (a,constantHistory a m)

theorem noisyStepAt_basis (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (a b c e : Qubit) :
    (noisyStepAt p hp hp1 a).branch Qubit Qubit 2 b (basisState c ⊗ₖ basisState e) =
      (transition p a b:ℂ) • (basisState b ⊗ₖ basisState e) := by
  rw [noisyStepAt,localStep_branch,mixInstrument_lift_branch]
  simp only [lift_branch_tensor,prepare_basis,transition]
  fin_cases a <;> fin_cases b <;> simp <;> ext i j <;> simp [Complex.real_smul]

theorem noisySuffix_run (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) (a e : Qubit)
    (h : History 2 m) :
    run Qubit Qubit 2 (noisySuffix p hp hp1 m a) h (basisState a ⊗ₖ basisState e) =
      (pathWeight p a h:ℂ) • (basisState (lastBit a h) ⊗ₖ basisState e) := by
  induction m generalizing a with
  | zero => simp [noisySuffix,run,pathWeight,lastBit]
  | succ m ih =>
    rcases h with ⟨b,h⟩
    simp only [noisySuffix,run,noisyStepAt_basis,run_smul,ih,pathWeight,lastBit,
      Complex.ofReal_mul,smul_smul]

theorem pathWeight_nonneg (p : ℝ) (hp : 0≤p) (hp1 : p≤1) {m : ℕ} (a : Qubit)
    (h : History 2 m) : 0≤pathWeight p a h := by
  induction m generalizing a with
  | zero => simp [pathWeight]
  | succ m ih =>
    rcases h with ⟨b,h⟩
    exact mul_nonneg (by unfold transition; split_ifs <;> linarith) (ih b h)

theorem pathWeight_constant (p : ℝ) (m : ℕ) (a : Qubit) :
    pathWeight p a (constantHistory a m)=(1-p)^m := by
  induction m with
  | zero => simp [pathWeight]
  | succ m ih => simp [pathWeight,constantHistory,transition,ih,pow_succ,mul_comm]

theorem lastBit_constant (m : ℕ) (a : Qubit) : lastBit a (constantHistory a m)=a := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih

local instance historyDecidableEq : (m : ℕ) → DecidableEq (History 2 m)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | m+1 => @instDecidableEqProd _ _ inferInstance (historyDecidableEq m)

theorem idealSuffix_run (m : ℕ) (a e : Qubit) (h : History 2 m) :
    run Qubit Qubit 2 (idealSuffix m a) h (basisState a ⊗ₖ basisState e) =
      if h=constantHistory a m then basisState (lastBit a h) ⊗ₖ basisState e else 0 := by
  classical
  induction m generalizing a with
  | zero => cases h; simp [idealSuffix,run,lastBit,constantHistory]
  | succ m ih =>
    rcases h with ⟨b,h⟩
    change run Qubit Qubit 2 (idealSuffix m b) h
      ((idealStep a).branch Qubit Qubit 2 b (basisState a ⊗ₖ basisState e)) =
      if (b,h)=(a,constantHistory a m) then basisState (lastBit b h) ⊗ₖ basisState e else 0
    rw [idealStep_basis]
    simp only [Prod.mk.injEq]
    by_cases hb : b=a
    · subst b
      simpa only [ite_true,true_and] using ih a h
    · simp [hb,run_zero]

theorem noisySuffix_weight (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) (a e : Qubit)
    (h : History 2 m) :
    weight Qubit Qubit 2 (noisySuffix p hp hp1 m a) h (basisState a ⊗ₖ basisState e) =
      pathWeight p a h := by
  simp only [weight,noisySuffix_run,Matrix.trace_smul,(basisJoint_density (lastBit a h) e).2,
    smul_eq_mul,mul_one,Complex.ofReal_re]

theorem pathWeight_sum (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) (a : Qubit) :
    (∑ h : History 2 m, pathWeight p a h)=1 := by
  have ht := sum_weight Qubit Qubit 2 (noisySuffix p hp hp1 m a)
    (basisState a ⊗ₖ basisState 0)
  simpa only [noisySuffix_weight,(basisJoint_density a 0).2,Complex.one_re] using ht

/-- Exact distance from a normalized finite law to a point mass. -/
theorem point_law_variation {α : Type*} [Fintype α] [DecidableEq α]
    (q : α → ℝ) (hq : ∀ x,0≤q x) (hs : ∑ x,q x=1) (a : α) :
    (∑ x, |q x-(if x=a then 1 else 0)|)/2 = 1-q a := by
  have ha : q a≤1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun x _ => hq x) (Finset.mem_univ a)
  have hh : ∀ x, |q x-(if x=a then 1 else 0)| = q x + (if x=a then 1-2*q a else 0) := by
    intro x
    by_cases hx : x=a
    · subst x
      simp only [ite_true]
      rw [abs_of_nonpos (by linarith)]
      ring
    · simp [hx,abs_of_nonneg (hq x)]
  simp only [hh,Finset.sum_add_distrib,hs]
  simp
  ring

theorem noisySuffix_branch_norm (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    (a e : Qubit) (h : History 2 m) :
    traceNorm (run Qubit Qubit 2 (noisySuffix p hp hp1 m a) h (basisState a ⊗ₖ basisState e) -
      run Qubit Qubit 2 (idealSuffix m a) h (basisState a ⊗ₖ basisState e)) =
      |pathWeight p a h-(if h=constantHistory a m then 1 else 0)| := by
  classical
  rw [noisySuffix_run,idealSuffix_run]
  split_ifs
  · have he : (pathWeight p a h:ℂ) • (basisState (lastBit a h) ⊗ₖ basisState e) -
        (basisState (lastBit a h) ⊗ₖ basisState e) =
        ((pathWeight p a h-1:ℝ):ℂ) • (basisState (lastBit a h) ⊗ₖ basisState e) := by
      push_cast
      module
    rw [he]
    exact density_ray_norm (basisJoint_density (lastBit a h) e) (pathWeight p a h-1)
  · simpa only [sub_zero] using density_ray_norm (basisJoint_density (lastBit a h) e) (pathWeight p a h)

theorem noisySuffix_outputDistance (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) (a e : Qubit) :
    outputDistance Qubit Qubit 2 (noisySuffix p hp hp1 m a) (idealSuffix m a)
      (basisState a ⊗ₖ basisState e) (basisState a ⊗ₖ basisState e) = 1-(1-p)^m := by
  classical
  simp only [outputDistance,noisySuffix_branch_norm]
  rw [point_law_variation _ (pathWeight_nonneg p hp hp1 a) (pathWeight_sum p hp hp1 m a),
    pathWeight_constant]

theorem idealSuffix_weight (m : ℕ) (a e : Qubit) (h : History 2 m) :
    weight Qubit Qubit 2 (idealSuffix m a) h (basisState a ⊗ₖ basisState e) =
      if h=constantHistory a m then 1 else 0 := by
  rw [weight,idealSuffix_run]
  split_ifs <;> simp [(basisJoint_density (lastBit a h) e).2]

theorem noisySuffix_historyVariation (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) (a e : Qubit) :
    historyVariation Qubit Qubit 2 (noisySuffix p hp hp1 m a) (idealSuffix m a)
      (basisState a ⊗ₖ basisState e) (basisState a ⊗ₖ basisState e) = 1-(1-p)^m := by
  simp only [historyVariation,noisySuffix_weight,idealSuffix_weight]
  rw [point_law_variation _ (pathWeight_nonneg p hp hp1 a) (pathWeight_sum p hp hp1 m a),
    pathWeight_constant]

theorem outputDistance_smul {n : ℕ} (T U : Tree S E o n)
    (X Y : Matrix (S × E) (S × E) ℂ) {c : ℝ} (hc : 0≤c) :
    outputDistance S E o T U ((c:ℂ) • X) ((c:ℂ) • Y) = c*outputDistance S E o T U X Y := by
  simp only [outputDistance,run_smul,← smul_sub,traceNorm_smul_nonneg hc]
  rw [← Finset.mul_sum]
  ring

theorem historyVariation_smul {n : ℕ} (T U : Tree S E o n)
    (X Y : Matrix (S × E) (S × E) ℂ) {c : ℝ} (hc : 0≤c) :
    historyVariation S E o T U ((c:ℂ) • X) ((c:ℂ) • Y) = c*historyVariation S E o T U X Y := by
  simp only [historyVariation,weight,run_smul,Matrix.trace_smul,smul_eq_mul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    ← mul_sub,abs_mul,abs_of_nonneg hc]
  rw [← Finset.mul_sum]
  ring

theorem historyVariation_node {n : ℕ} (D D' : Step S E o)
    (F G : Fin o → Tree S E o n) (X Y : Matrix (S × E) (S × E) ℂ) :
    historyVariation S E o (.node D F) (.node D' G) X Y =
      ∑ a, historyVariation S E o (F a) (G a) (D.branch S E o a X) (D'.branch S E o a Y) := by
  change (∑ h : Fin o × History o n, _) / 2 = _
  simp only [weight,run,Fintype.sum_prod_type,historyVariation,Finset.sum_div]

theorem noisyFeedback_run (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    (a : Qubit) (h : History 2 m) :
    run Qubit Qubit 2 (noisyFeedback p hp hp1 m) (a,h) correlatedInput =
      ((1/2:ℂ)*(pathWeight p a h:ℂ)) • (basisState (lastBit a h) ⊗ₖ basisState a) := by
  simp only [noisyFeedback,run,readStep_correlated,run_smul,noisySuffix_run,smul_smul]

theorem idealFeedback_run (m : ℕ) (a : Qubit) (h : History 2 m) :
    run Qubit Qubit 2 (idealFeedback m) (a,h) correlatedInput =
      if h=constantHistory a m then (1/2:ℂ) • (basisState a ⊗ₖ basisState a) else 0 := by
  simp only [idealFeedback,run,readStep_correlated,run_smul,idealSuffix_run]
  split_ifs with hh
  · subst h; rw [lastBit_constant]
  · simp

theorem noisyFeedback_outputDistance (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    outputDistance Qubit Qubit 2 (noisyFeedback p hp hp1 m) (idealFeedback m)
      correlatedInput correlatedInput = 1-(1-p)^m := by
  rw [noisyFeedback,idealFeedback,outputDistance_node]
  simp only [readStep_correlated]
  have hc : (1/2:ℂ)=((1/2:ℝ):ℂ) := by norm_num
  rw [hc]
  simp only [outputDistance_smul Qubit Qubit 2 _ _ _ _ (by norm_num : (0:ℝ)≤1/2),
    noisySuffix_outputDistance,Fin.sum_univ_two]
  ring

theorem noisyFeedback_historyVariation (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    historyVariation Qubit Qubit 2 (noisyFeedback p hp hp1 m) (idealFeedback m)
      correlatedInput correlatedInput = 1-(1-p)^m := by
  rw [noisyFeedback,idealFeedback,historyVariation_node]
  simp only [readStep_correlated]
  have hc : (1/2:ℂ)=((1/2:ℝ):ℂ) := by norm_num
  rw [hc]
  simp only [historyVariation_smul Qubit Qubit 2 _ _ _ _ (by norm_num : (0:ℝ)≤1/2),
    noisySuffix_historyVariation,Fin.sum_univ_two]
  ring

theorem noisyStepAt_localError (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (a : Qubit) :
    LocalError Qubit Qubit 2 (noisyStepAt p hp hp1 a) (idealStep a) p := by
  exact mixed_instrument_localError Qubit Qubit 2 (fun _ : Fin 1 => 1)
    (by simp [IsKrausChannel]) (FiniteInstrument.prepare a) (FiniteInstrument.prepare (1-a)) p hp hp1

theorem noisySuffix_pairedErrors (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) (a : Qubit) :
    PairedErrors Qubit Qubit 2 (noisySuffix p hp hp1 m a) (idealSuffix m a) (List.replicate m p) := by
  induction m generalizing a with
  | zero => exact .done
  | succ m ih => exact .node (noisyStepAt_localError p hp hp1 a) (List.length_replicate ..) (fun b => ih b)

theorem noisyFeedback_pairedErrors (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    PairedErrors Qubit Qubit 2 (noisyFeedback p hp hp1 m) (idealFeedback m) (0::List.replicate m p) :=
  .node (localError_refl Qubit Qubit 2 readStep) (List.length_replicate ..)
    (noisySuffix_pairedErrors p hp hp1 m)

theorem noisyFeedback_capped (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    outputDistance Qubit Qubit 2 (noisyFeedback p hp hp1 m) (idealFeedback m)
      correlatedInput correlatedInput ≤ min 1 ((m:ℝ)*p) := by
  have h := pairedErrors_capped Qubit Qubit 2 (noisyFeedback_pairedErrors p hp hp1 m)
    correlatedInput_density correlatedInput_density
  simpa only [traceDist_self,List.sum_cons,List.sum_replicate,nsmul_eq_mul,zero_add] using h

theorem noisyFeedback_survival_bound (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    1-(1-p)^m ≤ min 1 ((m:ℝ)*p) := by
  rw [← noisyFeedback_outputDistance p hp hp1 m]
  exact noisyFeedback_capped p hp hp1 m

theorem outputDistance_comm {n : ℕ} (T U : Tree S E o n)
    (X Y : Matrix (S × E) (S × E) ℂ) :
    outputDistance S E o T U X Y=outputDistance S E o U T Y X := by
  unfold outputDistance
  apply congrArg (fun t : ℝ => t/2)
  apply Finset.sum_congr rfl
  intro h _
  rw [← traceNorm_neg (run S E o U h Y-run S E o T h X),neg_sub]

theorem historyVariation_comm {n : ℕ} (T U : Tree S E o n)
    (X Y : Matrix (S × E) (S × E) ℂ) :
    historyVariation S E o T U X Y=historyVariation S E o U T Y X := by
  simp only [historyVariation,abs_sub_comm]

/-- Exact noisy-feedback survival law, with total depth m+1 and retained memory. -/
theorem noisyFeedback_exact (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) :
    outputDistance Qubit Qubit 2 (idealFeedback m) (noisyFeedback p hp hp1 m)
      correlatedInput correlatedInput = 1-(1-p)^m ∧
    historyVariation Qubit Qubit 2 (idealFeedback m) (noisyFeedback p hp hp1 m)
      correlatedInput correlatedInput = 1-(1-p)^m ∧
    1-(1-p)^m ≤ min 1 ((m:ℝ)*p) := by
  rw [outputDistance_comm,historyVariation_comm]
  exact ⟨noisyFeedback_outputDistance p hp hp1 m,noisyFeedback_historyVariation p hp hp1 m,
    noisyFeedback_survival_bound p hp hp1 m⟩

theorem noisyFeedback_zero_depth (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    outputDistance Qubit Qubit 2 (noisyFeedback p hp hp1 0) (idealFeedback 0)
      correlatedInput correlatedInput=0 := by rw [noisyFeedback_outputDistance]; simp

theorem noisyFeedback_zero_noise (m : ℕ) :
    outputDistance Qubit Qubit 2 (noisyFeedback 0 le_rfl (by norm_num) m) (idealFeedback m)
      correlatedInput correlatedInput=0 := by rw [noisyFeedback_outputDistance]; simp

theorem noisyFeedback_full_noise (m : ℕ) (hm : 0<m) :
    outputDistance Qubit Qubit 2 (noisyFeedback 1 (by norm_num) le_rfl m) (idealFeedback m)
      correlatedInput correlatedInput=1 := by
  rw [noisyFeedback_outputDistance]
  simp [Nat.ne_of_gt hm]

theorem noisyFeedback_single_sharp (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    outputDistance Qubit Qubit 2 (noisyFeedback p hp hp1 1) (idealFeedback 1)
      correlatedInput correlatedInput=p := by rw [noisyFeedback_outputDistance]; simp

theorem noisyFeedback_two_identification :
    noisyFeedback (1/4) (by norm_num) (by norm_num) 2=noisyTwo ∧ idealFeedback 2=idealTwo := ⟨rfl,rfl⟩

theorem noisyFeedback_weight (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ)
    (a : Qubit) (h : History 2 m) :
    weight Qubit Qubit 2 (noisyFeedback p hp hp1 m) (a,h) correlatedInput =
      (1/2)*pathWeight p a h := by
  simp only [weight,noisyFeedback_run,Matrix.trace_smul,(basisJoint_density (lastBit a h) a).2,
    smul_eq_mul,mul_one,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  norm_num

theorem noisyFeedback_first_marginal (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (m : ℕ) (a : Qubit) :
    (∑ h : History 2 m, weight Qubit Qubit 2 (noisyFeedback p hp hp1 m) (a,h) correlatedInput)=1/2 := by
  simp only [noisyFeedback_weight,← Finset.mul_sum]
  rw [pathWeight_sum p hp hp1 m a,mul_one]

theorem pathWeight_pos (p : ℝ) (hp : 0<p) (hp1 : p<1) {m : ℕ} (a : Qubit)
    (h : History 2 m) : 0<pathWeight p a h := by
  induction m generalizing a with
  | zero => simp [pathWeight]
  | succ m ih =>
    rcases h with ⟨b,h⟩
    exact mul_pos (by unfold transition; split_ifs <;> linarith) (ih b h)

theorem noisyFeedback_every_history_pos (p : ℝ) (hp : 0<p) (hp1 : p<1) (m : ℕ)
    (a : Qubit) (h : History 2 m) :
    0<weight Qubit Qubit 2 (noisyFeedback p hp.le hp1.le m) (a,h) correlatedInput := by
  rw [noisyFeedback_weight]
  exact mul_pos (by norm_num) (pathWeight_pos p hp hp1 a h)

/-- Both independently mixed fields feed the same finite-tree telescope through an
actual intermediate step; the continuations can differ at every history. -/
theorem mixed_both_node_capped {k l n : ℕ}
    (K : Fin k → Matrix (S × E) (S × E) ℂ) (L : Fin l → Matrix (S × E) (S × E) ℂ)
    (hK : IsKrausChannel K) (hL : IsKrausChannel L) (D D' : FiniteInstrument S o)
    (p q : ℝ) (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hq1 : q≤1)
    (F G : Fin o → Tree S E o n) (es : List ℝ) (hlen : es.length=n)
    (ht : ∀ a,PairedErrors S E o (F a) (G a) es)
    {X Y : Matrix (S × E) (S × E) ℂ} (hX : IsDensityOperator X) (hY : IsDensityOperator Y) :
    outputDistance S E o
      (.node (realizedStep S E o (mixKraus K L p) (mixKraus_channel hK hL hp hp1)
        (mixInstrument D D' q hq hq1)) F)
      (.node (realizedStep S E o K hK D) G) X Y ≤ min 1 (traceDist X Y+(p+q)+es.sum) := by
  have ht' := PairedErrors.node (mixed_both_localError S E o K L hK hL D D' p q hp hp1 hq hq1) hlen ht
  simpa only [List.sum_cons,add_assoc] using pairedErrors_capped S E o ht' hX hY

theorem idealFeedback_weight (m : ℕ) (a : Qubit) (h : History 2 m) :
    weight Qubit Qubit 2 (idealFeedback m) (a,h) correlatedInput =
      if h=constantHistory a m then 1/2 else 0 := by
  rw [weight,idealFeedback_run]
  split_ifs <;> simp [Matrix.trace_smul,(basisJoint_density a a).2]

/-! The uniform local premise ranges over all densities on the explicit finite
system and retained environment, including correlated inputs. The generic
error telescope is additive; the multiplicative survival identity belongs only
to the realized feedback family above. No bound for extra unmodeled ancillas,
postselection, sampling uncertainty, quotient-rank stability, or physical time
is claimed. The recursive pathWeight is the product of the transition factors
along the complete actual history; its normalization was derived from run. -/

end SKEFTHawking.QuantumNetwork.FiniteAdaptiveMapPerturbation
