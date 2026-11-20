import SKEFTHawking.QuantumNetwork.FiniteAdaptiveProcessRobustness

/-!
# Complete Kraus paths of actual adaptive strategies

Evolution precedes the local instrument at each node. The complete path operator
multiplies the continuation on the left. All histories, including zero branches,
remain in the outcome space.
-/
namespace SKEFTHawking.QuantumNetwork.FiniteAdaptiveKrausRealization
open Matrix FiniteInterventionProcess
open scoped BigOperators ComplexOrder Kronecker

variable {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]
variable {o : ℕ}

instance historyDecidableEq : (n : ℕ) → DecidableEq (History o n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n+1 => @instDecidableEqProd _ _ inferInstance (historyDecidableEq n)

/-- Internal indices depend on the entire realized history. -/
def Path : {n : ℕ} → (T : Tree S E o n) → History o n → Type
  | 0, .done, _ => Unit
  | _+1, .node D F, (a,h) => (Fin D.instrument.count × Fin D.count) × Path (F a) h

instance pathFintype : {n : ℕ} → (T : Tree S E o n) → (h : History o n) → Fintype (Path T h)
  | 0, .done, _ => inferInstanceAs (Fintype Unit)
  | _+1, .node _ F, (a,h) =>
      @instFintypeProd _ _ inferInstance (pathFintype (F a) h)

/-- The local operation acts after the joint evolution. -/
noncomputable def stepKraus (D : Step S E o) (a : Fin o)
    (z : Fin D.instrument.count × Fin D.count) : Matrix (S × E) (S × E) ℂ :=
  (D.instrument.lift E).operators a z.1 * D.evolution z.2

/-- Later operations multiply earlier operations on the left. -/
noncomputable def pathKraus : {n : ℕ} → (T : Tree S E o n) → (h : History o n) →
    Path T h → Matrix (S × E) (S × E) ℂ
  | 0, .done, _ => fun _ => 1
  | _+1, .node D F, (a,h) => fun z => pathKraus (F a) h z.2 * stepKraus D a z.1

theorem path_card_node {n : ℕ} (D : Step S E o) (F : Fin o → Tree S E o n)
    (a : Fin o) (h : History o n) :
    Fintype.card (Path (.node D F) (a,h)) =
      D.instrument.count * D.count * Fintype.card (Path (F a) h) := by
  change Fintype.card ((Fin D.instrument.count × Fin D.count) × Path (F a) h) = _
  simp

theorem step_branch_eq (D : Step S E o) (a : Fin o)
    (X : Matrix (S × E) (S × E) ℂ) :
    D.branch S E o a X = ∑ z, stepKraus D a z * X * (stepKraus D a z)ᴴ := by
  simp only [Step.branch, FiniteInstrument.branch, krausMap, stepKraus,
    Fintype.sum_prod_type, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rfl

/-- Exact complete-path semantics on every complex input matrix. -/
theorem run_eq_pathKraus {n : ℕ} (T : Tree S E o n) (h : History o n)
    (X : Matrix (S × E) (S × E) ℂ) :
    run S E o T h X = ∑ z, pathKraus T h z * X * (pathKraus T h z)ᴴ := by
  induction T generalizing X with
  | done => simp [Path, pathKraus, run]
  | node D F ih =>
    rcases h with ⟨a,h⟩
    change run S E o (F a) h (D.branch S E o a X) =
      ∑ z : (Fin D.instrument.count × Fin D.count) × Path (F a) h,
        (pathKraus (F a) h z.2 * stepKraus D a z.1) * X *
          (pathKraus (F a) h z.2 * stepKraus D a z.1)ᴴ
    rw [ih, step_branch_eq]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- The adjoint of a complete branch, before any reference state is chosen. -/
noncomputable def leafDual {n : ℕ} (T : Tree S E o n) (h : History o n)
    (Y : Matrix (S × E) (S × E) ℂ) : Matrix (S × E) (S × E) ℂ :=
  ∑ z, (pathKraus T h z)ᴴ * Y * pathKraus T h z

noncomputable def leafEffect {n : ℕ} (T : Tree S E o n) (h : History o n) :
    Matrix (S × E) (S × E) ℂ := leafDual T h 1

theorem leafDual_node {n : ℕ} (D : Step S E o) (F : Fin o → Tree S E o n)
    (a : Fin o) (h : History o n) (Y : Matrix (S × E) (S × E) ℂ) :
    leafDual (.node D F) (a,h) Y =
      ∑ z, (stepKraus D a z)ᴴ * leafDual (F a) h Y * stepKraus D a z := by
  change (∑ z : (Fin D.instrument.count × Fin D.count) × Path (F a) h,
      (pathKraus (F a) h z.2 * stepKraus D a z.1)ᴴ * Y *
        (pathKraus (F a) h z.2 * stepKraus D a z.1)) = _
  rw [Fintype.sum_prod_type]
  simp only [leafDual, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem step_complete (D : Step S E o) :
    ∑ a, ∑ z, (stepKraus D a z)ᴴ * stepKraus D a z = 1 := by
  simp only [stepKraus, Fintype.sum_prod_type, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [← Matrix.mul_assoc, ← Matrix.sum_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_sum]
  erw [(D.instrument.lift E).normalized]
  simpa [IsKrausChannel] using D.normalized

theorem leafEffect_sum {n : ℕ} (T : Tree S E o n) : ∑ h, leafEffect T h = 1 := by
  induction T with
  | done => simp [leafEffect, leafDual, Path, pathKraus, History]
  | node D F ih =>
    change (∑ h : Fin o × History o _, leafDual (.node D F) h 1) = _
    rw [Fintype.sum_prod_type]
    simp_rw [leafDual_node]
    apply Eq.trans _ (step_complete D)
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    simp only [← Matrix.mul_sum, ← Matrix.sum_mul]
    change (∑ z, (stepKraus D a z)ᴴ * (∑ h, leafEffect (F a) h) * stepKraus D a z) = _
    rw [ih]
    simp

/-- Total completeness is derived from the actual nodes, including all zero leaves. -/
theorem path_complete {n : ℕ} (T : Tree S E o n) :
    ∑ h, ∑ z, (pathKraus T h z)ᴴ * pathKraus T h z = 1 := by
  simpa [leafEffect, leafDual] using leafEffect_sum T

theorem leaf_trace_duality {n : ℕ} (T : Tree S E o n) (h : History o n)
    (Y X : Matrix (S × E) (S × E) ℂ) :
    (Y * run S E o T h X).trace = (leafDual T h Y * X).trace := by
  rw [run_eq_pathKraus]
  simp only [leafDual, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro z _
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (Y * pathKraus T h z * X) (pathKraus T h z)ᴴ

theorem leafEffect_posSemidef {n : ℕ} (T : Tree S E o n) (h : History o n) :
    (leafEffect T h).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro z _
  exact Matrix.PosSemidef.one.conjTranspose_mul_mul_same _

theorem leafEffect_adjoint {n : ℕ} (T : Tree S E o n) (h : History o n) :
    (leafEffect T h)ᴴ = leafEffect T h := (leafEffect_posSemidef T h).isHermitian

theorem leafDual_node_backward {n : ℕ} (D : Step S E o) (F : Fin o → Tree S E o n)
    (a : Fin o) (h : History o n) (Y : Matrix (S × E) (S × E) ℂ) :
    leafDual (.node D F) (a,h) Y =
      FiniteAdaptiveProcessRobustness.dual D.evolution
        (FiniteAdaptiveProcessRobustness.dual ((D.instrument.lift E).operators a)
          (leafDual (F a) h Y)) := by
  rw [leafDual_node]
  simp only [stepKraus, FiniteAdaptiveProcessRobustness.dual,
    Fintype.sum_prod_type, Matrix.conjTranspose_mul, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_assoc]
  rw [Finset.sum_comm]
  rfl

/-- The compiled leaf effect is the existing backward recursion for that exact event. -/
theorem leafEffect_event {n : ℕ} (T : Tree S E o n) (h : History o n) :
    leafEffect T h = FiniteAdaptiveProcessRobustness.effect T
      (fun g => if g = h then 1 else 0) := by
  classical
  induction T with
  | done => cases h; simp [leafEffect, leafDual, pathKraus, Path,
      FiniteAdaptiveProcessRobustness.effect]
  | node D F ih =>
    rcases h with ⟨a,h⟩
    have hi : ∀ b, FiniteAdaptiveProcessRobustness.effect (F b)
        (fun g => if (b,g) = (a,h) then 1 else 0) =
          if b = a then leafEffect (F b) h else 0 := by
      intro b
      by_cases hb : b = a
      · subst b
        simpa using (ih a h).symm
      · simp [hb, FiniteAdaptiveProcessRobustness.effect_zero]
    change leafDual (.node D F) (a,h) 1 =
      FiniteAdaptiveProcessRobustness.nodeEffect D
        (fun b => FiniteAdaptiveProcessRobustness.effect (F b)
          (fun g => if (b,g) = (a,h) then 1 else 0))
    rw [leafDual_node_backward]
    simp only [hi, FiniteAdaptiveProcessRobustness.nodeEffect]
    congr 1
    simp [FiniteAdaptiveProcessRobustness.dual, leafEffect]

/-- One common internal index type, retaining every complete history. -/
def TotalPath {n : ℕ} (T : Tree S E o n) := Sigma (Path T)

instance totalPathFintype {n : ℕ} (T : Tree S E o n) : Fintype (TotalPath T) :=
  inferInstanceAs (Fintype (Sigma (Path T)))

noncomputable def paddedKraus {n : ℕ} (T : Tree S E o n) (h : History o n)
    (z : TotalPath T) : Matrix (S × E) (S × E) ℂ :=
  if z.1 = h then pathKraus T z.1 z.2 else 0

theorem padded_branch {n : ℕ} (T : Tree S E o n) (h : History o n)
    (X : Matrix (S × E) (S × E) ℂ) :
    (∑ z, paddedKraus T h z * X * (paddedKraus T h z)ᴴ) = run S E o T h X := by
  rw [run_eq_pathKraus]
  change (∑ z : Sigma (Path T), _) = _
  rw [Fintype.sum_sigma]
  simp [paddedKraus]

theorem padded_dual {n : ℕ} (T : Tree S E o n) (h : History o n)
    (Y : Matrix (S × E) (S × E) ℂ) :
    (∑ z, (paddedKraus T h z)ᴴ * Y * paddedKraus T h z) = leafDual T h Y := by
  change (∑ z : Sigma (Path T), _) = _
  rw [Fintype.sum_sigma]
  simp [paddedKraus, leafDual]

/-- Any finite enumerations give the same branch maps; neither selects positive leaves. -/
noncomputable def leafInstrumentWith {n q k : ℕ} (T : Tree S E o n)
    (eH : Fin q ≃ History o n) (eP : Fin k ≃ TotalPath T) :
    FiniteInstrument (S × E) q where
  count := k
  operators a z := paddedKraus T (eH a) (eP z)
  normalized := by
    have hr : ∀ a, (∑ z, (paddedKraus T (eH a) (eP z))ᴴ *
        paddedKraus T (eH a) (eP z)) = leafEffect T (eH a) := by
      intro a
      rw [eP.sum_comp (fun z => (paddedKraus T (eH a) z)ᴴ * paddedKraus T (eH a) z)]
      simpa [leafEffect] using padded_dual T (eH a) 1
    simp_rw [hr]
    rw [eH.sum_comp, leafEffect_sum]

theorem leafInstrumentWith_branch {n q k : ℕ} (T : Tree S E o n)
    (eH : Fin q ≃ History o n) (eP : Fin k ≃ TotalPath T) (a : Fin q)
    (X : Matrix (S × E) (S × E) ℂ) :
    (leafInstrumentWith T eH eP).branch a X = run S E o T (eH a) X := by
  change (∑ z, paddedKraus T (eH a) (eP z) * X * (paddedKraus T (eH a) (eP z))ᴴ) = _
  rw [eP.sum_comp (fun z => paddedKraus T (eH a) z * X * (paddedKraus T (eH a) z)ᴴ),
    padded_branch]

noncomputable def historyEquiv (o n : ℕ) : Fin (Fintype.card (History o n)) ≃ History o n :=
  (Fintype.equivFin (History o n)).symm

noncomputable def pathEquiv {n : ℕ} (T : Tree S E o n) :
    Fin (Fintype.card (TotalPath T)) ≃ TotalPath T := (Fintype.equivFin (TotalPath T)).symm

/-- The derived global forward instrument, with one outcome for every complete leaf. -/
noncomputable def leafInstrument {n : ℕ} (T : Tree S E o n) :
    FiniteInstrument (S × E) (Fintype.card (History o n)) :=
  leafInstrumentWith T (historyEquiv o n) (pathEquiv T)

theorem leafInstrument_branch {n : ℕ} (T : Tree S E o n)
    (a : Fin (Fintype.card (History o n))) (X : Matrix (S × E) (S × E) ℂ) :
    (leafInstrument T).branch a X = run S E o T (historyEquiv o n a) X :=
  leafInstrumentWith_branch T _ _ a X

/-- The singleton spectator is an exact carrier identification. -/
def joint (X : Matrix S S ℂ) : Matrix (S × Unit) (S × Unit) ℂ := X ⊗ₖ 1

def unJoint (X : Matrix (S × Unit) (S × Unit) ℂ) : Matrix S S ℂ :=
  fun i j => X (i,()) (j,())

omit [Fintype S] [DecidableEq S] in
theorem unJoint_joint (X : Matrix S S ℂ) : unJoint (joint X) = X := by
  ext i j
  simp [unJoint, joint]

omit [Fintype S] [DecidableEq S] in
theorem joint_unJoint (X : Matrix (S × Unit) (S × Unit) ℂ) : joint (unJoint X) = X := by
  ext ⟨i,u⟩ ⟨j,v⟩
  cases u; cases v
  simp [unJoint, joint]

omit [DecidableEq S] in
theorem unJoint_mul (X Y : Matrix (S × Unit) (S × Unit) ℂ) :
    unJoint (X * Y) = unJoint X * unJoint Y := by
  ext i j
  simp [unJoint, Matrix.mul_apply, Fintype.sum_prod_type]

omit [Fintype S] [DecidableEq S] in
theorem unJoint_adjoint (X : Matrix (S × Unit) (S × Unit) ℂ) :
    unJoint Xᴴ = (unJoint X)ᴴ := rfl

omit [Fintype S] in
theorem unJoint_one : unJoint (1 : Matrix (S × Unit) (S × Unit) ℂ) = 1 := by
  ext i j
  simp [unJoint, Matrix.one_apply]

omit [Fintype S] [DecidableEq S] in
theorem unJoint_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (S × Unit) (S × Unit) ℂ) :
    unJoint (∑ i ∈ s, f i) = ∑ i ∈ s, unJoint (f i) := by
  ext i j
  simp only [unJoint, Matrix.sum_apply]

omit [DecidableEq S] in
theorem unJoint_trace (X : Matrix (S × Unit) (S × Unit) ℂ) :
    (unJoint X).trace = X.trace := by
  simp [Matrix.trace, unJoint, Fintype.sum_prod_type]

omit [DecidableEq S] in
theorem joint_mul (X Y : Matrix S S ℂ) : joint (X * Y) = joint X * joint Y := by
  simp [joint, ← Matrix.mul_kronecker_mul]

omit [Fintype S] [DecidableEq S] in
theorem joint_adjoint (X : Matrix S S ℂ) : joint Xᴴ = (joint X)ᴴ := by
  simp [joint, Matrix.conjTranspose_kronecker]

omit [Fintype S] in
theorem joint_one : joint (1 : Matrix S S ℂ) = 1 := Matrix.one_kronecker_one

omit [Fintype S] [DecidableEq S] in
theorem joint_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix S S ℂ) :
    joint (∑ i ∈ s, f i) = ∑ i ∈ s, joint (f i) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  cases u; cases v
  simp [joint, Matrix.sum_apply]

omit [DecidableEq S] in
theorem joint_trace (X : Matrix S S ℂ) : (joint X).trace = X.trace := by
  rw [← unJoint_trace, unJoint_joint]

/-- Concatenation allows a different continuation after every complete prefix. -/
def appendTree : {n m : ℕ} → (T : Tree S E o n) →
    (History o n → Tree S E o m) → Tree S E o (m+n)
  | 0, _, .done, F => F ()
  | _+1, _, .node D G, F => .node D (fun a => appendTree (G a) (fun h => F (a,h)))

def appendHistory : {n m : ℕ} → History o n → History o m → History o (m+n)
  | 0, _, _, h => h
  | _+1, _, (a,h), g => (a, appendHistory h g)

theorem append_run {n m : ℕ} (T : Tree S E o n) (F : History o n → Tree S E o m)
    (h : History o n) (g : History o m) (X : Matrix (S × E) (S × E) ℂ) :
    run S E o (appendTree T F) (appendHistory h g) X =
      run S E o (F h) g (run S E o T h X) := by
  induction T generalizing X with
  | done => cases h; rfl
  | node D G ih => exact ih h.1 (fun t => F (h.1,t)) h.2 (D.branch S E o h.1 X)

variable {m : ℕ}

/-- Injective outcome recoding keeps unused outcomes as zero operators. -/
noncomputable def recodeKraus (I : FiniteInstrument S o) (e : Fin o ↪ Fin m)
    (b : Fin m) (k : Fin I.count) : Matrix S S ℂ :=
  ∑ a, if e a = b then I.operators a k else 0

theorem recodeKraus_image (I : FiniteInstrument S o) (e : Fin o ↪ Fin m)
    (a : Fin o) (k : Fin I.count) : recodeKraus I e (e a) k = I.operators a k := by
  simp [recodeKraus, e.injective.eq_iff]

theorem recodeKraus_invalid (I : FiniteInstrument S o) (e : Fin o ↪ Fin m)
    (b : Fin m) (hb : b ∉ Set.range e) (k : Fin I.count) : recodeKraus I e b k = 0 := by
  have hn : ∀ a, e a ≠ b := fun a h => hb ⟨a,h⟩
  simp [recodeKraus, hn]

noncomputable def recodeInstrument (I : FiniteInstrument S o) (e : Fin o ↪ Fin m) :
    FiniteInstrument S m where
  count := I.count
  operators := recodeKraus I e
  normalized := by
    have hs := Fintype.sum_of_injective e e.injective
      (fun a => ∑ k, (I.operators a k)ᴴ * I.operators a k)
      (fun b => ∑ k, (recodeKraus I e b k)ᴴ * recodeKraus I e b k)
      (by intro b hb; simp [recodeKraus_invalid I e b hb])
      (by intro a; simp [recodeKraus_image])
    exact hs.symm.trans I.normalized

noncomputable def recodeStep (D : Step S E o) (e : Fin o ↪ Fin m) : Step S E m where
  count := D.count
  evolution := D.evolution
  normalized := D.normalized
  instrument := recodeInstrument D.instrument e

theorem recodeStep_branch (D : Step S E o) (e : Fin o ↪ Fin m) (a : Fin o)
    (X : Matrix (S × E) (S × E) ℂ) :
    (recodeStep D e).branch S E m (e a) X = D.branch S E o a X := by
  simp only [Step.branch, recodeStep, FiniteInstrument.branch, FiniteInstrument.lift,
    recodeInstrument, krausMap, recodeKraus_image]
  rfl

theorem recodeStep_invalid (D : Step S E o) (e : Fin o ↪ Fin m) (b : Fin m)
    (hb : b ∉ Set.range e) (X : Matrix (S × E) (S × E) ℂ) :
    (recodeStep D e).branch S E m b X = 0 := by
  simp [Step.branch, recodeStep, FiniteInstrument.branch, FiniteInstrument.lift,
    recodeInstrument, krausMap, recodeKraus_invalid D.instrument e b hb]

noncomputable def decodeLabel (e : Fin o ↪ Fin m) (a₀ : Fin o) (b : Fin m) : Fin o :=
  if h : ∃ a, e a = b then h.choose else a₀

theorem decodeLabel_image (e : Fin o ↪ Fin m) (a₀ a : Fin o) :
    decodeLabel e a₀ (e a) = a := by
  unfold decodeLabel
  rw [dif_pos ⟨a,rfl⟩]
  exact e.injective (Exists.choose_spec (show ∃ b, e b = e a from ⟨a,rfl⟩))

/-- Invalid prefixes use a normalized existing subtree; their incoming state is zero. -/
noncomputable def recodeTree (e : Fin o ↪ Fin m) (a₀ : Fin o) :
    {n : ℕ} → Tree S E o n → Tree S E m n
  | 0, .done => .done
  | _+1, .node D F => .node (recodeStep D e)
      (fun b => recodeTree e a₀ (F (decodeLabel e a₀ b)))

def recodeHistory (e : Fin o ↪ Fin m) : {n : ℕ} → History o n → History m n
  | 0, _ => ()
  | _+1, (a,h) => (e a, recodeHistory e h)

theorem recodeHistory_injective (e : Fin o ↪ Fin m) (n : ℕ) :
    Function.Injective (@recodeHistory o m e n) := by
  induction n with
  | zero => intro a b _; cases a; cases b; rfl
  | succ n ih =>
    intro ⟨a,h⟩ ⟨b,g⟩ he
    have hp := Prod.mk.inj he
    exact Prod.ext (e.injective hp.1) (ih hp.2)

theorem recode_run (e : Fin o ↪ Fin m) (a₀ : Fin o) {n : ℕ}
    (T : Tree S E o n) (h : History o n) (X : Matrix (S × E) (S × E) ℂ) :
    run S E m (recodeTree e a₀ T) (recodeHistory e h) X = run S E o T h X := by
  induction T generalizing X with
  | done => rfl
  | node D F ih =>
    rcases h with ⟨a,h⟩
    simp only [recodeTree, recodeHistory, run, decodeLabel_image, recodeStep_branch, ih]

/-- Every history outside the encoding has zero output for the same arbitrary complex input. -/
theorem recode_invalid_zero (e : Fin o ↪ Fin m) (a₀ : Fin o) {n : ℕ}
    (T : Tree S E o n) (h : History m n)
    (hh : h ∉ Set.range (@recodeHistory o m e n)) (X : Matrix (S × E) (S × E) ℂ) :
    run S E m (recodeTree e a₀ T) h X = 0 := by
  induction T generalizing X with
  | done => exact (hh ⟨(),rfl⟩).elim
  | node D F ih =>
    rcases h with ⟨b,h⟩
    by_cases hb : b ∈ Set.range e
    · obtain ⟨a,rfl⟩ := hb
      have ht : h ∉ Set.range (@recodeHistory o m e _) := by
        rintro ⟨g,hg⟩
        exact hh ⟨(a,g), congrArg (Prod.mk (e a)) hg⟩
      simp only [recodeTree, run, decodeLabel_image]
      exact ih a h ht _
    · simp only [recodeTree, run]
      rw [recodeStep_invalid D e b hb, run_zero]

/-- The same path operators on the singleton-environment system carrier. -/
noncomputable def systemPathKraus {n : ℕ} (T : Tree S Unit o n) (h : History o n)
    (z : Path T h) : Matrix S S ℂ := unJoint (pathKraus T h z)

theorem system_run_eq_pathKraus {n : ℕ} (T : Tree S Unit o n) (h : History o n)
    (X : Matrix S S ℂ) :
    unJoint (run S Unit o T h (joint X)) =
      ∑ z, systemPathKraus T h z * X * (systemPathKraus T h z)ᴴ := by
  rw [run_eq_pathKraus, unJoint_sum]
  simp only [unJoint_mul, unJoint_adjoint, unJoint_joint, systemPathKraus]

theorem system_path_complete {n : ℕ} (T : Tree S Unit o n) :
    ∑ h, ∑ z, (systemPathKraus T h z)ᴴ * systemPathKraus T h z = 1 := by
  have he := congrArg unJoint (path_complete T)
  simpa only [unJoint_sum, unJoint_mul, unJoint_adjoint, unJoint_one,
    systemPathKraus] using he

theorem system_leafEffect {n : ℕ} (T : Tree S Unit o n) (h : History o n) :
    unJoint (leafEffect T h) = ∑ z, (systemPathKraus T h z)ᴴ * systemPathKraus T h z := by
  simp only [leafEffect, leafDual, unJoint_sum, unJoint_mul, unJoint_adjoint,
    Matrix.mul_one, systemPathKraus]

theorem system_leafEffect_event {n : ℕ} (T : Tree S Unit o n) (h : History o n) :
    joint (∑ z, (systemPathKraus T h z)ᴴ * systemPathKraus T h z) =
      FiniteAdaptiveProcessRobustness.effect T (fun g => if g = h then 1 else 0) := by
  rw [← system_leafEffect, joint_unJoint, leafEffect_event]

noncomputable def systemLeafInstrument {n : ℕ} (T : Tree S Unit o n) :
    FiniteInstrument S (Fintype.card (History o n)) where
  count := (leafInstrument T).count
  operators a z := unJoint ((leafInstrument T).operators a z)
  normalized := by
    have he := congrArg unJoint (leafInstrument T).normalized
    simpa only [unJoint_sum, unJoint_mul, unJoint_adjoint, unJoint_one] using he

theorem systemLeafInstrument_branch {n : ℕ} (T : Tree S Unit o n)
    (a : Fin (Fintype.card (History o n))) (X : Matrix S S ℂ) :
    (systemLeafInstrument T).branch a X =
      unJoint (run S Unit o T (historyEquiv o n a) (joint X)) := by
  rw [← leafInstrument_branch T a (joint X)]
  simp only [systemLeafInstrument, FiniteInstrument.branch, krausMap, unJoint_sum,
    unJoint_mul, unJoint_adjoint, unJoint_joint]
  rfl

def splitHistory : {n m : ℕ} → History o (m+n) → History o n × History o m
  | 0, _, h => ((),h)
  | _+1, _, (a,h) => let p := splitHistory h; ((a,p.1),p.2)

theorem split_appendHistory {n m : ℕ} (h : History o n) (g : History o m) :
    splitHistory (appendHistory h g) = (h,g) := by
  induction n with
  | zero => cases h; rfl
  | succ n ih => rcases h with ⟨a,h⟩; simp only [appendHistory, splitHistory, ih]

theorem append_splitHistory {n m : ℕ} (h : History o (m+n)) :
    appendHistory (splitHistory h).1 (splitHistory h).2 = h := by
  induction n with
  | zero => rfl
  | succ n ih => rcases h with ⟨a,h⟩; simp only [splitHistory, appendHistory, ih]

def appendEquiv (o n m : ℕ) : History o n × History o m ≃ History o (m+n) where
  toFun h := appendHistory h.1 h.2
  invFun := splitHistory
  left_inv h := split_appendHistory h.1 h.2
  right_inv := append_splitHistory

end SKEFTHawking.QuantumNetwork.FiniteAdaptiveKrausRealization

#check Nat
