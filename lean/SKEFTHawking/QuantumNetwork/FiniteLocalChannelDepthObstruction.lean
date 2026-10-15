import SKEFTHawking.QuantumNetwork.FiniteLocalChannelLayer
import SKEFTHawking.QuantumNetwork.BinaryMemoryRobustness

/-! A finite locality obstruction for shallow independent channels on four Boolean wires. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace SKEFTHawking.QuantumNetwork.FiniteLocalChannelDepthObstruction
open FiniteLocalChannelLayer

/-- The projection onto an actual event in the physical computational basis. -/
def eventEffect (p : Basis → Prop) [DecidablePred p] : PhysicalMatrix :=
  Matrix.diagonal (fun x => if p x then 1 else 0)

theorem eventEffect_pos (p : Basis → Prop) [DecidablePred p] :
    (eventEffect p).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro x
  dsimp
  split <;> simp

theorem eventEffect_idempotent (p : Basis → Prop) [DecidablePred p] :
    eventEffect p * eventEffect p = eventEffect p := by
  unfold eventEffect
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  split <;> simp

theorem eventEffect_binary (p : Basis → Prop) [DecidablePred p] :
    IsBinaryPOVM (eventEffect p) :=
  isBinaryPOVM_of_projection (eventEffect_pos p).isHermitian (eventEffect_idempotent p)

/-- Diagonal effects remove off-diagonal entries of an arbitrary complex input. -/
theorem eventEffect_trace (p : Basis → Prop) [DecidablePred p] (X : PhysicalMatrix) :
    (eventEffect p * X).trace = ∑ x, if p x then X x x else 0 := by
  simp [eventEffect, Matrix.trace, Matrix.diagonal_mul, ite_mul]

theorem eventEffect_probability (p : Basis → Prop) [DecidablePred p] (X : PhysicalMatrix) :
    binaryOutcomeProb (eventEffect p) X = (∑ x, if p x then X x x else 0).re := by
  rw [binaryOutcomeProb, eventEffect_trace]

theorem eventEffect_trace_im (p : Basis → Prop) [DecidablePred p]
    {X : PhysicalMatrix} (hX : IsDensityOperator X) :
    (eventEffect p * X).trace.im = 0 := by
  exact (Complex.le_def.mp (trace_mul_nonneg (eventEffect_pos p) hX.1)).2.symm

def singleEffect (w : Wire) : PhysicalMatrix := eventEffect (fun x => x w = true)
def pairEffect (u v : Wire) : PhysicalMatrix :=
  eventEffect (fun x => x u = true ∧ x v = true)

theorem singleEffect_binary (w : Wire) : IsBinaryPOVM (singleEffect w) :=
  eventEffect_binary _
theorem pairEffect_binary (u v : Wire) : IsBinaryPOVM (pairEffect u v) :=
  eventEffect_binary _

section Weighted
variable {I : Type*} [Fintype I] [DecidableEq I] {α : I → Type*}
  [∀ i, Fintype (α i)]

/-- Exact complex weighted diagonal sum for a dependent tensor. -/
theorem weighted_tensor_sum (A : ∀ i, Matrix (α i) (α i) ℂ)
    (f : ∀ i, α i → ℂ) :
    (∑ x : ∀ i, α i, (∏ i, f i (x i)) * tensor A x x) =
      ∏ i, ∑ a, f i a * A i a a := by
  simp only [tensor, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => f i a * A i a a)).symm

/-- Independent coordinate weights factor; a block may have an arbitrary matrix state. -/
theorem weighted_tensor_independent (A : ∀ i, Matrix (α i) (α i) ℂ)
    (hA : ∀ i, (A i).trace = 1) (f g : ∀ i, α i → ℂ)
    (hfg : ∀ i, (∀ a, f i a = 1) ∨ (∀ a, g i a = 1)) :
    (∑ x : ∀ i, α i, ((∏ i, f i (x i)) * (∏ i, g i (x i))) * tensor A x x) =
      (∑ x : ∀ i, α i, (∏ i, f i (x i)) * tensor A x x) *
      (∑ x : ∀ i, α i, (∏ i, g i (x i)) * tensor A x x) := by
  rw [weighted_tensor_sum, weighted_tensor_sum]
  simp_rw [← Finset.prod_mul_distrib]
  rw [weighted_tensor_sum A (fun i a => f i a * g i a)]
  apply Finset.prod_congr rfl
  intro i _
  rcases hfg i with hf | hg
  · simp [hf, show (∑ a, A i a a) = 1 from hA i]
  · simp [hg, show (∑ a, A i a a) = 1 from hA i]

/-- A weight supported on one coordinate, retaining dependent coordinate types. -/
def coordinateWeight (i : I) (f : α i → ℂ) : ∀ j, α j → ℂ :=
  Function.update (fun _ _ => 1) i f

omit [∀ i, Fintype (α i)] in
theorem coordinateWeight_product (i : I) (f : α i → ℂ) (x : ∀ j, α j) :
    (∏ j, coordinateWeight i f j (x j)) = f (x i) := by
  classical
  rw [Finset.prod_eq_single i]
  · simp [coordinateWeight]
  · intro j _ hji
    simp [coordinateWeight, hji]
  · simp

omit [Fintype I] [∀ i, Fintype (α i)] in
theorem coordinateWeight_disjoint {i j : I} (hij : i ≠ j)
    (f : α i → ℂ) (g : α j → ℂ) (k : I) :
    (∀ a, coordinateWeight i f k a = 1) ∨
      (∀ a, coordinateWeight j g k a = 1) := by
  classical
  by_cases hki : k = i
  · right
    subst k
    simp [coordinateWeight, hij]
  · left
    simp [coordinateWeight, hki]
/-- Two distinct coordinates have independent weighted diagonal sums. -/
theorem coordinate_tensor_independent (A : ∀ i, Matrix (α i) (α i) ℂ)
    (hA : ∀ i, (A i).trace = 1) {i j : I} (hij : i ≠ j)
    (f : α i → ℂ) (g : α j → ℂ) :
    (∑ x : ∀ i, α i, (f (x i) * g (x j)) * tensor A x x) =
      (∑ x : ∀ i, α i, f (x i) * tensor A x x) *
      (∑ x : ∀ i, α i, g (x j) * tensor A x x) := by
  have h := weighted_tensor_independent A hA
    (coordinateWeight i f) (coordinateWeight j g)
    (coordinateWeight_disjoint hij f g)
  simpa only [coordinateWeight_product] using h

end Weighted


/-- Event traces transported through the same equivalence on both matrix indices. -/
theorem eventEffect_trace_pull {I : Type*} [Fintype I] [DecidableEq I]
    {α : I → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (e : Basis ≃ (∀ i, α i)) (p : Basis → Prop) [DecidablePred p]
    (A : ∀ i, Matrix (α i) (α i) ℂ) :
    (eventEffect p * pull e (tensor A)).trace =
      ∑ x : ∀ i, α i, (if p (e.symm x) then 1 else 0) * tensor A x x := by
  rw [eventEffect_trace]
  rw [← e.symm.sum_comp (fun x => if p x then pull e (tensor A) x x else 0)]
  simp [pull, ite_mul]

/-- Every partition admits a pair in different blocks. -/
theorem different_blocks (P : Partition) :
    ∃ u v : Wire, u ≠ v ∧ P.blockOf u ≠ P.blockOf v := by
  by_contra h
  have hall : ∀ v : Wire, P.blockOf v = P.blockOf 0 := by
    intro v
    by_contra hv
    exact h ⟨0, v, fun he => hv (congrArg P.blockOf he.symm), Ne.symm hv⟩
  let f : Wire → P.Fiber (P.blockOf 0) := fun v => ⟨v, hall v⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact congrArg Subtype.val hab
  have hc := Fintype.card_le_of_injective f hf
  have hs := P.small (P.blockOf 0)
  norm_num only [Fintype.card_fin] at hc
  change 4 ≤ Fintype.card {w : Wire // P.blockOf w = P.blockOf 0} at hc
  omega

/-- Cross-block independence as an equality of complex traces. -/
theorem block_event_trace_factorization (P : Partition)
    (A : ∀ j, Matrix (P.LocalBasis j) (P.LocalBasis j) ℂ)
    (hA : ∀ j, (A j).trace = 1) {u v : Wire}
    (huv : P.blockOf u ≠ P.blockOf v) :
    (pairEffect u v * pull P.split (tensor A)).trace =
      (singleEffect u * pull P.split (tensor A)).trace *
      (singleEffect v * pull P.split (tensor A)).trace := by
  let f : P.LocalBasis (P.blockOf u) → ℂ := fun x => if x ⟨u, rfl⟩ = true then 1 else 0
  let g : P.LocalBasis (P.blockOf v) → ℂ := fun x => if x ⟨v, rfl⟩ = true then 1 else 0
  have h := coordinate_tensor_independent A hA huv f g
  simp only [pairEffect, singleEffect, eventEffect_trace_pull, Partition.glue_apply]
  convert h using 1 <;>
    simp [f, g, ite_and, ite_mul, mul_ite]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

/-- Density makes the actual complex single-event traces real. -/
theorem real_factorization {X : PhysicalMatrix} (hX : IsDensityOperator X)
    (u v : Wire)
    (h : (pairEffect u v * X).trace =
      (singleEffect u * X).trace * (singleEffect v * X).trace) :
    binaryOutcomeProb (pairEffect u v) X =
      binaryOutcomeProb (singleEffect u) X * binaryOutcomeProb (singleEffect v) X := by
  unfold binaryOutcomeProb
  rw [h, Complex.mul_re]
  have hu := eventEffect_trace_im (fun x => x u = true) hX
  change (singleEffect u * X).trace.im = 0 at hu
  rw [hu]
  ring

/-- Actual normalized local channels, including entangled pair outputs, factor across blocks. -/
theorem layer_event_factorization (L : Layer) (ρ : ProductInput) {u v : Wire}
    (huv : L.partition.blockOf u ≠ L.partition.blockOf v) :
    binaryOutcomeProb (pairEffect u v) (L.action ρ.state) =
      binaryOutcomeProb (singleEffect u) (L.action ρ.state) *
      binaryOutcomeProb (singleEffect v) (L.action ρ.state) := by
  apply real_factorization (L.action_density ρ.state_density) u v
  rw [L.action_productInput]
  exact block_event_trace_factorization L.partition (L.blockOutput ρ)
    (fun j => (L.blockOutput_density ρ j).2) huv

/-- The original product state factors for every distinct physical pair, including depth zero. -/
theorem product_event_trace_factorization (ρ : ProductInput) {u v : Wire} (huv : u ≠ v) :
    (pairEffect u v * ρ.state).trace =
      (singleEffect u * ρ.state).trace * (singleEffect v * ρ.state).trace := by
  have h := coordinate_tensor_independent ρ.localState (fun w => (ρ.density w).2) huv
    (fun b => if b = true then (1 : ℂ) else 0)
    (fun b => if b = true then (1 : ℂ) else 0)
  simp only [pairEffect, singleEffect, eventEffect_trace, ProductInput.state]
  convert h using 1 <;> simp [ite_and, ite_mul, mul_ite]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

theorem product_event_factorization (ρ : ProductInput) {u v : Wire} (huv : u ≠ v) :
    binaryOutcomeProb (pairEffect u v) ρ.state =
      binaryOutcomeProb (singleEffect u) ρ.state * binaryOutcomeProb (singleEffect v) ρ.state :=
  real_factorization ρ.state_density u v (product_event_trace_factorization ρ huv)


/-- A computational basis projector as an actual matrix unit. -/
def basisProjector (s : Basis) : PhysicalMatrix := Matrix.single s s 1

theorem basisProjector_diagonal (s : Basis) :
    basisProjector s = Matrix.diagonal (fun x => if x = s then (1 : ℂ) else 0) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [basisProjector, Matrix.single_apply, eq_comm]
  · simp [basisProjector, Matrix.single_apply, Matrix.diagonal_apply_ne _ hxy]
    intro hsx hsy
    exact hxy (hsx.symm.trans hsy)

theorem basisProjector_density (s : Basis) : IsDensityOperator (basisProjector s) := by
  rw [basisProjector_diagonal]
  refine ⟨Matrix.PosSemidef.diagonal (fun x => ?_), ?_⟩
  · split <;> simp
  · simp [Matrix.trace]

/-- The correlated mixture of the all-zero and all-one projectors. -/
def B4 : PhysicalMatrix :=
  (1 / 2 : ℂ) • basisProjector (fun _ => false) +
    (1 / 2 : ℂ) • basisProjector (fun _ => true)

theorem B4_density : IsDensityOperator B4 := by
  refine ⟨?_, ?_⟩
  · exact ((basisProjector_density (fun _ => false)).1.smul
      (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1 / 2)).add
      ((basisProjector_density (fun _ => true)).1.smul
        (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1 / 2))
  · norm_num [B4, Matrix.trace_add, Matrix.trace_smul,
      (basisProjector_density (fun _ => false)).2,
      (basisProjector_density (fun _ => true)).2]

theorem eventEffect_projector (p : Basis → Prop) [DecidablePred p] (s : Basis) :
    (eventEffect p * basisProjector s).trace = if p s then 1 else 0 := by
  rw [eventEffect_trace, basisProjector_diagonal, Finset.sum_eq_single s]
  · simp
  · intro x _ hxs
    simp [hxs]
  · simp

theorem eventEffect_B4 (p : Basis → Prop) [DecidablePred p] :
    (eventEffect p * B4).trace =
      (1 / 2 : ℂ) * (if p (fun _ => false) then 1 else 0) +
      (1 / 2 : ℂ) * (if p (fun _ => true) then 1 else 0) := by
  simp [B4, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_smul, eventEffect_projector]

theorem B4_single_probability (w : Wire) :
    binaryOutcomeProb (singleEffect w) B4 = 1 / 2 := by
  rw [binaryOutcomeProb, singleEffect, eventEffect_B4]
  norm_num

theorem B4_pair_probability (u v : Wire) :
    binaryOutcomeProb (pairEffect u v) B4 = 1 / 2 := by
  rw [binaryOutcomeProb, pairEffect, eventEffect_B4]
  norm_num

/-- A normalized singleton identity Kraus family on the same physical carrier. -/
def identityKraus : Fin 1 → PhysicalMatrix := fun _ => 1

theorem identityKraus_normalized : IsKrausChannel identityKraus := by
  simp [IsKrausChannel, identityKraus]

theorem identityKraus_action (X : PhysicalMatrix) : krausMap identityKraus X = X := by
  simp [krausMap, identityKraus]

/-- Identity preserves zero covariance of every distinct pair in an arbitrary complex product. -/
theorem identity_product_covariance (ρ : ProductInput) {u v : Wire} (huv : u ≠ v) :
    binaryOutcomeProb (pairEffect u v) (krausMap identityKraus ρ.state) -
      binaryOutcomeProb (singleEffect u) (krausMap identityKraus ρ.state) *
      binaryOutcomeProb (singleEffect v) (krausMap identityKraus ρ.state) = 0 := by
  rw [identityKraus_action, product_event_factorization ρ huv, sub_self]


/-- Three event error bounds force the stated quantitative covariance lower bound. -/
theorem covariance_polynomial_lower_bound {a b c δ : ℝ}
    (hb0 : 0 ≤ b) (hδ0 : 0 ≤ δ)
    (ha : |a - 1 / 2| ≤ δ) (hb : |b - 1 / 2| ≤ δ)
    (hc : |c - 1 / 2| ≤ δ) :
    1 / 4 - 2 * δ - δ ^ 2 ≤ c - a * b := by
  have hau := (abs_le.mp ha).2
  have hbu := (abs_le.mp hb).2
  have hcl := (abs_le.mp hc).1
  have hp : a * b ≤ (1 / 2 + δ) * (1 / 2 + δ) :=
    mul_le_mul (by linarith) (by linarith) hb0 (by linarith)
  nlinarith

theorem covariance_polynomial_positive {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10) :
    1 / 25 ≤ 1 / 4 - 2 * δ - δ ^ 2 := by
  have h := mul_nonneg (show 0 ≤ 1 / 10 - δ by linarith)
    (show 0 ≤ 21 / 10 + δ by linarith)
  nlinarith

/-- Actual binary effects distinguish any independent event pair from B4. -/
theorem independent_pair_traceDist_gt {X : PhysicalMatrix} (hX : IsDensityOperator X)
    (u v : Wire)
    (hfactor : binaryOutcomeProb (pairEffect u v) X =
      binaryOutcomeProb (singleEffect u) X * binaryOutcomeProb (singleEffect v) X) :
    1 / 10 < traceDist X B4 := by
  by_contra hn
  have hδ : traceDist X B4 ≤ 1 / 10 := le_of_not_gt hn
  have hδ0 := traceDist_nonneg X B4
  have ha := abs_binaryOutcomeProb_sub_le_traceDist (singleEffect_binary u) hX B4_density
  have hb := abs_binaryOutcomeProb_sub_le_traceDist (singleEffect_binary v) hX B4_density
  have hc := abs_binaryOutcomeProb_sub_le_traceDist (pairEffect_binary u v) hX B4_density
  rw [B4_single_probability] at ha hb
  rw [B4_pair_probability] at hc
  have hb0 := (binaryOutcomeProb_mem_Icc (singleEffect_binary v) hX).1
  have hl := covariance_polynomial_lower_bound hb0 hδ0 ha hb hc
  have hp := covariance_polynomial_positive hδ0 hδ
  rw [hfactor] at hl
  linarith

theorem product_traceDist_gt (ρ : ProductInput) : 1 / 10 < traceDist ρ.state B4 :=
  independent_pair_traceDist_gt ρ.state_density 0 1
    (product_event_factorization ρ (by decide))

theorem layer_traceDist_gt (L : Layer) (ρ : ProductInput) :
    1 / 10 < traceDist (L.action ρ.state) B4 := by
  obtain ⟨u, v, _, huv⟩ := different_blocks L.partition
  exact independent_pair_traceDist_gt (L.action_density ρ.state_density) u v
    (layer_event_factorization L ρ huv)

/-- Every chronological circuit of depth at most one stays strictly more than 1/10 from B4.
The input matrices may be complex and coherent, and every admitted partition is covered. -/
theorem shallow_traceDist_gt (ρ : ProductInput) (Ls : List Layer) (hdepth : depth Ls ≤ 1) :
    1 / 10 < traceDist (run Ls ρ.state) B4 := by
  cases Ls with
  | nil => exact product_traceDist_gt ρ
  | cons L Ls =>
    cases Ls with
    | nil => exact layer_traceDist_gt L ρ
    | cons M Ms => simp [depth] at hdepth

/-- The weak bound is a corollary of the strict shallow-depth obstruction. -/
theorem shallow_traceDist_ge (ρ : ProductInput) (Ls : List Layer) (hdepth : depth Ls ≤ 1) :
    1 / 10 ≤ traceDist (run Ls ρ.state) B4 :=
  (shallow_traceDist_gt ρ Ls hdepth).le

end SKEFTHawking.QuantumNetwork.FiniteLocalChannelDepthObstruction
