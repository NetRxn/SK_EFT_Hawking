import Mathlib

/-!
# The abstract SES → LES engine (zig-zag lemma) for ℕ-graded chain complexes

The project's singular machinery has integral long exact sequences only for *subspace pairs* and
*open Mayer–Vietoris covers*. The interlocking Smith sequences of a double cover
(`0 → A → C → B → 0` with `A = N·C`, `B = D·C` **abstract subcomplexes**, not subspace chains)
need the general tool: given a levelwise short exact sequence of ℕ-graded chain complexes of
`R`-modules

`0 → (M, dM) --f--> (N, dN) --g--> (P, dP) → 0`

(chain maps, `f` mono, `g` epi, `range f = ker g` levelwise), the homology modules
`Hml d n = cycles/boundaries` (degree-0 convention `cycles 0 = ⊤`, matching
`SingularHomologyInt.Homology`) fit into the long exact sequence

`… → Hml dM n → Hml dN n → Hml dP n --δ--> Hml dM (n−1) → …`

* `Hmap` — the induced map on homology of a chain map;
* `delta` — the connecting homomorphism (snake construction; all choices quotient out —
  `delta_mk_eq` is the choice-free computation rule);
* `exact_Hmap_Hmap`, `exact_Hmap_delta`, `exact_delta_Hmap` — the six-term exactness;
* `Hmap_surjective_deg_zero` — the degree-0 tail `H₀(N) ↠ H₀(P)`.

The base ring `R` is an abstract variable (instantiated at `ℤ` by the Smith solve) — this keeps
a single `Module R` instance path on every carrier and avoids the `ℤ`-module diamond
(`AddCommGroup.toIntModule` vs. a designated instance) entirely.

Consumers: the `H_*(ℝP³;ℤ)` Smith-sequence solve (`KummerRP3SmithSolve`) — and verbatim the
`Q = T⁴°/τ` transfer of the Kummer `b₂ = 22` accounting.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

namespace SKEFTHawking.ChainComplexLESInt

/-- Membership in `p.submoduleOf q` is ambient membership of the coercion (definitional). -/
theorem mem_submoduleOf {R A : Type} [Ring R] [AddCommGroup A] [Module R A]
    {p q : Submodule R A} {x : ↥q} : x ∈ p.submoduleOf q ↔ (x : A) ∈ p := Iff.rfl

variable {R : Type} [Ring R]
variable {M : ℕ → Type} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
variable {N : ℕ → Type} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
variable {P : ℕ → Type} [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]

/-! ## §0. Homology of an abstract ℕ-graded chain complex -/

/-- The cycles of an abstract complex; degree-0 convention `cycles 0 = ⊤`
(matches `SingularHomologyInt.cycles`). -/
def cycles (dM : ∀ n, M (n + 1) →ₗ[R] M n) : ∀ n, Submodule R (M n)
  | 0 => ⊤
  | m + 1 => LinearMap.ker (dM m)

/-- The boundaries of an abstract complex. -/
def boundaries (dM : ∀ n, M (n + 1) →ₗ[R] M n) (n : ℕ) : Submodule R (M n) :=
  LinearMap.range (dM n)

theorem mem_cycles_succ {dM : ∀ n, M (n + 1) →ₗ[R] M n} {m : ℕ} {z : M (m + 1)} :
    z ∈ cycles dM (m + 1) ↔ dM m z = 0 :=
  LinearMap.mem_ker

theorem mem_cycles_zero {dM : ∀ n, M (n + 1) →ₗ[R] M n} {z : M 0} : z ∈ cycles dM 0 :=
  Submodule.mem_top

/-- **Abstract homology** `Hₙ = ker ∂ₙ / im ∂ₙ₊₁` (same quotient shape as
`SingularHomologyInt.Homology`). -/
def Hml (dM : ∀ n, M (n + 1) →ₗ[R] M n) (n : ℕ) : Type :=
  (cycles dM n) ⧸ (boundaries dM n).submoduleOf (cycles dM n)

noncomputable instance (dM : ∀ n, M (n + 1) →ₗ[R] M n) (n : ℕ) : AddCommGroup (Hml dM n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (dM : ∀ n, M (n + 1) →ₗ[R] M n) (n : ℕ) : Module R (Hml dM n) :=
  inferInstanceAs (Module R (_ ⧸ _))

/-- The class projection `cycles → Hml`, bundled linearly. -/
noncomputable def Hml.mkHom (dM : ∀ n, M (n + 1) →ₗ[R] M n) (n : ℕ) :
    (cycles dM n) →ₗ[R] Hml dM n :=
  Submodule.mkQ ((boundaries dM n).submoduleOf (cycles dM n))

/-- The homology class of a cycle. -/
noncomputable def Hml.mk (dM : ∀ n, M (n + 1) →ₗ[R] M n) (n : ℕ) (z : cycles dM n) :
    Hml dM n :=
  Hml.mkHom dM n z

theorem Hml.mk_surjective (dM : ∀ n, M (n + 1) →ₗ[R] M n) (n : ℕ) :
    Function.Surjective (Hml.mk dM n) :=
  Submodule.mkQ_surjective _

/-- Class equality is boundary difference. -/
theorem Hml.mk_eq_mk_iff (dM : ∀ n, M (n + 1) →ₗ[R] M n) (n : ℕ) (z z' : cycles dM n) :
    Hml.mk dM n z = Hml.mk dM n z' ↔ (z : M n) - (z' : M n) ∈ boundaries dM n := by
  show Submodule.Quotient.mk z = Submodule.Quotient.mk z' ↔ _
  rw [Submodule.Quotient.eq]
  exact mem_submoduleOf

/-- Class vanishing is being a boundary. -/
theorem Hml.mk_eq_zero_iff (dM : ∀ n, M (n + 1) →ₗ[R] M n) (n : ℕ) (z : cycles dM n) :
    Hml.mk dM n z = 0 ↔ (z : M n) ∈ boundaries dM n := by
  show Submodule.Quotient.mk z = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_submoduleOf

/-! ## §1. Chain maps and induced maps on homology -/

variable {dM : ∀ n, M (n + 1) →ₗ[R] M n} {dN : ∀ n, N (n + 1) →ₗ[R] N n}
variable {dP : ∀ n, P (n + 1) →ₗ[R] P n}
variable {f : ∀ n, M n →ₗ[R] N n} {g : ∀ n, N n →ₗ[R] P n}

/-- A chain map sends cycles to cycles. -/
theorem map_mem_cycles (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    {n : ℕ} {z : M n} (hz : z ∈ cycles dM n) :
    f n z ∈ cycles dN n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
      rw [mem_cycles_succ, hf m z, mem_cycles_succ.mp hz, map_zero]

/-- The cycles-level restriction of a chain map. -/
noncomputable def cyclesMap
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x)) (n : ℕ) :
    (cycles dM n) →ₗ[R] (cycles dN n) :=
  (f n).restrict (fun _z hz => map_mem_cycles hf hz)

@[simp] theorem cyclesMap_coe
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x)) (n : ℕ)
    (z : cycles dM n) :
    (cyclesMap hf n z : N n) = f n (z : M n) := rfl

/-- **The induced map on abstract homology.** -/
noncomputable def Hmap
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x)) (n : ℕ) :
    Hml dM n →ₗ[R] Hml dN n :=
  Submodule.liftQ _ ((Hml.mkHom dN n).comp (cyclesMap hf n)) (by
    rintro z hz
    rw [mem_submoduleOf] at hz
    obtain ⟨w, hw⟩ := hz
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    show Hml.mk dN n (cyclesMap hf n z) = 0
    rw [Hml.mk_eq_zero_iff, cyclesMap_coe]
    exact ⟨f (n + 1) w, by rw [hf n w, hw]⟩)

@[simp] theorem Hmap_mk
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x)) (n : ℕ)
    (z : cycles dM n) :
    Hmap hf n (Hml.mk dM n z) = Hml.mk dN n (cyclesMap hf n z) := rfl

/-! ## §2. The connecting homomorphism of a levelwise SES of chain complexes -/

/-- `g ∘ f = 0` levelwise (from exactness). -/
theorem g_f_eq_zero (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    (n : ℕ) (x : M n) : g n (f n x) = 0 := by
  have h : f n x ∈ LinearMap.ker (g n) := by
    rw [← hexact n]
    exact ⟨x, rfl⟩
  exact LinearMap.mem_ker.mp h

/-- **The connecting well-definedness**: for a cycle `z ∈ Pₙ₊₁`, ANY `g`-preimage `y` and ANY
`f`-preimage `x` of `∂y` land in one homology class of `Mₙ` — the class is choice-free. -/
theorem connect_wd
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hfinj : ∀ n, Function.Injective (f n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    {n : ℕ} (z : P (n + 1))
    (y y' : N (n + 1)) (hy : g (n + 1) y = z) (hy' : g (n + 1) y' = z)
    (x x' : M n) (hx : f n x = dN n y) (hx' : f n x' = dN n y')
    (hxc : x ∈ cycles dM n) (hx'c : x' ∈ cycles dM n) :
    Hml.mk dM n ⟨x, hxc⟩ = Hml.mk dM n ⟨x', hx'c⟩ := by
  rw [Hml.mk_eq_mk_iff]
  show x - x' ∈ boundaries dM n
  have hyy : y - y' ∈ LinearMap.ker (g (n + 1)) := by
    rw [LinearMap.mem_ker, map_sub, hy, hy', sub_self]
  rw [← hexact (n + 1)] at hyy
  obtain ⟨w, hw⟩ := hyy
  refine ⟨w, hfinj n ?_⟩
  rw [← hf n w, hw, map_sub, map_sub, hx, hx']

/-- The chosen `g`-preimage of a chain. -/
noncomputable def pickY (hgsurj : ∀ n, Function.Surjective (g n)) {n : ℕ} (z : P n) : N n :=
  (hgsurj n z).choose

theorem g_pickY (hgsurj : ∀ n, Function.Surjective (g n)) {n : ℕ} (z : P n) :
    g n (pickY hgsurj z) = z := (hgsurj n z).choose_spec

/-- For a cycle `z`, `∂(pickY z)` is killed by `g`. -/
theorem g_d_pickY (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hgsurj : ∀ n, Function.Surjective (g n)) {n : ℕ} (z : cycles dP (n + 1)) :
    g n (dN n (pickY hgsurj (z : P (n + 1)))) = 0 := by
  rw [← hg n, g_pickY, mem_cycles_succ.mp z.2]

/-- The chosen `f`-preimage of `∂(pickY z)`. -/
noncomputable def pickX
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    {n : ℕ} (z : cycles dP (n + 1)) : M n :=
  (show dN n (pickY hgsurj (z : P (n + 1))) ∈ LinearMap.range (f n) by
    rw [hexact n]
    exact LinearMap.mem_ker.mpr (g_d_pickY hg hgsurj z)).choose

theorem f_pickX
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    {n : ℕ} (z : cycles dP (n + 1)) :
    f n (pickX hg hgsurj hexact z) = dN n (pickY hgsurj (z : P (n + 1))) :=
  (show dN n (pickY hgsurj (z : P (n + 1))) ∈ LinearMap.range (f n) by
    rw [hexact n]
    exact LinearMap.mem_ker.mpr (g_d_pickY hg hgsurj z)).choose_spec

theorem pickX_mem_cycles
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hddN : ∀ (n : ℕ) (x : N (n + 2)), dN n (dN (n + 1) x) = 0)
    (hfinj : ∀ n, Function.Injective (f n))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    {n : ℕ} (z : cycles dP (n + 1)) :
    pickX hg hgsurj hexact z ∈ cycles dM n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
      rw [mem_cycles_succ]
      apply hfinj m
      rw [← hf m, f_pickX, hddN, map_zero]

/-- The connecting value on a cycle (all choices quotient out, `connect_wd`). -/
noncomputable def deltaCyc
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hddN : ∀ (n : ℕ) (x : N (n + 2)), dN n (dN (n + 1) x) = 0)
    (hfinj : ∀ n, Function.Injective (f n))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    {n : ℕ} (z : cycles dP (n + 1)) : Hml dM n :=
  Hml.mk dM n ⟨pickX hg hgsurj hexact z, pickX_mem_cycles hf hg hddN hfinj hgsurj hexact z⟩

/-- The choice-free computation rule for `deltaCyc`. -/
theorem deltaCyc_eq
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hddN : ∀ (n : ℕ) (x : N (n + 2)), dN n (dN (n + 1) x) = 0)
    (hfinj : ∀ n, Function.Injective (f n))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    {n : ℕ} (z : cycles dP (n + 1))
    (y : N (n + 1)) (hy : g (n + 1) y = (z : P (n + 1)))
    (x : M n) (hx : f n x = dN n y) (hxc : x ∈ cycles dM n) :
    deltaCyc hf hg hddN hfinj hgsurj hexact z = Hml.mk dM n ⟨x, hxc⟩ :=
  connect_wd hf hfinj hexact (z : P (n + 1)) _ y (g_pickY hgsurj _) hy _ x
    (f_pickX hg hgsurj hexact z) hx _ hxc

theorem deltaCyc_add
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hddN : ∀ (n : ℕ) (x : N (n + 2)), dN n (dN (n + 1) x) = 0)
    (hfinj : ∀ n, Function.Injective (f n))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    {n : ℕ} (z z' : cycles dP (n + 1)) :
    deltaCyc hf hg hddN hfinj hgsurj hexact (z + z')
      = deltaCyc hf hg hddN hfinj hgsurj hexact z
        + deltaCyc hf hg hddN hfinj hgsurj hexact z' := by
  have hy : g (n + 1) (pickY hgsurj (z : P (n + 1)) + pickY hgsurj (z' : P (n + 1)))
      = ((z + z' : cycles dP (n + 1)) : P (n + 1)) := by
    rw [map_add, g_pickY, g_pickY]
    rfl
  have hx : f n (pickX hg hgsurj hexact z + pickX hg hgsurj hexact z')
      = dN n (pickY hgsurj (z : P (n + 1)) + pickY hgsurj (z' : P (n + 1))) := by
    rw [map_add, map_add, f_pickX, f_pickX]
  rw [deltaCyc_eq hf hg hddN hfinj hgsurj hexact (z + z') _ hy _ hx
    (Submodule.add_mem _ (pickX_mem_cycles hf hg hddN hfinj hgsurj hexact z)
      (pickX_mem_cycles hf hg hddN hfinj hgsurj hexact z'))]
  show Hml.mkHom dM n _ = Hml.mkHom dM n _ + Hml.mkHom dM n _
  rw [← map_add]
  congr 1

theorem deltaCyc_smul
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hddN : ∀ (n : ℕ) (x : N (n + 2)), dN n (dN (n + 1) x) = 0)
    (hfinj : ∀ n, Function.Injective (f n))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    {n : ℕ} (a : R) (z : cycles dP (n + 1)) :
    deltaCyc hf hg hddN hfinj hgsurj hexact (a • z)
      = a • deltaCyc hf hg hddN hfinj hgsurj hexact z := by
  have hy : g (n + 1) (a • pickY hgsurj (z : P (n + 1)))
      = ((a • z : cycles dP (n + 1)) : P (n + 1)) := by
    rw [LinearMap.map_smul, g_pickY]
    rfl
  have hx : f n (a • pickX hg hgsurj hexact z)
      = dN n (a • pickY hgsurj (z : P (n + 1))) := by
    rw [LinearMap.map_smul, LinearMap.map_smul, f_pickX]
  rw [deltaCyc_eq hf hg hddN hfinj hgsurj hexact (a • z) _ hy _ hx
    (Submodule.smul_mem _ a (pickX_mem_cycles hf hg hddN hfinj hgsurj hexact z))]
  show Hml.mkHom dM n _ = a • Hml.mkHom dM n _
  rw [← LinearMap.map_smul]
  congr 1

/-- The connecting homomorphism on cycles, bundled. -/
noncomputable def deltaCycHom
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hddN : ∀ (n : ℕ) (x : N (n + 2)), dN n (dN (n + 1) x) = 0)
    (hfinj : ∀ n, Function.Injective (f n))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    (n : ℕ) : (cycles dP (n + 1)) →ₗ[R] Hml dM n where
  toFun := deltaCyc hf hg hddN hfinj hgsurj hexact
  map_add' z z' := deltaCyc_add hf hg hddN hfinj hgsurj hexact z z'
  map_smul' a z := deltaCyc_smul hf hg hddN hfinj hgsurj hexact a z

/-- **The connecting homomorphism** `δ : Hₙ₊₁(P) → Hₙ(M)` of the SES of chain complexes. -/
noncomputable def delta
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hddN : ∀ (n : ℕ) (x : N (n + 2)), dN n (dN (n + 1) x) = 0)
    (hfinj : ∀ n, Function.Injective (f n))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    (n : ℕ) : Hml dP (n + 1) →ₗ[R] Hml dM n :=
  Submodule.liftQ _ (deltaCycHom hf hg hddN hfinj hgsurj hexact n) (by
    rintro z hz
    rw [mem_submoduleOf] at hz
    obtain ⟨w, hw⟩ := hz
    rw [LinearMap.mem_ker]
    show deltaCyc hf hg hddN hfinj hgsurj hexact z = 0
    have hyz : g (n + 1) (dN (n + 1) (pickY hgsurj w)) = (z : P (n + 1)) := by
      rw [← hg (n + 1), g_pickY, hw]
    have hx : f n (0 : M n) = dN n (dN (n + 1) (pickY hgsurj w)) := by
      rw [map_zero, hddN]
    rw [deltaCyc_eq hf hg hddN hfinj hgsurj hexact z _ hyz 0 hx (Submodule.zero_mem _)]
    rw [Hml.mk_eq_zero_iff]
    exact Submodule.zero_mem _)

/-- **The choice-free computation rule for `δ`** — the instantiation workhorse: to compute
`δ[z]`, produce ANY `g`-preimage `y` of `z` and ANY `f`-preimage `x` of `∂y`. -/
theorem delta_mk_eq
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hddN : ∀ (n : ℕ) (x : N (n + 2)), dN n (dN (n + 1) x) = 0)
    (hfinj : ∀ n, Function.Injective (f n))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    {n : ℕ} (z : cycles dP (n + 1))
    (y : N (n + 1)) (hy : g (n + 1) y = (z : P (n + 1)))
    (x : M n) (hx : f n x = dN n y) (hxc : x ∈ cycles dM n) :
    delta hf hg hddN hfinj hgsurj hexact n (Hml.mk dP (n + 1) z)
      = Hml.mk dM n ⟨x, hxc⟩ := by
  show deltaCyc hf hg hddN hfinj hgsurj hexact z = _
  exact deltaCyc_eq hf hg hddN hfinj hgsurj hexact z y hy x hx hxc

/-! ## §3. The six-term exactness -/

/-- **Exactness at `Hₙ(N)`**: `ker H(g) = im H(f)`. -/
theorem exact_Hmap_Hmap
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hddN : ∀ (n : ℕ) (x : N (n + 2)), dN n (dN (n + 1) x) = 0)
    (hfinj : ∀ n, Function.Injective (f n))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    (n : ℕ) :
    Function.Exact (Hmap hf n) (Hmap hg n) := by
  intro yh
  obtain ⟨y, rfl⟩ := Hml.mk_surjective dN n yh
  constructor
  · intro h0
    rw [Hmap_mk, Hml.mk_eq_zero_iff] at h0
    obtain ⟨w, hw⟩ := h0
    have hw' : dP n w = g n (y : N n) := hw
    obtain ⟨v, hv⟩ := hgsurj (n + 1) w
    have hker : g n ((y : N n) - dN n v) = 0 := by
      rw [map_sub, ← hg n, hv, hw', sub_self]
    obtain ⟨x, hx⟩ : (y : N n) - dN n v ∈ LinearMap.range (f n) := by
      rw [hexact n]
      exact LinearMap.mem_ker.mpr hker
    have hxc : x ∈ cycles dM n := by
      cases n with
      | zero => exact Submodule.mem_top
      | succ m =>
          rw [mem_cycles_succ]
          apply hfinj m
          rw [← hf m, hx, map_zero, map_sub, mem_cycles_succ.mp y.2, hddN, sub_self]
    refine ⟨Hml.mk dM n ⟨x, hxc⟩, ?_⟩
    rw [Hmap_mk, Hml.mk_eq_mk_iff]
    show f n x - (y : N n) ∈ boundaries dN n
    rw [hx]
    exact ⟨-v, by rw [map_neg]; abel⟩
  · rintro ⟨xh, hxh⟩
    obtain ⟨x, rfl⟩ := Hml.mk_surjective dM n xh
    rw [← hxh, Hmap_mk, Hmap_mk, Hml.mk_eq_zero_iff]
    show g n (f n (x : M n)) ∈ boundaries dP n
    rw [g_f_eq_zero hexact]
    exact Submodule.zero_mem _

/-- **Exactness at `Hₙ₊₁(P)`**: `ker δ = im H(g)`. -/
theorem exact_Hmap_delta
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hddN : ∀ (n : ℕ) (x : N (n + 2)), dN n (dN (n + 1) x) = 0)
    (hfinj : ∀ n, Function.Injective (f n))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    (n : ℕ) :
    Function.Exact (Hmap hg (n + 1)) (delta hf hg hddN hfinj hgsurj hexact n) := by
  intro zh
  obtain ⟨z, rfl⟩ := Hml.mk_surjective dP (n + 1) zh
  constructor
  · intro h0
    -- δ[z] = 0: the chosen x is a boundary x = ∂w; then y − f(w) is a cycle over z
    have h1 : deltaCyc hf hg hddN hfinj hgsurj hexact z = 0 := h0
    rw [deltaCyc, Hml.mk_eq_zero_iff] at h1
    obtain ⟨w, hw⟩ := h1
    have hw' : dM n w = pickX hg hgsurj hexact z := hw
    set y := pickY hgsurj (z : P (n + 1)) with hydef
    have hcyc : (y - f (n + 1) w) ∈ cycles dN (n + 1) := by
      rw [mem_cycles_succ, map_sub, hf n w, hw', f_pickX, sub_self]
    refine ⟨Hml.mk dN (n + 1) ⟨y - f (n + 1) w, hcyc⟩, ?_⟩
    rw [Hmap_mk]
    have hcm : cyclesMap hg (n + 1) ⟨y - f (n + 1) w, hcyc⟩ = z := by
      apply Subtype.ext
      show g (n + 1) (y - f (n + 1) w) = (z : P (n + 1))
      rw [map_sub, g_f_eq_zero hexact, sub_zero, hydef, g_pickY]
    rw [hcm]
  · rintro ⟨yh, hyh⟩
    obtain ⟨y, rfl⟩ := Hml.mk_surjective dN (n + 1) yh
    rw [← hyh, Hmap_mk]
    have hgy : g (n + 1) (y : N (n + 1))
        = ((cyclesMap hg (n + 1) y : cycles dP (n + 1)) : P (n + 1)) := rfl
    have hx : f n 0 = dN n (y : N (n + 1)) := by
      rw [map_zero, mem_cycles_succ.mp y.2]
    rw [delta_mk_eq hf hg hddN hfinj hgsurj hexact _ _ hgy 0 hx (Submodule.zero_mem _)]
    rw [Hml.mk_eq_zero_iff]
    exact Submodule.zero_mem _

/-- **Exactness at `Hₙ(M)`**: `ker H(f) = im δ`. -/
theorem exact_delta_Hmap
    (hf : ∀ (n : ℕ) (x : M (n + 1)), dN n (f (n + 1) x) = f n (dM n x))
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hddN : ∀ (n : ℕ) (x : N (n + 2)), dN n (dN (n + 1) x) = 0)
    (hfinj : ∀ n, Function.Injective (f n))
    (hgsurj : ∀ n, Function.Surjective (g n))
    (hexact : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    (n : ℕ) :
    Function.Exact (delta hf hg hddN hfinj hgsurj hexact n) (Hmap hf n) := by
  intro xh
  obtain ⟨x, rfl⟩ := Hml.mk_surjective dM n xh
  constructor
  · intro h0
    rw [Hmap_mk, Hml.mk_eq_zero_iff] at h0
    obtain ⟨y, hy⟩ := h0
    have hy' : dN n y = f n (x : M n) := hy
    -- z := g y is a cycle in P with δ[z] = [x]
    have hzc : g (n + 1) y ∈ cycles dP (n + 1) := by
      rw [mem_cycles_succ, hg n, hy', g_f_eq_zero hexact]
    refine ⟨Hml.mk dP (n + 1) ⟨g (n + 1) y, hzc⟩, ?_⟩
    have h2 := delta_mk_eq hf hg hddN hfinj hgsurj hexact
      (⟨g (n + 1) y, hzc⟩ : cycles dP (n + 1)) y rfl (x : M n) hy'.symm x.2
    rw [h2]
  · rintro ⟨zh, hzh⟩
    obtain ⟨z, rfl⟩ := Hml.mk_surjective dP (n + 1) zh
    rw [← hzh]
    show Hmap hf n (deltaCyc hf hg hddN hfinj hgsurj hexact z) = 0
    rw [deltaCyc, Hmap_mk, Hml.mk_eq_zero_iff]
    show f n (pickX hg hgsurj hexact z) ∈ boundaries dN n
    rw [f_pickX]
    exact ⟨pickY hgsurj (z : P (n + 1)), rfl⟩

/-- **The degree-0 tail**: `H₀(N) ↠ H₀(P)` (every degree-0 chain is a cycle, `g` is epi). -/
theorem Hmap_surjective_deg_zero
    (hg : ∀ (n : ℕ) (x : N (n + 1)), dP n (g (n + 1) x) = g n (dN n x))
    (hgsurj : ∀ n, Function.Surjective (g n)) :
    Function.Surjective (Hmap hg 0) := by
  intro zh
  obtain ⟨z, rfl⟩ := Hml.mk_surjective dP 0 zh
  obtain ⟨y, hy⟩ := hgsurj 0 (z : P 0)
  refine ⟨Hml.mk dN 0 ⟨y, Submodule.mem_top⟩, ?_⟩
  rw [Hmap_mk]
  congr 1
  exact Subtype.ext hy

end SKEFTHawking.ChainComplexLESInt
