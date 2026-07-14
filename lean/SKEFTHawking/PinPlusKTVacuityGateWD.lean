/-
# Phase 5q.H W-D VACUITY GATE (round 3) — KERNEL-CHECKED EXPLOIT: `KTNonSplit` is FALSE
# on the as-built CharPair carrier, for EVERY W-admissibility provider.

**Gate finding (vector b / c of the W-D adversarial gate).** The W-D statement layer
(`PinPlusKTExtension.lean`) treats `KTNonSplit prov : 8 • [ℝP⁴] ≠ 0` as the open non-split bit
(dossier §5: "the one KT terminal Prop with a genuinely open attack surface"). This module proves
the attack LANDS: `8 • [ℝP⁴] = 0` is derivable with ZERO geometric input, so `KTNonSplit prov` is
REFUTED for every `prov`, and the headline assembly `kt_equiv_zmod16`'s hypothesis pair
`{KTKernelCard, KTNonSplit}` is UNSATISFIABLE on this carrier.

**The mechanism (why the carrier admits this).** `CharPairBor.L` is a FREE field — the membrane
tie (design item 2/3: `L = ker(H₁(∂Q) → H₁(Q))` of an actual characteristic membrane `Q ⊆ W`,
plus the relative characteristic condition) is deferred to wt3. So ANY metabolic Lagrangian of the
joint enhancement furnishes a `CharPairBor`, whether or not any membrane realizes it. The
anti-collapse engine (`brown_eq_of_taylorLeg_lagrangian`) only obstructs bordisms whose joint
enhancement has `brown ≠ 0` — i.e. the relation enforces exactly Witt-class equality (mod-8), not
Pin⁺ bordism. Consequently the UN-reversed double `σ ⊔ σ` bounds the plain cylinder
(`doublingBordism`) as soon as `brown(q_σ) ∈ {0, 4}`:

* take `σ₄ := [ℝP⁴]⁴` (the 4-fold `sumStr` of the honest witness, `brown(q₄) = 4`);
* the joint form of the doubling is `(q₄ ⊕ q₄) ⊕ (−0) ` with `brown = 8 = 0 ∈ ZMod 8`;
* an explicit metabolic Lagrangian exists: the GRAPH of the linear isometry
  `φ : x ↦ x + (∑ x)·𝟙` on `Fin 4 → ZMod 2` (matrix `J + I`), which satisfies
  `q₄(φ x) = −q₄(x)` — its graph is (a reindex of) the extended Hamming code `e₈`, the
  self-dual doubly-even `[8,4,4]` code. The in-tree engine `graphSub_metabolic` certifies it;
* `w₂(W) = 0`-admissibility (`P14`/`P23`/`hwu`) comes from the provider itself — the provider
  quantifies over ALL bordisms, and `W = (ℝP⁴)⁴ × I` here is honestly `w₂ = 0`, so even the
  intended honest provider supplies it. The exploit does NOT need a degenerate provider.

**What this kills.** `negBor` (the honest inverse law) kills `σ̄ ⊔ σ`; the L-freedom ALSO kills
`σ ⊔ σ` whenever `2·brown(q_σ) = 0`. Hence on this carrier `⟨[ℝP⁴]⟩ ≅ ℤ/8`, NOT ℤ/16:
`addOrderOf [ℝP⁴] ∣ 8` (corollary below), directly contradicting the conditional
`kt_rp4_addOrderOf = 16`. The `{0,8}` kernel distinction the KT §5 extension needs is not merely
invisible to `(Σ, q)` — on the as-built relation it is provably COLLAPSED. The fix is statement/
carrier-shape work, not proof work: the kernel Props must be stated over a carrier whose `Bor`
carries the membrane tie (item 2/3) — L pinned to an actual `ker(H₁(∂Q) → H₁(Q))` — otherwise any
future "discharge" of `KTNonSplit` is impossible (it is false), and `kt_equiv_zmod16` is vacuous.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTExtension

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.RP4CharPairWitness
open SKEFTHawking.RP4Witness
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTExtension

namespace SKEFTHawking.PinPlusKTVacuityGateWD

/-! ## §1. The `J + I` isometry `φ(x) = x + (∑ x)·𝟙` — `q₄ ∘ φ = −q₄` with the same polar form

On `Fin 4 → ZMod 2`, `φ` adds the total parity to every coordinate: weight-1 vectors map to
weight-3 (`3 ≡ 3·1 mod 4`), weight-2 to weight-2 (`2 ≡ 3·2 mod 4`), weight-3 to weight-1
(`1 ≡ 3·3 mod 4`), weight-4 to weight-4 (`0 ≡ 3·4 mod 4`) — exactly `q ↦ 3q = −q` on the rank-4
standard form. It is a `B`-isometry (`(J+I)ᵀ(J+I) = I` over `F₂` in rank 4) and an involution. -/

/-- `φ(x) i = x i + ∑ⱼ x j` — the `J + I` matrix on `Fin 4 → ZMod 2`. -/
def phiFun : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) := fun x i => x i + ∑ j, x j

lemma phiFun_invol : ∀ x, phiFun (phiFun x) = x := by decide

lemma phiFun_add : ∀ x y, phiFun (x + y) = phiFun x + phiFun y := by decide

/-- `φ` as a `ZMod 2`-linear equivalence (an involution). -/
def phiLin : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) where
  toFun := phiFun
  invFun := phiFun
  left_inv := phiFun_invol
  right_inv := phiFun_invol
  map_add' := phiFun_add
  map_smul' := by decide

/-! ## §2. The concrete 4-fold `ℝP⁴` structure (balanced tree) and its rank-4 enhancement -/

/-- The balanced 4-fold disjoint union `(ℝP⁴ ⊔ ℝP⁴) ⊔ (ℝP⁴ ⊔ ℝP⁴)`. -/
noncomputable def s4M : SingularManifold.{0} PUnit.{1} 0 (𝓡 4) :=
  (rp4SM.sum rp4SM).sum (rp4SM.sum rp4SM)

/-- The balanced 4-fold `sumStr` of the honest `ℝP⁴` char-pair witness — the representative of
`(2 • [ℝP⁴]) + (2 • [ℝP⁴]) = 4 • [ℝP⁴]`. Its enhancement has `brown = 4`. -/
noncomputable def sig4 : CharPairStrBundled (𝓡 4) s4M :=
  charPairBundledSumStr (charPairBundledSumStr rp4CharPair rp4CharPair)
    (charPairBundledSumStr rp4CharPair rp4CharPair)

/-- The rank-4 enhancement carried by `sig4` (defeq to nested `orthSum`/`reindex` of
`stdQuadratic 1`; the `Fin 4` ascription pins `(1+1)+(1+1) ≡ 4`). -/
noncomputable def q4 : Z4Quadratic (Fin 4) := sig4.toCharPairStr.q

/-- **`φ` negates `q₄`**: `(−q₄)(φ a) = q₄(a)` — the isometry `q₄ ≅ −q₄` (finite check). -/
lemma hq_phi : ∀ a, (Z4Quadratic.neg q4).q (phiFun a) = q4.q a := by decide

/-- **`φ` preserves the polar form** (`neg` keeps `B`; `J+I` is `B`-orthogonal in rank 4). -/
lemma hB_phi : ∀ a a', (Z4Quadratic.neg q4).B (phiFun a) (phiFun a') = q4.B a a' := by decide

/-- `Z4Quadratic` double negation is the identity (`−(−q) = q`, same polar form). -/
lemma z4_neg_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι) :
    Z4Quadratic.neg (Z4Quadratic.neg Q) = Q :=
  z4_ext (funext fun _ => neg_neg _) rfl

/-! ## §3. The fake membrane kernel — the graph of `φ` is metabolic for the UN-negated `q₄ ⊞ q₄`

This is the exploit's heart: `orthSum q₄ q₄ = orthSum q₄ (neg (neg q₄))`, and the graph of the
`q₄ ≅ neg q₄` isometry `φ` is a metabolic Lagrangian by the in-tree engine `graphSub_metabolic`.
(Concretely the graph `{(a, φ a)}` is a copy of the extended Hamming code `e₈` — self-dual,
doubly-even — inside `F₂⁸`.) NO membrane in `(ℝP⁴)⁴ × I` realizes this Lagrangian; the carrier
accepts it because `CharPairBor.L` is untethered (item 2/3 deferral). -/

/-- The graph Lagrangian is metabolic for the un-negated doubled form `q₄ ⊞ q₄`. -/
lemma L44_metabolic :
    IsMetabolic (Z4Quadratic.orthSum q4 q4) (graphSub phiLin) := by
  have h := graphSub_metabolic (qσ := q4) (qτ := Z4Quadratic.neg q4) phiLin hq_phi hB_phi
  rwa [z4_neg_neg] at h

/-! ## §4. The killer `CharPairBor`: the UN-reversed double `σ₄ ⊔ σ₄` bounds the plain cylinder -/

/-- **The exploit witness**: a full `CharPairBor` on `doublingBordism s4M` between
`sumStr σ₄ σ₄` (NOT `sumStr (revStr σ₄) σ₄`!) and the empty structure. Assembled from
`graphSub_metabolic` (§3) transported by the in-tree `IsMetabolic.reindex`/`.orthSum` engines,
with item-1 admissibility drawn from the provider (as every op witness draws it). -/
noncomputable def doubleKillerBor (prov : CharPairWProvider (𝓡 4) 0) :
    CharPairBor (doublingBordism s4M)
      (charPairSumStr sig4.toCharPairStr sig4.toCharPairStr) charPairEmptyStr :=
  have hSe : IsMetabolic (Z4Quadratic.neg (stdQuadratic 0))
      (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)) :=
    ⟨fun l _ => by rw [Subsingleton.elim l 0]; exact (Z4Quadratic.neg (stdQuadratic 0)).q_zero,
     fun _ _ => Submodule.mem_top⟩
  have hSs : IsMetabolic (charPairSumStr sig4.toCharPairStr sig4.toCharPairStr).q
      ((graphSub phiLin).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv)) :=
    L44_metabolic.reindex finSumFinEquiv
  have hmeta := hSs.orthSum hSe
  mkCharPairBor prov (doublingBordism s4M)
    (by
      haveI : T2Space rp4SM.M := rp4CharPair.toCharPairStr.t2
      exact inferInstanceAs
        (T2Space (((rp4SM.M ⊕ rp4SM.M) ⊕ (rp4SM.M ⊕ rp4SM.M)) × Set.Icc (0 : ℝ) 1)))
    (blockSub ((graphSub phiLin).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv))
      (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)))
    hmeta.1 hmeta.2

/-! ## §4.5. THE ROUND-4.5 SELF-ATTACK — the exploit REPLAYS on the membrane-TIED carrier through
a SYNTHETIC `bInc` (the honest-intermediate residual, named and kernel-encoded by the lead)

The arm-4 re-gate migration moved the live carrier onto `CharPairBorTied` (`L = ker mem.bInc`,
never a free submodule). That kills the round-3 "write any submodule into `L`" exploit shape — but
`GeoMembrane.bInc` is itself still an un-tethered linear-map field (the geometric realization by an
actual compact-T2 membrane `Q ⊆ W` is the named in-flight obligation), and the `graphSub`-defining
map has kernel EXACTLY the e₈ graph. So the exploit replays through a synthetic membrane datum:
the tie NARROWS the hole to precisely the realization obligation — it does not close it. The §5
refutations below therefore PERSIST on the migrated carrier (riding `doubleKillerBorTied`), the
W-D binders stay FROZEN, and the discharge path is the realization strengthening
(`GeoRealizationData`/`GeoMembrane.ofGeometric` — the wt2 seam) followed by the fresh re-gate. -/

/-- **The SYNTHETIC doubling `bInc`**: `graphBInc phiLin` (whose kernel is the e₈ graph,
definitionally) transported to the `sumStr`-reindexed doubling domain — `negBorBInc`'s shape with
the honest fold `cylBd` replaced by the e₈ graph map. Type-checks because `bInc` is (still)
un-tethered to an actual membrane. -/
noncomputable def doubleKillerBInc :
    (Fin (4 + 4) ⊕ Fin 0 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  (graphBInc phiLin).comp
    ((LinearMap.funLeft (ZMod 2) (ZMod 2) (finSumFinEquiv (m := 4) (n := 4))).comp
      (LinearMap.funLeft (ZMod 2) (ZMod 2) (Sum.inl : Fin (4 + 4) → Fin (4 + 4) ⊕ Fin 0)))

/-- The synthetic `bInc`'s computed kernel is exactly the free exploit's Lagrangian — the
reindexed e₈ graph, block-summed with the empty τ-end. -/
theorem doubleKillerBInc_ker :
    LinearMap.ker doubleKillerBInc
      = blockSub ((graphSub phiLin).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv))
          (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)) := by
  ext x
  rw [LinearMap.mem_ker, mem_blockSub, Submodule.mem_comap, graphSub, LinearMap.mem_ker]
  constructor
  · intro h; exact ⟨h, Submodule.mem_top⟩
  · intro h; exact h.1

/-- **The exploit witness, REPLAYED on the tied carrier**: a full `CharPairBorTied` on
`doublingBordism s4M` between `sumStr σ₄ σ₄` (UN-reversed!) and the empty structure, via the
synthetic e₈ membrane datum. The metabolic content is verbatim `doubleKillerBor`'s. -/
noncomputable def doubleKillerBorTied (prov : CharPairWProvider (𝓡 4) 0) :
    CharPairBorTied (doublingBordism s4M)
      (charPairSumStr sig4.toCharPairStr sig4.toCharPairStr) charPairEmptyStr :=
  have hSe : IsMetabolic (Z4Quadratic.neg (stdQuadratic 0))
      (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)) :=
    ⟨fun l _ => by rw [Subsingleton.elim l 0]; exact (Z4Quadratic.neg (stdQuadratic 0)).q_zero,
     fun _ _ => Submodule.mem_top⟩
  have hSs : IsMetabolic (charPairSumStr sig4.toCharPairStr sig4.toCharPairStr).q
      ((graphSub phiLin).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv)) :=
    L44_metabolic.reindex finSumFinEquiv
  have hmeta := hSs.orthSum hSe
  mkCharPairBorTied prov (doublingBordism s4M)
    (by
      haveI : T2Space rp4SM.M := rp4CharPair.toCharPairStr.t2
      exact inferInstanceAs
        (T2Space (((rp4SM.M ⊕ rp4SM.M) ⊕ (rp4SM.M ⊕ rp4SM.M)) × Set.Icc (0 : ℝ) 1)))
    ⟨_, doubleKillerBInc⟩
    (by show TaylorLegVanishes _ _ (LinearMap.ker doubleKillerBInc)
        rw [doubleKillerBInc_ker]; exact hmeta.1)
    (by show JointLagrangian _ _ (LinearMap.ker doubleKillerBInc)
        rw [doubleKillerBInc_ker]; exact hmeta.2)

/-! ## §5. THE REFUTATION — `8 • [ℝP⁴] = 0` for every provider (PERSISTS post-migration: the
statements are over the LIVE carrier — tied since the arm-4 re-gate migration — and ride the
§4.5 synthetic replay; the free-shape exploit `doubleKillerBor` (§4) is retained as the round-3
registry record) -/

/-- **`k₀ = 8 • [ℝP⁴] = 0` on the as-built carrier, for EVERY W-admissibility provider** — the
W-D non-split bit is FALSE, with zero geometric input beyond the in-tree witnesses. -/
theorem ktKernelRep_eq_zero (prov : CharPairWProvider (𝓡 4) 0) :
    ktKernelRep prov = 0 := by
  have hT2W : T2Space (doublingBordism s4M).W := by
    haveI : T2Space rp4SM.M := rp4CharPair.toCharPairStr.t2
    exact inferInstanceAs
      (T2Space (((rp4SM.M ⊕ rp4SM.M) ⊕ (rp4SM.M ⊕ rp4SM.M)) × Set.Icc (0 : ℝ) 1))
  have key : T2DataBordismGrp.mk (pinPlusCharPairData prov)
        ⟨s4M.sum s4M, charPairBundledSumStr sig4 sig4⟩
      = (0 : T2DataBordismGrp (pinPlusCharPairData prov)) :=
    T2DataBordismGrp.mk_eq_of_bordant _
      ⟨doublingBordism s4M, hT2W, ⟨⟨doubleKillerBorTied prov⟩⟩⟩
  show (8 : ℕ) • ktRP4Class prov = 0
  have h84 : (8 : ℕ) • ktRP4Class prov
      = (4 : ℕ) • ktRP4Class prov + (4 : ℕ) • ktRP4Class prov := by
    rw [← add_nsmul]
  have h42 : (4 : ℕ) • ktRP4Class prov
      = (2 : ℕ) • ktRP4Class prov + (2 : ℕ) • ktRP4Class prov := by
    rw [← add_nsmul]
  have h2 : (2 : ℕ) • ktRP4Class prov = ktRP4Class prov + ktRP4Class prov :=
    two_nsmul _
  rw [h84, h42, h2]
  exact key

/-- **`KTNonSplit` is REFUTED for every provider** — the "genuinely open" bit is not open. -/
theorem ktNonSplit_false (prov : CharPairWProvider (𝓡 4) 0) : ¬ KTNonSplit prov :=
  fun h => h (ktKernelRep_eq_zero prov)

/-- **The headline assembly's hypothesis pair is UNSATISFIABLE**: no discharge of
`{KTKernelCard, KTNonSplit}` can ever exist on this carrier, so `kt_equiv_zmod16` is vacuous. -/
theorem kt_binders_unsatisfiable (prov : CharPairWProvider (𝓡 4) 0) :
    ¬ (KTKernelCard prov ∧ KTNonSplit prov) :=
  fun h => ktNonSplit_false prov h.2

/-- **The Kummer-target shape (option 1) is unsatisfiable for every candidate `κ`**: any
`KTNonSplitKummerTarget` witness would make `κ = k₀ = 0` yet `κ ≠ 0`. -/
theorem ktKummerTarget_unsatisfiable (prov : CharPairWProvider (𝓡 4) 0)
    (κ : T2DataBordismGrp (pinPlusCharPairData prov)) :
    ¬ KTNonSplitKummerTarget prov κ := by
  rintro ⟨_, hκ, hrep⟩
  exact hκ (by rw [← hrep, ktKernelRep_eq_zero])

/-- **`addOrderOf [ℝP⁴] ∣ 8` on the as-built carrier** — the odd generator has order dividing 8
(and exactly 8, by `charPairBrown [ℝP⁴] = 1`): the carrier's cyclic part is ℤ/8, NOT ℤ/16.
Directly contradicts the conditional `kt_rp4_addOrderOf = 16` — confirming its hypotheses can
never be discharged. -/
theorem ktRP4Class_addOrderOf_dvd_eight (prov : CharPairWProvider (𝓡 4) 0) :
    addOrderOf (ktRP4Class prov) ∣ 8 :=
  addOrderOf_dvd_of_nsmul_eq_zero (ktKernelRep_eq_zero prov)

/-! ## §6. SECONDARY EXHIBIT — ✅ CLOSED BY `hchar` (arm-4 R1, 2026-07-14)

**Historical finding (vector b, honest-semantics):** the free `(n, q)` fields admitted a FAKE
rank-0 structure `fakeRP4RankZero` on ℝP⁴ itself — honest cert, EMPTY "characteristic surface",
`n = 0` — a geometrically impossible char pair (`w₂ + w₁² = x² ≠ 0` on ℝP⁴ forces a NON-empty
characteristic surface). It lay in `ker(charPairBrown)` while honestly `∉ {0, k₀}` (its underlying
manifold has `w₁⁴[ℝP⁴] = 1 ≠ 0`), so `KTKernelCard` as stated quantified over fake classes. The
round-5 (n, q, surf) BASIS tie did NOT exclude it (the empty surface's tie is degenerate-but-
honest: `surfClass = 0`, `q.B = 0 = ⟨·,0⟩`).

**The closure:** the arm-4 R1 **characteristic-surface tie `hchar`**
(`⟨a, emb₊[Σ]⟩ = μ(a ⌣ a)`, `Nonempty`-guarded, on `CharPairStrBundled`) makes the exhibit
UNINHABITABLE — `fakeRP4RankZero` no longer type-checks (it cannot supply `hchar`), and this is a
THEOREM, not just a failed elaboration: `RP4CharPairWitness.rp4_bundle_surfClass_pushforward_ne_zero`
(`⟨x², emb₊[Σ]⟩ = μ(x²⌣x²) = 1` forces `emb₊[Σ] ≠ 0` for EVERY ℝP⁴ bundle) and its corollary
`RP4CharPairWitness.no_empty_surface_bundle_on_rp4` (`Σ = ∅ ⟹ False`). The kernel Props no longer
quantify over empty-surface fakes on ℝP⁴; the fake def and its kernel-membership record are removed
with this closure. (The §5 SYNTHETIC-`bInc` refutations are UNAFFECTED — `doubleKillerBorTied`
rides honest sum-witnesses, which now carry `hchar` compositionally; the W-D binders stay FROZEN on
the `bInc` geometric-realization obligation, §4.5.) -/

end SKEFTHawking.PinPlusKTVacuityGateWD
