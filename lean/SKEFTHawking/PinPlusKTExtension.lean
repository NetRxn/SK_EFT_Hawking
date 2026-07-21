/-
# Phase 5q.H W-D (completeness OPENER — STATEMENT LAYER) — the KT §5 extension on
# the honest CharPair carrier

⛔ GATE VERDICT (W-D vacuity gate round 3, 2026-07-13, kernel-checked — `PinPlusKTVacuityGateWD` +
no-go `free-membrane-kernel-kills-nonsplit`): on the AS-BUILT carrier (membrane kernel `L` a free
field), `KTNonSplit` is FALSE for every provider (`ktNonSplit_false`: the e₈-graph Lagrangian kills
`8•[ℝP⁴]`) and the binder pair `{KTKernelCard, KTNonSplit}` is jointly UNSATISFIABLE
(`kt_binders_unsatisfiable`). The assembly algebra below (`kt_equiv_zmod16` etc.) is sound and
SURVIVES the carrier fix; do NOT attempt to discharge the binders until `CharPairBor` carries the
certified membrane `Q` with `L` COMPUTED as `ker(H₁(∂Q)→H₁(Q))` + the relative characteristic tie
(the frozen v4 item-2/3 spec), after which the layer must be RE-GATED. `KTKernelCard` additionally
quantified over hchar-untethered classes (`fakeRP4RankZero`) — ✅ CLOSED (arm-4 R1, 2026-07-14): the
`hchar` characteristic-surface tie landed on `CharPairStrBundled`; the fake exhibit is uninhabitable
(`RP4CharPairWitness.no_empty_surface_bundle_on_rp4`, backed by
`rp4_bundle_surfClass_pushforward_ne_zero`).

✅ CARRIER FIX LANDED (W-A Round 4, `PinPlusCharPairMembraneTie.lean`, 2026-07-13): the tied
`CharPairBorTied` COMPUTES `L = ker mem.bInc` from a certified membrane's boundary-inclusion — no free
submodule. The acceptance test PASSES: the honest cylinder/doubling membrane's fold-kernel is the
anti-diagonal (`cylGeoMembrane`, `diagonal_mem_cylGeoMembrane`), which KILLS the un-reversed double
(`untwisted_double_fails_taylor_on_cyl`: `2·q₄ ≠ 0` on the diagonal) while the e₈-graph Lagrangian is
excluded (`cylKernel_ne_e8`/`e8_omits_diagonal`: it omits the diagonal, so it is not a geometric
kernel). The honest `negBor` inverse law SURVIVES (`charPairNegBorTied`) and the anti-collapse engine
descends (`CharPairBorTied.brown_eq`).

✅ RE-GATE MIGRATION LANDED (arm 4, 2026-07-14): `pinPlusCharPairData`'s `Bor` is now the TIED
`CharPairBorTied` in-place (all eight op witnesses tied, `PinPlusCharPairData` §9.6); the free
`CharPairBor` is retained upstream as the registry-backing shape only. ⚠ The binders below are
STILL NOT discharged — the round-4.5 SELF-ATTACK (`PinPlusKTVacuityGateWD` §4.5,
`doubleKillerBorTied`) replays the exploit through a SYNTHETIC `bInc` (kernel = the e₈ graph), so
`ktNonSplit_false`/`kt_binders_unsatisfiable` PERSIST on the migrated carrier. Discharge path:
the geometric-realization strengthening (`GeoRealizationData`/`GeoMembrane.ofGeometric` — the
`PinPlusCharPairMembraneGeoRealization` seam) + the `(n,q,surf)` tie, then the fresh Fable
re-gate.

Route: KT-LMS 151 §5 (`Lit-Search/Phase-5qH/KT_LMS_Section5_completeness_proof_extracted.md`,
Thm 5.2 / Lemma 5.3 / §6) on the FAITHFUL carrier `G := T2DataBordismGrp (pinPlusCharPairData prov)`.
The DONE surjection `charPairBrown : G →+ ZMod 8` (`RP4CharPairWitness.charPairBrown_surjective`) is
the `[∩w₁²]` characteristic-surface Brown map — a mod-8 door, honestly (the `{0,8}` kernel is
invisible to the `(Σ,q)` data: the fake-ℝP⁴ 9-vs-1 fact, dossier §0). W-D's target is the extension

  `0 → ℤ/2 → G → ℤ/8 → 0`   (non-split ⟹ `G ≅ ℤ/16`, `addOrderOf [ℝP⁴] = 16`).

This module **states** the completeness Props (the kernel analysis + the non-split bit) as NAMED
binders — NOT axioms, NOT discharged — and **proves** the pure-group-theory ASSEMBLY that consumes
them (`card = 16`, `addOrderOf [ℝP⁴] = 16`, `G ≃+ ZMod 16`). The Props are W-D/W-E completeness
content that must face their own vacuity gate BEFORE anything consumes them; here we only STATE +
SELF-TEST (§5). Nothing over the vacated `DataBordismGrp`; frozen carrier shapes untouched.

Standing no-go compliance (dossier §7): the ÷16 content is honestly geometric (NOT a lattice Arf —
`nogo_lattice_arf_not_sigma8`) and the grade is enhancement-tied (NOT a free grade —
`synthetic-grade-ker-bot-nogo`); the non-split bit is carried in the w₁-dual `V`/ψ, NOT an H¹
`comp` coordinate (`comp-twist-doubling-incompatible`). The kernel Props are stated as HYPOTHESES,
never proved here as `ker = ⊥`-style unconditional facts.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairCarrier
import SKEFTHawking.RP4CharPairWitness
import SKEFTHawking.PinPlusExactSequence

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.RP4CharPairWitness
open SKEFTHawking.RP4Witness SKEFTHawking.RP4Manifold
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism

namespace SKEFTHawking.PinPlusKTExtension

variable {k : WithTop ℕ∞}

/-! ## §1. The two named classes on the honest carrier: `[ℝP⁴]` and the kernel representative -/

/-- **The `ℝP⁴` class** `g := [ℝP⁴] ∈ G` — the DONE odd generator: `charPairBrown g = 1` generates
`ZMod 8` (`charPairBrown_rp4_eq_one`) and `g ≠ 0` (`charPairBrown_rp4_ne_zero`). -/
noncomputable def ktRP4Class (prov : CharPairWProviderPerOp (𝓡 4) k) :
    T2DataBordismGrp (pinPlusCharPairData prov) :=
  T2DataBordismGrp.mk (pinPlusCharPairData prov) ⟨rp4SM_k k, rp4CharPairK k⟩

/-- **The kernel representative** `k₀ := 8 • [ℝP⁴] ∈ G`. Since `charPairBrown (8 • g) = 8 • 1 = 0`
in `ZMod 8`, `k₀` lies in `ker(charPairBrown)` (the mod-8 door is blind to it — dossier §5). KT §5:
`k₀` is the NONZERO order-2 kernel class `= [Kummer]` (non-splitness); the `(Σ,q)` data cannot tell
whether it is `0` or `[Kummer]`, which is exactly why `KTNonSplit` is a genuine open bit. -/
noncomputable def ktKernelRep (prov : CharPairWProviderPerOp (𝓡 4) k) :
    T2DataBordismGrp (pinPlusCharPairData prov) :=
  (8 : ℕ) • ktRP4Class prov

/-! ## §2. The completeness Props (STATED as named binders; NOT discharged here) -/

/-- **W-D completeness Prop (i) — the kernel is 2-torsion.** Every `charPairBrown`-kernel class is
its own negative. KT §5 content: `ker(→ ℤ/8) = image of Ω₄^{Spin} ≅ ℤ/2·[Kummer]`, a 2-torsion
group. Stated as a HYPOTHESIS — its discharge is the empty-Σ spin-image analysis (§4) + Lemma 5.3's
double-cover ÷32; this module does not prove it (it faces the vacuity gate first). -/
def KTKernelOrderTwo (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ∀ x : T2DataBordismGrp (pinPlusCharPairData prov), charPairBrown prov x = 0 → x + x = 0

/-- **W-D completeness Prop (ii) — the kernel has ≤ 2 elements, exactly `{0, k₀}`.** Every
`charPairBrown`-kernel class is either `0` or the representative `k₀ = 8 • [ℝP⁴]`. This is the
concrete, falsifiable shape of `ker(charPairBrown) ≅ ℤ/2` (KT §5: the image of `Ω₄^{Spin}` is the
Kummer ℤ/2). Non-vacuous (it names the two elements; an infinite kernel refutes it) — the honest
`card(ker) ≤ 2` bound the assembly's `card = 16` consumes. Stated as a HYPOTHESIS. -/
def KTKernelCard (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ∀ x : T2DataBordismGrp (pinPlusCharPairData prov),
    charPairBrown prov x = 0 → x = 0 ∨ x = ktKernelRep prov

/-- **W-D completeness Prop (iii) — the NON-SPLIT bit `8 • [ℝP⁴] ≠ 0`.** The dossier's critical
node (§5). `charPairBrown (8 • [ℝP⁴]) = 8 • 1 = 0`, so `8 • [ℝP⁴]` IS a kernel element; non-splitness
= it is the NONZERO one. The mod-8 `charPairBrown` door is blind to `{0, 8}`, so the odd/16 content
is NOT supplied by `charPairBrown` — this bit needs the structural `8 • [ℝP⁴] = [Kummer] ≠ 0` (§3,
option 1) or the KT `ψ ∈ ℚ/32ℤ` index witness. Stated as a HYPOTHESIS — the most likely stall point
regardless of route (dossier §5). -/
def KTNonSplit (prov : CharPairWProviderPerOp (𝓡 4) k) : Prop :=
  ktKernelRep prov ≠ 0

/-- **The option-1 resolution TARGET shape** for `KTNonSplit` (dossier §5, best case): `8 • [ℝP⁴]`
equals a nonzero Kummer-flavoured kernel class `κ` — `charPairBrown κ = 0` (spin-image, empty-Σ),
`κ ≠ 0`, and `k₀ = κ`. NO spin/Kummer witness exists on the carrier yet, so this is the ABSTRACT
form (parameterized by `κ`); §4 documents what the Kummer witness needs: a `CharPairStrBundled` with
`Σ = ∅` (rank-0 enhancement) on a K3-like carrier — the empty-Σ spin specialization (do NOT build
K3). `KTNonSplitKummerTarget prov κ → KTNonSplit prov` (the witness discharges the open bit). -/
def KTNonSplitKummerTarget (prov : CharPairWProviderPerOp (𝓡 4) k)
    (κ : T2DataBordismGrp (pinPlusCharPairData prov)) : Prop :=
  charPairBrown prov κ = 0 ∧ κ ≠ 0 ∧ ktKernelRep prov = κ

/-- The Kummer-target shape DOES discharge the non-split bit (option 1 ⟹ Prop (iii)). A cheap
consistency tie: if a nonzero Kummer class `κ` equals `k₀`, then `k₀ ≠ 0`. -/
theorem KTNonSplit_of_KummerTarget (prov : CharPairWProviderPerOp (𝓡 4) k)
    {κ : T2DataBordismGrp (pinPlusCharPairData prov)} (h : KTNonSplitKummerTarget prov κ) :
    KTNonSplit prov := by
  obtain ⟨_, hκ, hrep⟩ := h
  rw [KTNonSplit, hrep]; exact hκ

/-! ## §3. Basic consistency of the two classes (SELF-TEST group, cylBor-style: values check out) -/

/-- `charPairBrown [ℝP⁴] = 1` — the DONE odd generator value, re-exposed at `ktRP4Class`. -/
theorem charPairBrown_ktRP4Class (prov : CharPairWProviderPerOp (𝓡 4) k) :
    charPairBrown prov (ktRP4Class prov) = 1 :=
  charPairBrown_rp4_eq_one prov

/-- `[ℝP⁴] ≠ 0` — the DONE first non-triviality, re-exposed at `ktRP4Class`. -/
theorem ktRP4Class_ne_zero (prov : CharPairWProviderPerOp (𝓡 4) k) : ktRP4Class prov ≠ 0 :=
  charPairBrown_rp4_ne_zero prov

/-- **`k₀ = 8 • [ℝP⁴]` genuinely lies in `ker(charPairBrown)`** — `charPairBrown k₀ = 8 • 1 = 0`
in `ZMod 8`. The consistency tie the whole non-split story rests on: `k₀` is a kernel element, so
`KTNonSplit` asks precisely whether that kernel element is the zero one or not. -/
theorem charPairBrown_ktKernelRep (prov : CharPairWProviderPerOp (𝓡 4) k) :
    charPairBrown prov (ktKernelRep prov) = 0 := by
  rw [ktKernelRep, map_nsmul, charPairBrown_ktRP4Class]
  decide

/-! ## §4. The empty-Σ spin specialization — spin classes land in `ker(charPairBrown)` automatically

A Spin 4-manifold has `w₁ = w₂ = 0`, so its characteristic surface `Σ` (dual to `w₂ + w₁²`) is
EMPTY: the char-pair enhancement has rank `n = 0`, so `charPairBrown` of its class is `0` (the
enhancement's Brown invariant of a rank-0 form is `0`). This is KT §5's "any class in the kernel is
Pin⁺-bordant to a Spin manifold" reflected on the carrier: the spin image is inside the kernel,
automatically. The Kummer witness `κ` (§2 option 1) is exactly such an empty-Σ class on a K3-like
carrier (NOT built here). -/

/-- **A rank-0 `ZMod 4`-quadratic form has Brown invariant `0`.** `Z4Quadratic (Fin 0)` is unique
(`z4_ext` + the trivial domain), equal to `stdQuadratic 0`, whose Brown invariant is `↑0 = 0`. -/
theorem brown_rank_zero (q : Z4Quadratic (Fin 0)) : q.brown = 0 := by
  have hq : q = stdQuadratic 0 := by
    apply z4_ext
    · funext x; rw [Subsingleton.elim x 0, q.q_zero, (stdQuadratic 0).q_zero]
    · funext x y
      rw [Subsingleton.elim x 0, Subsingleton.elim y 0, q.B_zero_left,
        (stdQuadratic 0).B_zero_left]
  rw [hq, brown_stdQuadratic, Nat.cast_zero]

/-- **The empty-Σ spin specialization (a theorem, nearly rfl-adjacent).** Any char-pair class whose
characteristic surface is empty (enhancement rank `n = 0`) lands in `ker(charPairBrown)`. This is the
carrier-generic "spin classes are in the kernel" fact — the discharge shape for `KTKernelCard`'s
`{0, k₀}` characterization and the empty-Σ Kummer witness (§2 option 1). -/
theorem charPairBrown_of_rank_zero (prov : CharPairWProviderPerOp (𝓡 4) k)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) (hn : p.2.n = 0) :
    charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 := by
  rw [charPairBrown_mk]
  have key : ∀ (j : ℕ) (q : Z4Quadratic (Fin j)), j = 0 → q.brown = 0 := by
    rintro j q rfl; exact brown_rank_zero q
  exact key p.2.n p.2.q hn

/-! ## §5. THE ASSEMBLY — the KT §5 extension `0 → ℤ/2 → G → ℤ/8 → 0` on the honest carrier

The pure group-theory assembly is the carrier-generic `PinPlusExactSequence` algebra (KT Thm 5.2):
a surjection `p : G →+ ZMod 8` with `Nat.card (ker p) = 2`, a generator `g` with `p g = 1` and
`8 • g ≠ 0`, force `Nat.card G = 16`, `addOrderOf g = 16`, and `Nonempty (G ≃+ ZMod 16)`. Here
`p := charPairBrown prov` (surjective, DONE), `g := [ℝP⁴]` (`p g = 1`, DONE), and the disclosed
completeness inputs are the two named binders `KTKernelCard` (⟹ `Nat.card (ker p) = 2`) and
`KTNonSplit` (`8 • g ≠ 0`). Each is genuinely load-bearing (self-test §6). -/

/-- **The kernel-cardinality bridge** — `Nat.card (ker charPairBrown) = 2` from the two named
completeness binders. `KTKernelCard` pins `ker ⊆ {0, k₀}`; `KTNonSplit` gives `k₀ ≠ 0`; and
`k₀ = 8 • [ℝP⁴]` lies in the kernel (`charPairBrown_ktKernelRep`). This is KT Lemma 5.3's content
(`ker [∩w₁²] = image Ω₄^{Spin} ≅ ℤ/2`) restated as a card fact, feeding the generic assembly. BOTH
binders are load-bearing here: drop `KTKernelCard` and the `{0, k₀}` cover is gone (card unbounded);
drop `KTNonSplit` and `{0, k₀}` may collapse to one element (card 1). -/
theorem kernel_card_two (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hcard : KTKernelCard prov) (hns : KTNonSplit prov) :
    Nat.card (charPairBrown prov).ker = 2 := by
  have hmem : ktKernelRep prov ∈ (charPairBrown prov).ker := by
    rw [AddMonoidHom.mem_ker]; exact charPairBrown_ktKernelRep prov
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨0, (charPairBrown prov).ker.zero_mem⟩, ⟨ktKernelRep prov, hmem⟩, ?_, ?_⟩
  · intro h
    exact hns (Subtype.ext_iff.mp h).symm
  · rw [Set.eq_univ_iff_forall]
    rintro ⟨x, hx⟩
    rw [AddMonoidHom.mem_ker] at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hcard x hx with h0 | hk
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext hk)

/-- **ASSEMBLY (cardinality) — `Nat.card G = 16`** on the honest CharPair carrier, conditional on the
two named binders. `card = 2 · 8` = |ker| · |G ⧸ ker| (Lagrange on the exact sequence). NOTE `= 16`
(not `≤ 16`): the equality FORCES `Finite G` — it does not vacuously hold for an unknown/infinite `G`
(where `Nat.card = 0`), so it is the honest, non-vacuous cardinality claim. -/
theorem kt_card_eq_16 (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hcard : KTKernelCard prov) (hns : KTNonSplit prov) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData prov)) = 16 :=
  PinPlusExactSequence.card_G_eq_16 (charPairBrown prov) (charPairBrown_surjective prov)
    (kernel_card_two prov hcard hns)

/-- **ASSEMBLY (order) — `addOrderOf [ℝP⁴] = 16`** conditional on the two binders. `8 ∣ order`
(`charPairBrown [ℝP⁴] = 1` generates `ℤ/8`); `order ∣ 16` (`8 • [ℝP⁴]` is the order-2 kernel class,
so `16 • [ℝP⁴] = 0`); `¬ order ∣ 8` (`8 • [ℝP⁴] ≠ 0`, `KTNonSplit`) ⟹ order = 16. -/
theorem kt_rp4_addOrderOf (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hcard : KTKernelCard prov) (hns : KTNonSplit prov) :
    addOrderOf (ktRP4Class prov) = 16 :=
  PinPlusExactSequence.order_g_eq_16 (charPairBrown prov) (ktRP4Class prov)
    (charPairBrown_ktRP4Class prov) hns (kernel_card_two prov hcard hns)

/-- **THE HEADLINE ASSEMBLY — `G ≃+ ZMod 16`** (KT Thm 5.2 on the honest CharPair carrier),
CONDITIONAL on the two named completeness binders `KTKernelCard` and `KTNonSplit` (each a Prop, never
an axiom; neither discharged here). The DONE facts (`charPairBrown` surjective, `charPairBrown [ℝP⁴]
= 1`) are supplied in-tree; the two binders are the KT §5 disclosed geometric inputs (Lemma 5.3's
`ker ≅ ℤ/2` and the ψ-witness non-split bit `8 • [ℝP⁴] ≠ 0`). This is the honest disclosed form: the
ℤ/16 is assembled FROM BELOW (`2 · 8`), NOT read off any carried grade. -/
theorem kt_equiv_zmod16 (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hcard : KTKernelCard prov) (hns : KTNonSplit prov) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  PinPlusExactSequence.zmod16_of_kt_exact_sequence (charPairBrown prov)
    (charPairBrown_surjective prov) (kernel_card_two prov hcard hns) (ktRP4Class prov)
    (charPairBrown_ktRP4Class prov) hns

/-- **The two kernel Props are two faces of `ker ≅ ℤ/2`** — `KTKernelOrderTwo` (2-torsion) is a
CONSEQUENCE of `KTKernelCard` (≤ 2 elements) + `KTNonSplit` (nonzero rep), NOT an independent input.
Honest disclosure guarding the vacuity gate: since a group of order 2 is `ℤ/2`, everything in a
≤ 2-element kernel with a nonzero element is automatically 2-torsion. This is why the headline
assembly consumes only `{KTKernelCard, KTNonSplit}` — adding `KTKernelOrderTwo` would be a redundant
(non-load-bearing) hypothesis. -/
theorem kt_kernelOrderTwo_of_card (prov : CharPairWProviderPerOp (𝓡 4) k)
    (hcard : KTKernelCard prov) (hns : KTNonSplit prov) : KTKernelOrderTwo prov := by
  intro x hx
  have h2 : ktKernelRep prov + ktKernelRep prov = 0 := by
    have hmem : charPairBrown prov (ktKernelRep prov + ktKernelRep prov) = 0 := by
      rw [map_add, charPairBrown_ktKernelRep, add_zero]
    rcases hcard _ hmem with h0 | hk
    · exact h0
    · exact absurd (add_left_cancel (a := ktKernelRep prov) (by rw [add_zero]; exact hk)) hns
  rcases hcard x hx with h0 | hk
  · rw [h0, add_zero]
  · rw [hk]; exact h2

/-! ## §6. SELF-TESTS — the pre-gate vacuity sanity (the Fable vacuity attack will deepen this)

**(a) The three completeness Props are NOT trivially dischargeable** (probed live via
`lean_multi_attempt`; recorded here — the file carries no failing code). With ZERO geometric input,
each Prop resists every bookkeeping tactic — the necessary condition for surviving the vacuity gate:

* `KTKernelOrderTwo prov` (`∀ x, charPairBrown prov x = 0 → x + x = 0`): `decide` errors (free
  variables / unknown carrier `G`); `intro x hx; abel` leaves `2 • x = 0` UNSOLVED (the hypothesis
  `charPairBrown x = 0` gives no route to `x + x = 0` for an arbitrary carrier class); `simp`,
  `aesop`, `omega`, `exact hx` (type mismatch `ZMod 8`-eq vs group-eq) all fail. The 2-torsion is a
  genuine geometric fact about `ker(charPairBrown)`, not algebra.
* `KTKernelCard prov` (`∀ x, charPairBrown prov x = 0 → x = 0 ∨ x = k₀`): `tauto` reduces to the open
  `x = ktKernelRep prov` and fails; `left; exact hx` type-mismatches; `simp`/`aesop` make no
  progress. The `{0, k₀}` characterization is the geometric Lemma-5.3 content.
* `KTNonSplit prov` (`8 • [ℝP⁴] ≠ 0`): **the sharpest check** — `intro h; exact absurd h
  (ktRP4Class_ne_zero prov)` FAILS with a type mismatch (`ktRP4Class_ne_zero` proves `[ℝP⁴] ≠ 0`, but
  `KTNonSplit` needs `8 • [ℝP⁴] ≠ 0`). So the DONE non-triviality (grade `1`) does NOT supply the
  non-split bit (grade `0`, in the kernel): the mod-8 `charPairBrown` door is BLIND to whether
  `8 • [ℝP⁴]` is `0` or `[Kummer]` (dossier §5). This confirms `KTNonSplit` is the genuinely open
  node, not a repackaging of an in-tree fact. `decide`/`simp`/`aesop` also fail.

**(b) The assembly's hypotheses are load-bearing** (`kt_equiv_zmod16`, `kt_card_eq_16`,
`kt_rp4_addOrderOf` all take exactly `{KTKernelCard, KTNonSplit}`):
* `KTKernelCard` feeds `kernel_card_two`'s `{0, k₀}` cover — without it `Nat.card (ker) ≤ 2` is gone
  and `card_G_eq_16`'s `hker : Nat.card (ker) = 2` is unprovable (the `2` in `16 = 2 · 8` disappears).
* `KTNonSplit` feeds BOTH the `card = 2` (rules out the `{0, k₀}`-collapse to a 1-element kernel, i.e.
  `card = 1`, giving `card G = 8`) AND `order_g_eq_16`'s `hg8 : 8 • [ℝP⁴] ≠ 0` (rules out
  `addOrderOf [ℝP⁴] = 8`, i.e. the SPLIT extension `G ≅ ℤ/8 ⊕ ℤ/2`). Dropping it degrades the
  conclusion from `ℤ/16` to `ℤ/8 ⊕ ℤ/2` — precisely the non-split bit.
* `KTKernelOrderTwo` is DELIBERATELY NOT an assembly hypothesis: it is a CONSEQUENCE of the other two
  (`kt_kernelOrderTwo_of_card`), so including it would be a redundant, non-load-bearing binder (a
  vacuity smell). The two faces of `ker ≅ ℤ/2` are carried honestly: card by `KTKernelCard`, torsion
  as a derived fact.

**(c) Consistency ties (cylBor-style — the computed values check out):** `charPairBrown_ktRP4Class`
(`= 1`, the DONE generator), `charPairBrown_ktKernelRep` (`= 0`, `k₀` genuinely in the kernel),
`ktRP4Class_ne_zero` (`[ℝP⁴] ≠ 0`), and `KTNonSplit_of_KummerTarget` (option-1 ⟹ non-split) all
hold. The Kummer witness `κ` that would discharge `KTNonSplit` needs (dossier §5, §4 here): a
`CharPairStrBundled` with `Σ = ∅` (rank-0 enhancement, `charPairBrown_of_rank_zero` ⟹ in the kernel)
on a K3-like carrier, with `κ ≠ 0` and `k₀ = κ` — the empty-Σ spin specialization (NOT built here). -/

end SKEFTHawking.PinPlusKTExtension
