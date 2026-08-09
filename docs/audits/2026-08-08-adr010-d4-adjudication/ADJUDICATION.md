# ADR-010 §D4 — the merge/split/retire adjudication

**Date:** 2026-08-08 · **Delegated by the operator**, 2026-08-08: *"I'm delegating the final
grouping order to you, since we've retrofitted with apexes & measured. Intent is to create quality
publications at appropriate venues. Think like a referee and as a reader at the relevant venues to
decide on any bundle merge / disposition question."*

**Method, per ADR-010 C4.** Every verdict below rests on the manuscripts read in full, their
metadata, their retrofit FINDINGS, and closures re-derived live from declared apexes. Where a
verdict rests on something not read, it says so.

---

## 0. The measurement that was not available when the audit recommended 21 → 16

All 21 bundles now declare apex theorems, so **closure is computable for the first time**. The
2026-08-06 probe could only seed closures from *what the drafts cite*; it said so, and named the
gap: *"the difference between it and the tables above is exactly the difference between what the
drafts cite and what the bundles claim."*

Live pairwise closure overlap (declarations; `scripts/bundle_closure.py`, all 21 declared, zero
unresolved apexes):

| pair | Jaccard | shared | as % of the smaller |
|---|---|---|---|
| **D2 + L2** | **0.705** | 391 | **91 % of L2** |
| F + D3 | 0.295 | 126 | 57 % of F |
| D1 + I1 | 0.140 | 30 | 41 % of I1 |
| E1 + E2 | 0.116 | 5 | 42 % of E2 |
| **D4 + D8** | **0.106** | **280** | **45 % of D4** |
| D3 + L3 | 0.059 | 20 | 71 % of L3 |
| D9 + D10 | 0.057 | 50 | 16 % of D10 |
| **D6 + D9** | **0.000** | **0** | **0** |
| **D10 + D11** | **0.000** | **0** | **0** |
| D6 + D12, D9 + D12, D1 + D7, D3 + L2 | ≤ 0.004 | ≤ 3 | — |

⚠️ **Two of these invert the audit's headline, and neither inversion means what it appears to
mean at first reading.** Both are unpacked below. Closure sizes carry
`truncated_private` (D4 82, D8 103, D11 47) per the probe's standing caveat.

---

## 1. D6 + D9 — **DO NOT MERGE.** Excise, do not consolidate.

### The finding

`D6 ∩ D9 = 0` by closure and **78 shared theorems** by direct reference. Both are true, and the
D6 retrofit already reconciled them before I re-derived either: *"D6 and D9 do not overlap. §5.4
and D9 overlap, because §5.4 is D9's content."* The declaration-level zero is an artifact of D6
declaring only its four headline sections — the sections that overlap D9 in nothing.

**Read in full, the manuscripts settle it beyond the counts.** D6 §5.4
(`sec:wstate:envelope`, lines 504–991, **44 % of the draft**) and D9 §§2–4 describe *the same
theorems by name*: `diamondDist_dephasing_eq`, `diamondDist_errorBasisKraus_eq`,
`diamondDist_weylKraus_eq`, `diamondDist_spamBitFlip_eq`, `negativityBellDiag_eq`,
`no_local_distillation_to_bellPair`, `logNegativity_add`, `logNegB_maxEntState`,
`distillation_single_copy_bound`, `logNegB_ncopy`, `bbpsswRecurrence_gt`,
`dejmps_single_step_can_decrease`, `teleportAvgFidelity_horodecki_unconditional`,
`bb84_crossover_exists`, `fortescueLoYield_gt_two_thirds`, `swapChain_fidelity_envelope`,
`avgGateFidelity_eq`, `plobBound`, and the whole coherence-fidelity family.

This is not shared background. **It is one corpus written up twice.**

### Why a merge is the wrong remedy, as a referee would see it

**D9 is the stronger manuscript and a merge would damage it.** It is a coherent five-layer paper
with a genuine methodological headline (the two-layer posture: formula layer machine-verified,
identification layer cited and carried as a named hypothesis), a §Documented walls section listing
five things the verified layer does not contain, and honesty witnesses — the DEJMPS
non-monotonicity counterexample, the un-asserted BB84 decimal, the un-claimed Fortescue–Lo
optimality. It is appropriately venued at PRX Quantum / Quantum.

**D9 CONTAINS D6 §5.4's scope and extends it; it does not merely duplicate it.** Measured by
content family across both drafts:

| family | D6 §5.4 | D9 |
|---|---|---|
| diamond-norm program incl. Watrous strong duality (`diamondDist_eq_choiSDP`) | ✅ | ✅ |
| negativity / PPT / log-negativity ladder | ✅ (22 mentions) | ✅ (13) |
| entropy + majorization (Klein, Gibbs, sharp Audenaert) | ❌ **0** | ✅ **16** |
| network capacity, max-flow/min-cut, Ford–Fulkerson | ❌ **0** | ✅ **12** |
| von Neumann / relative entropy | ❌ **0** | ✅ **15** |
| readout-window envelopes, rational-enclosure technique | ❌ | ✅ |

⚠️ **CORRECTION to my own first pass, recorded rather than smoothed over.** I wrote that D9
*"strictly supersedes"* §5.4 and cited three things §5.4 *"has none of"*. **Two of the three were
wrong** — D6 §5.4 carries the full Watrous strong duality, and it carries *more* negativity text
than D9 does. Only the entropy/majorization and max-flow legs held.

⚠️ **And the probe that produced the error is itself worth recording**, because it is the same trap
twice: my first pass used `\|` as alternation under `grep -E`, where it is a literal pipe, so a
three-way alternation searched for one literal string and returned 0 for D9 on content D9 plainly
has. A second pattern using `.` between name parts missed every draft that writes Lean names as
`diamondDist\_eq\_choiSDP` — **the LaTeX-escaped-underscore trap already recorded in
`QA_QI_INFRASTRUCTURE_MAP` §5**, met again from a new direction.

**The verdict does not move, and the corrected reason is stronger:** D9's five-layer scope strictly
*contains* §5.4's subject and adds four families §5.4 has nothing of, so §5.4 is a shorter retelling
inside a smaller frame. There is nothing to consolidate *into* D9.

**Merging would bolt four unrelated fault-tolerance vignettes onto a device-certification paper.**
Williamson–Yoder gauging overhead, Shor ECC-256 T-counts, APM-LDPC hashing bounds and W-state
cyclotomic measurement have no relationship to trace norms and readout floors beyond both being
quantum. A referee reads that as an appendix that does not belong, and it would cost D9 its
strongest asset, which is that it is *about one thing*.

### The verdict

1. **Excise D6 §5.4 to a cross-reference.** The idiom is already in D6's own §2, which is a
   15-line pointer saying D8 owns the Solovay–Kitaev primitive and D6 consumes it. §5.4 gets the
   same shape, pointing at D9.
2. **D6 is then ~620 lines and must be refilled from its own substrate, not re-chartered.** Per C5
   the claims do not move to fit the container.
3. **The substrate to refill it with already exists and is un-homed.** Measured live
   (predicate: every declaration in `lean_deps.json` under `SKEFTHawking.FaultTolerance`, homed =
   present in some bundle's declared-apex closure):

   | module | un-homed decls | what it is |
   |---|---|---|
   | `Basic` | 95 | Pauli / circuit-op algebra |
   | `StabilizerCode` | 43 | stabilizer-code substrate |
   | `NoiseModelMT` | 33 | Bernoulli-product / local-stochastic noise |
   | `ExRec` | 31 | **extended rectangles — the core AGP construct** |
   | `Malignant` | 22 | malignant-pair attestation |
   | `NoiseModel` | 21 | local-stochastic noise model |
   | `Counting` | 16 | AGP-rigorous Steane malignant-pair counts |
   | `SteaneCode` | 16 | the [[7,1,3]] code |
   | `Chernoff` | 9 | pair-failure bounds, AGP recursion step |
   | `AGP.Threshold` | 8 | **the Aliferis–Gottesman–Preskill threshold theorem** |
   | `Concatenation` | 7 | AGP level sequence, below-threshold behaviour |
   | `DoubleExp` | 3 | double-exponential suppression |
   | — partial gaps | 38 | `APMLdpc` 15, `ShorTGateCount` 19, `WStateQFT` 4 |

   **342 declarations in D6's own namespace reach no bundle.** ⚠️ This is larger than the D6
   retrofit's *"10 modules / 143 declarations"*, and the predicates differ — the retrofit counted
   author-written declarations across a hand-listed 10 modules. **`ExRec` and `StabilizerCode`, 74
   declarations, are in neither its list nor any bundle**, and the extended rectangle is the
   central object of the AGP threshold argument. The direction is the retrofit's; the scope is
   larger.

4. **That is what a paper titled "Formally Verified Fault-Tolerant Quantum Computation Substrate"
   should contain** — threshold theorem, extended rectangles, concatenation, double-exponential
   suppression, malignant-pair counting, noise models, the Steane code — and it is a stronger and
   more novel claim than any of the four vignettes currently carrying the title.

**So the boundary failure is real, the audit measured it correctly, and the remedy it proposed
would have made both papers worse.** D6 is not too close to D9. D6 is holding D9's paper and not
holding its own.

### Defects to fix in D6 while it is open (found in the full read)

- **§1.3 "D6 sits in the project's 15-bundle publication architecture."** Live roster is 21.
- **§5.4 "17 kernel-only modules."** The `QuantumNetwork` family holds 104. (D9 says 103 — also off
  by one, its own retrofit found it.)
- **Venue is wrong.** The metadata and `\documentclass` say PRD; the content is QEC resource
  counting, code rates, T-gate budgets and a measurement basis. That is PRX Quantum / Quantum,
  where its siblings D8 and D9 already sit. PRD fits nothing in the draft.
- **§4's forward reference** to *"real-interval-arithmetic substrate currently absent from Mathlib
  v4.29.1"* — the pin is v4.32.0, and D9 §5 ships exactly the rational-enclosure technique that
  paragraph says is missing. Two siblings disagree about whether the project has the capability.

---

## 2. D10 + D11 — **DO NOT MERGE.** The proposal rests on a retracted measurement.

### Provenance of the proposal matters here

ADR-010 §"What remains" states the position plainly: *"the other three proposed merges (D6+D9+D12,
D10+D11, E1+E2) are **untested** — D11 and D12 reference zero Lean declarations, so a merge argument
for them cannot be built from substrate overlap and must be built some other way."*

**That premise was withdrawn the next day** as an extraction artifact: both bundles route every
reference through a `\thm{}` wrapper the extractor could not see, and D11 in fact references 95
declarations across 22 modules. So the D10+D11 merge was never argued from evidence — it was
deferred pending evidence, on the strength of a number that turned out to be wrong. The evidence now
exists.

### The evidence

**`D10 ∩ D11 = 0` by closure**, and it is not an under-declaration artifact of the kind that
explained D6+D9: D10 declares 33 apexes reaching 311 declarations across 17 modules (depth 13), D11
declares 73 reaching 413 across 22 (depth 6). Both are richly declared and they share nothing.

**Read in full, the two manuscripts are methodologically opposed, which is the stronger reason.**

| | D10 | D11 |
|---|---|---|
| through-line | formalize the *analytic* structure theorems: unbounded operators, essential self-adjointness, semigroups | *avoid* analysis: "machine-checked condensed-matter conclusions do not need it" — discrete and algebraic certificates only |
| substrate | built **on PhysLib**'s unbounded-operator resolvent, spectral, and CPTP/Choi layers | **imports no PhysLib at all** — its acknowledgments say so explicitly: "the complete import set is Mathlib plus intra-bundle dependencies" |
| headline method | Kato–Rellich, Fourier–Kato, matrix exponentials | Fukui–Hatsugai–Suzuki plaquettes, rational enclosures, `decide` on finite types |
| venue | J. Chem. Phys. / PRX Quantum | PRB |

A merged manuscript would have to assert both *"we build on the analytic substrate"* and *"we show
you don't need the analytic substrate"* as its contribution. **That is not a long paper; it is an
incoherent one**, and the incoherence would land on D11, which currently has the sharper and more
unusual methodological claim of the two.

The venue split is independent and equally decisive. A PRB referee has no use for Hohenberg–Kohn
self-adjointness or GKSL semigroups; a J. Chem. Phys. referee has none for lattice Chern numbers on
a Haldane model. **Neither merged half would survive its own referee.**

### Verdict

**Keep D10 and D11 separate.** No substrate to consolidate, opposed methods, disjoint venues.

### ADR-010 §Open item 2 — answered, both halves

> *"Whether D10 ships the Coulomb result or waits for the DFT layer, including whether PhysLib's
> now-reachable spectral theory makes D10's in-tree Kato–Rellich redundant."*

**(a) Ship it. The Coulomb result is already unconditional.** `molecularHamiltonian_essSelfAdjoint`
is live in `SKEFTHawking.CoulombRelativeBound` and kernel-pure — axioms exactly
`{propext, Classical.choice, Quot.sound}` — as are its three formerly-disclosed inputs
`kineticOperator_isSelfAdjoint_closure`, `coulomb_isRelBounded`, and the in-tree
`IsRelBounded.extend_to_closure`. Verified in `lean_deps.json`, not read from the draft. The
conditional predecessor is retained as `..._of_hpot_hrel`. There is nothing left to wait for.

**(b) PhysLib does NOT make the in-tree Kato–Rellich redundant.** Measured against the resolved
package at pin `c4843367`: PhysLib supplies `IsEssentiallySelfAdjoint` as a *definition* and one
criterion, `isEssentiallySelfAdjoint_of_defectNumber_eq_zero` — the von Neumann defect-index route.
**The strings `Kato`, `Rellich`, `relBound` and `RelativelyBounded` do not occur anywhere in
PhysLib.** There is no relative-boundedness perturbation theorem to inherit.

⚠️ **The two routes are not interchangeable**, which is why the absence is decisive rather than a
naming gap: the defect-index criterion asks for the deficiency subspaces of the *full* operator,
which for a molecular many-body Coulomb Hamiltonian is the hard problem itself. Kato–Rellich is the
perturbative route that makes it tractable — self-adjoint kinetic part, symmetric potential,
relative bound $a<1$. D10 built the theorem it needed because the library has the definition and not
the theorem.

**Consequence for the charter:** D10's headline stands as drafted and neither the post-bump PhysLib
reachability nor Phase 6BB changes it. The one remaining conditional content is the
semibounded-functional input to the variational/Levy–Lieb theorems, which the draft already
enumerates in §6 with a discharge plan.

### Defects to fix in D10 while it is open

- **§2 pins the toolchain at `v4.29.1`.** Live pin is `v4.32.0` / Mathlib `81a5d257`. Already
  reported by the registered `paper_toolchain_pin_drift` check; D11 has the pin right, in the same
  corpus, so the two siblings disagree in print.
- **Venue field reads `PRD | PRX Quantum | J. Chem. Phys.`** PRD fits none of NEGF transport, DFT or
  Lindblad. Drop it and pick between the other two.

---

## 3. E1 + E2 — **DO NOT MERGE.** A merged PRL is arithmetically impossible.

### The decisive constraint is length, and it is not close

Recompiled 2026-08-08 (`compile_bundle_pdf.py --force`, so these are this draft's sizes, not a
stale PDF's): **E1 = 5 pages, E2 = 5 pages**, both `revtex4-2` `prl` two-column. PRL's limit is
3750 word-equivalents ≈ **4 printed pages**, which is the ceiling both bundles declare in
`length_target`.

**Each letter is already ~25 % over the limit on its own.** Two over-length letters cannot become
one letter. The merge is not a close call that turns on taste; it fails on arithmetic before any
editorial question is reached. The only merged form that fits is a PRR article, which trades the
venue down for both.

### And the venue trade is the wrong direction for what these papers are

Read in full, E1 and E2 are the same *shape*: a falsifiable SK-EFT prediction computed at one named
group's published device parameters, addressed to that group. E1 closes with an explicit *"request
to the LKB team for current device-parameter values to allow band-tightening before measurement."*
E2 gives the Dean-device noise PSD, its peak frequency, and the integration time to SNR 1.

**The reader of E1 is the Paris-LKB polariton group. The reader of E2 is the Dean graphene group.**
That is precisely the audience a PRL Letter reaches and a PRR article does not. Merging produces one
paper addressed to neither, in a weaker venue, for the sake of a roster number.

Their shared substrate is one apex, `AcousticMetric.hawking_temp_from_surface_gravity`, which both
declare and both explicitly disclose as a `rfl`-discharge with the substantive content upstream.
Closure J = 0.116 on 5 shared declarations. **There is no corpus to consolidate.**

### Verdict

**Keep E1 and E2 separate, both at PRL.** Each needs a ~1-page cut, which is ordinary letter
editing and the opposite of a merge.

### ADR-010 §Open item 5 — the graphene Γ_H adjudication, narrowed

> *"a physics adjudication that inverts E2's headline and therefore bears on whether E1+E2 should merge."*

**It does not bear on the merge** — the length arithmetic decides that independently, and E1 does not
contain Γ_H, δ_diss, or any dissipative correction at all (its story is dispersive: δ_disp = -πD²/6
across 0.19–0.46, plus stimulated-Hawking gain). **The defect is E2-only.** But it is real, and it is
load-bearing for E2's headline, so it is settled here as far as it can be without a physics call.

**Confirmed by independent derivation, both numbers to two significant figures:**

| quantity | value |
|---|---|
| η/(sT) at Majumdar 4×KSS, T = 150 K | 1.62 × 10⁻¹⁴ **s** |
| (κ/c_s)² at κ = 2.0 × 10¹² s⁻¹, c_s = 4.4 × 10⁵ m/s | 2.07 × 10¹³ **m⁻²** |
| **as printed:** (η/(sT))(κ/c_s)² | 0.33 — units **s·m⁻²**, and a rate must be s⁻¹ |
| δ_diss as printed | 1.67 × 10⁻¹³ (E2 says "~10⁻¹³") ✓ reproduces |

⚠️ **But the audit's *"in both the paper and `formulas.py`"* is half wrong, and the half matters.**
`formulas.py:473` is `Gamma_H = (gamma_1 + gamma_2) * (kappa / c_s) ** 2`, and its docstring declares
**γ₁, γ₂ in [m²/s]**. m²/s × m⁻² = s⁻¹. **The code is dimensionally sound.** The defect is E2's prose
substituting η/(sT), a *time*, into a slot the pipeline defines as a *kinematic viscosity*. Fixing
`formulas.py` would break a correct function; the manuscript is what is wrong.

**What the replacement should be — a recommendation, not a ruling.** η/(sT) becomes a kinematic
viscosity by multiplying by the square of the velocity in the fluid's momentum-density relation
g = (e+p)v/v², not by the sound speed. For the graphene Dirac fluid that velocity is **v_F**, the
emergent light speed, not c_s:

| substitution | ν [m²/s] | Γ_H [s⁻¹] | δ_diss |
|---|---|---|---|
| ν = (η/(sT))·c_s² | 3.14 × 10⁻³ | 6.5 × 10¹⁰ | **3.2 × 10⁻²** (the audit's ~3e-2) |
| **ν = (η/(sT))·v_F²** (recommended) | 1.62 × 10⁻² | 3.3 × 10¹¹ | **1.7 × 10⁻¹** |
| ν = (4/3)(η/(sT))·v_F², conformal | 2.16 × 10⁻² | 4.5 × 10¹¹ | **2.2 × 10⁻¹** |

⚠️ **The prefactor is genuinely open and is the operator's call**, because it depends on how the
project's own `SecondOrderSK.GammaH` defines γ₁+γ₂ against the conformal sound-attenuation constant.
**Not verified: whether γ₁+γ₂ equals (4/3)ν, ν, or another O(1) multiple of it.** Recorded as
unverified, per C4.

**What is not open: δ_diss is not 10⁻¹³, and it is not negligible.** Every candidate above puts it
between 3 % and 22 %, against δ_disp ≈ −2.8 %.

**This strengthens E2 rather than weakening it, which is the opposite of what §Open item 5
anticipated.** E2 currently concludes that *"the SK-EFT framework's value for graphene is therefore
the systematic organization of corrections (and the formal verification), not a specific dissipative
modification of T_H."* That is a self-deprecating conclusion produced by a unit error. Corrected,
graphene is the platform where the SK-EFT's dissipative correction is **measurable and comparable in
magnitude to the dispersive one, with the opposite sign** — which is the SK-EFT program's central
claim, and a far better Letter. Per C5 the claim is being made *stronger*, not resized.

**Blocking:** E2 must not ship until this is adjudicated. The abstract's "eleven orders of magnitude
below the dispersive correction" is the headline, and it is wrong by roughly twelve orders.

---

## 4. D4 → D8 — **DO NOT MERGE. Already resolved, by reassignment rather than concatenation.**

ADR-010's C3 correction had this right before the closure existed: D4 §9 and D8 are *"independently
written treatments of the same subject over almost disjoint substrate"*, sharing 0.1 % of text
shingles, so *"merging D4 §9 into D8 would delete almost nothing."* What was actually wrong was a
**priority and attribution conflict**, and that has since been fixed the right way — **four
`GenericSU2` apexes moved D4 → D8** at the 2026-08-07 retrofit, on the strength of D8 ceding
Fibonacci to D4 explicitly in words, twice. D4's closure fell 753 → 620 declarations and 61 → 43
modules as independent corroboration.

**The residual `D4 ∩ D8 = 280` is not duplication; it is the shared Lie-algebraic core** —
`OneParameterSubgroupSU2` 108, `SU2LieAlgebra` 30, `SolovayKitaevPathA` 27. That is what
"instantiate, don't re-derive" looks like measured from both sides, and it is an argument for two
containers over one substrate, not for one container.

**Verdict: keep D4 and D8 separate.** The boundary is now drawn and each draft states its own side.

### ⚠️ The meta-finding, which is why closure must never be read alone

**The two pairs fail in opposite directions, and the closure number alone gives the wrong answer for
both:**

| pair | closure says | manuscripts say | correct action |
|---|---|---|---|
| **D6 + D9** | **0 shared** → "unrelated, keep apart" | 488 lines of D6 is D9's corpus, same theorems by name | **excise from D6** |
| **D4 + D8** | **280 shared, 45 % of D4** → "duplicated, merge" | explicit cession in D8's own text; disjoint developed content | **keep apart** |

A merge policy driven by the intersection number would have excised the wrong bundle and merged the
wrong pair. **ADR-010 C4 is the load-bearing constraint in this whole exercise, not a ceremonial
one:** closure measures shared *substrate*, and merge decisions turn on shared *claims*, which only
the manuscripts carry.

---

## 5. L1 — **RETIRE as a publication target.** The claim survives; the container does not.

ADR-010 §Open item 3 offers three dispositions: *"re-found the falsification, restate it as a
project-constructed identification, or retire it."*

### What L1 is, read in full

**Substrate:** 18 declarations in **one** module at depth 1 — the thinnest in the portfolio. Of
L1's 11 `GravitationalWaves` apexes, **D3 already declares 5 and F declares 3**, and per the L1
retrofit *"the falsification headline itself — both endpoint falsifiers, the bundled corollary, the
disjointness theorem and its frame-independent form — is already declared by D3 and F."*

**Three referee problems, from the draft's own text:**

1. **The 14 orders of magnitude are a property of a self-chosen prior, not of a measurement.** The
   draft is admirably explicit — the natural range χ ∈ [0.1, 10] is *"a project-adopted naturalness
   window … a modeling choice of this project, not a published derivation"*, anchored to *"the
   project-internal anchor for the order-of-magnitude prior."* Strip the window and the physics is
   one line: c_GW = c√χ, so GW170817 forces χ = 1 to 10⁻¹⁴. A referee will say that immediately.

2. **The formal content is trivial inequalities.** The biconditional is a √/squaring round-trip
   closed by `nlinarith`; the two falsifiers are √(1/10) ≤ 1/2 and √10 ≥ 2 closed by `linarith`.
   **This is the pattern the project's own preemptive-strengthening discipline names and prohibits**
   — a theorem dischargeable by `norm_num` is not the contribution.

3. **The prior art is a crowded 2017 literature and the draft engages none of it.** GW170817's
   c_GW = c constraint eliminated large families of modified-gravity and emergent-gravity models
   within months, in several PRLs. A Letter reporting that it also eliminates one more kinematic
   identification needs to say what is new against that body of work. ⚠️ **Not verified: whether
   `papers/L1/` cites that literature anywhere outside the ~200 lines read.** Recorded as
   unverified.

### Verdict, and why it is not a walk-back

**Retire L1 as a bundle. Keep the result where it is already developed: D3's lane closure, cited by
F.** D3 frames it correctly — one closed lane among several in an emergent-gravity survey, which is
the honest weight of a one-line kinematic exclusion.

⚠️ **This is a container decision, not a claim decision, and the distinction is exactly the one
C5 and `feedback-remediation-build-dont-walkback` police.** Nothing is narrowed, hedged or
downgraded: the falsification theorem, both falsifiers and the disjointness result stay in the Lean
corpus and stay asserted at full strength in D3 and F, which already declare them. What is retired
is a *venue claim* — that this result carries a standalone PRL — and that claim was never a physics
claim.

**If the operator prefers to keep L1**, the honest path is option 1, re-founding: *derive* χ_vest
from the RPA bubble rather than adopting a decade window, and position against the 2017 constraint
literature. That is a research program, not an edit, and it should be scheduled as one rather than
absorbed into a redraft.

---

## 6. Recommended roster — 21 → 20, and the number is an output

| proposal (audit's 21 → 16) | verdict here | roster effect |
|---|---|---|
| D6 + D9 → D6★ | ❌ **rejected** — excise D6 §5.4 instead, refill D6 from the un-homed AGP chain | 0 |
| D6 + D9 + D12 | ❌ **rejected** — `D6 ∩ D12 = 0`, `D9 ∩ D12 = 3` | 0 |
| D10 + D11 → D10★ | ❌ **rejected** — zero overlap, opposed methods, disjoint venues | 0 |
| E1 + E2 → E★ | ❌ **rejected** — two 5 pp letters cannot make one 4 pp PRL; different named audiences | 0 |
| D7 folded into D1 | ❌ **rejected** — already resolved by the D1 → D7 apex reassignment (D1 fell 249 → 171) | 0 |
| D4 §9 → D8 | ❌ **rejected as a merge** — already resolved by moving four apexes D4 → D8 | 0 |
| — | ✅ **L1 retired** (new; not in the audit's list) | **−1** |

**Recommended roster: 20.** ⚠️ **That number is a consequence, not a target.** Six merges were
tested against the manuscripts and every one failed; one retirement the audit never proposed
succeeded. **A recommendation of 16 could only have been reached by not reading the drafts** — which
is the exact failure C4 was written to prevent, and the audit itself flagged in its §7 as what it
could not check.

**The portfolio's problem was never the count.** It was that content sat in the wrong containers:
D6 held D9's paper, D4 held D8's apexes, D1 held D7's, and L1 held a claim D3 already developed.
Three of those four are now fixed by reassignment. **Reassignment, not consolidation, is what this
portfolio needed**, and it changes the roster by one.

### Sequencing (the trap ADR-010 §Consequences names)

The audit warned that merges should land before further Stage-13 work on D6/D7/D9/D10/D11/D12/E1/E2,
*"or that work is spent on containers that are about to be dissolved."* **With no merges
recommended, that trap is closed** and Stage-9/10/13 work on those bundles is safe to proceed.

One ordering constraint survives and it is D6's: **§5.4's excision drops D6 to ~7 pp before the AGP
lift raises it**, so D6's length gate will read worse mid-repair than it does now. That is the
repair working, not regressing. Sequence the excision and the AGP lift as **one** wave so D6 is
never measured in between.
