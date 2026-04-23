# Phase 5x Wave 4 — Fang-Gu Torsion Dark Matter Assessment

**Project:** SK_EFT_Hawking / Phase 5x (Dark Sector Connections)
**Wave:** W4 — Fang-Gu Torsion DM (assessment + narrow kinematic-obstruction Lean module)
**Filed:** 2026-04-22 (session 3 revision — strengthened per audit of prior draft)
**Author:** assessment memo + `lean/SKEFTHawking/FangGuTorsionDM.lean` (10 theorems, 0 sorry, 0 new axioms)
**Primary source:** `Lit-Search/Phase-5x/Fang-Gu Torsion Dark Matter  Phenomenology from Topological Gravity.md`
**Roadmap anchor:** `SK_EFT_Hawking/docs/roadmaps/Phase5x_Roadmap.md` lines 354–382 (Wave 4), 603–645 (Wave 8 cross-connections), 650–663 (Paper 17 structure).

---

## 1. Executive Summary

**Verdict: Structurally compatible with the ADW architecture, but kinematically obstructed at the
standard cold-dark-matter level.** Fang-Gu (FG) torsion dark matter is a self-consistent,
topologically protected dark-sector channel that fits naturally into the ADW vestigial-tetrad
phase hierarchy already formalized in this project. However, the central kinematic feature of
the FG construction — a *traceless* e-loop stress-energy tensor, `η^{μν} T_{μν}^{loop} = 0`,
which is the mechanism that enforces `R = 0` in the emergent Einstein equation — forces the
perfect-fluid equation of state to be `w = p/ρ = 1/3` as a tree-level algebraic identity. That is
radiation-like scaling (`ρ ∝ a⁻⁴`), not the `w = 0` dust scaling that defines CDM (`ρ ∝ a⁻³`),
and the Newtonian Poisson source becomes `ρ + 3p = 2ρ` (double the standard CDM gravitational
coupling). Both consequences are formalized in this session as
`lean/SKEFTHawking/FangGuTorsionDM.lean` (10 theorems, 0 sorry, 0 new axioms); see §6 below and
Appendix C.

This obstruction is *kinematic*, not a fatal no-go: several literature-level escape hatches —
cosmic-string-gas coarse-graining, effective loop velocity dispersion, trace-anomalous quantum
corrections — could in principle give a macroscopic equation of state distinct from the
microscopic `w = 1/3`. None of those rescues is supplied by the 2021 (arXiv:2106.10242) or 2023
(arXiv:2312.17196) Fang-Gu papers. Separately, the FG mass spectrum and relic abundance are set
by microscopic loop-condensation parameters (`θ`, loop-size distribution) that the construction
does not fix. Direct/indirect detection is categorically ruled out (σ_nucleon ~ 10⁻⁹⁰ cm², no SM
gauge vertex); the only distinctive phenomenological signatures are gravitational and at
thresholds far below any current or planned instrument.

**Recommended Phase 5x priority:** LOW relative to the rest of the phase. W4 earns the narrow
Lean module (kinematic obstruction, load-bearing for Paper 17 framing) but does not open into a
full 8-stage pipeline wave. FG torsion DM earns a short dedicated section (≤1 page) in Paper 17
framed as *compatible with but not drop-in CDM* — the kinematic obstruction must be explicit,
not glossed. Full pipeline revisit only if (a) a microscopic loop condensation model lands
upstream, (b) a trace-anomalous completion (cosmic-string-gas EoS, sub-sonic velocity
dispersion) is formalized, or (c) W6 vestigial relics produces an EP-violation observable that
FG-DM would contribute to.

---

## 2. Physical Mechanism

### 2.1 Fang-Gu construction (arXiv:2106.10242, follow-up arXiv:2312.17196)

The 3+1D topological-gravity action has three quantized TQFT terms (research §1.1):

```
S_Top = (k1/4π) ∫ ε_abcd R^ab ∧ e^c ∧ e^d
      + (k2/2π) ∫ B^ab ∧ R^ab
      + (k3/2π) ∫ B̃^a ∧ T^a
```

with `k1, k2 ∈ 2ℤ`, `k3 ∈ ℤ` (analogous to 2+1D Chern-Simons level quantization). This admits two
loop species:

- **ω-loops** (flux lines of the spin connection), coupled to 2-form B^ab.
- **e-loops** (flux lines of the tetrad connection), coupled to 2-form B̃^a.

The `k3 B̃ ∧ T` term encodes three-loop braiding statistics between ω-loops and e-loops.

### 2.2 Condensation → emergent Einstein gravity

ω-loop condensation generates a topological mass term `S_θ = -(θ/2π) ∫ B ∧ B`. The equations of
motion then force `B^ab = (1/θ) R^ab`, `T^a = 0`, recovering the vacuum Einstein-Cartan equation
`ε_abcd e^b ∧ R^cd = 0`; `⟨e^a_μ⟩ = (1/l_p) δ^a_μ` generates the background metric with `l_p`
identified as the Planck length and `κ = π l_p² = 16πG` (research §1.2). This parallels the ADW
mechanism in which the tetrad condensate emerges from an NJL-type gap equation — see §4 below.

### 2.3 Uncondensed e-loops as DM

The three-loop braiding implies:

1. e-loops linked to ω-loops get confined at the Planck scale (cannot survive in the IR).
2. **Unlinked** e-loops survive as free topological excitations in the low-energy phase.

These unlinked e-loops are the FG dark-matter candidates. They are:

- **1D extended objects** (closed flux tubes of the tetrad connection), not point particles.
- **Without SM gauge coupling** — SM fields couple to `ω^ab` (spin connection), not to `B̃^a`.
- **Topologically stable** — conserved winding-number charge, no perturbative decay channels,
  annihilation requires coincident opposite-charge loop un-linking.

The coupling to Dirac matter is `-(l_p/8) σ_abc ψ̄ γ^abc ψ` — extremely weak (Planck-suppressed)
and does not give a Hehl-Boos-type contact interaction (research §3.1).

### 2.4 Why torsion but not Ricci curvature (the *R* = 0 mechanism)

Varying the full action against `B̃^a` gives `T^a = l_p σ^a`, where `σ^a_{μν}` is the e-loop current
2-form. **The loop current is the *only* source of torsion in the FG construction — Dirac fermions
do not source torsion.** This is the radical departure from standard Einstein-Cartan where
fermions *are* the torsion source via the axial current.

The loop stress-energy tensor is traceless: `η^{fd} G̃_{fd} = -R = 0` (research §1.4). Geometrically:

- `G_{μν} = R_{μν} - ½ g_{μν} R → G_{μν} = R_{μν}` when *R* = 0.
- Null geodesics of the full metric still bend — gravitational lensing proceeds normally.
- The distinctive signature lives in the Weyl tensor `C_{μνρσ}` and in sub-galactic velocity
  dispersion, where the traceless `(ρ + 3p)` correction in the Newtonian Poisson equation matters.

### 2.5 Relation to ADW emergent gravity (formalized in this project)

Both FG and ADW/Volovik (arXiv:2312.09435) use:

- A fermionic/topological vacuum as the substrate.
- A two-step symmetry breaking `disorder → GR (vestigial) → ECSK (tetrad)`.
- The tetrad as primary order parameter, the metric as secondary (vestigial) condensate.

In ADW the order parameter is the 4-fermion condensate `⟨Ê^a_μ Ê^b_ν⟩`; in FG it is encoded
in the TQFT levels `(k_1, k_2, k_3)`. These are plausibly distinct microscopic descriptions of
the same macroscopic emergent-gravity phase structure (research §5.1). This structural
overlap is what makes W4 relevant to the project at all.

---

## 3. Quantitative Predictions

From the deep research file (§Block 3, §Block 4) and cross-referenced against standard reviews:

| Quantity | FG-DM prediction | Status |
|---|---|---|
| Mass scale | `m_DM ~ (θ/2π) · L/l_p²` — Planck × parametric | **Undetermined** (θ, L not fixed by theory) |
| Cross-section σ(DM-nucleon) | `~10⁻⁹⁰ cm²` (purely gravitational) | 42 orders of magnitude below LZ 2024 (`2.1 × 10⁻⁴⁸` cm² at 36 GeV, arXiv:2410.17036) |
| Annihilation channel | Loop un-linking → gravitons only | No SM indirect-detection signal |
| Self-interaction σ/m | Topological at Planck scale, negligible at galactic | Passes Bullet Cluster `σ/m < 1` cm²/g (Markevitch 2004) easily |
| Equation of state | Traceless T^μν → `w = p/ρ = 1/3` as tree-level algebraic identity | **Kinematic obstruction — see §3.1 and Appendix C.** Radiation-like, not dust. Formalized in `FangGuTorsionDM.traceless_iff_w_one_third`. |
| Scaling in FRW | `ρ ∝ a⁻⁴` (radiation-like, from `w = 1/3`) | Incompatible with CDM `ρ ∝ a⁻³` unless a trace-anomalous completion is supplied. |
| Newtonian Poisson source | `ρ + 3p = 2ρ` in the traceless regime | Double the CDM coupling. Formalized in `FangGuTorsionDM.traceless_poisson_source_doubled`. |
| BBN contribution | Relativistic (`ρ ∝ a⁻⁴`) until a trace-anomalous completion kicks in | Contributes to `ΔN_eff` unless loops are trace-anomalously non-relativistic by `T ~ 1` MeV; no such mechanism in FG 2021/2023 |
| Free-streaming / sound speed | Set by loop tension `T_L ~ θ/(2πl_p²)` | Parametric; CMB/LSS constraints not calculable |
| Rotation curves | Modified Poisson `∇²Φ = 8πGρ` at tree level (doubled coupling) | Would amplify velocity dispersion by `√2` vs standard CDM at fixed ρ — formally falsifiable; only approaches CDM if the trace-anomalous completion restores `w ≈ 0` |
| Gravitational lensing | Standard (Weyl-tensor correction sub-leading) | No practical discriminator |
| Halo shape | Collisionless CDM-like | No distinguishing prediction |
| Torsion-induced spin precession | `Ω ~ l_p σ / ℏ` in DM halo | Far below neutron-UCN (Ivanov-Wellenzohn 2016, PRD 93 045031) and Kostelecky-Russell-Tasson (arXiv:0712.4393, `10⁻³¹` GeV) sensitivities |
| BBN contribution | Matter-like if non-relativistic by `T ~ 1` MeV | Depends on unknown mass — no quantitative bound |
| Merger / Bullet Cluster behavior | Collisionless pass-through (topological self-interaction ≪ galactic) | Consistent with observation; no unique fingerprint |

**Bottom line (direct/indirect):** FG-DM is phenomenologically *invisible* to every current and
planned direct, indirect, and astrophysical probe. Its only falsifiable direct-torsion
prediction is at levels `~30+` orders of magnitude below laboratory sensitivities.

**Bottom line (cosmological, new in this revision):** the traceless-T condition enforces
`w = 1/3` at tree level, which gives FG-DM radiation-like a⁻⁴ scaling and a doubled Poisson
coupling. These are formally falsifiable consequences (structure growth, BBN N_eff, velocity
dispersion), but testing them requires either (a) accepting the 2021/2023 FG construction as a
genuinely radiation-like component (ruled out by relic abundance and CMB phenomenology), or (b)
supplying a trace-anomalous completion — which no published FG extension provides. See §3.1.

### 3.1 The kinematic obstruction (trace → EOS → scaling)

The obstruction is a tree-level algebraic identity, not a model-dependent phenomenon. Spelled
out for a fresh reader:

1. **Setup.** Fang-Gu 2021 derives `R = 0` in the emergent Einstein equation by imposing
   `η^{μν} T_{μν}^{loop} = 0` (research file lines 80–82; the trace of `G_{μν} = 8πG T_{μν}`
   gives `−R = 8πG · T^μ_μ`, so traceless `T` forces `R = 0`).
2. **Perfect-fluid consequence.** For any perfect fluid with energy density ρ, isotropic
   pressure p, and Minkowski signature `(−, +, +, +)`, the mixed-index trace is
   `T^μ_μ = −ρ + 3p`. Vanishing trace forces `p = ρ/3`, i.e. `w = 1/3`.
3. **FRW scaling.** The standard continuity equation `dρ/dt = −3H (ρ + p)` gives `ρ ∝ a^{−3(1+w)}`.
   For `w = 1/3` this is `ρ ∝ a⁻⁴` (radiation-like), not `ρ ∝ a⁻³` (CDM).
4. **Newtonian consequence.** The general-relativistic Poisson equation in the weak-field
   limit is `∇²Φ = 4πG (ρ + 3p)`. For dust (`p = 0`) the source is `ρ`. For a traceless fluid
   (`p = ρ/3`) the source is `2ρ` — the effective gravitational coupling is *doubled* at fixed
   energy density.

Items (1)–(4) are *tree-level algebra* — no quantum corrections, no coarse-graining, no
cosmological assumptions beyond perfect-fluid FRW. They are formalized in
`lean/SKEFTHawking/FangGuTorsionDM.lean` (theorems `traceless_iff_w_one_third`,
`traceless_not_dust`, `traceless_poisson_source_doubled`, `fg_cdm_obstruction`) — `0` sorry,
only the three standard Lean axioms, no `gapped_interface_axiom`.

**What this does NOT prove.** It does not prove FG torsion DM is ruled out as a dark-sector
candidate. It proves that the 2021/2023 construction — taken literally, as a perfect fluid with
microscopic traceless `T` — cannot be CDM. Three literature-level escape hatches remain
*logically* open:

- **Cosmic-string-gas averaging.** First-look intuition suggests FG loops could be treated
  as cosmic strings, exploiting their Vilenkin-Shellard scaling-regime `w ≈ −1/3` as an
  escape from `w = 1/3`. On second thought this rescue is *tighter than it appears*: a
  Nambu-Goto cosmic string has mixed trace `T^μ_μ = −2ρ`, not zero, because its `T^{ii} = −ρ`
  tension breaks tracelessness. So FG loops — which *require* microscopic tracelessness for
  `R = 0` — cannot be Nambu-Goto strings in the standard sense. Under bulk isotropy + perfect
  fluid (the standard cosmological approximation), SO(3) averaging of traceless microscopic
  pieces gives a traceless macroscopic tensor, and the perfect-fluid identity
  `T^μ_μ = −ρ + 3p` still forces `w = 1/3`. The only genuine escape here is non-equilibrium
  string-network cosmology (tracking correlation functions beyond perfect fluid), which is
  standard for cosmic strings but is not supplied for FG loops in 2021/2023. A formal closure
  of this rescue path is sketched in the session-3 design note (see status memory
  `project_sk_eft_status.md`); Phase 6 candidate as `FangGuStringGasClosure.lean` if ever
  worth opening.
- **Sub-sonic velocity dispersion.** If loop peculiar velocities `v_loop` satisfy
  `v_loop² ≪ c²` at cosmologically relevant epochs, the kinetic contribution to `T^ii` is
  suppressed, and the effective macroscopic pressure can be `≪ ρ/3` even if the microscopic
  stress tensor is traceless. This is the implicit assumption in the research file's remark
  that "the relevant density ρ_DM still clusters via gravitational instability" (line 263), but
  the research does not quantify the suppression or specify when it dominates.
- **Trace-anomalous quantum completion.** The classical trace `T^μ_μ = 0` can be lifted by a
  quantum anomaly (analogous to the QCD trace anomaly giving a nonzero gluon condensate
  contribution to `T^μ_μ`). No calculation of the FG trace anomaly exists.

Each of these would flip W4 from "memo + kinematic-obstruction module" to "full 8-stage
pipeline wave with a trace-anomalous completion module." None is supplied by the published FG
construction; we flag the three as Phase-6 revisit triggers in §6.

---

## 4. Structural Constraints from Existing Lean Results

The project already contains significant Lean formalization of the emergent-gravity sector that
*structurally* constrains FG-DM without ever mentioning it explicitly. The cross-references below
are by absolute path and theorem name.

### 4.1 `lean/SKEFTHawking/ADWMechanism.lean` (21 theorems)

- `ADWMechanism.critical_coupling_pos` (line 177) — `G_c > 0` whenever `Λ > 0` and `N_f > 0`.
- `ADWMechanism.curvature_zero_at_Gc` (line 202) — critical point of V_eff.
- `ADWMechanism.pos_C_gives_full_tetrad` / `zero_C_no_fluct_gives_pregeometric` /
  `zero_C_with_fluct_gives_vestigial` (lines 229–241) — three-phase structure pinned down formally.

**Constraint on FG-DM:** The ADW phase structure predicts three distinct emergent-gravity regimes
(pre-geometric / vestigial / tetrad). FG e-loops are defined as IR excitations of the pre-condensation
TQFT; to survive into our present universe they must persist across the ADW tetrad condensation.
The Lean machinery forbids arbitrary assignments — the *same* `G_c` controls when the tetrad
condenses, and once the tetrad VEV exists (the regime of `pos_C_gives_full_tetrad`), classical
torsion `T^a = l_p σ^a` is well-defined and FG loops source it (research §5.2).

### 4.2 `lean/SKEFTHawking/TetradGapEquation.lean` (20 theorems)

- `TetradGapEquation.criticalCoupling_formula` (line 191) — `G_c = 8π² / (N_f Λ²)` (NJL form).
- `TetradGapEquation.criticalCoupling_eq_adw` (line 205) — matches the ADW gap-equation prediction.
- `TetradGapEquation.bifurcation_at_Gc` (line 357) — trivial ↔ non-trivial fixed point transition.
- `TetradGapEquation.gap_vestigial_connection` (line 390) — ties gap-equation solutions to the
  vestigial-phase parameter.

**Constraint on FG-DM:** Any identification of the topological gap `Δ_FG ~ θ/l_p²` with an
ADW-sector gap has to live on this `Δ*(G)` curve. In particular, for FG-DM mass to fall below the
Planck scale the theory must sit in a *specific* region of `G`-space. The Lean formalization does
not compute `Δ_FG` directly, but it does constrain the structural coupling between the
tetrad-condensation scale and any emergent torsion-coupled sector.

### 4.3 `lean/SKEFTHawking/VestigialSusceptibility.lean` (16 theorems)

- `VestigialSusceptibility.u_g_positive_adw` (line 89) — gradient-energy positivity in ADW.
- `VestigialSusceptibility.vestigial_before_tetrad` (line 185) — formalizes the disorder→vestigial→tetrad
  phase hierarchy.
- `VestigialSusceptibility.vestigial_window_exponential` (line 220) — exponential decay window
  of the vestigial regime.

**Constraint on FG-DM:** FG e-loops as "relics across the phase transition" (research §5.2) are only
coherent if the vestigial window is non-zero. `vestigial_window_exponential` formalizes the
condition for a finite-measure vestigial epoch; `vestigial_window_vanishes` rules out the alternative.
Any cosmological FG-DM relic abundance computation must be consistent with this structure.

### 4.4 `lean/SKEFTHawking/VestigialGravity.lean` (18 theorems)

- `VestigialGravity.ep_violation_in_vestigial` (line 107) — **EP violation in the vestigial phase
  proven formally.**
- `VestigialGravity.ep_only_in_full_tetrad` (line 113) — EP restored only once the tetrad VEV turns on.
- `VestigialGravity.phase_hierarchy` (line 135) and `metric_monotone` (line 143) — monotone phase
  ordering.

**Constraint on FG-DM:** The research §2.4 flags EP violation as a potential cosmological
signature of FG-DM *if* FG loops inherit fermionic character from the underlying ECSK phase. The
Lean theorem `ep_violation_in_vestigial` **already forbids the naive expectation** that the EP
holds during the vestigial epoch — bosons couple to the full metric `g_{μν}`, fermions to the
tetradic `η_{ab} e^a e^b`. FG-DM predictions in this regime must be consistent with this formal
statement; crucially, they cannot claim EP-preserving dynamics during the vestigial epoch.

### 4.5 `lean/SKEFTHawking/FractonNonAbelian.lean` (14 theorems)

- `FractonNonAbelian.no_fracton_is_ym_compatible` (line 76) — fractons cannot carry non-abelian
  gauge charges.
- `FractonNonAbelian.all_obstructions_hold` (line 167) — four-way obstruction conjunction.
- `FractonNonAbelian.param_gap_grows` (line 198) — obstruction strengthens with gauge rank.

**Constraint on FG-DM:** FG e-loops are topological gauge-theory excitations, but *abelian* (they
couple to 2-form gauge fields `B̃^a` with abelian gauge structure, not to non-abelian connections
on an internal bundle). The `no_fracton_is_ym_compatible` argument does not transfer directly — FG
loops are not fractons — but the *structural* insight (topological extended objects cannot carry
non-abelian gauge charge) reinforces the FG prediction that e-loops have no SM gauge coupling.
This is consistent and mutually reinforcing, not a new constraint.

---

## 5. Cross-Connection: "Fang-Gu × ADW vestigial — two independent torsion channels"

**Roadmap W8 table entry** (Phase5x_Roadmap.md line 616): *"Two independent torsion channels coexist
in tetrad phase — both fermion-sourced (Boos-Hehl) and loop-sourced (FG), strength: High (structural)."*

**Concretely, what this means:**

1. Standard Einstein-Cartan (and ADW after condensation) contains fermion-sourced torsion:
   integrating out `T^a` from the ECSK action generates the Boos-Hehl 4-fermion contact term
   `L_{4f} = (3/16 M_P²) [α² V^μ V_μ + α β V^μ A_μ - (1 - β²) A^μ A_μ]` (research §2.3), sourced by
   `A^μ = ψ̄ γ⁵ γ^μ ψ`.

2. FG construction contains loop-sourced torsion: `T^a = l_p σ^a` where `σ^a` is the e-loop current.
   **FG explicitly states Dirac fermions do *not* source torsion in their framework** — a direct
   contradiction with standard EC.

3. **Reconciliation in a joint ADW+FG phase:** Both sources can coexist if one interprets them as
   additive contributions to `T^a`:
   `T^a = T^a_fermion (Boos-Hehl) + T^a_loop (FG-specific, l_p σ^a)`.

4. Crucially, the two channels couple to *different* auxiliary 2-form fields (`ω^ab` for fermions
   via ECSK, `B̃^a` for loops via FG). At **tree level** they are structurally orthogonal:
   integrating out fermion-sourced torsion generates a *fermion-fermion* contact (Boos-Hehl);
   integrating out loop-sourced torsion does not generate fermion-fermion couplings because FG
   loops do not enter the fermionic action at the classical level.

   **Caveat (new in this revision).** This orthogonality is a tree-level statement. At one loop,
   graviton exchange in the shared gravitational sector can mediate fermion–loop mixing: a fermion
   bilinear radiates a graviton that couples to the loop stress tensor, producing an effective
   four-point vertex suppressed by `1/M_Pl²`. This mixing is Planck-suppressed and does not change
   the qualitative "two separate channels" picture, but calling the channels *structurally
   orthogonal* requires the tree-level qualifier. Formalizing the one-loop mixing would require
   perturbative-gravity infrastructure outside the current project scope.

5. **Observational consequence:** the Boos-Hehl contact interaction — a legitimate, computable
   prediction of ADW — survives in the combined picture. FG-DM adds a parallel torsion sector that
   is detectable (in principle) only through dynamical-torsion effects on extended gravitational
   observables, at levels far below current sensitivity.

**This is a conceptual synthesis insight, not a computation.** It does not yield a new quantitative
prediction; it establishes that ADW and FG are *tree-level* compatible in the tetrad phase without
overclaiming a merger of their phenomenologies.

---

## 6. Scope of the Lean module shipped with this memo

**Session-3 revision (2026-04-22).** The prior draft of this memo concluded with "no new Lean
module in Phase 5x." Review of that draft against the research file flagged that the
traceless-T → `w = 1/3` consequence was a load-bearing falsifiability claim about whether FG
torsion DM can be CDM, and that leaving it narrative weakened the Paper 17 framing. One narrow
Lean module has therefore been added: `lean/SKEFTHawking/FangGuTorsionDM.lean` (10 theorems,
`0` sorry, `0` new axioms — only the three standard Lean axioms `propext`, `Classical.choice`,
`Quot.sound` per `lean_verify`).

**What the module is:** tree-level perfect-fluid algebra. `PerfectFluidData` struct
(`ρ`, `p`), definitions of the mixed-index trace `−ρ + 3p`, the EoS parameter `w = p/ρ`, the
dust predicate `p = 0`, and the Newtonian Poisson source `ρ + 3p`. Five main theorems:

| Theorem | Statement |
|---|---|
| `traceless_iff_w_one_third` | For `ρ > 0`, `mink_trace = 0 ↔ w = 1/3`. |
| `traceless_not_dust` | Traceless + `ρ > 0` ⇒ ¬ dust. |
| `traceless_poisson_source_doubled` | Traceless ⇒ Poisson source `= 2ρ`. |
| `dust_poisson_source_equals_rho` | Dust ⇒ Poisson source `= ρ`. |
| `fg_cdm_obstruction` | Conjunction of the above: traceless + `ρ > 0` ⇒ ¬ dust ∧ Poisson `= 2ρ`. |

Plus the converse flag `dust_not_traceless`, three concrete numerical witnesses, and a
placeholder summary theorem. All proofs close by `linarith` / `ring` / `field_simp` / `norm_num`
— no external physics input, no heartbeat overrides, no `sorry`.

**What the module is NOT:** not a full formalization of FG torsion DM. It does not encode the
TQFT action, loop condensation, or `R = 0` mechanism. It encodes the single tree-level perfect-
fluid identity that turns the traceless-T condition into a *falsifiable* obstruction on FG-DM as
CDM. That identity is load-bearing for Paper 17's framing of FG-DM as "not drop-in CDM" and
therefore worth formal status; everything else in the FG construction is narrative assessment
and remains in this memo without Lean.

**Why this is the right scope.** The alternatives considered and rejected:

- *Full 8-stage W4 pipeline.* Rejected — the FG mass spectrum is parametrically undetermined
  (no loop-condensation model in the 2021/2023 papers), so quantitative relic abundance / BBN /
  structure-formation predictions cannot be computed. No Python module, no figures, no paper
  claims beyond the kinematic obstruction are available at current theory state.
- *Zero Lean module (the prior draft).* Rejected on review — leaves the traceless-T → `w = 1/3`
  claim as narrative, loses load-bearing status for Paper 17 framing, and fails the project's
  invariant that falsifiable claims trace to formal theorems.
- *Broad FG-sector module (≥15 theorems).* Rejected — would require axiomatizing the FG TQFT
  action (not in Mathlib) or importing new topological-gravity infrastructure. Low return for
  high effort at current Phase 5x priority.

**When to revisit** (judgement flips to full pipeline with a broader Lean module):

1. A derivation of `θ` / loop-size distribution from the ADW gap equation or from Phase 5m
   quantum-group structures lands in `Lit-Search`.
2. A trace-anomalous completion (cosmic-string-gas averaging, velocity-dispersion EoS, or
   quantum trace anomaly) is published for FG e-loops, giving a macroscopic `w ≠ 1/3` and
   restoring CDM-like phenomenology.
3. W6 (vestigial relics) produces a quantitative EP-violation observable for which FG-DM's
   fermionic-loop coupling gives a *different* prediction than vestigial condensate defects.
4. A microscopic bridge between the FG TQFT levels `(k_1, k_2, k_3)` and the ADW NJL couplings
   `(G, Λ, N_f)` is found — at that point `TetradGapEquation.lean` could be extended with an
   FG-sector identification.

---

## 7. Decision / Next Step

**Recommendation: short dedicated section in Paper 17 + narrow Lean module (already shipped) +
cross-connection mention in Wave 8 synthesis.**

Specifically:

1. **Paper 17 §7 ("Torsion dark matter from topological gravity"), ≤1 page** — present FG as a
   structurally well-motivated dark-sector candidate that is **kinematically obstructed at the
   CDM level** by the traceless-T condition (`w = 1/3` tree-level). Cite
   `FangGuTorsionDM.fg_cdm_obstruction` as the formal statement. Flag the three literature
   escape hatches (cosmic-string-gas averaging, sub-sonic velocity dispersion, quantum trace
   anomaly) as *logically available but not realized in 2021/2023 FG papers*. Give the
   σ ~ 10⁻⁹⁰ cm² and `R = 0` signatures for completeness. Cite ADWMechanism /
   VestigialGravity / TetradGapEquation as the formal ADW backbone the FG picture is
   compatible with.
2. **Wave 8 synthesis cross-matrix** — include the two-channel-torsion observation with "High
   (structural, tree-level)" strength — add the tree-level qualifier. Cite this memo.
3. **Paper 17 claim discipline.** Frame FG-DM as a *compatible-but-kinematically-obstructed*
   channel, not a *verified* CDM candidate. Verified claims (from this project's Lean
   formalization): ADW phase structure; vestigial EP violation; fracton YM obstruction; FG
   kinematic obstruction (new in session 3). FG-DM is not a verified CDM candidate by this
   project. This distinction must be explicit in the paper text and in `PAPER_DEPENDENCIES`.
4. **No Python module, no new tests, no figures.** The obstruction is algebraic; the Lean
   module suffices.

**Justification (one sentence):** Fang-Gu torsion DM is internally consistent and cleanly slots
into the project's emergent-gravity architecture, but the tree-level trace condition forces a
radiation-like EoS that is incompatible with CDM — a falsifiable claim worth formalizing in a
narrow kinematic-obstruction module, not a full W4 pipeline wave.

---

## Appendix A: Mapping deep-research sections to this memo

| Memo § | Research file § | Key content |
|---|---|---|
| 2.1 | Block 1 §1.1 | Three-term topological action, level quantization |
| 2.2 | Block 1 §1.2 | ω-loop condensation → vacuum Einstein-Cartan |
| 2.3 | Block 1 §1.3, 1.5, 1.6 | Unlinked e-loops, topological stability, extended 1D objects |
| 2.4 | Block 1 §1.4 | Traceless T^μν → R = 0 mechanism |
| 2.5 | Block 5 §5.1 | ADW structural compatibility |
| 3 | Block 3 §3.1–3.4, Block 4 table | Cross-sections, detection signatures |
| 4 | Block 5 §5.2, Block 2 §2.3, 2.4 | Vestigial phase mapping, EP violation, two torsion channels |
| 5 | Block 5 §5.3 | Two-channel torsion reconciliation |
| 6 | Assessment Summary §1–4 priority gaps | Parametric undetermination, formalization upside |

## Appendix B: Files and paths referenced

Lean modules (all absolute paths under `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/`):

- **NEW this session** — `FangGuTorsionDM.lean`, 10 theorems, `0` sorry, `0` new axioms. See Appendix C.
- `ADWMechanism.lean` — 21 theorems, lines 177, 202, 229–241 cited.
- `TetradGapEquation.lean` — 20 theorems, lines 191, 205, 357, 390 cited.
- `VestigialSusceptibility.lean` — 16 theorems, lines 89, 185, 220 cited.
- `VestigialGravity.lean` — 18 theorems, lines 107, 113, 135, 143 cited.
- `FractonNonAbelian.lean` — 14 theorems, lines 76, 167, 198 cited.

Documentation:

- `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5x_Roadmap.md` (Wave 4: 354–382; Wave 8: 603–645; Paper 17: 650–663).
- `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/Lit-Search/Phase-5x/Fang-Gu Torsion Dark Matter  Phenomenology from Topological Gravity.md` (primary research source, 422 lines; kinematic obstruction flagged at lines 263–265).

External references (arXiv / journal):

- Fang & Gu, arXiv:2106.10242 (primary; trace condition at eq. 13–17).
- Fang & Gu, arXiv:2312.17196 (topological supergravity, Einstein gravity emergence).
- Volovik, arXiv:2312.09435 (ADW / vestigial gravity).
- Boos & Hehl, arXiv:1606.09273 (EC 4-fermion contact).
- Shaposhnikov & Shkerin, arXiv:2008.11686 (EC portal DM).
- LZ, arXiv:2410.17036 (direct-detection limits, 2024).
- Markevitch et al., ApJ 606, 819 (Bullet Cluster).
- Ivanov & Wellenzohn, PRD 93, 045031 (neutron UCN torsion).
- Kostelecky, Russell, Tasson, arXiv:0712.4393 (torsion LV constraints).

---

## Appendix C: `lean/SKEFTHawking/FangGuTorsionDM.lean` contents

Added in session 3 per memo revision. File lives at
`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/lean/SKEFTHawking/FangGuTorsionDM.lean`,
imported in root `SKEFTHawking.lean`, builds clean at 8419 jobs. Axioms: only `propext`,
`Classical.choice`, `Quot.sound` (`lean_verify` on `fg_cdm_obstruction`).

**Definitions.**

- `PerfectFluidData` — struct with `rho : ℝ` and `p : ℝ` fields (Inhabited).
- `mink_trace (s) := −s.rho + 3 * s.p` — mixed-index trace `T^μ_μ` in signature `(−, +, +, +)`.
- `eos_w (s) := s.p / s.rho` — equation-of-state parameter (noncomputable; total division).
- `is_dust (s) : Prop := s.p = 0` — CDM / dust predicate.
- `poisson_source (s) := s.rho + 3 * s.p` — Newtonian source `ρ + 3p`.

**Main theorems (5).**

| # | Name | Statement |
|---|---|---|
| FG1 | `traceless_iff_w_one_third` | `0 < ρ → (mink_trace s = 0 ↔ eos_w s = 1/3)` |
| FG2 | `traceless_not_dust` | `0 < ρ → mink_trace s = 0 → ¬ is_dust s` |
| FG3 | `traceless_poisson_source_doubled` | `mink_trace s = 0 → poisson_source s = 2 * s.rho` |
| FG4 | `dust_poisson_source_equals_rho` | `is_dust s → poisson_source s = s.rho` |
| FG5 | `fg_cdm_obstruction` | `0 < ρ ∧ mink_trace s = 0 → ¬ is_dust s ∧ poisson_source s = 2 * s.rho` |

**Supporting (5).**

- `dust_not_traceless` — converse flag: dust + `ρ > 0` ⇒ `mink_trace ≠ 0`.
- `witness_dust_trace_nonzero` — `mink_trace ⟨1, 0⟩ = −1`.
- `witness_radiation_traceless` — `mink_trace ⟨3, 1⟩ = 0` (concrete `w = 1/3` point).
- `witness_radiation_poisson_doubled` — `poisson_source ⟨3, 1⟩ = 6` (= 2·3).
- `fang_gu_torsion_dm_summary` — placeholder summary.

**Physical reading of `fg_cdm_obstruction`.** Any perfect-fluid FRW component with positive
energy density and traceless microscopic stress tensor is simultaneously (a) not CDM (radiation-
like scaling `ρ ∝ a⁻⁴`), and (b) sources a Newtonian Poisson equation with doubled gravitational
coupling. Fang-Gu 2021 places e-loop dark matter in exactly this regime. A CDM-like macroscopic
description requires a trace-anomalous completion not supplied by the published construction.

**What the module does not prove.** It does not rule out FG torsion DM as a dark-sector
candidate; it does not model the full TQFT action; it does not address quantum trace
anomalies or coarse-grained loop-gas averaging. Those are explicitly out of scope (see §6
revisit triggers).
