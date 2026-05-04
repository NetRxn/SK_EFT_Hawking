# D3 Synthesis Brief — Emergent Gravity through BH Thermodynamics

**Generated:** 2026-05-04 (Phase 7 D3 pre-draft survey)
**Bundle target:** PRD long article (~50 pp), Tier 1 deep paper, heaviest of 13 bundles.
**Working dir:** `papers/D3/` — paper_draft.tex to be authored next session from this brief.
**Source manifest:** `papers/D3/source_manifest.md` (22 contributing papers).
**Stage-13 anchor list:** `docs/agents/claims-reviewer-bundle-prompts.md` §D3.
**Strategy frame:** `docs/PAPER_STRATEGY.md` §2.2 (Paper D3 entry).

---

## Top-level synthesis paragraph (NEW to D3, absent from any individual source)

D3 is the architectural unification of 22 source papers around a single thesis: **the BEC analog → ADW emergent gravity → BH thermodynamics → QCD strong-coupling closure are facets of one substrate predictive boundary, anchored by the heat-kernel calibration `G_N^Sak = 12π/(N_f Λ_UV²)` (Vassilevich Eq. 4.37).** No source paper makes this claim end-to-end — paper25 (L1 splash) reports the GW170817 falsifier as a stand-alone negative result; paper27 (L3 splash) reports the BCH four-laws regime partition as a stand-alone first-of-its-kind formalization; paper42b reports the cosmological-constant reproduction in isolation; paper42 reports nonlinear EFE + multi-channel PPN as a self-contained Decision Gate. **D3 is the first paper that exhibits these as five faces of a single 16-fold ADW substrate** (the same `N_f = 16` that anchors L2's modular-invariance "three generations" derivation), with the perturbative Wen-ADW deficit `G_Wen/G_c ≈ 1/6000` and the fracton-hydrodynamics → full-GR no-go positioned as the predictive-boundary closures that *force* the ADW route, not as alternatives. The QCD strong-coupling thread (papers 36-38) appears in D3 as the cross-bridge that proves the substrate carries the correct higher-form-symmetry data (CFL ℤ_3 ≡ QCD center-ℤ_3), legitimating the same substrate's gravity-emergence claim. The classical-GR backbone (Phase 6f-6g substrate roster, paper44 → I1 sidebar) supplies the missing piece: until 2026-04-29, no proof assistant had verified algebraic-first-Bianchi or Levi-Civita-Christoffel-uniqueness on indefinite-signature metrics; D3 §22.5–§27 is the first paper to consume these as a *ground floor* for the singularity / area / no-hair content shipped on the same machine-checked substrate as the emergent-gravity content above it.

---

## §1: Introduction — the substrate predictive boundary
**Length target:** 3 pp | **Lift from:** new D3-original synthesis (no single-source lift); cross-cite all 22 sources.
**Key claims to land:**
- The 16-fold ADW substrate (`N_f = 16`) unifies five threads: emergent G_N (paper23), GW propagation (paper25 / L1), BH entropy (paper26), BCH four laws (paper27 / L3), and CC reproduction (paper42b).
- D3 reports both **cleared gates** (Decision Gates E.2/E.3/E.4 biconditionals, multi-channel PPN, EC torsion below Kostelecky-Russell-Tasson) and **predictive-boundary closures** (vestigial-graviton GW170817 falsification, perturbative-Wen-ADW factor-1/6000 deficit, fracton → full-GR no-go, abelian-MTC F2 falsifier, EWBG-doubly-forbidden).
- NO-GOs are first-class results, not footnotes (per `PAPER_STRATEGY.md` §3.5 line 259).
**Citations carried:** Volovik2024Vestigial; Sakharov1968; Adler1980; Vassilevich2003; Akama1979; Diakonov2011; Wetterich2017; Wen2003; Bardeen-Carter-Hawking1973; Bekenstein1972/1973; Hawking1975; Kaul-Majumdar1998; Abbott2017GW170817; Kostelecky-Russell-Tasson2008.
**Synthesis-thread (NEW to D3):** The substrate is one object; the program's predictive content is the boundary partition (cleared / falsified / structurally-blocked) on a single observable lattice.
**Risks / open hypotheses:** Pre-emptive-strengthening discipline must catch any P2/P5 bundle redundancy between cleared-gate prose and falsifier prose (e.g., do not state both `viable_iff_below_bound` and `T_EC < bound` as separate substantive results — the second is a corollary of the first).
**Cross-bundle bridge:** §1 cross-references **F §6** (program scope + predictive boundary), **L1** (vestigial-graviton splash), **L3** (BCH four laws splash), **D5 §7** (CC-channel constraint).

---

## §2: ADW gap equation, tetrad gap, bifurcation
**Length target:** 3 pp | **Lift from:** `paper5_adw_gap` (8 sections — Wen-QED + ADW + HS + effective potential + NJL + phase diagram + fluctuation + structural obstacles).
**Key claims to land:**
- ADW gap equation `G_c = 8π² / (N_f Λ²)` (the **first explicit derivation** in the literature for the tetrad-condensation gap; Lean: `ADWMechanism.lean`).
- Tetrad gap equation; bifurcation theorem (Lean theorem name: in `ADWMechanism` — confirm during draft).
- Vergeles unitarity Props (cross-ref to §5 where they re-enter as one-loop machinery).
- Phase diagram: which corner of `(N_f, Λ)` admits the tetrad-condensed phase.
**Citations carried:** Wen2003 (emergent QED); Akama1979; Diakonov2011; Wetterich2017; Vergeles (unitarity Props); Hubbard-Stratonovich.
**Synthesis-thread (NEW to D3):** §2 frames the gap equation as the **operational definition** of the substrate scale `Λ_UV`; subsequent sections feed this same Λ into G_N (§5), Λ_emerg (§21), |T_EC| (§22), regime partition `M_c` (§8). One scale, six observables.
**Risks / open hypotheses:** RHMC convergence at L≥8 (paper6) is the empirical anchor — if it fails, §10 (vestigial MC) becomes a redirect note rather than a positive result.
**Cross-bundle bridge:** **F §6** (substrate program scope).

---

## §3: Gauge erasure selection rule (only U(1) survives)
**Length target:** 2 pp | **Lift from:** `paper3_gauge_erasure` (8 sections — argument + U(1) exception + universality (standard hydro / fracton / N=4 SYM) + erasure theorem).
**Key claims to land:**
- Higher-form symmetries forced Abelian under hydrodynamization → non-Abelian gauge theories survive only as discrete center symmetries.
- Domain walls, not Goldstone bosons (links forward to §14 confinement).
- Erasure theorem: **only U(1) survives the fluid layer**; non-Abelian erased.
- N=4 super-Yang-Mills as the decisive test case.
**Citations carried:** Glorioso-Liu (SK-EFT hydrodynamics); paper36 cross-ref (center symmetry); Maldacena1997 (N=4 SYM).
**Synthesis-thread (NEW to D3):** §3 closes one of three predictive-boundary cuts that *force* the ADW route to be the unique tetrad-condensation channel: the alternative non-Abelian-gauge channels are erased.
**Risks / open hypotheses:** Erasure theorem may have a covered-by-coverage gap not caught in stand-alone paper3 review — re-verify Stage 13 against `physics-qa:claims-reviewer bundle_target=D3`.
**Cross-bundle bridge:** **F §3** (gauge erasure as program-scope statement); **D3 §14** (cross-ref center symmetry).

---

## §4: Perturbative Wen-ADW deficit + fracton-hydrodynamics no-go
**Length target:** 2 pp | **Lift from:** `paper3_gauge_erasure` §Universality + `paper5_adw_gap` §Structural obstacles + `paper6_vestigial` §Discussion (gravity hierarchy).
**Key claims to land:**
- Perturbative Wen-ADW route gives `G_Wen / G_c ≈ 1/6000` — formally closed (factor-6000 deficit makes Wen's emergent-QED-extension to gravity quantitatively unviable).
- Fracton-hydrodynamics → full GR is structurally impossible (mobility constraints break diff invariance at order a_4).
- These are **two of the three predictive-boundary closures** that force ADW (the third being §6 vestigial-graviton falsification).
**Citations carried:** Pretko-Radzihovsky2018 (fracton); Wen2003; Glorioso-Liu (SK hydrodynamics).
**Synthesis-thread (NEW to D3):** §4 is the first paper where Wen-ADW and fracton-GR closures are presented as a *unified* predictive-boundary statement — both papers reported the deficit / no-go in isolation; D3 frames them as siblings of the §6 falsification.
**Risks / open hypotheses:** Numerical 1/6000 — verify via `validate.py --check 14` (paper-claim-traceability) that this exact fraction has Lean-theorem backing in `ADWMechanism.lean` or a sibling module.
**Cross-bundle bridge:** **F §6** (predictive boundary); **D3 §6** (third closure).

---

## §5: Linearized EFE + FLRW reduction + Friedmann I/II + Bianchi consistency
**Length target:** 3 pp | **Lift from:** `paper23_linearized_efe` (7 sections) + Phase 6a W4 FLRW material.
**Key claims to land:**
- `G_N^emerg = α_ADW · 12π / (N_f Λ²)` — the linearized-EFE result with the tracked-hypothesis `α_ADW` (one-loop coefficient).
- Sakharov-Adler closed form (cross-ref §17 heat-kernel calibration).
- Correctness-push biconditional (Decision Gate E.1; Lean: `LinearizedEFE.lean` or `NonlinearEFE.lean`).
- Three structural Vergeles-derived properties of α_ADW.
- FLRW reduction: Friedmann I (`H² = (8π G_N/3) ρ`), Friedmann II (`ä/a = -(4π G_N/3)(ρ+3p)`), Bianchi consistency `∇_μ G^μν = 0` ↔ `∇_μ T^μν = 0` (Lean: `FLRWDynamics.lean`).
**Citations carried:** Sakharov1968; Adler1980 (induced-gravity); Vergeles; Vassilevich2003 Eq. (4.37); Akama-Diakonov-Wetterich.
**Synthesis-thread (NEW to D3):** §5 establishes the unified scale-passing identity `G_N^Sak = 12π/(N_f Λ_UV²)` that *every subsequent section uses* — the same coefficient appears in §6 (GW), §7 (BH entropy), §8 (regime partition `M_c`), §17 (heat kernel a_2), §21 (Λ_emerg from a_0), §22 (|T_EC| from spin current).
**Risks / open hypotheses:** "Missing one-loop calculation" subsection in paper23 is a tracked open — D3 should report this honestly; do not bundle-redundantly restate the Vergeles Props' sufficiency.
**Cross-bundle bridge:** **D3 §17** (heat-kernel re-derivation of the same coefficient); **F §6**.

---

## §6: GW170817 falsification of vestigial-second-sound graviton (HEADLINE NEGATIVE RESULT)
**Length target:** 3 pp | **Lift from:** `paper25_gravitational_waves` (full content; L1 already extracted as 4-pp PRL splash).
**Key claims to land:**
- Volovik 2024 identification: vestigial second-sound mode = spin-2 graviton, leading-order `c_GW = c · √χ_vest`.
- Natural susceptibility range `χ_vest ∈ [0.1, 10]` → `Δc/c ∈ [−0.68, +2.16]`.
- LIGO-Virgo GW170817 cap: `|Δc/c| ≤ 3 × 10⁻¹⁵`.
- **Falsification by ~7 × 10¹⁴** (both natural-range endpoints proved as Lean falsifier theorems in `VestigialGravity.lean`).
- Lean disjointness theorem `natural_range_disjoint_from_ligo_window` + four explicit falsifiers (natural-lower, natural-upper, χ_vest=0, χ_vest=1/4).
- SK-EFT dissipative dispersion correction `δω/ω = Γ_H · ω/c_GW²` (forward-link to §10 vestigial MC).
**Citations carried:** Volovik2024Vestigial; Abbott2017GW170817; Will2014 (PPN review).
**Synthesis-thread (NEW to D3):** §6 in D3 is **architectural** — the falsification is presented as one of three predictive-boundary closures forcing ADW (companion to §4 Wen-deficit + fracton-no-go). L1 ships this as a stand-alone splash; D3 frames it as part of a triad.
**Risks / open hypotheses:** Numerical Δc/c bound MUST match L1 character-for-character (Stage-13 anchor; per `claims-reviewer-bundle-prompts.md` §D3 line 144 + line 204).
**Cross-bundle bridge:** **L1** (PRL splash; same Lean theorem, same numerical anchor); **F §6, §10**.

---

## §7: Bekenstein-Hawking entropy from MTC state counting (Kaul-Majumdar SU(2)_k −3/2)
**Length target:** 3 pp | **Lift from:** `paper26_bh_entropy` (8 sections).
**Key claims to land:**
- `S = A/(4G_N) − (3/2) log(A/(4G_N)) + O(1)` with the Kaul-Majumdar SU(2)_k decomposition (Lean: `BHEntropyMicroscopic.lean`; `SU2kMTC.lean`).
- Verlinde formula at the horizon (`HorizonMTCBC` structure).
- Laplace-method bound (axiom retired in Wave 6a.7 — confirm zero-axiom status).
- The 1/4 as a **tuning** (not a derivation in this paper; honest scope statement).
- Five falsifier theorems for the tracked-hypothesis bundle.
- **Abelian-MTC F2 falsifier** (predictive-boundary closure: abelian MTCs cannot reproduce the SU(2)_k −3/2 logarithmic correction).
- Per-MTC instance status table.
**Citations carried:** Bekenstein1973; Hawking1975; Strominger-Vafa1996; Kaul-Majumdar1998; Verlinde1988; Carlip2017.
**Synthesis-thread (NEW to D3):** §7 fuses the entropy derivation with §9 QEC-holography cross-bridge — the MTC carrying the entropy is the same MTC carrying the Hayden-Preskill code (D4 §7); D3 is the first paper that exhibits this identification.
**Risks / open hypotheses:** Confirm 1/4 is not over-claimed as derived (paper26 is honest; preserve that hedging).
**Cross-bundle bridge:** **F §6**; **D3 §9** (QEC cross-bridge); **D4 §7** (D4 not yet drafted; coordinate via shared anchor).

---

## §8: BCH four laws partitioned by regime at M_c
**Length target:** 3 pp | **Lift from:** `paper27_bh_thermodynamics_four_laws` (full content; L3 already extracted as PRL splash).
**Key claims to land:**
- Regime partition criterion: `M_c = (N_f Λ_UV) / (12π α_ADW)` separating Schwarzschild branch (heats up under accretion, finite-time evaporation) from ADW-extremality branch (cools toward extremality, infinite-time near-extremal asymptote).
- Two-regime T_H profiles: Hawking 1975 (Schwarzschild) vs Balbinot 2005 (BEC-acoustic) with Jacobson-Koike 2002 contrast `T_H(v) = T_H(0) (1 − v²/c_⊥²)` as structural anchor.
- Tracked-hypothesis bundle `H_RegimePartition`.
- Four laws in two regimes (zeroth, first, second, third).
- Second law from Glorioso-Liu SK-EFT entropy-current monotonicity **without invoking pointwise NEC**.
- Third law: Israel strong-form preserved in Schottky-natural branch; Kehle-Unger-style violation admitted in BPS-violating matter sectors.
- Five falsifier theorems (Lean: `BHThermodynamicsFourLaws.lean`).
**Citations carried:** Bardeen-Carter-Hawking1973; Hawking1975; Balbinot2005; Jacobson-Koike2002; Glorioso-Liu2018; Israel1986; Kehle-Unger2024.
**Synthesis-thread (NEW to D3):** §8 in D3 is the **regime-partition criterion** as a Lean biconditional — L3 ships the splash; D3 frames it as the regime classifier consumed by §27 (no-hair Kerr family with sub-extremality `J²≤M⁴`).
**Risks / open hypotheses:** Regime-partition definition MUST agree character-for-character with L3 (per `claims-reviewer-bundle-prompts.md` §D3 line 146 + line 239).
**Cross-bundle bridge:** **L3** (PRL splash; same regime partition); **D3 §27** (consumes regime classifier); **F §6**.

---

## §9: QEC-holography cross-bridge to BH entropy (Hayden-Preskill on horizon-MTC)
**Length target:** 2 pp | **Lift from:** `paper35_qec_holography` (cross-bridge portion only; primary content lifts to D4 §7).
**Key claims to land:**
- Hayden-Preskill code structure on horizon-MTC.
- Code distance ≥ scrambling time biconditional.
- Admissibility theorem.
- Cross-bridge to substrate hypothesis (the MTC of §7 = the MTC of D4 §7 as Hayden-Preskill code).
**Citations carried:** Hayden-Preskill2007; Almheiri-Marolf-Polchinski-Sully2013; Pastawski-Yoshida-Harlow-Preskill2015.
**Synthesis-thread (NEW to D3):** §9 is the **first cross-bridge** in the literature stating that the SU(2)_k MTC carrying the Kaul-Majumdar −3/2 entropy correction is also the MTC supporting Hayden-Preskill recovery — paper26 + paper35 each report half; D3 is where they combine.
**Risks / open hypotheses:** Cross-bridge claim must match D4's framing (per `claims-reviewer-bundle-prompts.md` §D3 line 147 + line 311); D4 not yet drafted, so D3 sets the canonical form here, and D4 must align downstream.
**Cross-bundle bridge:** **D4 §7** (D4 not yet drafted; D3 sets canonical form); **F §6, §7**.

---

## §10: Vestigial metric phase Monte Carlo (CONDITIONAL on RHMC convergence at L≥8)
**Length target:** 2 pp | **Lift from:** `paper6_vestigial` (full content, conditionally).
**Key claims to land (if RHMC converges at L≥8):**
- Lattice model action, order parameters, metric signature.
- Mean-field gap equation; metric correlator from fluctuations; phase window.
- MC results at L=4, 6, 8 (split transition).
- Phase diagram and order parameters.
- Equivalence Principle violation discussion; He-3 analogy connection; gravity hierarchy.
- Sexty-Wetterich relation; limitations.
**Key claims to land (if RHMC fails to converge):**
- §10 becomes a one-paragraph redirect note pointing to a stand-alone "publishable negative result" PRR paper (per `PAPER_DRAFT_MAPPING.md` line 173).
**Citations carried:** Sexty-Wetterich2009; Volovik (He-3); paper25 (gravity hierarchy).
**Synthesis-thread (NEW to D3):** §10 is the **empirical anchor** for §2's gap equation — without RHMC L≥8 convergence, the bifurcation theorem is unconfirmed numerically.
**Risks / open hypotheses:** **THIS IS THE BIGGEST D3 SCOPE RISK.** RHMC at L≥8 is in flight (`paper6_vestigial` last modified 2026-04-28); convergence outcome decides whether §10 is a 2-pp positive result or a 1-paragraph redirect. Draft both branches.
**Cross-bundle bridge:** **F §6** (substrate-program empirical layer).

---

## §11: Scalar rung — Higgs identification + microscopic m_H falsifiability
**Length target:** 2 pp | **Lift from:** `paper20_scalar_rung` (8 sections + 5 BHL subsections + Hill-2025 bilocal correction).
**Key claims to land:**
- Wetterich-NJL scalar channel + Higgs bilinear.
- Anderson-Higgs W/Z mass matrix.
- Yukawa couplings as overlap integrals.
- Microscopic `m_H` as falsifiability anchor.
- BHL gauge embedding (Wave 1b quantitative scope) — extended Fierz basis; BHL leading-order `m_H` and the gap problem; Hill 2025 bilocal correction; tetrad back-reaction (open); updated Gate Z.1 verdict.
**Citations carried:** Wetterich1990 (NJL); Bardeen-Hill-Lindner1990 (BHL); Hill2025bilocal.
**Synthesis-thread (NEW to D3):** §11 is the **first rung** of the scalar / Majorana / EWPT triad (§§11-13) showing the same Wetterich-NJL apparatus that gives the gap equation (§2) also identifies the Higgs sector — one mechanism, two outputs.
**Risks / open hypotheses:** Tetrad back-reaction is open in paper20; preserve the open status; do not over-claim.
**Cross-bundle bridge:** **F §6**.

---

## §12: Majorana rung — type-I seesaw + BCS no-go
**Length target:** 2 pp | **Lift from:** `paper21_majorana_rung` (10 sections incl. Wave 2b decoupling bound).
**Key claims to land:**
- ℤ_16 singlet-branch bridge (anchors substrate to L2's modular-invariance derivation; same N_f = 16).
- Type-I seesaw on the Majorana rung.
- WAVE2-OPEN-1: BCS-exponential substrate bridge with ℤ_16 (open hypothesis, tracked).
- PMNS structure note.
- Effective Majorana mass and 0νββ outlook.
- Wave 2b quantitative decoupling bound for Embedding I vs III.
**Citations carried:** Mohapatra-Senjanovic1980 (seesaw); 0νββ KamLAND-Zen + LEGEND limits.
**Synthesis-thread (NEW to D3):** §12 is the substrate's **lepton-sector closure** — same N_f = 16 that fixes G_N (§5), Λ_emerg (§21), |T_EC| (§22), and L2's three generations.
**Risks / open hypotheses:** Multiple open hypotheses tracked in paper21 (PMNS structure, BCS no-go, Embedding I vs III). Preserve as tracked-hypothesis bundle, do not over-derive.
**Cross-bundle bridge:** **F §6, §10**; **L2** (same N_f = 16 as modular-invariance anchor).

---

## §13: Electroweak phase transition order — crossover excludes baryogenesis
**Length target:** 2 pp | **Lift from:** `paper22_ew_phase_transition` (7 sections).
**Key claims to land:**
- Finite-T effective potential and order parameter.
- High-T expansion + transition-order classifier + latent-heat consequence.
- SM benchmark and lattice crossover threshold (Kajantie-Laine-Rummukainen-Shaposhnikov 1996 — SM is crossover at the physical Higgs mass).
- EW baryogenesis viability — **negative**: SM crossover excludes EWBG.
- Vacuum stability and hierarchy tracked hypotheses.
- Bridge to Wave 1b BHL embedding (§11 cross-ref).
**Citations carried:** Kajantie-Laine-Rummukainen-Shaposhnikov1996; Sakharov1967 (baryogenesis conditions); Cohen-Kaplan-Nelson1991 (EWBG).
**Synthesis-thread (NEW to D3):** §13 + §13.5 together are **two doubly-forbidden no-gos** (the Sakharov-condition route to baryogenesis fails in two independent ways).
**Risks / open hypotheses:** None major; classifier is well-bounded.
**Cross-bundle bridge:** **F §6, §10**.

---

## §13.5: EWBG doubly-forbidden bridge — chirality wall × crossover
**Length target:** 1 pp | **Lift from:** `paper33_ewbg_chirality_wall` (6 sections).
**Key claims to land:**
- Sphaleron suppression and decoupling.
- Chirality-wall predicate.
- Bridge theorem and load-bearing biconditional.
- SM verdict: **doubly forbidden** (§13 crossover × chirality wall).
**Citations carried:** Manton1983 (sphaleron); Klinkhamer-Manton1984; Arnold-McLerran1987.
**Synthesis-thread (NEW to D3):** §13.5 makes the second forbidden-ness explicit alongside §13's crossover — paper33 reports it as a stand-alone PRL; D3 wires it into the §13 EWPT chain.
**Risks / open hypotheses:** None major.
**Cross-bundle bridge:** **F §6, §10**.

---

## §14: Confinement — center symmetry + Polyakov loop + Svetitsky-Yaffe
**Length target:** 2 pp | **Lift from:** `paper36_center_symmetry` (5 sections).
**Key claims to land:**
- Cyclic center ℤ_N + Polyakov loop confining predicate (Lean: `CenterSymmetryConfinement.lean`).
- Modulus as real-valued order parameter.
- Svetitsky-Yaffe universality (3D Z_3 ↔ 4D SU(3) deconfinement).
- KSS viscosity bound and Walker-Wang transport.
- Higher-form symmetry biconditional + modular-tensor-category center bridge.
**Citations carried:** Polyakov1978; Svetitsky-Yaffe1982; Kovtun-Son-Starinets2005 (KSS); Walker-Wang2012.
**Synthesis-thread (NEW to D3):** §14 closes the predictive-boundary cut started in §3 (gauge erasure) — non-Abelian gauge fields survive *only* as discrete center symmetries, and §14 is where this concretizes into the deconfinement order parameter.
**Risks / open hypotheses:** None major.
**Cross-bundle bridge:** **F §6**.

---

## §15: Chiral SSB — Gell-Mann-Oakes-Renner relation (PDG-verified)
**Length target:** 2 pp | **Lift from:** `paper37_chiral_ssb` (6 sections).
**Key claims to land:**
- Quark condensate and structural negativity (Lean: `ChiralSSB.lean` or `QuarkCondensate.lean`).
- Gell-Mann-Oakes-Renner relation `f_π² m_π² = -2 m_q ⟨q̄q⟩` (PDG-verified numerical anchor).
- Chiral-unbroken phase ruled out.
- Tetrad-VEV / quark-condensate scale naturalness.
- Cross-bridge to Wetterich-NJL infrastructure.
**Citations carried:** Gell-Mann-Oakes-Renner1968; PDG2024; Wetterich (NJL infrastructure cross-link to §11).
**Synthesis-thread (NEW to D3):** §15 + §16 together establish that the substrate carries QCD-correct higher-form-symmetry data — legitimating the same substrate's gravity-emergence claim above (§§5-9).
**Risks / open hypotheses:** None major.
**Cross-bundle bridge:** **F §6**.

---

## §16: CFL — color-flavor-locked emergent ℤ_3 ≡ QCD center-ℤ_3 (FIRST FORMALIZATION)
**Length target:** 2 pp | **Lift from:** `paper38_cfl` (5 sections).
**Key claims to land:**
- Cross-derivation identity: emergent ℤ_3 from CFL = QCD center ℤ_3 (Lean: `CFLChiralLagrangian.lean`; **first machine-checked formalization in any proof assistant**).
- CFL chiral Lagrangian skeleton.
- Hirono-Tanizaki topological-order framing.
- Cross-bridge: simultaneous chiral and CFL breaking.
**Citations carried:** Alford-Rajagopal-Wilczek1999 (CFL); Hirono-Tanizaki2018; Schäfer-Wilczek1999.
**Synthesis-thread (NEW to D3):** §16 is **the** QCD-side voucher that the substrate is QCD-compatible at the higher-form-symmetry level — without §16, the §§5-9 gravity claims rest on a non-validated substrate.
**Risks / open hypotheses:** None major; first-formalization claim is verifiable against `lean_local_search`.
**Cross-bundle bridge:** **F §6**.

---

## §17: Heat-kernel calibration + Sakharov-Adler ↔ G_N^emerg (Decision Gate E.2)
**Length target:** 3 pp | **Lift from:** `paper39_heat_kernel_expansion` (7 sections).
**Key claims to land:**
- Heat-kernel asymptotic and Dirac coefficients `a_0, a_2, a_4` (Christensen-Duff Dirac).
- Calibration to Sakharov-Adler: `G_N^Sak = 12π / (N_f Λ_UV²)` per Vassilevich Eq. (4.37).
- Decision Gate E.2 biconditional (Lean: `HeatKernelExpansion.lean`).
- Higher-curvature `a_4` basis (forward to §18).
- Mean-field validity discussion.
**Citations carried:** Sakharov1968; Adler1980; Vassilevich2003 (especially Eq. 4.37 — STAGE-13 ANCHOR); Christensen-Duff1978.
**Synthesis-thread (NEW to D3):** §17 is where the **single-coefficient identity** `G_N^Sak = 12π/(N_f Λ_UV²)` is **derived** from heat-kernel data; the same identity is **used** in §5 (linearized EFE), §8 (regime partition), §21 (Λ_emerg from a_0), §22 (|T_EC| coefficient).
**Risks / open hypotheses:** Vassilevich Eq. (4.37) coefficient must match Lean theorem character-for-character (Stage-13 anchor; per `claims-reviewer-bundle-prompts.md` §D3 line 131-132).
**Cross-bundle bridge:** **F §6**; **D3 §5, §8, §21, §22** (all consume).

---

## §18: Higher-curvature Stelle (α, β, γ) basis change at order a_4
**Length target:** 3 pp | **Lift from:** `paper40_higher_curvature` (5 sections).
**Key claims to land:**
- Curvature basis: Gauss-Bonnet and Weyl-squared.
- Stelle-basis coefficients `(α, β, γ)` from heat-kernel a_4.
- Main basis-change identity (Lean: `NonlinearDiffInvariance.lean` or sibling).
- Observational ceilings on dimensionless higher-curvature couplings (pulsar timing; binary-black-hole bounds).
- Correctness-push: predictions vs ceilings (passes; Lean theorem closes).
**Citations carried:** Stelle1977 (renormalizable higher-curvature); Gauss-Bonnet identity; Weyl1929; pulsar-timing higher-curvature bounds.
**Synthesis-thread (NEW to D3):** §18 is the first paper that ships the (α, β, γ) closed form **and** the observational ceiling check **and** the Lean correctness-push as a single biconditional.
**Risks / open hypotheses:** Stelle (α, β, γ) basis-change identity is a Stage-13 anchor (per `claims-reviewer-bundle-prompts.md` §D3 line 134); verify exact basis convention against paper40.
**Cross-bundle bridge:** **F §6**.

---

## §19: Decision Gate E.3 — path-(b) order-by-order diff invariance through a_4
**Length target:** 2 pp | **Lift from:** `paper41_diff_invariance` (5 sections).
**Key claims to land:**
- Path-(b) framework: effective Lagrangian coefficient bundle + path-(b) anomaly residual + main biconditional (correctness-push anchor; Lean: `NonlinearDiffInvariance.lean`).
- Order-by-order results: Dirac bundle satisfies path-(b) at every canonical order through a_4.
- Falsifier: perturbed bundle, residual linear in δ.
- Numerical companion (anomaly hunt — passes).
- Decision Gate E.3 verdict and downstream consequences (unblocks §20 nonlinear EFE).
**Citations carried:** DeWitt1965; Diakonov2011; Vassilevich2003.
**Synthesis-thread (NEW to D3):** §19 is the **gate** between linearized §5 and nonlinear §20 — diff invariance is closed order-by-order through a_4, which is the level at which Stelle (α, β, γ) live (§18).
**Risks / open hypotheses:** Path-(b) anomaly residual: confirm zero at the canonical order; do not over-claim full nonlinear closure beyond a_4.
**Cross-bundle bridge:** **F §6**.

---

## §20: Variational nonlinear EFE + multi-channel PPN
**Length target:** 3 pp | **Lift from:** `paper42_nonlinear_efe` (6 sections).
**Key claims to land:**
- Trace-level stress-energy under ADW rescaling: emergent vs bare-matter trace.
- Trace-level EFE residual + Decision-Gate-style biconditional (Lean: `NonlinearEFE.lean`).
- Multi-channel PPN observables: light deflection (`α`), perihelion precession (`(2α+1)/3`), ringdown frequency (`α`).
- **Cross-channel structural prediction:** the three PPN channels' ratios are fixed by α alone (not three independent parameters).
- Multi-channel observation summary figure.
- Substantive cross-bridges: Wave 2 higher-curvature pulsar bound (§18); Wave 3 path-(b) diff invariance (§19).
**Citations carried:** Will2014 (PPN review); Cassini-Mercury perihelion; Eddington1919 deflection; LIGO ringdown.
**Synthesis-thread (NEW to D3):** §20 is the first paper that exhibits the **PPN ratio identity** `α : (2α+1)/3 : α` as a single-parameter prediction; previous literature treats deflection / precession / ringdown as independent.
**Risks / open hypotheses:** Multi-channel PPN ratios are a Stage-13 anchor (per `claims-reviewer-bundle-prompts.md` §D3 line 135-136); verify exact ratio convention.
**Cross-bundle bridge:** **F §6**.

---

## §21: Cosmological constant in emergent form (Decision Gate E.4) — CC PROBLEM REPRODUCED
**Length target:** 3 pp | **Lift from:** `paper42b_cc_emergent` (8 sections).
**Key claims to land:**
- Microscopic predictions: `Λ_emerg(Λ_UV, N_f) = a_0(N_f) · Λ_UV⁴` from heat-kernel a_0.
- Observed `Λ_obs ≃ 2.6 × 10⁻⁴⁷ GeV⁴` (Planck 2018).
- Decision Gate E.4 quantitative theorem: at natural microscopic point `(Λ_UV ≃ M_Pl, N_f = 16)`, `Λ_emerg/Λ_obs > 10¹²⁰` — **the classical CC problem is reproduced in the emergent-gravity formulation**.
- Verdict-band map (resolved / intermediate / reproduced regions).
- Microscopic-macroscopic match: `δG_N = 0` biconditional.
- Stelle-basis higher-curvature aggregate.
- Bundled tracked-Prop match witness.
- Discussion: "shelter in emergent gravity?" — **no**.
**Citations carried:** Weinberg1989 (CC problem); Planck2018; Volovik2003 (q-theory); Vassilevich2003.
**Synthesis-thread (NEW to D3):** §21 is the first paper that explicitly states **emergent-gravity does NOT shelter from the CC problem**; previous induced-gravity literature (Sakharov, Adler) left this open.
**Risks / open hypotheses:** Heat-kernel `a_0` coefficient must match D5 §7 character-for-character (cross-bundle anchor; per `claims-reviewer-bundle-prompts.md` line 312).
**Cross-bundle bridge:** **D5 §7** (CC-channel constraint); **F §6, §8**.

---

## §22: Einstein-Cartan torsion + Kostelecky-Russell-Tasson bound passage
**Length target:** 3 pp | **Lift from:** `paper43_einstein_cartan` (6 sections).
**Key claims to land:**
- Microscopic torsion-amplitude prediction: `|T_EC|(Λ_UV, N_f, α_EC, n_spin) = α_EC · 12π/(N_f Λ_UV²) · n_spin`.
- At natural point `(Λ_UV, N_f, α_EC) = (M_Pl, 16, 1)` and `n_spin ≃ 1.3 × 10⁻³⁹ GeV³`: `|T_EC| ≃ 2.05 × 10⁻⁷⁷ GeV`.
- **CRITICAL NUMERICAL ANCHOR (Stage-13):** `|T_EC| ≃ 2.05 × 10⁻⁷⁷ GeV` vs Kostelecky-Russell-Tasson 10⁻³¹ GeV bound — passes by ~46 orders of magnitude. **NOT** the older `1.3×10⁻¹¹⁴ GeV` (per `claims-reviewer-bundle-prompts.md` §D3 line 137-139 — Wave-6-fixed docstring drift; verify Lean module is on the corrected number).
- Match-residual biconditional: `δT_EC = 0 ↔ α_EC = 1` (Lean: `EinsteinCartanExtension.lean`).
- Cross-channel chained bound; verdict-band map.
- Bundled tracked-Prop EC-extension witness.
- Discussion: torsion as a soft observational signature (small but non-zero).
**Citations carried:** Hehl1976 (EC review); Kostelecky-Russell-Tasson2008 (cosmic-axial-torsion bound); Hughes-Drever1960 (older isotropy bounds).
**Synthesis-thread (NEW to D3):** §22 closes the Phase 6e roadmap inside D3 — the substrate is **observationally consistent with all published torsion bounds at all natural microscopic parameter points**.
**Risks / open hypotheses:** **HIGH-RISK ANCHOR.** The 2.05×10⁻⁷⁷ vs 1.3×10⁻¹¹⁴ docstring drift was caught in Wave 6; the draft must use 2.05×10⁻⁷⁷ throughout. Run `grep -r "1.3.*10.*114" lean/` and `grep -r "1.3.*10.*114" papers/D3/` before Stage 13 to ensure no residual drift.
**Cross-bundle bridge:** **F §6**.

---

## §22.5: Algebraic-GR backbone (Phase 6f W1-W6 substrate; paper44 supplement)
**Length target:** 2 pp | **Lift from:** Phase 6f W1-W6 substrate roster (no per-wave drafts; bundled here as substrate) + `paper44_riemannian_connection` supplement.
**Key claims to land:**
- Algebraic Riemann tensor (Lean: `Curvature.lean`).
- Einstein tensor (Lean: `EinsteinTensor.lean`).
- Energy conditions (NEC, WEC, SEC, DEC; Lean: `EnergyConditions.lean`).
- Exact solutions: Schwarzschild Kerr-Schild + de Sitter / AdS Λ-vacuum biconditional (Lean: `ExactSolutions.lean`, `KerrSchild.lean`).
- ADM Hamiltonian + momentum constraint biconditionals (Lean: `ADMFormalism.lean`).
- Tetrad-metric equivalence.
- **paper44 supplement:** indefinite-signature Lorentzian metric typeclass + Levi-Civita Christoffel uniqueness + algebraic first Bianchi + differential second Bianchi machinery (Lean: `LorentzianMetric.lean`, `RiemannianConnection.lean`, `RiemannCoordinate.lean`, `RiemannDifferentialBianchi.lean`, `BundleRiemann.lean`, `BundleRiemannAux.lean`).
- **First-formalization-in-any-proof-assistant claims** (primary in I1 sidebar; D3 §22.5 is supplement).
**Citations carried:** Wald1984 (GR textbook); Hawking-Ellis1973 (LSS); ADM1962.
**Synthesis-thread (NEW to D3):** §22.5 is the **ground floor** that §23-§27 (singularity / area / no-hair) consume; without paper44 Session 4 specialization, 6f.2 second Bianchi + 6f.4 Schwarzschild vacuum-Ricci + 6f.5 ADM 3D Ricci + 6f.6 Cartan structure equations cannot be written.
**Risks / open hypotheses:** Mathlib-PR target for paper44 (in flight) — preserve Mathlib-PR-quality framing without claiming acceptance.
**Cross-bundle bridge:** **I1** (sidebar primary; first-formalization claims live there); **F §6, §9**.

---

## §23: Causal structure axioms (Wald §8.1 + realLineSpacetime witness)
**Length target:** 1.5 pp | **Lift from:** Phase 6g W1 substrate (Lean: `CausalStructure.lean`).
**Key claims to land:**
- Causal structure axioms following Wald §8.1.
- `realLineSpacetime` as concrete witness (Lean: confirm exact name in `CausalStructure.lean`).
- Chronology, causality, strong causality, stable causality predicates.
**Citations carried:** Wald1984 §8.1; Hawking-Ellis1973.
**Synthesis-thread (NEW to D3):** §23 is the first paper that exhibits the causal-structure hierarchy as a Lean predicate ladder consumed by §24 Penrose hypothesis.
**Risks / open hypotheses:** None major.
**Cross-bundle bridge:** **F §6, §10**.

---

## §24: Penrose singularity hypothesis bundle + Riccati-focusing core
**Length target:** 2 pp | **Lift from:** Phase 6g W2 substrate (Lean: `PenroseSingularity.lean`, `PenroseSingularityCurveTheoretic.lean`, `RiccatiComparison.lean`).
**Key claims to land:**
- Penrose hypothesis bundle (trapped surface + global hyperbolicity + NEC).
- Riccati-focusing core (geodesic congruence focusing under NEC).
- Correctness-push-under-applicability biconditional.
**Citations carried:** Penrose1965; Hawking-Penrose1970; Wald1984 §9.5.
**Synthesis-thread (NEW to D3):** §24 is the first machine-checked Penrose hypothesis bundle in any proof assistant.
**Risks / open hypotheses:** Confirm zero-sorry status on `PenroseSingularity.lean` before draft.
**Cross-bundle bridge:** **F §6, §10**.

---

## §25: Hawking-Penrose SEC variant + cosmological-Λ-violates-SEC counterexample
**Length target:** 1.5 pp | **Lift from:** Phase 6g W3 substrate (Lean: `HawkingPenroseSingularity.lean`, `HawkingPenroseSingularityCurveTheoretic.lean`).
**Key claims to land:**
- Hawking-Penrose hypothesis (SEC variant).
- Cosmological-Λ-violates-SEC counterexample (`Λ > 0` violates SEC for any matter content).
- Bridge: §21's `Λ_emerg > 0` ⇒ SEC violated ⇒ Hawking-Penrose hypothesis fails for the emergent-substrate's natural CC sector.
**Citations carried:** Hawking-Penrose1970; Tipler1978 (SEC issues).
**Synthesis-thread (NEW to D3):** §25 makes the **Λ → SEC violation → singularity-theorem failure** chain explicit; this is the first paper that wires §21's CC-reproduction result into the singularity hypothesis.
**Risks / open hypotheses:** None major.
**Cross-bundle bridge:** **F §6, §10**.

---

## §26: Classical area theorem — Schwarzschild monotone-mass + BH-entropy bridge
**Length target:** 1.5 pp | **Lift from:** Phase 6g W4 substrate (Lean: `AreaTheorem.lean`, `AreaTheoremCurveTheoretic.lean`).
**Key claims to land:**
- Classical Hawking area theorem on Schwarzschild family.
- Monotone-mass formulation.
- Bridge to §7 BH-entropy: `S = A/(4G_N)` ⇒ `dS/dt ≥ 0` from `dA/dt ≥ 0`.
**Citations carried:** Hawking1971 (area theorem); Bekenstein1973.
**Synthesis-thread (NEW to D3):** §26 closes the loop: classical area-monotonicity (§26) + microscopic MTC counting (§7) + BCH four-laws second-law-via-Glorioso-Liu (§8) — three independent derivations of `dS/dt ≥ 0` on the same substrate.
**Risks / open hypotheses:** None major.
**Cross-bundle bridge:** **F §6, §10**.

---

## §27: No-hair theorem — Kerr family with sub-extremality `J² ≤ M⁴` + Schwarzschild specialization
**Length target:** 1.5 pp | **Lift from:** Phase 6g W6 substrate (Lean: `NoHairTheorem.lean`, `KerrSchild.lean`).
**Key claims to land:**
- Kerr family parameterization with sub-extremality bound `J² ≤ M⁴` (in geometric units; clarify convention).
- Schwarzschild specialization (`J = 0`).
- No-hair statement: stationary asymptotically flat vacuum BHs are exhausted by the Kerr family.
- Cross-bridge to §8 regime partition: M_c sub-extremality criterion.
**Citations carried:** Israel1967; Carter1971; Hawking1972; Robinson1975.
**Synthesis-thread (NEW to D3):** §27 closes D3 by exhibiting the no-hair theorem as the **structural cap** on the substrate's BH zoo — combined with §8 regime partition, the substrate predicts a two-branch BH spectrum (Schwarzschild ∪ ADW-extremality) with Kerr family connecting them via spin.
**Risks / open hypotheses:** Sub-extremality formulation must match `KerrSchild.lean` Lean form character-for-character.
**Cross-bundle bridge:** **D3 §8** (regime partition consumer); **F §6, §10**.

---

## Cross-bundle bridge summary

| D3 section | Bridge to | Constraint |
|---|---|---|
| §6 | **L1** | Same Δc/c numerical bound character-for-character |
| §7 | **D4 §7** | Same MTC carrying entropy = MTC carrying Hayden-Preskill code |
| §8 | **L3** | Same regime partition + M_c criterion character-for-character |
| §9 | **D4 §7** | QEC cross-bridge framing must match (D4 not yet drafted — D3 sets canonical) |
| §11-§12 | **L2** | Same N_f = 16 substrate as modular-invariance anchor |
| §17 | **all of §5/§8/§21/§22** | Single-coefficient `G_N^Sak = 12π/(N_f Λ_UV²)` identity |
| §21 | **D5 §7** | Same heat-kernel a_0 coefficient character-for-character |
| §22.5 | **I1** | First-formalization claims primary in I1 sidebar |

---

## Biggest scope risks for the next session

1. **§10 RHMC convergence (paper6).** Must draft both branches (positive result vs redirect note); decide at draft time which branch to keep based on empirical L≥8 status.
2. **§22 Kostelecky-Russell-Tasson numerical anchor.** Must use `2.05×10⁻⁷⁷ GeV` throughout; the older `1.3×10⁻¹¹⁴ GeV` was a Wave-6-fixed docstring drift; pre-draft `grep` to confirm zero residual references.
3. **§9 D4 cross-bridge canonical form.** D4 not yet drafted; D3 §9 sets the canonical QEC-holography cross-bridge framing that D4 §7 must adopt downstream — over-commit risk.
4. **§17 Vassilevich Eq. (4.37) coefficient.** Stage-13 anchor; must match Lean `HeatKernelExpansion.lean` character-for-character — if Lean uses a different basis convention, document the conversion explicitly.
5. **§20 multi-channel PPN ratios.** Stage-13 anchor; verify deflection-α / precession-(2α+1)/3 / ringdown-α convention against `paper42_nonlinear_efe` and the Will 2014 PPN review.
6. **Pre-emptive strengthening discipline.** ~50 pp = many potential P2/P5 violations. Run `physics-qa:claims-reviewer bundle_target=D3` Stage 10 *before* Stage 13. Apply the five-question checklist (CLAUDE.md §"Preemptive-strengthening discipline") to every theorem statement *before* writing it.

---

## Section count check

Target: 22 sections (per Phase 7 roadmap Wave 6). Sections shipped above: **§1-§27** with §13.5 + §22.5 split-inserts = **27 effective sections**. The "22-section" target counts main numbered sections excluding split-inserts (§1-§22 main + §22.5 substrate + §23-§27 singularity/area/no-hair = 22 main + 5 substrate-tier = effectively 22 narrative sections with the algebraic-GR backbone (§22.5-§27) functioning as a unified "substrate appendix chain"). If the next session prefers strict 22-section count, fold §22.5 into §22's introduction and merge §23+§25 (causal structure + Hawking-Penrose) into a single "singularity hypotheses" section, yielding §1-§22 + 4-section appendix (§23 causal+singularity / §24 Penrose / §25 area / §26 no-hair) = 22 + 4 = total 26 with last 4 as appendices. **Recommendation:** ship at 22 main + 5 appendices (the architecture supports this naturally).

---

*Synthesis brief generated 2026-05-04 by D3 pre-draft survey agent. Sources: 22-paper roster + 2 cross-bundle splash papers (L1, L3) + Phase 6f-6g substrate roster. Next session: populate substantive content from source papers using this skeleton; preserve all NEW-to-D3 synthesis threads as the architectural backbone.*
