# Stage-13 Re-Review + Attribution-Content Sweep — 2026-06-10

**Authorized:** 2026-06-10 (user: "take the rest off the deferral list and continue").
**Protocol:** `docs/roadmaps/AttributionContentSweep_Roadmap.md`.
**Reviewer:** fresh-context, read-only. Pass 1 = Stage-13 re-invocation; Pass 2 =
attribution-content verification (read the cached primary source, confirm the
specific quantitative/structural claim the draft attributes to each anchor
citation). Verdicts: SUPPORTED / SUPPORTED-WITH-CAVEAT / NOT-SUPPORTED /
SOURCE-MISSING / EXEMPT-NOCACHE (textbook/pre-arXiv, no cache by design).

This is the canonical genuine-fresh-context review doc for the bundles below;
each bundle's `bundle_metadata.json` `last_stage13_review` is set to 2026-06-10
with `stage13_review_doc` pointing here (anchor `#<bundle>`).

Anchor lists: `docs/agents/claims-reviewer-bundle-prompts.md`.

---

## L1 — GW170817 / vestigial-graviton  {#l1}

**Source:** paper25. **Verifier:** lead session (direct).
**Verdict: GREEN.** 3/3 anchors SUPPORTED; both Stage-13 BLOCKERs satisfied; no
NOT-SUPPORTED findings; no edits required.

| Anchor (bibkey · claim) | Verdict | Evidence |
|---|---|---|
| `Abbott2017GW170817` · GW170817 multi-messenger speed bound `−3×10⁻¹⁵ ≤ Δc/c ≤ +7×10⁻¹⁶` (two-sided `|Δc/c| ≤ 3×10⁻¹⁵`) | SUPPORTED | Cached PDF (`Lit-Search/Phase-6a/primary-sources/Abbott2017GW170817.pdf`, ApJL 848 L13, DOI 10.3847/2041-8213/aa920c) contains `−3 × 10⁻¹⁵` in the fractional-speed-of-gravity bound — the canonical literature value. Registry title/journal/DOI correct. |
| Vestigial-graviton dispersion forecast at the project's natural `χ_vest ∈ [0.1,10]` range | SUPPORTED | Range framed as "a project-adopted order-unity" window (L1 L43–45), **not** externally attributed — the Vergeles2025 fabrication-class fix (`ca0d0f36`/`f1a0829f`) holds. `Vergeles2025` is now cited only for "unitarity of the underlying lattice-fermion framework" (L1 L96–97, L141–142), its actual PRD 112 054509 (2025) result. |
| GW170817 falsification factor `~7×10¹⁴` in the natural range | SUPPORTED | `thm:falsifier-upper` yields `\|Δc/c\|/τ ≈ 7.21×10¹⁴` at χ=10 (L1 L189–191); identical value in D3 §6 (D3 L485). Abstract "~7×10¹⁴" rounds correctly. |

**Stage-13 BLOCKERs:** (1) Δc/c numerical bound matches D3 §6 **character-for-character** — VERIFIED (L1 L40/41/110 ≡ D3 L149/150/631–633). (2) Abbott2017GW170817 bibitem cached + `doi_verified: True` — VERIFIED.

No prior `last_stage13_review` staleness (L1 not flagged by `bundle_source_freshness`); this re-review confirms the standing 2026-05-07 GREEN under the attribution-content protocol.

---

## D5 — Dark sector under substrate constraints  {#d5}

**Verifier:** read-only agent + lead adjudication. **Verdict: GREEN.** 19 anchors —
**16 SUPPORTED / 3 CAVEAT / 0 NOT-SUPPORTED.** No fabrications. DESI2025 (w0/wa,
2.8σ/4.2σ), VanWaerbeke2025 (ρ_DE≈6.7×10⁻⁹ eV⁴, ~240×), **HalenkaMiller2020**
(Verlinde >5σ under nominal assumptions, weakens with systematics — the earlier
fabrication-class fix holds, verbatim), Touboul2017/MICROSCOPE (η<10⁻¹⁵ Ti/Pt),
PlazaKraiselburd2025fR (ΔAIC≈ΔBIC≳20), Luciano (+4.7 Table II) all verbatim-confirmed.
Caveats (already hedged in draft): Tyagi −8/−13 is a GT-framework reading labelled
"Tsallis-limit"; FLS √(ρ₀a³) is draft-side "placeholder" modeling; r_d∈[144,153] Mpc
is a draft bracketing band (sources center ~147–150).

## D1 — Analog Hawking across three platforms  {#d1}

**Verifier:** read-only agent + lead adjudication (Falque PDF re-checked directly).
**Verdict: GREEN after fixes.** 12 anchors — 1 NOT-SUPPORTED + 1 CAVEAT fixed this sweep:
- **`Falque2025` §6.1 (NOT-SUPPORTED → FIXED):** draft said $c_s\approx0.40$ µm/ps measured
  "via shock-front velocimetry" — "shock" appears **0×** in Falque2025; the method is
  off-axis interferometry + spectral reconstruction of the Bogoliubov dispersion (the
  $c_s$ number is correct, only the method was fabricated). Prose corrected.
- **`Steinhauer2016` Table I (CAVEAT → FIXED):** row "$^{87}$Rb BEC (Steinhauer) ~0.35 nK"
  — 0.35 nK is de Nova's predicted value; Steinhauer's own measured $T_H$ is 1.2 nK.
  Row relabelled "(Steinhauer/de~Nova)" to match the abstract.
- SUPPORTED verbatim: Geurs2025 (de Laval nozzle + hydraulic jump), Majumdar2025
  (L/L₀>200, σ_Q≈4e²/h), deNova2019 (0.35 nK), Viermann2022 (curved-spacetime sim, not
  Hawking — hedged). SOURCE-MISSING: Zhao2023 (metadata-only cache; numbers plausible).

## E1 — Paris-LKB polariton letter  {#e1}

**Verifier:** read-only agent. **Verdict: GREEN.** 12 load-bearing claims —
**6 SUPPORTED / 6 CAVEAT / 0 NOT-SUPPORTED.** No fabrications. Highest-risk device specs
all verbatim against full-text PDFs: Falque2025 ($c_s$≈0.40 µm/ps, ξ=3.4/4.0 µm,
κ=7×10¹⁰/1.1×10¹¹ s⁻¹), Penn-TMD (g=16.8 meV, Q≈914, ~4 fJ, γ_LP=1.8 meV). Caveats:
"§IV.1" is the project's internal label for Falque §IV.A (provenance.py-consistent);
metadata-only citations (Estrecho/Stepanov/Claude/Jacquet/Grisins) rest the reservoir
percentages on provenance.py (human-verified 2026-04-28). **Registry-title hygiene
(flagged, non-blocking):** the `Amelio2020` registry `title` ("Theory of the coherence
of topological lasers") disagrees with its cached JSON ("Perspectives in superfluidity
in resonantly driven polariton fluids") — both are real Amelio–Carusotto 2020 papers, so
the right resolution depends on which E1 cites; deferred to a careful registry-hygiene
pass rather than guessed. The citation resolves correctly for E1's use either way.

## E2 — Dean-Kim-Lucas graphene letter  {#e2}

**Verifier:** read-only agent + lead adjudication (Falque PDF re-checked: "$T_{HR}=\hbar\kappa/k_B=3$ K").
**Verdict: GREEN after fixes.** 12 claims — 1 NOT-SUPPORTED + 2 CAVEAT fixed this sweep:
- **`Falque2025` (NOT-SUPPORTED → FIXED):** draft claimed graphene 2.4 K is "four orders
  of magnitude above the exciton-polariton platform's $T_H\sim0.1$ K." The "four orders"
  is wrong (it is ~1.4 orders); corrected to "more than an order of magnitude above," with
  a convention note (the $\sim0.1$ K is the standard $T_H=\hbar\kappa/2\pi k_B$, D1-table
  consistent; Falque quote the un-normalised $\hbar\kappa/k_B\approx3$ K).
- **`Geurs2025` (CAVEAT → FIXED):** draft said the analog-Hawking interpretation is "not a
  finding of Ref.[Geurs2025]" — Geurs *does* give an order-of-magnitude $T_H\sim500$ mK.
  Reworded to acknowledge Geurs' estimate while keeping the spectrum/noise-PSD as the
  Letter's own.
- **`Geurs2025` 150 K (CAVEAT → FIXED):** 150 K is the high-bias *electron* temperature
  (lattice bath ~10 K), not "ambient/operating." Symbol `T_amb`→`T_e`; prose relabelled.
- SUPPORTED verbatim: Majumdar2025 (σ_Q, L/L₀>200, η/s within ×4 of KSS), KSS2005
  (ℏ/4πk_B), Geurs2025 (440 km/s, de Laval), deNova2019 (0.35 nK).

## D3 — Emergent gravity through BH thermodynamics  {#d3}

**Verifier:** read-only agent (downloaded Sen2013 full text) + lead adjudication
(Sen2013 + DOnofrio PDFs re-checked directly). **Verdict: GREEN after fixes.** 23 anchors —
2 NOT-SUPPORTED + caveats fixed this sweep:
- **`Sen2013` §7 (NOT-SUPPORTED → FIXED):** prose gave the 4D Schwarzschild log-coefficient
  as "$-(45/2)$" — Sen's actual value is $C_{local}=212/45$, net $77/45\approx+1.71$ (PDF
  confirms "212/45"). The **Lean was already correct** (`senFourDimSchwarzschildLogCoeff
  := 212/45−3`); only the prose had drifted. Corrected to $+(212/45-3)=77/45\approx+1.71$
  vs Kaul–Majumdar $-3/2$ (disagreement narrative preserved).
- **`KLRS1996` §13 (NOT-SUPPORTED → FIXED):** "$T_c\approx159$ GeV at $m_H=125$ GeV" was
  mis-attributed to KLRS1996 (which studied $m_H=60$–180 GeV, no 159 GeV). 159 GeV is
  D'Onofrio–Rummukainen 2016 (arXiv:1508.07161, PDF cached, contains "159.5"; title
  arXiv-API-verified). Added `DOnofrioRummukainen2016` to the registry + D3 bibitem; KLRS
  retained for the crossover-existence verdict (endpoint $m_{H,c}\approx80$ GeV).
- SUPPORTED verbatim: Abbott2017GW170817 (Δc/c, both occurrences), KosteleckyRussellTasson2008
  (10⁻³¹ GeV torsion), KaulMajumdar2000 (−3/2), HalenkaMiller2020 (>5σ + systematics caveat),
  GMOR, KamLANDZen2024 (⟨m_ββ⟩, with NME-range caveat). Minor: Vassilevich "Eq 4.37" wrong
  eq-number lives only in a LaTeX comment (not rendered); Crooks1999 registry path bug
  (points to Phase-6n; file is at Phase-1-and-Background) — both noted, non-blocking.

## D8 — Kernel-Verified Universal Quantum Gate Compilation  {#d8}

**Verifier:** read-only agent (full-text where cached). **Verdict: GREEN.** 10 anchors —
3 SUPPORTED / 7 CAVEAT / 0 NOT-SUPPORTED. The highest-risk newer 6AM–6AP content verified:
AKN1998 Lemma 12.6 diamond bound (‖V V†−W W†‖_◇ ≤ 2‖V−W‖) verbatim; KMM2013ancilla
(arXiv:1212.0822) Lagrange-four-square + 2-ancilla verbatim; GilesSelinger2013 column lemma;
Selinger2015 Hyp 29 prime-distribution; DawsonNielsen honest 3.97 exponent. CAVEATs are
abstract-only caches (RossSelinger2016 deep C.x lemmas confirmed via verbatim Phase-6x/6AM
deep-research instead of the primary PDF), not attribution errors. **Doc fix:** anchor-list
L357 had wrong arXiv id for AaronsonGottesman (quant-ph/0403025=Bravyi-Kitaev; correct
quant-ph/0406196) — D8 bibliography.bib already correct; anchor-list corrected this sweep.

## L3 — BCH four laws by regime  {#l3}

**Verifier:** read-only agent (full-text Balbinot + Jacobson-Koike). **Verdict: GREEN.**
7 anchors — 5 SUPPORTED / 2 CAVEAT / 0 NOT-SUPPORTED. Balbinot2005PRD Eq.(8.4)
$T=(\hbar c/2\pi)\kappa[1-(563/720\pi)\varepsilon\kappa^3 cA_0 t]$ verbatim incl. the
563/720π coefficient (BEC-acoustic cooling primary — NOT 3He-A heating, per
`feedback_deep_research_analog_conflation`); Jacobson-Koike Eq.(13) verbatim (Schwarzschild
contrast branch); Hawking1975 (metadata-only, canonical T_H=κ/2π). M_c functional form
self-disclosed as project-original. No fabrications.

## D4 — Topological quantum computation foundations  {#d4}

**Verifier:** read-only agent. **Verdict: GREEN.** 5 anchors — 2 SUPPORTED / 2 CAVEAT /
0 NOT-SUPPORTED / 1 SOURCE-MISSING. FreedmanLarsenWang2002 (Fibonacci/SU(2) braid density,
universal) and DawsonNielsen2006 (length exponent 3.97 = log5/log(3/2), confirmed via
Phase-6p DR vs the abstract's runtime-rounded ≈2) verified. SOURCE-MISSING: AharonovArad2011
Lemma 6.1 (abstract-only cache — not a fabrication, unverifiable from cache; human PDF gate).
Caveats: DawsonNielsen "C≤4" is the exponent bound not a length constant (minor); Colangelo2025
T_c≈8.7 K matches "about 9 K".

## D6 — Formally Verified Fault-Tolerant Quantum Computation Substrate  {#d6}

**Verifier:** read-only agent + lead adjudication. **Verdict: GREEN after fix.** 9 anchors —
1 NOT-SUPPORTED fixed this sweep:
- **`BravyiKitaev2005MagicState` §5 (NOT-SUPPORTED → FIXED):** the "exact ancilla-free
  Toffoli→7-T decomposition" was attributed to Bravyi-Kitaev 2005, which is the
  *magic-state-distillation* paper and contains no such decomposition. The 7-T figure is
  correct standard physics — re-attributed to NielsenChuang2010 (the standard Clifford+T
  construction); the §5 630M/490M T-budgets (which depend on the 7× factor) are unchanged
  and correct. Orphan Bravyi-Kitaev bibitem replaced with NielsenChuang2010.
- SUPPORTED verbatim: BabbushGidneyEtAl2026ECC256Shor (1200 q/90M Toffoli, 1450 q/70M,
  secp256k1), WilliamsonYoder2026 (linear-in-weight up to polylog), DurVidalCirac2000
  (GHZ/W inequivalence), ChungHajdusekVanMeter2025 (simulators agree fidelity, differ timing),
  ShorPreskill2000 (BB84 rate). Forward-dated published venues (W-Y Nat. Phys. 2026) flagged
  for the human DOI gate (caches are arXiv preprints).

## D7 — Classical Simulability and Quantum Advantage via Tensor Networks  {#d7}

**Verifier:** read-only agent + lead adjudication. **Verdict: GREEN after cache fix.**
6 anchors — 0 NOT-SUPPORTED; 1 cache-integrity defect fixed this sweep:
- **`BiancoResta2011` cache (SOURCE-MISSING/wrong-file → FIXED):** the registry `arxiv` id
  was `1106.4014` (= Sau-Halperin-Flensberg-Das Sarma, the paper the stale cache actually
  held); the real Bianco-Resta "Mapping topological order in coordinate space" is
  `1111.5697` (title-matched). Registry id corrected + PDF re-fetched (cache now holds the
  correct paper). Background-only citation; no body claim affected.
- SUPPORTED verbatim: TindallMello…2026 (300+ qubits, BP, D-Wave Advantage2, Kibble-Zurek),
  AntaoSunFumegaLado2026 (268M sites, Chebyshev-TN, local Chern markers), ChertkovChernyak2006
  (loop series = BP + loop terms, BP exact on trees). Caveat: lattice-naming paraphrase
  ("2D square/3D cubic" vs source "cylindrical/dimerized cubic"; diamond matches) — minor.
  Forward-dated Science 2026 venue flagged for the human DOI gate.

---

## paper10_modular_generation — source-paper verification (clears D2/L2/F)  {#paper10}

**Context:** D2, L2, and F were RED because the 6 open findings of the
`2026-06-08-2242-internal-adversarial` paper10 review carried no supersession
entries. paper10 is owned by the active Phase 5q.B session; per the roadmap's
coordination gate, its supersession records must land with this sweep's D2/L2 visit.
User authorized fixing paper10 prose this session (2026-06-10).

**Finding: paper10's prose is already clean on disk** — the f6048c48 reframe
("reframe D2/L2/paper10 onto unconditional 16∣σ", 2026-06-08) plus the landed
`SpinRokhlinInterface.lean` (`SmoothSpinManifold4.rokhlin`, `sixteen_convergence_unconditional`,
2026-06-09) resolve all six. **No paper10 prose edit was needed** (verified by direct
read), so the 5q.B-owned draft is left untouched; only the supersession ledger is updated.

| Finding (2242) | Severity | Resolution on current disk (verified 2026-06-10) |
|---|---|---|
| 5.1 — 16∣σ framed as hypothesis | critical | RESOLVED: abstract L36–40 + body L226–248 call it "an unconditional kernel-pure theorem… not an assumed input" (`SmoothSpinManifold4.rokhlin`); L251 "external input" now refers only to Wang's cobordism four-phenomena equivalence (legitimately unformalized). |
| 5.2 — ChangeOfRings.lean credited with the isomorphism | critical | RESOLVED: L343–348 cite Weibel Thm 2.6.1 for the standard fact and state "`ChangeOfRings.lean` documents this isomorphism but does not itself supply a machine-checked proof." |
| 6.1 — unconditional companion not disclosed | critical | RESOLVED: L242–248 disclose both `sixteen_convergence_full` (hypothesis form) and `sixteen_convergence_unconditional`, "we cite the unconditional form for the substantive claim"; L323–324 cite the unconditional form. |
| 5.3 — abstract overstates Ext closing "why 16" | major | RESOLVED: no Ext-overstatement phrasing present; 16∣σ framed via van der Blij 8∣σ + the single 2∣σ/8 topological factor. |
| 9.1 — stale count literals (~5× off) | major | RESOLVED: counts are macro-driven (`\totaltheorems`/`\leanmodules`/`\axiomcount`); no stale `2237`/`170`/`11039`/`853` literals remain. |
| 5.4 — "physics axiom" contradicts zero-axiom | minor | RESOLVED: the "well-motivated physics axiom" phrasing is gone. |

All six superseded in `docs/review_finding_supersessions.json` (status `fixed`,
`superseded_by` = this doc). D2/L2/F thereby clear to 0 open blockers and, with the
2026-06-10 recorded review, GREEN. (2.1 cross-paper-contradiction and the 3.x scan were
already superseded prior to this sweep.)

## D2 / L2 / F — cleared via paper10 supersession  {#d2 #l2 #f}

**D2** (Anomaly constraints) / **L2** (Three generations from modular invariance) / **F**
(flagship survey) were RED solely on the 6 inherited paper10 (2242) findings, now superseded
(§paper10 above; all resolved on the current paper10 disk — no 5q.B-owned prose edit needed).
With the supersessions + the 2026-06-10 recorded review, all three clear to GREEN.
- **D2:** own anchors intact — generation constraint N_f≡0 (mod 3), the 24∣c₋ chain, Ext over
  the Steenrod subalgebra A(1); the 2026-06-08-2315 re-review had already cleared D2's
  bundle-level blockers.
- **L2:** modular-generation N_f≡0 (mod 3) + 24∣c₋ load-bearing chain, consistent with D2 §2.
- **F:** inherits all sibling corrections this sweep (D1 Falque method, D3 Sen/KLRS, E2 Falque/Geurs,
  D6 Bravyi-Kitaev→Nielsen-Chuang, D7 Bianco-Resta cache) plus the paper10 supersessions.

---

*Sweep totals (18 bundles): 6 fabrication-class NOT-SUPPORTED fixed (D1 Falque-method;
E2 Falque-4-orders; D3 Sen −45/2→212/45 + KLRS→D'Onofrio; D6 Bravyi-Kitaev→Nielsen-Chuang),
1 cache-integrity fix (D7 Bianco-Resta arxiv id), 1 new citation added+cached (DOnofrioRummukainen2016),
2 SOURCE-MISSING flagged for the human PDF/DOI gate (AharonovArad Lemma 6.1; forward-dated
published venues), 1 registry-title hygiene flagged (Amelio2020). 0 remaining open BLOCKERs
across all 18 bundles after paper10 supersession.*

## D9 — Kernel-Verified Quantum-Network and Device-Characterization Certification Substrate  {#d9}

**Verifier:** read-only agent. **Verdict: GREEN.** 16 load-bearing anchors —
11 SUPPORTED / 3 CAVEAT / 2 EXEMPT / 0 NOT-SUPPORTED. No fabrications. Verbatim-confirmed:
PLOB2017 ($-\log_2(1-\eta)$, $\eta/\ln 2$ penalty), Audenaert2007 (sharp $T\log(d-1)+H_2(T)$),
Nielsen2002 ($(dF_e+1)/(d+1)$), VidalWerner2002 (log-negativity additive, $E_D\le E_N$),
FortescueLo2007 ($D/(D+1)\to1$; optimality correctly left as the cited conjecture),
ShorPreskill2000 ($r=1-2h_2(e)$, ~11% as implicit root only), BennettDiVincenzoSmolin1997
(erasure $1-p$), Magesan2011 (RB↔diamond, model cited not proven), Jin2015 (Boltzmann thermal
population). **Two-layer posture intact at all four canonical instances**; Caves1982 ships as a
named hypothesis `hcaves` (never axiom/proof — consistent with the zero-project-local-axiom
claim). 17 textbook/pre-arXiv refs (Choi/Uhlmann/Peres/Watrous/Bhatia/…) EXEMPT-NOCACHE, all
standard facts correctly attributed. **Figures (4): all `\includegraphics`/`\ref` resolve,
captions match.** Cosmetic fix this sweep: 3 shared `fig_qnet_*` PNGs carried a stale in-image
"D6 §6" title (leftover from the D6-seeded QN figures) — titles made bundle-neutral and the D9
copies regenerated. CAVEATs: FvdG inequality + Chung fidelity-clause correct-attribution but in
non-extractable display-math; Horodecki $(2F+1)/3$ via the standard cited result.
