# Cross-Bundle Portfolio Coherence — Publication-Readiness Audit

**Auditor:** CROSS-portfolio-coherence (the whole-portfolio auditor; 13-auditor sweep)
**Date:** 2026-08-01

**Artifacts examined:** all 21 `papers/{F,D1..D12,L1,L2,L3,I1,I2,I3,E1,E2}/paper_draft.tex`;
`docs/PAPER_STRATEGY.md`; `docs/PAPER_DRAFT_MAPPING.md`; `docs/counts.tex`; `docs/counts.json`;
`lean/SKEFTHawking/**`; every `papers/<B>/source_manifest.md`; the doc/script/metadata corpus
enumerated in §5.

**Method (reproducible).** Rather than reading impressionistically I built four extractors over
all 21 drafts, with LaTeX comment lines (`%`) stripped and character→line maps preserved so every
hit carries a line number:

1. **Lean-identifier collision map** — every `\thm{…}`, `\lean{…}`, `\verb|…|` and `\texttt{…}`
   token matching `[A-Za-z][A-Za-z0-9_.']{6,}` containing `_` or `.`, deduplicated across bundles.
   Result: **1,328 distinct Lean-ish names; 199 appear in ≥2 bundles.**
2. **Near-duplicate paragraph detector** — 8-gram shingle sets per paragraph, containment
   coefficient `|A∩B| / min(|A|,|B|)`, threshold 0.30, with `\bibitem` blocks, `%%` bookkeeping
   comments and the boilerplate AI-disclosure section excluded (these produce ~290 spurious hits
   and are *not* prose duplication).
3. **Quantity probe** — 23 regexes for shared physical constants, ranges and named identities.
4. **Roster/pin/count probe** — toolchain pins, axiom-count statements, bundle-count statements.

Scripts are transient; every claim below is restated as a `file:line` + quotation so it can be
re-checked by hand.

**Scope note.** Ten sibling auditors are grading the manuscripts one bundle-family at a time. I do
not repeat their per-bundle manuscript critique (length, prose scars, figure absence, bibliography
integrity). My subject is the portfolio as a portfolio: duplication, declared boundaries,
cross-manuscript contradiction, coverage, the roster count, and whether 21 is the right number.

---

## Verdict summary

The rubric's per-bundle table does not fit a cross-cutting scope. The portfolio-level equivalent:

| Portfolio axis | Grade | One-line justification |
|---|---|---|
| **Duplication control** | **F** | D6 and D9 present **78 identical Lean theorems** in the same order; D6 §5.4 (4,067 w = 56% of D6) is D9's corpus restated. D4 §9 (3,206 w) is D8's corpus, in defiance of an explicit strategy-doc re-point. |
| **Boundary integrity** | **D** | 3 of 8 declared consumption edges exist in the manuscripts (D6→D8, D9→D8, D9→I3). 5 exist **only in the planning document** (D12→D9, I3→D3/D5/E1, D11↔D2, D10↔D11, D4→D8 re-point). |
| **Cross-manuscript consistency (physics)** | **B** | Genuinely good: every shared physical constant I probed agrees across bundles. The failures are in *metadata*, not physics. |
| **Cross-manuscript consistency (metadata)** | **F** | Four different toolchain pins across bundles (v4.28.0 / v4.29.0 / v4.29.1 / v4.32.0) for one library; five different roster counts (14/15/17) stated *inside* manuscripts, two of them in **bibitems**. |
| **Flagship coverage** | **F** | F indexes D1–D5 (9–14 references each) and mentions D6/D7/D8 once apiece. **D9, D10, D11, D12: zero references.** The declared "citation anchor / index of every machine-checked headline result" omits 7 of 12 deep papers. |
| **Roster documentation hygiene** | **F** | 51 live sites across the repo — 15 of them *inside manuscripts* — state a stale roster count or membership (13, 14, 15, 17, 18, 20, D1–D5, D1–D8, D1–D9, D1–D10). |
| **Source coverage / provenance** | **D** | 16 manifest-claimed sections across 7 bundles exist only as commented-out stubs while the append log still counts them as landed; 2 source drafts reach no bundle; D7 has no manifest at all. |
| **Portfolio sizing** | **D** | 12 Tier-1 "deep papers" total ~181 compiled pp against a ~475 pp charter. Only D3 (57 pp) meets its own target. |

**Overall: the operator's complaint is substantiated, and it is worse than "might duplicate
content."** Two Tier-1 papers targeting the same journal contain the same 78 theorems; a third
carries 3,206 words the strategy document says were moved elsewhere, including a *priority claim*
that its destination bundle also asserts.

**The two defects have a common mechanism**, and naming it matters for the fix: the bundle
architecture grew 13 → 21 by *authorizing new containers* over material that was already lifted
somewhere, without a reconciliation step that removes the old copy or records the move as executed.
§4.1 shows the receipt — the Phase 6AA staging preprint still declares itself "bundle D6 §6" while
the strategy doc assigns it to D9. Each individual authorization was defensible; the absent
step is *dissolution of the prior home*. Adding a 22nd bundle without fixing that mechanism will
reproduce the problem.

**Distance to a coherent portfolio:** `restructure` (roster consolidation + boundary enforcement),
not `copy-edit`.

---

## 1. Duplication map

### 1.1 Shared Lean theorem names — the sharpest signal

199 of 1,328 distinct Lean identifiers appear in ≥2 bundles. Grouped by the bundle set they
collide in (counts = number of distinct theorem names shared by exactly that group):

| # names | Bundle group | Verdict |
|---|---|---|
| **78** | **D6 + D9** | **REDUNDANT — P0.** See §1.2. |
| 15 | D3 + F | Legitimate (deep → flagship index). |
| 11 | D3 + I1 | Legitimate (I1 uses D3 modules as methodology worked cases). |
| 9 | D2 + L2 | Legitimate (declared L2-from-D2 carve-out). |
| 7 | D4 + F | Legitimate. |
| 7 | D3 + L3 | Legitimate (declared L3-from-D3 carve-out). |
| **5** | **D4 + D8** | **REDUNDANT — P0.** See §1.3. |
| 5 | D6 + I3 | Legitimate *if* cited; D6 uses I3's LDP modules (`CramerIID.lean`, `Sanov.lean`, `Contraction.lean`, `Varadhan.lean`, `LDPCompatibleSKEFT.lean`) — D6 does not cite I3. See §2. |
| 3 | D3 + L1 | Legitimate (declared L1-from-D3 carve-out). |
| 3 | D1 + E1 / 3 D1 + E2 / 3 D1+D7+E1+E2 | Legitimate (declared E-from-D1 carve-outs). |
| 3 | D3 + D5 + F, 3 D3+D5, 3 D5+F | Legitimate. |
| 3 | D4 + I2 | Legitimate (I2 is D4's library paper). |
| 2 | D8 + D9 | Legitimate — `diamondDist_cliffordTCompile_le` is the declared D9→D8 seam, and it **is** cited on both sides (`D8:674`, `D9:222`). This is the model the other edges should follow. |
| 2 | D1 + D7 | See §6 — D7's headline theorem lives as much in D1 as in D7. |

Full collision list is reproducible with the extractor described above; the two P0 groups are
detailed below.

### 1.2 P0 — D6 ⇄ D9: 78 shared theorems, 56% of D6 is D9's paper

`papers/D6/paper_draft.tex:504–992` is a single 489-line subsection titled

> `D6:504` `\subsection{Protocol-level extension: a verified network-fidelity envelope (Phase~6AA)}`

It runs **4,067 words** — **56% of D6's 7,227 total**. Its content is the Phase 6AA–6AK
quantum-network / diamond-norm / entropy / device-characterization corpus, which
`docs/PAPER_STRATEGY.md:160` assigns *in full* to **D9** as layers (i)–(iv) of that bundle's
charter. D9's manuscript (§2 "The diamond-norm program", §3 "The entropy and majorization corpus",
§4 "Network envelopes", §5 "The device-characterization envelope family") covers the same ground.

Sample of the 78 collisions (D6 line ↔ D9 line), all in the same conceptual order in both papers:

| Theorem | D6 | D9 |
|---|---|---|
| `traceDist_triangle` | 639 | 258 |
| `one_sub_sqrtFidelity_le_traceDist` | 665 | 269 |
| `diamondDist_ge_maxEntangled` | 680 | 321 |
| `diamondDist_eq_choiSDP` | 714 | 338 |
| `diamondDist_le_dual_witness` | 766 | 329 |
| `diamondDist_ampDamp_le` | 780 | 388 |
| `sqrtFidelity_jointly_concave` | 815 | 291 |
| `avgGateFidelity_coherenceChannel` | 832 | 756 |
| `negativityBellDiag_werner` | 882 | 496 |
| `logNegativity_add` | 910 | 509 |
| `bb84KeyRate_pos_iff_binEntropy_lt` | 569 | 629 |
| `fortescueLoYield_gt_two_thirds` | 578 | 642 |
| `plobBound_strictMonoOn` | 986 | 696 |
| `expNeg046_tight` | 560 | 947 |

They are not merely the same results — they are the same *exposition*. Compare the Fortescue–Lo
treatment:

- `D6:576–581`: "`w3_beats_ghz_randomization_advantage` proves W₃'s randomization advantage over its
  specified-pair single-copy bound (2/3) is strictly positive (reducing to the shipped
  `fortescueLoYield_gt_two_thirds`) … and `fortescueLoYield_tendsto_one` (D/(D+1)→1) matches the
  GHZ₃ rate asymptotically."
- `D9:640–645`: "Fortescue–Lo random-pair yield D/(D+1) surpasses the single-copy specified-pair
  bound ⅔ for D ≥ 3 (`\lean{fortescueLoYield\_gt\_two\_thirds}`), the W₃-vs-GHZ₃ randomization
  advantage is strictly positive (`\lean{w3\_beats\_ghz\_randomization\_advantage}`), and the yield
  tends to 1 (`\lean{fortescueLoYield\_tendsto\_one}`…)."

The only systematic difference is markup convention: D6 uses `\verb|…|` (213 occurrences, 0
`\lean{}`), D9 uses `\lean{…}` (188 occurrences, 0 `\verb`). That is the signature of the same
material being lifted twice through different tooling, not of two papers making different
contributions.

**Verdict: REDUNDANT, and a submission hazard.** Both bundles name *PRX Quantum / Quantum* as
target (`PAPER_STRATEGY.md:391, 394`). Submitting both would put duplicate-submission /
self-plagiarism material in front of the same editorial board.

**Aggravating factor (flagged for the D6 auditor, not scored here):** the D6 section is organised by
*internal phase number* — `D6:542` "Phase 6AB extensions", `D6:563` "Phase 6AC extensions",
`D6:617` "Phase 6AE (in progress): a general mixed-state / channel layer", `D6:629` "Phase 6AF: the
analytic core, discharged", `D6:782` "Phase 6AI: … (closed)". A referee reads a wave-log, not a
paper. `D6:617` also *promises work in progress* inside a submission draft.

| ID | Sev | Axis | Location | Finding | Required end state | Size |
|---|---|---|---|---|---|---|
| X-01 | P0 | 5 | `D6/paper_draft.tex:504–992` ⇄ `D9/paper_draft.tex:235–1010` | 78 shared Lean theorems; 4,067 w of D6 (56%) restates D9's declared charter content; both target PRX Quantum/Quantum | Either merge D6+D9 into one bundle (recommended, §6), or delete D6 §5.4 entirely and replace it with a 1-paragraph citation of D9 | medium (delete-and-cite) / large (merge) |

### 1.3 P0 — D4 ⇄ D8: a re-pointed section that never moved, with a duplicated priority claim

`docs/PAPER_STRATEGY.md:152` states the boundary explicitly:

> "The Phase 6p Fibonacci density + Phase 6t quantitative-SK content that the draft mapping
> previously routed to D4 §9.1–9.5 is **re-pointed to D8** as the substrate's origin point, **with a
> D4 cross-reference paragraph retained**."

`docs/PAPER_DRAFT_MAPPING.md:86–87` repeats it twice ("re-pointed from D4 §9.1-9.2 per D8
authorization 2026-05-31"; "re-pointed from D4 §9.3-9.5").

**It did not happen.** `D4/paper_draft.tex:834` still opens

> `\section{Fibonacci-anyon density in SU(2) and quantitative Solovay--Kitaev compilation}`

running lines 834–1394 = **3,206 words**, which is **62% of D8's entire 5,186-word manuscript**. It
is a full section with its own subsections (`D4:865` F.21 density, `D4:926` Dawson–Nielsen bound,
`D4:987` the eight-module Phase 6t pipeline, `D4:1064` Path A constructive compiler, `D4:1261`
"Multi-alphabet showcase: the Phase 6u/6x generic substrate") — not a cross-reference paragraph.
Shared identifiers confirm the overlap: `SolovayKitaevQuantitative.lean` (D4:1036 / D8:295),
`FibSU2Density.lean` (D4:890 / D8:296), `skLevel_polylog` (D4:978 / D8:441),
`cliffordT_accPt_one_unconditional` (D4:1297 / D8:213),
`solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_constructive_tight_unconditional`
(D4:1301 / D8:217).

Worse, both bundles assert **priority over the same result**:

- `D4:1189` `\paragraph{Primacy claim.}` … "no proof assistant has shipped a kernel-verified
  quantitative Solovay–Kitaev length bound of any form … the conservative claim form, that this
  substrate is the **first** kernel-verified quantitative Solovay–Kitaev infrastructure …"
- `D8:31–34` (abstract) "We report what is, to our knowledge, the **first** machine-checked
  development of universal quantum gate compilation as a *theory* rather than a single algorithm…"
  and `D8:42` "to our knowledge the **first** kernel-verified quantitative Solovay–Kitaev theorem at
  general dimension in any proof assistant".

A referee who receives both — plausible, since D4 names *PRX Quantum* among its targets and D8 names
*PRX Quantum* first — sees two manuscripts from one author each claiming a first over overlapping
substrate. This is the failure mode the rubric flags as P0 ("a refuted or unsupportable priority
claim").

| ID | Sev | Axis | Location | Finding | Required end state | Size |
|---|---|---|---|---|---|---|
| X-02 | P0 | 5 | `D4/paper_draft.tex:834–1394` vs `D8/paper_draft.tex` | 3,206 w of quantitative-SK content still in D4 despite two planning docs recording it as re-pointed to D8; both carry a "first kernel-verified quantitative Solovay–Kitaev" priority claim | Execute the declared re-point: delete D4 §9, leave the one declared cross-reference paragraph pointing at D8; the priority claim lives in D8 only | small (deletion) — but D4 loses 3.2k w, see §6 |

### 1.4 Substantial prose overlap (near-duplicate paragraphs)

After excluding bibliography entries, `%%` bookkeeping comments and the shared AI-disclosure block
(which are *supposed* to be identical), only **10** paragraph pairs exceed 0.30 shingle
containment. Prose duplication is genuinely low. The real hits:

| Containment | Location A | Location B | Content | Verdict |
|---|---|---|---|---|
| **1.00** | `F:546` | `D3:401` | "𝒩=4 super-Yang–Mills carries a one-form SU(N) symmetry above the conformal threshold but a ℤ_N centre at the hydrodynamic fixed point…" — 50 of 50 shingles identical | **Verbatim reuse.** F and D3 go to different journals (RMP/Phys. Reports vs PRD). Rewrite F's version as a summary or attribute-and-quote. |
| **0.84** | `F:526` | `D3:391` | Platform-universality of the erasure mechanism (Pretko–Radzihovsky, Maldacena) | Same. |
| **0.77** | `F:506` | `D3:380` | Non-Abelian one-form symmetry / colour-screening argument | Same. |
| 0.59 | `F:843` | `D2:929` | The chirality-wall gapped-interface hypothesis paragraph | Same; rewrite F's as index-level. |
| 0.45 | `F:490` | `D3:367` | Glorioso–Liu higher-form erasure statement | Same. |
| 0.41 / 0.34 / 0.33 | `F:177,955,1121` | `D3:2183,427,2183` | Predictive-register / Wen-ADW closure paragraphs | Same. |
| **0.40** | `D6:888` | `D9:500` | `NegativityMonotone.lean` — partial-transpose entanglement-monotone paragraph | Part of the §1.2 D6/D9 redundancy. |
| 0.34 | `D1:619` | `E1:301` | Shot-count/SNR comparison ("SNR ≈ 11 at G(0.1κ) ≈ 1.14 — factor 10³–10⁶ improvement") | Legitimate splash/deep, but should be phrased differently in each. |

**Verdict on F ⇄ D3:** the flagship is meant to *index* the deep papers ("summary; full content in
Tier 1 #1", `PAPER_STRATEGY.md:56–60`). Six paragraphs at 0.33–1.00 containment are not summaries;
they are the same text. Since F and D3 target different publishers, this is a
self-plagiarism/copyright exposure, not merely inelegance. **P1**, `small` per paragraph.

| ID | Sev | Axis | Location | Finding | Required end state | Size |
|---|---|---|---|---|---|---|
| X-03 | P1 | 5 | `F:490,506,526,546,843,955,1121` ⇄ `D3:367,380,391,401,427,2183` + `D2:929` | 6–7 paragraphs reused near-verbatim between the flagship and its deep papers, across different publishers | F's versions rewritten as genuine 2–4 sentence index entries with `\cite` to the deep paper | small |

### 1.5 Declared carve-outs — is the depth there?

The rubric asks whether the deep paper earns the overlap. Compiled page counts
(`pdfinfo papers/<B>/paper_draft.pdf`; see §7 for the staleness caveat):

| Family | Deep | Splash(es) | Ratio | Verdict |
|---|---|---|---|---|
| D3 / L1 + L3 | **57 pp** | 3 pp + 4 pp | 8:1 | **Healthy.** D3 adds real depth; 3 + 7 shared theorem names is right for a carve-out. |
| D2 / L2 | 11 pp | 4 pp | 2.75:1 | **Thin.** 9 shared theorem names against an 11 pp parent. D2 must roughly triple before L2's carve-out is justified. |
| D1 / E1 + E2 | **9 pp** | 5 pp + 5 pp | **0.9:1** | **Inverted — this is a real defect.** The deep paper is *smaller than its two letters combined*. `E1` and `E2` are each 5 pp against a stated 2–3 pp target, and D1 is 9 pp against a stated ~40 pp target. |

The D1 family is the clearest structural failure among the declared carve-outs: three manuscripts,
19 pp total, covering one subject, none at its own charter length.

---

## 2. Boundary integrity — declared edges vs. the manuscripts

For each boundary `docs/PAPER_STRATEGY.md` §2.2 declares, I checked whether the manuscript actually
carries the cross-reference.

| Declared edge | Strategy-doc source | Present in manuscript? | Evidence |
|---|---|---|---|
| **D6 → D8** (consumes the SK primitive) | `:152`, `:391` | ✅ **YES — exemplary** | `D6:130` `\section{The Solovay--Kitaev compilation primitive}`; `D6:138` "the sibling bundle **D8**"; `D6:140` "D6 *consumes* D8's quantitative Solovay–Kitaev headline as the per-non-Clifford-rotation compilation primitive in §§\ref{sec:gaugingQEC}–\ref{sec:wstate}". |
| **D8 → D4** (cites D4 for the Fibonacci anchor) | `:152` | ✅ YES | `D8:762` `\paragraph{Relationship to companion work.}` … "this paper cites for the Fibonacci anchor and generalizes". |
| **D4 → D8** (only a cross-ref paragraph retained) | `:152` | ❌ **VIOLATED** | D4 retains the whole 3,206-w section (§1.3). D4 mentions D8 once (`D4:~1250` region, "bundle D8"). |
| **D9 → D8** (channel/compiler seam) | `:162` | ✅ YES | `D9:220` "The verified-compilation bundle (D8) owns the surrounding territory"; `D9:225` "this paper cites D8 for the compiler layer"; `D9:1037`. Backed by a shared theorem, `diamondDist_cliffordTCompile_le` (D8:674 / D9:222). |
| **D9 → I3** (consumes LDP foundations) | `:162` | ✅ YES | `D9:232` "The stochastic-calculus bundle (I3) owns the large-deviation foundations"; `D9:798–801`. |
| **D9 ⇄ D6** (device envelopes beneath the logical layer) | `:162` | ❌ **VIOLATED — inverted** | Instead of a citation, D6 absorbed D9's corpus wholesale (§1.2). Neither paper cites the other for it: D9 §5.6 `:911` "Interface to the logical layer" does not name D6. |
| **D12 → D9** (ceilings consume D9's relaxation/thermal envelopes) | `:194` ("this is a **D12→D9 consumption edge**"), `:196` | ❌ **PLANNING-DOC ONLY** | `grep -n '\bD9\b' D12/paper_draft.tex` → **no hits in the body.** The only near-hit is `D12:482`, a filename `tests/test_bundle_formulas_d11_d12.py`. The strategy doc explicitly corrected this on 2026-07-30 and the correction never reached the manuscript. |
| **D12 → I3** (Chernoff-exponent seam consumes LDP) | `:196` | ❌ PLANNING-DOC ONLY | No `I3` reference in D12. |
| **D12 → D11 / D11 → D12** (band-theory instantiations) | `:196` | ❌ PLANNING-DOC ONLY | No cross-reference either way. |
| **D9 → D12** ("D9 gaining a citable physical floor beneath its device envelopes") | `:196` | ❌ PLANNING-DOC ONLY | F/D9 predate D12; never back-filled. |
| **D11 ⇄ D2** (who owns the 16-convergence / Phase 6CC reframe) | `:180`, `:182` | ❌ **UNRESOLVED IN BOTH** | D11 never mentions D2, `Pin⁺`, `6CC` or the 16-convergence (only `D11:430` "all sixteen vertices", unrelated). D2 never mentions D11, metamaterials or a condensed-matter reframe. The strategy leaves ownership as "attaches here **or** to D2 … at first lift"; both bundles have now lifted and **neither took it**. The reframe is orphaned. |
| **D10 ⇄ D11** (sibling substrate-breadth pair) | `:172`, `:182` | ❌ PLANNING-DOC ONLY | Neither draft mentions the other. |
| **I3 → D3 / D5 / E1** (LDP foundations consumed downstream) | `:266`, `:268` | ❌ **ASYMMETRIC** | I3 names its consumers (`I3:242` "targets (D3, D5, E1; §\ref{sec:cross-bridges})"). The consumers do not reciprocate: D3's only `LDPCompatibleSKEFT` occurrence is `D3:2428`, a `%%` **lift-note comment** (invisible in the PDF); **D5 and E1 contain no LDP / Cramér / I3 reference at all.** |
| **D6 → I3** (undeclared but real) | — | ❌ MISSING CITATION | D6 cites five I3 modules by name — `CramerIID.lean` (D6:335), `Sanov.lean` (335), `Contraction.lean` (336), `Varadhan.lean` (335), `LDPCompatibleSKEFT.lean` (336) — without naming I3 anywhere. |
| **F → D1…D12** (flagship indexes every deep paper) | `:33`, `:47`, `:50` | ❌ **MAJOR GAP** | Reference counts in F: D1=9, D2=12, D3=14, D4=11, D5=12, L1=5, L2=4, L3=3, I1=11, I2=8, E1=6, E2=6 — but **D6=1, D7=1, D8=1, I3=1, and D9=D10=D11=D12=0.** |

**Score: 3 of 14 checked edges honoured; 1 violated by absorption; 10 exist only in the plan.**

The F gap deserves its own finding. `PAPER_STRATEGY.md:33` says the flagship is "the citation anchor
… Every other paper in the program cites it," and `:47` that it must "**Index every** machine-checked
headline result and every formal NO-GO with cross-references to Tier 1 deep papers." F's 12 sections
(`F:98,287,487,576,736,898,1206,1393,1570,1727,1951,2084`) cover the original five deep papers and
contain **no section** for FT-QC (D6), tensor-network simulability (D7), gate compilation (D8),
device/network certification (D9), comp-chem (D10), band theory (D11), or detector metrology (D12).
That is seven Tier-1 bundles — more than half the deep-paper roster and, by theorem count, the
majority of the substrate — absent from the program's own survey article.

| ID | Sev | Axis | Location | Finding | Required end state | Size |
|---|---|---|---|---|---|---|
| X-04 | P1 | 5 | `D12/paper_draft.tex` (whole) | The D12→D9 consumption edge, explicitly recorded as a correction in `PAPER_STRATEGY.md:194`, is absent from the manuscript. D12's composite ceilings cite no source for the relaxation/thermal envelopes they compose. | D12 §5 cites D9 for `readoutDecayProb_enclosure` / thermal-assignment floors; D9 gains a reciprocal forward pointer | small |
| X-05 | P1 | 5 | `D5/paper_draft.tex`, `E1/paper_draft.tex`, `D3:2428` | I3 names D3/D5/E1 as its downstream consumers; none of the three cites I3. D3's only reference is inside a `%%` comment. | Each consumer cites I3 where it invokes `LDPCompatibleSKEFT` / Cramér, or I3 drops the claim | small |
| X-06 | P1 | 5 | `D6:335–336` | D6 cites five I3 modules by filename without naming or citing I3 | Add the I3 citation | trivial |
| X-07 | P1 | 5 | `D11/paper_draft.tex`, `D2/paper_draft.tex` | The Phase 6CC 2D-class-D SPT / Pin⁺ reframe was left as "attaches to D11 **or** D2 at first lift"; both have lifted and neither claims it. Content orphaned. | Assign ownership in the strategy doc and land it, or record it explicitly as deferred in both manuscripts | small (decision) + new-work (content) |
| X-08 | P1 | 1,5 | `F/paper_draft.tex` §§1–12 | Flagship has zero references to D9/D10/D11/D12 and one each to D6/D7/D8/I3; charter requires it to index all Tier-1 results | Either add index sections for the 7 uncovered bundles (~25–35 pp of new writing) or shrink the roster so F's coverage matches (see §6) | substantial-new-writing |
| X-09 | P2 | 5 | `D10/paper_draft.tex`, `D11/paper_draft.tex` | Declared sibling pair; neither manuscript acknowledges the other | Reciprocal scope paragraph, or merge (§6) | trivial |

---

## 3. Contradiction sweep

### 3.1 Physical constants — clean (a genuine strength)

I probed 23 shared quantities across all bundles. **Every shared physical value agrees.** Examples:

| Quantity | Bundles | Value | Agree? |
|---|---|---|---|
| GW170817 propagation cap | D3:149, F:990, L1:40 | `3×10⁻¹⁵` | ✅ |
| Vestigial-graviton falsification factor | D3:153, F:70, I1:1031, L1:47 | `7×10¹⁴` | ✅ |
| χ_vest natural range | D3:144, F:985, L1:43 | `[0.1, 10]` | ✅ |
| Δc/c natural range | D3:147, L1:46 | `[−0.68, +2.16]` | ✅ |
| Wen-ADW deficit | D3:35, F:192, L1:331 | `1/6000` | ✅ |
| Λ_emerg/Λ_obs | D3:49, F:83 | `10¹⁰⁰` bound, `10¹²²` heuristic | ✅ (both papers make the same rigorous/heuristic distinction) |
| Graphene Wiedemann–Franz | D1:82, E2:31, F:706 | `L/L₀ > 200` | ✅ |
| Polariton SNR | D1:621, E1:46 | `SNR ≈ 11` | ✅ |
| Critical mass `M_c` | D3:115, F:1185, L3 (macro form) | `N_f Λ_UV/(12π α_ADW)` | ✅ |
| BH entropy log correction | D3:700, F:72 | `−(3/2) log(A/4G)` | ✅ |

This is worth stating plainly because it is the portfolio's best cross-cutting property and the part
the existing claims-reviewer machinery evidently does well. The contradictions are all in
*metadata*.

### 3.2 P0 — the toolchain pin is stated four different ways

`SK_EFT_Hawking/CLAUDE.md` records the current pin: Mathlib `81a5d257` = v4.32.0 tag, toolchain
`leanprover/lean4:v4.32.0`, PhysLib `c4843367` (bumped 2026-07-29). Across the drafts:

| Pin stated | Bundles | Evidence |
|---|---|---|
| **v4.32.0 / `81a5d257` / `c4843367`** (correct) | D11, D12 | `D11:84,85,543,546`; `D12:128,129` |
| **v4.29.1 / `5e932f97`** (stale) | D2, D6, D9, L2 | `D2:15` `\newcommand{\mathlibcommit}{5e932f97}`; `D6:327` "Mathlib v4.29.1", `D6:787`; `D9:1074`; `L2:12`, `L2:387` "under Lean 4 v4.29.1 against Mathlib commit `\mathlibcommit{}`" |
| **v4.29.1** (stale, no commit) | D10 | `D10:105` |
| **v4.29.0** (stale, and never a project pin in that form) | I1, I3, E1, E2 | `I1:1182`; `I3:1197`; `E1:449,453`; `E2:484,488` |
| **v4.28.0** | I1 | `I1:1180` — *legitimate*: this is Aristotle's own pinned toolchain, correctly distinguished |

A referee reading D11 and D9 together sees the same library certified against two different
compilers. A referee reading E2 (v4.29.0) and D12 (v4.32.0) — both device-physics papers from the
same substrate — sees the same thing.

**Root cause, and why it will recur:** there is *no single source of truth for the pin*.
`docs/counts.tex` (auto-generated, `\totaltheorems`, `\axiomcount`, …) defines **no** Mathlib-commit
or toolchain macro. Instead `\mathlibcommit` is hardcoded per-draft in exactly two files —
`D2:15` and `L2:12` — and every other bundle writes the version as free text. Fixing the 32 sites
by hand will drift again at the next bump.

| ID | Sev | Axis | Location | Finding | Required end state | Size |
|---|---|---|---|---|---|---|
| X-10 | P0 | 4 | `D2:15,`; `L2:12,387`; `D6:327,787`; `D9:1074`; `D10:105`; `I1:1182`; `I3:1197`; `E1:449,453`; `E2:484,488` vs `D11:84–85`, `D12:128–129` | Four different toolchain/Mathlib pins stated across bundles for one library; ~15 stale sites | `update_counts.py` emits `\mathlibcommit`, `\physlibcommit`, `\leantoolchain` into `docs/counts.tex`; every bundle uses the macros; free-text versions deleted | small (mechanical) + trivial (script) |

### 3.3 P0 — five different roster counts stated *inside* the manuscripts

This is the manuscript-facing half of §5. Referee-visible, and two of them are in **bibitems**:

| Count | Location | Quoted text |
|---|---|---|
| **14** | `D3:2760` | bibitem: "``SK-EFT Hawking **14-bundle** publication architecture,''" |
| **14** | `D4:1500` | bibitem: "``SK-EFT Hawking **14-bundle** publication architecture,''" |
| **14** | `I3:1292` | bibitem: "*SK–EFT Hawking **14-bundle** publication architecture (project paper-strategy frame)*" |
| **15** | `D6:116` | "`\paragraph{Bundle architecture.}` D6 sits in the project's **15-bundle** …" |
| **17** | `F:134,137,852,1686,2151,2172,2189` | "`\subsection{The 17-bundle publication architecture}`"; "ships across $17$ publication targets"; bibitem `F:2189` "``SK–EFT Hawking **17-bundle** publication architecture,''" |
| **17** | `I1:189,1039,1065,1759` | "consolidates per-wave drafts into **seventeen** publication targets" (×2 in body + abstract-adjacent) |
| *(21, correct)* | — | stated nowhere in any manuscript |

Three self-citations to a *nonexistent* "14-bundle architecture" document appear in three separate
bibliographies. A referee who follows the citation finds a document that says twenty-one.

| ID | Sev | Axis | Location | Finding | Required end state | Size |
|---|---|---|---|---|---|---|
| X-11 | P0 | 4 | `D3:2760`, `D4:1500`, `I3:1292`, `D6:116`, `F:134,137,852,1686,2151,2172,2189`, `I1:189,1039,1065,1759` | Manuscripts state the roster as 14, 15 and 17 — three of them in bibitems, one in a section heading. Truth is 21 (or whatever §6 settles on). | A single `\bundlecount` macro in `counts.tex`; all free-text counts and the bibitem titles regenerated | small |

### 3.4 Theorem / axiom counts — mostly clean, with a gap

`docs/counts.tex` (regenerated 2026-08-01) is canonical: `\totaltheorems{26103}`,
`\leanmodules{2012}`, `\axiomcount{0}`, `\sorrycount{0}`. I independently confirmed the axiom count
is genuinely 0: `grep -rnE "^[[:space:]]*axiom [A-Za-z_]" lean/SKEFTHawking/` returns 8 hits, **all
of which are docstring continuation lines**, not declarations.

Macro adoption is uneven, which is the same failure mode as the pin:

| Uses `counts.tex` macros | Hardcodes literals or omits |
|---|---|
| F(13 macro uses), D2(17), L2(10), I1(8), D5(6), E1(4), D9(3), D12(3), D6(3), L1(2), I2(2), D1(1), I3(1), L3(1), E2(1) | **D7 (0 references to counts.tex at all), D10 (0), D3 (0 macro uses), D4 (0), D8 (1), D11 (7 but 0 macros)** |

`D9:118,1067` hardcodes "103 Lean modules"; `I2:575,683` hardcodes "245 theorems / 27 modules";
`I3:31,202,219,303` hardcodes "12 Lean modules". These are *per-bundle* scopes and may well be
correct — but they are not regenerated, so they will silently rot. Not a contradiction today;
flagged as a maintenance hazard.

**One residual internal slip (not a cross-bundle contradiction):** `D2:195` says a falsifying
construction "would refute `gapped_interface_axiom`", while `D2:78` and `D2:141` correctly say that
axiom "was converted to a tracked `Prop`" on 2026-05-19. D4:766, D5:161, F:848, I1:611 and L2:390 all
state the converted status consistently. So the portfolio agrees; D2 contradicts *itself* in one
sentence. **P3**, `trivial`, for the D2 auditor.

---

## 4. Coverage and orphans

**Census.** `papers/` holds **45** per-wave source directories (`paper1_*`…`paper45_*`,
`note_rt_ch_bounds`, `experimental_predictions`, `phase6AA_qnetwork_preprint`).
`docs/PAPER_DRAFT_MAPPING.md` §1 names **41** of them. In the other direction, **0** mapping rows
name a directory that does not exist. The 23 `_phase6*_lean_only` / `*_writeup` handles are
sourceless by design (`find papers -maxdepth 1 -iname '*_lean_only*'` → empty) and are not orphans.

### 4.1 Orphan sources — 4 confirmed

| Source dir | In mapping? | Content in any bundle? | Verdict |
|---|---|---|---|
| **`paper31_vestigial_inflation_no_go`** | `grep -c` → **0** | Probes `hilltop` / `slow-roll` / `inflation` → **D3: 0, F: 0, D5: 1** (incidental) | **TRUE ORPHAN.** Title: "Vestigial natural-branch slow-roll inflation cannot reproduce…"; §3 "The η-problem at the natural hilltop". A structural NO-GO — exactly the class `PAPER_STRATEGY.md:32` calls "first-class deliverables" — that reaches **no bundle at all**. |
| **`experimental_predictions`** | **0** | 11 distinctive numeric constants from `prediction_tables.tex` → **0 overlap with D1** | **TRUE ORPHAN.** "Spectral Predictions for Analog Hawking Radiation: Platform-Specific Tables from SK-EFT" — §§ Platform Parameters / Spectral Predictions / Detector Requirements / Kappa-Scaling Test. Note D1, D3, D4, D6, D7, D10–D12 all have **zero tables**; here is a directory of ready-made ones that never landed. |
| **`paper45_phase6m_review`** | **0** | Subject matter *is* in D5 (26–29 hits on `causal-set`/`entropic`/`Jacobson`) — but via two *separate* synthetic rows (`D5_phase6m_lean_only`, `_phase6m_lean_closure_`, mapping :69–70) | **BYPASSED, not lost.** Content landed; this specific draft is untracked. Low risk, but it means the mapping cannot answer "did paper45 land?" |
| **`phase6AA_qnetwork_preprint`** | 1 prose mention (mapping :106 region), no §1 row | Partial: 1 of 4 distinctive constants reaches D9 | **ORPHANED FROM THE TABLE — and the smoking gun for X-01.** See below. |

**The `phase6AA` attribution conflict explains the D6/D9 duplication.** The preprint's own header
still reads:

> `papers/phase6AA_qnetwork_preprint/preprint_draft.md:7` — "**Bridging preprint draft — SK_EFT_Hawking
> bundle D6 §6 (Phases 6AA–6AD).**"

while `docs/PAPER_STRATEGY.md:164` names the same file as **D9's** staging draft. The Phase
6AA–6AD network corpus was routed to D6 first, lifted there (→ `D6:504–992`), and then D9 was
authorized on 2026-06-10 over the same material and lifted it again. **Neither lift removed the
other.** X-01 is not a drafting accident; it is an un-reconciled re-authorization, and the stale
header is the surviving evidence.

### 4.2 Manifest → draft drift: 16 "lifted" sections that never rendered

All 20 present manifests are auto-generated from `PAPER_DRAFT_MAPPING.md` by
`scripts/bundle_source_manifest.py`, so a manifest row is a *claim of a landing*. Sixteen such rows,
across **7 bundles**, were registered in `append_log.json` (`"stage13_redo_required": true`) but
the LaTeX is a commented-out stub placed **after `\end{thebibliography}`**. Verified by
`grep -c "no rendered content" papers/*/paper_draft.tex`:

`D1: 4 · I1: 3 · D4: 3 · D2: 2 · D5: 2 · L1: 1 · I2: 1` — 16 total; all other bundles: 0.

Each carries the identical marker, e.g. `papers/D1/paper_draft.tex:1189`:

> "%% (Section heading + label commented out 2026-05-06 Session 2: empty post-bibliography stub from
> `bundle_append.py` default-insertion; bookkeeping anchor preserved as LaTeX comment, no rendered
> content. **Append-log entry retains source-contribution registration.**)"

That last sentence is the defect: the append log still counts the contribution. Representative
casualties — D1 §3 "BEC SK-EFT geometric envelope (NOT Gevrey-1)", D1 §5 "LDP linear-response
framework", D1 §6 "Quantum Crooks no-go (Perarnau-Llobet)", D1 §6 "Boostless/Carrollian soft
theorems", D2 §3 (SymTFT/Drinfeld-centre), D4 §6 (Lindbladian S-matrix NO-GO), D4 §8 (ETH refutation
tableau), D5 §13 (bootstrap-uniqueness NO-GO landscape), L1 §4 (Kerr-Schild single-copy).

**The worst case is I2.** `papers/I2/paper_draft.tex:1013` is a stub — and
`_phase6n_W1b_lean_only` is **I2's only manifest-listed source**. I2's real content
(VerifiedJackknife, Hopf extensions, MTC instances) is present but traces to unlisted Phase 5c/5o
material. So I2's manifest describes a contribution the paper does not contain, and omits everything
it does.

This also bears on §1: **D1 is 73% below its target while carrying four un-rendered sections.** Some
of the deep papers' length shortfall is content that was written, registered as landed, and then
commented out.

### 4.3 Mapping rows asserting landings that did not occur

**(a) The D4→D8 re-point.** `PAPER_DRAFT_MAPPING.md:86,87` record `_phase6p_W2cd_lean_only` and
`_phase6t_lean_only` as "**D8 §1/§2** … re-pointed from D4 §9.1–9.5" with disposition "Synthesize
(re-pointed to D8)". The content is still in D4 (`D4:834–1394`). X-02 from the coverage side.

**(b) The flagship rows.** Eleven mapping rows for the compilation/certification corpus end
"+ **F §7**" (`PAPER_DRAFT_MAPPING.md:86,87,96,97,99,100,101,102,103,104,105`). F mentions D8 exactly
**once** and D9–D12 **zero** times (§2). None of these landings occurred.

### 4.4 Unsupported bundles

**`papers/D7/source_manifest.md` does not exist** — 20 of 21 bundles have one
(`ls papers/*/source_manifest.md | wc -l` → 20). `papers/D7/bundle_metadata.json` carries
`"source_manifest_last_regen": null` alongside `"stage13_status": "green"`. So the portfolio's
shortest manuscript (3 pp) is also the only one with no recorded provenance, and it is marked green.

| ID | Sev | Axis | Location | Finding | Required end state | Size |
|---|---|---|---|---|---|---|
| X-12 | P1 | 6 | `docs/PAPER_DRAFT_MAPPING.md:86,87,96,97,99–105` | 11 rows assert an "F §7" flagship landing that never happened; 2 rows assert a D4→D8 re-point that never happened | Land the content or mark the rows `deferred`; a mapping that records intent as fact is worse than none | medium |
| X-15 | P0 | 1,6 | `D1:1186–1232` (4), `I1:1834–1872` (3), `D4:1525–1567` (3), `D2:1376–1403` (2), `D5:1496–1522` (2), `L1:378`, `I2:1013` | 16 manifest-claimed sections exist only as commented-out post-bibliography stubs while `append_log.json` still registers the contribution as landed | Render the content or de-register it; `validate.py` gains a check that a manifest row with an append-log entry has rendered LaTeX | medium |
| X-16 | P1 | 6 | `papers/paper31_vestigial_inflation_no_go/`, `papers/experimental_predictions/` | Two source drafts map to no bundle and appear in none; paper31 is a structural NO-GO (a declared first-class output class), `experimental_predictions` is a set of ready tables in a portfolio where 8 bundles have zero tables | Assign both (paper31 → D3 or D5; `experimental_predictions` → D1/E★) or record them as deliberately retired | small |
| X-17 | P1 | 6 | `papers/D7/` (no `source_manifest.md`; `bundle_metadata.json` `source_manifest_last_regen: null`, `stage13_status: green`) | The only bundle with no provenance manifest is also the shortest draft and is marked Stage-13 green | Regenerate the manifest; re-open Stage 13 (moot if D7 folds into D1 per §6) | trivial |
| X-18 | P2 | 6 | `papers/phase6AA_qnetwork_preprint/preprint_draft.md:7` | Staging preprint's header claims bundle **D6 §6**; `PAPER_STRATEGY.md:164` claims **D9** — the un-reconciled re-authorization that produced X-01 | Reconcile to whichever bundle survives §6, and add the file as a tracked mapping row | trivial |

---

## 5. The roster question — every inconsistent statement

`docs/PAPER_STRATEGY.md:27,68,405` and `scripts/bundle_registry.py:87–201` are correct and current:
**21 targets** — F, D1–D12, L1–L3, I1–I3, E1, E2. `bundle_registry.py` (created 2026-07-30) is the
machine source of truth, and `validate.py --check bundle_registry_consistency` enforces it against
every Python consumer, so **no script hardcodes a stale roster**. The drift is entirely in prose.

The workspace-level `CLAUDE.md`'s "20 / D1–D11" is *not* the only stale site — it is one of **51**
(15 inside manuscripts, 36 in docs/scripts). Complete list, grouped by what they claim. Dated
historical snapshots are listed separately at the end and need no action.

### 5.1 Manuscript-internal (referee-visible — the worst class)

| # | File : Line | Claims |
|---|---|---|
| 1 | `papers/D3/paper_draft.tex:2760` | bibitem "SK-EFT Hawking **14-bundle** publication architecture" |
| 2 | `papers/D4/paper_draft.tex:1500` | bibitem "**14-bundle**" |
| 3 | `papers/I3/paper_draft.tex:1292` | bibitem "**14-bundle**" |
| 4 | `papers/D6/paper_draft.tex:116` | "D6 sits in the project's **15-bundle** …" |
| 5–11 | `papers/F/paper_draft.tex:134,137,852,1686,2151,2172,2189` | "**17**-bundle" ×7, incl. a `\subsection` heading and a bibitem |
| 12–15 | `papers/I1/paper_draft.tex:189,1039,1065,1759` | "**seventeen** publication targets" ×3 + "17" |

### 5.2 Repo documentation (operator-visible)

| # | File : Line | Quoted | Claims |
|---|---|---|---|
| 16 | `README.md:191` | "All **17** bundle targets are content-complete; the original 14 cleared…" | 17 |
| 17 | `README.md:240` | "organized as **17 publication targets**: one Tier-0 flagship, **eight** Tier-1 themed deep papers…" | 17 / D1–D8 |
| 18 | `README.md:261` | "all **17** bundles show 0 blockers" | 17 |
| 19 | `README.md:363` | "`papers/  # 42 per-wave drafts + 17 publication bundles`" | 17 |
| 20 | `README.md:365` | "`├── D1/ D2/ D3/ D4/ D5/ D6/ D7/ D8/ # Tier 1 deep papers`" | **membership omits D9–D12** |
| 21 | `README.md:380` | "`PAPER_STRATEGY.md  # Canonical 17-bundle architecture`" | 17 |
| 22 | `README.md:502` | "*Last updated: 2026-05-31 (… 17 publication targets)*" | 17 (whole file unsynced since 2026-05-31) |
| 23 | `SK_EFT_Hawking_Inventory_Index.md:5` (and near-dup at :13) | "**17-bundle** publication architecture (D8 added 2026-05-31)" | 17 |
| 24 | `SK_EFT_Hawking_Inventory_Index.md:406` | "(F, D1–D8, L1–L3, I1, I2, I3, E1, E2 — **17 targets**)" — *this is stated as Pipeline Invariant #14* | 17 / D1–D8 |
| 25 | `SK_EFT_Hawking_Inventory_Index.md:411` | "`## 7. Bundle status (17 publication targets)`" | 17 |
| 26 | `SK_EFT_Hawking_Inventory_Index.md:415` | "All 17 bundles are drafted (`papers/{F,D1–D8,…}` all exist)" | 17 / D1–D8 |
| 27 | `SK_EFT_Hawking_Inventory_Index.md:442` | "`papers/{F,D1,D2,D3,D4,D5,D6,D7,D8,L1,L2,L3,I1,I2,I3,E1,E2}/`" | **explicit membership, omits D9–D12** |
| 28 | `SK_EFT_Hawking_Inventory_Index.md:556` | "17-bundle publication architecture (canonical)" | 17 |
| 29 | `SK_EFT_Hawking_Inventory.md:1278` | "**17 publication bundles ALL drafted** (F, D1–D8, …)" — in the Project Status *table* | 17 |
| 30 | `SK_EFT_Hawking_Inventory.md:1288` | same, in the Project Status paragraph — **contradicts the same file's line 903** which says 21 | 17 |
| 31 | `docs/agents/claims-reviewer-bundle-prompts.md:21–22` | "one of the **17 bundle codes**: `F`, `D1`–`D8`, …" — *the document's own body has D9–D12 sections at :398,:572,:626,:734* | 17 / D1–D8 |
| 32–36 | `docs/RESEARCH_STATUS_OVERVIEW.md:484,488,492,514,587` | "= **17**", "gate × **17-bundle**", "**The 17 publication targets:**", "All 17 bundles are drafted", "**17-bundle architecture**" | 17 |
| 37 | `docs/QI_REGISTER.md:241` | "extracts … from all **17 bundle drafts**" | 17 |
| 38 | `docs/ARXIV_DEPOSIT_PLAN.md:4` | "the **17 publication bundles**" | 17 |
| 39 | `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md:281` | "**17-bundle** architecture; defines bundles eligible for late absorption" | 17 |
| 40 | `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md:68` | "does not fit any of the existing **13 bundles** … a 14th+ bundle target" — *a live procedural rule* | 13 |
| 41 | `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md:269` | "**Stage B** — … existing **13 bundle targets**" | 13 |
| 42 | `docs/WAVE_EXECUTION_PIPELINE.md:80` | "`E1`, `E2` — the **18-target architecture**" | 18 |
| 43 | `docs/WAVE_EXECUTION_PIPELINE.md:689` | "one of `F`, `D1`–`D9`, `L1`–`L3`, `I1`–`I3`, `E1`, `E2` — **18 targets**" — **this is the text of Pipeline Invariant #14 itself** | 18 / D1–D9 |
| 44 | `docs/DASHBOARD.md:98` | "**18-bundle** architecture (1 flagship F + **9** Tier 1 deep + …)" | 18 |
| 45 | `docs/DASHBOARD.md:162` | "`# Regenerates … (N-gate × 18-bundle matrix)`" | 18 |
| 46 | `docs/BUNDLE_DIRECTORY_SCHEMA.md:197` | "`_VALID_BUNDLE_TARGETS` enum now covers `F, D1–D5, L1–L3, I1, I2, I3, E1, E2` (**14** entries)" | 14 / D1–D5 |
| 47 | `docs/BUNDLE_LIFT_PROCEDURE.md:313` | "validated the procedure across all **14 bundles'**" | 14 |
| 48 | `src/core/citations.py:96` | "`# Note: publication bundles (F, D1–D5, L1–L3, I1–I3, E1, E2) are *not* registered here.`" | membership D1–D5 |
| 49 | `src/core/citations.py:8149–8150` | `'provides': ['14-bundle publication architecture (1 flagship + 5 Tier-1 deep + …)']`, `'notes': '… Verified against PAPER_STRATEGY.md 2026-05-11.'` — a **citation-registry entry describing PAPER_STRATEGY.md itself** | 14 / D1–D5 |
| 50 | `scripts/build_graph.py:123` | "`blind to the 20 bundle directories (D1–D10, E1–E2, F, I1–I3, L1–L3)`" | 20 / D1–D10 |
| 51 | *(outside this repo)* `Fluid-Based-Physics-Research/CLAUDE.md` | "1 flagship + 11 Tier 1 deep [D1–D11] …" and "**twenty**" | 20 / D1–D11 |

**The three most load-bearing** (they are rules, not snapshots, so they actively misdirect future
work): #43 `WAVE_EXECUTION_PIPELINE.md:689` (Pipeline Invariant #14 text, "D1–D9, 18 targets"),
#24 `SK_EFT_Hawking_Inventory_Index.md:406` (same invariant restated as "D1–D8, 17 targets"), and
#40/#41 `LATE_PHASE6_ABSORPTION_PROTOCOL.md:68,269` (the Stage-B authorization threshold, "13
bundles"). A future wave following any of these would mis-route or spuriously request
authorization.

**Dated historical snapshots — no action needed** (they correctly narrate the roster at their own
date: 13→14→15→16→17→18→20→21): `docs/roadmaps/Phase6i,6n,6o,6p,6v,6w,7,7a,AttributionContentSweep`,
`docs/stakeholder/Phase6n,6o,6v,6w,7 + companion_guide`, `PAPER_STRATEGY.md:341`,
`PAPER_DRAFT_MAPPING.md:88`, `SK_EFT_Hawking_Inventory.md:9,11,936`,
`SK_EFT_Hawking_Inventory_Index.md:67,81`, and the two frozen feasibility/review documents.
`.claude/worktrees/*/` mirrors of stale files are gitignored clones — fix main and re-sync the
slots, don't edit them.

| ID | Sev | Axis | Location | Finding | Required end state | Size |
|---|---|---|---|---|---|---|
| X-13 | P0 | 4 | 15 manuscript sites (§5.1) | Roster stated as 14/15/17 inside submission drafts, incl. 4 bibitems and a section heading | Single `\bundlecount` macro from `counts.tex`; regenerate | small |
| X-14 | P1 | — | 36 doc/script sites (§5.2) | Roster count/membership stale across README, both Inventory files, 5 docs/, 2 src/ sites, 1 script comment, and the workspace CLAUDE.md — including three *rule* texts | `bundle_registry.py` becomes the doc source too: generate the roster sentence, or add a `validate.py` check that greps prose for `\d+[- ]bundle` and diffs against the registry | medium |

---

## 6. Portfolio-level judgement — is twenty-one the right number?

**No. Twenty-one is roughly six too many, and the excess is concentrated in exactly the place where
the duplication lives.**

### 6.1 The evidence

Compiled page counts (`pdfinfo`) against each bundle's own stated target
(`PAPER_STRATEGY.md` §6). Bundles marked † have a PDF older than the `.tex`; for those I give the
word-count-derived estimate at the portfolio's own measured ~590 w/pp (calibrated on F: 13,577 w /
23 pp).

| Tier | Bundle | pp | Target | Words | Verdict |
|---|---|---|---|---|---|
| 0 | F † | 23 (~23) | 80–150 | 13,577 | **71% short** |
| 1 | D1 † | 9 (~11) | ~40 | 6,327 | 73% short |
| 1 | D2 | 11 | ~30 | 8,056 | 63% short |
| 1 | **D3** | **57** | ~50 | 13,914 | **at target** |
| 1 | D4 | 31 | ~40 | 8,461 | close — *but 3.2k w of it is D8's* |
| 1 | D5 † | 14 | ~40 | 8,405 | 65% short |
| 1 | D6 | 12 | ~40 | 7,227 | 70% short — *and 4.1k w of it is D9's* |
| 1 | D7 † | 3 (~3) | ~40 | 1,809 | **93% short** |
| 1 | D8 | 9 | ~45 | 5,186 | 80% short |
| 1 | D9 | 10 | ~40 | 6,671 | 75% short |
| 1 | D10 | 5 | ~40 | 2,451 | **88% short** |
| 1 | D11 | 9 | ~40 | 5,802 | 78% short |
| 1 | D12 | 11 | ~35 | 7,416 | 69% short |
| 2 | L1 / L2 / L3 | 3 / 4 / 4 | 4 | 1,965 / 2,632 / 2,264 | **all fine** |
| 3 | I1 / I2 / I3 | 23 / 15 / 18 | ~25 / ~15 / ~15 | 11,872 / 5,296 / 6,963 | **all fine** |
| 4 | E1 / E2 | 5 / 5 | 2–3 | 3,125 / 3,053 | ~2× over |

**Tier 1 aggregate: 12 papers, ~181 pp, against a ~475 pp charter — 62% short in aggregate.** Only
D3 meets its target. Meanwhile the Tier-2 and Tier-3 papers, which have *modest* targets, all hit
them. That asymmetry is diagnostic: the program is not short of results, it is short of *deep-paper
architecture*. Splitting the same substrate into more Tier-1 containers made each container thinner
without adding content — and, where two containers drew on the same substrate (D6/D9, D4/D8), it
duplicated instead of dividing.

A second diagnostic: **F, D1, D2, D3, D4, D6, D7, D10, D11, D12 and I3 contain zero figures and zero
tables** (`grep -c 'begin{figure}\|begin{table}'`). D3 is a 57-page article with no figure and no
table. Whatever else the roster does, it is not producing manuscripts shaped like the articles their
target journals print. And §4.1 found an orphaned `papers/experimental_predictions/` directory of
ready-made platform-parameter and detector-requirement tables that reached none of them.

A third: some of the shortfall is **self-inflicted rather than unwritten**. D1 is 73% below target
while carrying four sections that were lifted, registered in its append log, and then left as
commented-out stubs (§4.2). Before concluding that a bundle needs new physics, check whether its
content is sitting in the file behind `%%`.

### 6.2 Where merging produces a stronger paper

**(a) D6 + D9 + D12 → one bundle.** The strategy document has already written this paper's outline
without noticing: `PAPER_STRATEGY.md:196` — "the stack now descends **D6 (logical) → D9
(channel/device) → D12 (physical detection)**". That is a three-layer architecture, i.e. one
article's section plan, not three articles. Merging eliminates the portfolio's single largest
defect (78 duplicated theorems) *and* produces a real paper: 12 + 10 + 11 = 33 pp, minus ~7 pp of
D6/D9 double-count ≈ **26 pp**, which with the connective argument a merged paper needs reaches the
~35–40 pp PRX Quantum length honestly. Working title: *Kernel-Verified Certification of Quantum
Devices: From Detector Floors to Logical-Layer Fidelity.* All three currently name PRX Quantum /
Quantum, so there is no audience cost.

**(b) D4 §9 → D8.** Not a merge, an execution of the boundary the strategy already decided
(§1.3). D8 goes 9 → ~15 pp and owns the compilation priority claim outright; D4 goes 31 → ~25 pp and
becomes what its charter says it is — the categorical/TQC-foundations paper. Both improve.

**(c) D10 + D11 → one bundle.** Authorized the same day (2026-06-29) as one act
(`PAPER_STRATEGY.md:172,182`: "sibling to D11"; "sibling to D10"), same rationale
("public substrate-breadth extension enabled by the PhysLib dependency"), same posture
(defensive publication), overlapping venue lists (PRD / PRX Quantum). Neither manuscript cites the
other, which tells you they are not really two arguments. 5 + 9 = 14 pp → a ~20 pp *Kernel-Verified
Condensed-Matter and Molecular-Physics Substrate* is a publishable paper; two 5–9 pp defensive
publications are not.

**(d) D7 → D1.** D7 is 3 pp — the shortest thing in the portfolio and 93% below its own target. Its
headline is literally `analog_hawking_quantum_advantage_demarcation`, and its two central modules
(`AnalogHawkingDemarcation.lean`, `KibbleZurekUnruh.lean`) plus
`surface_gravity_bounds_kzm_exponent`, `analog_hawking_fourCycleFree_demarcation` and
`fourCycleFree_nonneg_iff_ldp_rate_zero` are *already cited in D1, E1 and E2*. It is a section of the
analog-Hawking paper that got a bundle. Folding it in takes D1 from 9 → ~13 pp and gives D1 a
genuinely novel closing section ("when is this platform classically simulable?"). The generic
BP/Chebyshev-TN substrate that motivated the spin-out ("24-theorem Mathlib-PR-quality BP
substrate", `PAPER_STRATEGY.md:140`) belongs in **I2**, the library paper, where a Mathlib-upstream
framing is the point.

**(e) E1 + E2 → one letter.** Each is 5 pp against a 2–3 pp target, and together they exceed their
parent D1. Two experimental teams (Paris LKB polariton; Dean/Kim/Lucas graphene) is a good reason for
two *sections*, not two PRL submissions with a shared bibliography and shared
`AcousticMetric.hawking_temp_from_surface_gravity` / `Basic.hawkingTemp` / `Basic.SonicHorizon`
theorems (E1:233–237 / E2:109–113). One 3–4 pp PRR letter — *Falsifiable Analog-Hawking Predictions
at Two Solid-State Device Platforms* — reaches both teams and is more likely to be accepted than
either alone. (If the operator's priority is per-team engagement over publication, keep two — but
then D1 must be ≥30 pp first, or the letters have no deep paper to stand on.)

### 6.3 Where the split is genuinely warranted — keep these

- **L1, L2, L3.** All three are at PRL length, all three carve a genuinely news-shaped result out of
  a much larger parent (D3 is 8× L1+L3). This is the pattern working. Do not touch it.
- **I1, I2, I3.** All at target, distinct audiences (physics-methodology / tensor-category library /
  Mathlib probability WG), distinct venues, and I3's downstream role is real even if uncited (§2).
- **D2, D3, D5.** Distinct subcommunities (HEP anomaly, gravitational physics, cosmology/DM). D3 is
  the portfolio's one healthy deep paper. D2 and D5 are short but not *duplicative* — they need
  writing, not merging.
- **D4 and D8 as separate papers** — once §6.2(b) executes. Categorical foundations (CMP-flavoured)
  and gate compilation (PRX Quantum) are genuinely different referee pools.

### 6.4 Recommended roster — 16 targets

| Tier | Target | Composition | Est. pp now → after |
|---|---|---|---|
| 0 | **F** | flagship, must index all of the below | 23 → 80+ (`substantial-new-writing`) |
| 1 | **D1** | analog Hawking + **D7** simulability demarcation | 9+3 → ~30 |
| 1 | **D2** | anomaly constraints (unchanged) | 11 → ~30 |
| 1 | **D3** | emergent gravity (unchanged) | 57 ✅ |
| 1 | **D4** | TQC/categorical foundations, **minus §9** | 31 → ~25 ✅ |
| 1 | **D5** | dark sector (unchanged) | 14 → ~30 |
| 1 | **D6★** | **D6 + D9 + D12** — device/network certification stack | 33−7 → ~35 |
| 1 | **D8** | universal compilation, **plus D4 §9** | 9 → ~15 → ~30 |
| 1 | **D10★** | **D10 + D11** — condensed-matter/molecular substrate | 14 → ~20 |
| 2 | **L1, L2, L3** | unchanged | ✅ |
| 3 | **I1, I2, I3** | I2 additionally absorbs D7's generic BP substrate | ✅ |
| 4 | **E★** | **E1 + E2** combined experimental letter | 10 → ~4 |

**8 Tier-1 deep papers instead of 12.** This is not a retreat — it is the same substrate in
containers sized to what the substrate supports. It removes the 78-theorem D6/D9 duplication, the
D4/D8 boundary breach and the duplicated priority claim, brings the flagship's coverage burden from
12 deep papers down to 8 (of which it already covers 5), and leaves every remaining bundle with a
credible path to its stated length.

**Sequencing implication:** the merges should land *before* any further Stage-13 or lift work on
D6/D7/D9/D10/D11/D12/E1/E2, or that work is spent on containers that are about to be dissolved.

**The one thing I would not do:** shrink the *targets* to match the current drafts (i.e. re-declare
the 12 deep papers as letters). Several bundles have the substrate for a real article — D8's five
alphabets, D9's five certification layers, D12's five floor/ceiling layers — and the shortfall is
writing, not physics. Redefining a 40 pp charter down to 10 pp to make the draft compliant would be
the walk-back this project's own remediation posture forbids.

---

## 7. What I could not check

- **Compile status.** I did not re-run `latexmk` on the 21 drafts; the ten sibling per-bundle
  auditors own that. Page counts in §6.1 come from the **existing** `paper_draft.pdf` artefacts.
  Five are stale (PDF mtime older than `.tex`): **F, D1, D5, D7, E1** — for these I cross-checked
  against a word-count estimate at the portfolio's measured ~590 w/pp and the two agreed within
  ~1 pp, but a re-compile could move them. Treat those five as ±2 pp.
- **Whether each cross-citation *supports* its sentence.** I verified cross-bundle citations
  *exist* (or do not). I did not verify that, e.g., D9's citation of I3 attaches to a sentence I3
  actually backs — that is Axis-4 spot-check work owned by the per-bundle auditors.
- **The 78 D6/D9 theorem statements against Lean.** I established the two manuscripts present the
  same theorem *names* with the same physics; I did not open `lean/SKEFTHawking/QuantumNetwork/` to
  confirm each statement matches both prose renderings. A statement-level divergence between the
  two papers (which would upgrade X-01 from "redundant" to "contradictory") remains possible and
  is worth one pass by whoever executes the merge.
- **Semantic near-duplication below my 0.30 shingle threshold.** Paragraphs saying the same thing in
  substantially different words are invisible to an 8-gram detector. The D6/D9 case was caught by
  the *theorem-name* extractor, not the prose one — so I am reasonably confident the method catches
  the load-bearing cases, but a paraphrased duplication elsewhere could be missed.
- **`papers/AutomatedReviews/`** and per-bundle `audit_log.jsonl` / `prose_state.json` were not
  swept; per the rubric, prior review status is evidence to be checked rather than inherited, and I
  based every finding on the manuscripts themselves.
- **Non-`paper_draft.tex` bundle files.** I used `source_manifest.md`, `append_log.json` and
  `bundle_metadata.json` for §4, but did not audit `change_log.md` or the metadata files for pin /
  roster drift; given the §3.2 and §5 patterns, expect more there.
- **Whether the 16 stub sections (§4.2) are recoverable.** I confirmed they do not render and that
  the append log still counts them. I did not check whether the original lifted text survives
  elsewhere (roadmaps, wave notes, git history) or must be re-authored — which is the difference
  between `small` and `new-work` on X-15. Whoever remediates should check `git log -S` on the marker
  string first.
- **The four orphan drafts' remaining content.** For `paper31` and `experimental_predictions` I
  probed 3 and 11 distinctive strings respectively and got zero hits in the plausible destinations.
  A probe miss is not proof of total absence — a paraphrased landing would evade it — but combined
  with their absence from every mapping row I am confident they are unassigned.
- **`docs/PAPER_DRAFT_MAPPING.md` §2 (the inverse bundle→source view)** was consulted only where a
  §1 row was in question; a full §1↔§2 consistency check was out of scope.
