# Independent D8 finding 1.8 figure review

**ACCEPT the seven-path figure repair for the original finding. Replace the author's assert-based Verify before canonical closure.** The reviewed figures, manuscript placements and scientific data satisfy the original coverage and length-figure obligations. The supplied fail-closed replacement is accepted as a deterministic check of the reviewed assets, manifest, labels and removed deferrals.

## Scope and pins

The canonical initial continuity check returned exit 0, `fresh=true`, `changed=[]` for task `D8-original-figure-1.8-review` at clean MAIN `040ca78710432a995ab99a3d9b47db9f10cafa62`. I read the ROOT notebook, author report, original finding, figure-reviewer role, complete text patch, manuscript and renderer manifests. Independently checked every base and candidate path against the source manifest. Applied the five text paths in temporary scratch space and compared each resulting file byte for byte with the proposed candidate. Verified the two separately installed PNGs against their pinned hashes. No repository, slot, Git index, finding or ledger changes were made.

| Artifact or candidate path | SHA256 |
| --- | --- |
| Text patch | `1d66b8ede98f82ce9988f57ab75bfb991478133edecb0d8df56195307d79a6dc` |
| `src/core/formulas.py` | `b4d224ba924485c231c2949ecd57183ef61e7fa968fa88e922532c521c9a8e00` |
| `src/core/visualizations.py` | `b1e5d5f6e63c459ca8e3a691701f2d5c38bd9ac2f781610cbe3fd101cefc3553` |
| `scripts/review_figures.py` | `cfb2ba43e52fbf31ad728c67c0c5851a20cd4127ffaf52b51d25b9df0af89407` |
| `papers/D8/paper_draft.tex` | `7f41debe84efa53330c7f0c9300346f0467de01e177da89a0b554e28dac995b1` |
| `papers/D8/figures/review_manifest.json` | `142e81cff7f0447f4e98442edfdc53d497e75c54fec64043fed8df6bf9322892` |
| `papers/D8/figures/d8_fig1_alphabet_dimension_map.png` | `916aa0770bae2cf96d2ac17b41c42a4947b482c428a54c6e90e17c746e93c51b` |
| `papers/D8/figures/d8_fig4_length_comparison.png` | `054e12a55e99d267d96ca3e2e3d07fc09e0954ea9a9b452c338bc49712fc83ae` |
| Scratch PDF | `969a86e6d70e795a339e16e9c08158585d3ebbda0af864dad52b94998d29327d` |

## Figure decisions

| Figure | Rendering | Science | Style and caption |
| --- | --- | --- | --- |
| Coverage map, manuscript Fig. 2 on p. 6 | Pass. Six labels, symbols and right-column explanations legible without clipping. | Pass. Exactly the four families and six variants of Table II. Three SU(2), one SU(4), two SU(8), with the amber marker on the T-free CCZ route. | Pass. Serif, blue/amber, accurate caption and resolved table reference. |
| Length comparison, manuscript Fig. 4 on p. 9 | Pass. Three distinct panels with readable titles, tick labels, axis units and caption. | Pass. Native cost and precision conventions match the actual theorem statements. | Pass. No common scale or implied cross-panel ranking. The dashed conditional panel and other panel titles remain legible at manuscript scale. |

I viewed both exact standalone PNGs and both supplied rendered pages, then independently rasterized and inspected pages 6 and 9 of the pinned PDF using Poppler. The PDF image list confirms the respective 2160×820 and 2280×820 embedded assets. Both are placed in their expected sections. This is a review of the two affected figures. The renderer receipt belongs to the author. I independently checked the registry entries, both generator and structural-checker dispatch maps, and the bundle manifest. Existing figures and bundle-level Stage 9 status require their own review.

Coverage annotations preserve the Table II evidence: algebraic integrality obstruction for Clifford+T, Chebyshev and triple-angle inputs for the two Read–Rezayi variants, Brylinski entanglement for trapped-ion MS, dense H/T/CNOT subalphabet with T, and trace obstruction for T-free CCZ. Fibonacci and wave labels are absent. The map is a schematic of theorem coverage rather than an experimental plot.

Balanced commutator uses `SolovayKitaevLengthBound.skLength_at_skLevel_polylog_le` for the **auxiliary recurrence length**, with `skLengthConst=1000`, `skLengthExponent=Real.log 5 / Real.log (3 / 2)`, and the actual `ε₀_value=1/8388608`. The local matrix ℓ∞ operator norm is instantiated in `CliffordTCompiler.lean`. Its `cliffordTCompile_correct` has a separate actual output-length conjunct with `cliffordTFiniteCover_maxLength`, which the plot does not claim. The plotted interval runs from 10^-12 to 2^-23, within the proved regime.

Ross–Selinger uses the implication `KMM.gridFindT u k b = some t` in `rossSelinger_log_length_explicit`. The displayed equivalent increment 8k follows from the proved logarithmic expression at first-column δ=(1+√2)/(√2)^k. The total word bound is N₃+8k. The noncomputable N₃ is a field selected from the KMMReduction construction and no numerical value is supplied. The panel plots only the increment and identifies both conditions in the figure and caption.

KMM uses `Gate3.kmm_universal_headline`. For every U in SU(2) and k∈ℕ it gives a three-qubit Clifford+T list of length at most 50400k+812 and a unit-modulus global phase. The initialized input has two ancillas in |00⟩ and a normalized system state. The theorem bounds the squared ℓ² output distance to the phase-adjusted target by 9(2/4^k+2√2/2^k). The change to the adjacent text correctly attaches O(2^-k) to the squared error. Panels two and three use integer k as the native precision parameter and report the corresponding metric in the caption. A common physical precision axis would imply equivalence of different error notions.

I executed only the selected candidate formula and figure definitions in a scratch Python process with NumPy and Plotly. Independent arithmetic matched all six row positions and 174 plotted samples, including the two ancillary error series. SK endpoints were approximately 526,534,274.013 and 59,343,029.859. The grid increment runs 32 to 320. KMM runs 202,412 to 2,016,812. No Lean execution or additional renderer generation was needed for these controls.

## Verify disposition and closure boundary

The original historical `grep -c "figuredeferred" papers/D8/paper_draft.tex` outputs 3 on current pinned HEAD, including the macro input, and exits 0. On the repaired draft its zero-match convention exits 1. Preserve it verbatim as history and replace the active declared line. The author's proposed command under ordinary Python gave candidate/baseline/altered-PNG exit codes 0/1/1. With `PYTHONOPTIMIZE=1` it gave 0/0/0. All its asserts disappear.

The exact replacement is `/tmp/publication-d8-figure-1-8-verify-r2.command.txt`, SHA256 `70af3c9c48fdf4ba54fd4d77a83befc27e15049f1afc1821075c9c734c572a3f`. It uses explicit `require` failures and checks exact PNG hashes, one correct manuscript figure pairing per label, unique registered manifest membership and no deferrals. I executed its identical shell bytes under a clean PATH with and without `PYTHONOPTIMIZE=1`. Both modes passed candidate (exit 0) and rejected baseline deferrals, altered PNG bytes, swapped figure labels and a missing manifest row (each exit 1 with its own diagnostic). The replacement passes the canonical field parser and writer trimming round-trip as a single-backtick Markdown code span.

For authorized adoption, put that exact line in section 1.8's sole active `- **Verify:**` field. Add the former grep verbatim in a separate historical field that does not match the active label, with its exit-semantic defect. Keep original finding ID, expectation and source history. Once the actual candidate and declared Verify are present, run the canonical writer from the accepted checkout, using `uv run python scripts/close_finding.py --doc papers/AutomatedReviews/2026-08-15-d8-stage10-redraft/D8.md --section 1.8 --status fixed --commit <actual-fix-commit> --evidence <independent-pins-and-review-rationale>`. The writer executes its declared Verify when `--verify` is omitted. Candidate acceptance establishes the scope of this finding. No ledger closure, Stage-9 transition, full gates, rebuild or publication acceptance was performed in this review. Other D8 findings and the earlier schematic remain separate.

Final canonical continuity check returned `fresh=true` and `changed=[]` for the same packet and frozen candidate.
