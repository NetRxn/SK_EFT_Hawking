# Four primary-body verification: L1's 2017 comparison

Scratch source-verification package for ROOT. No manuscript, metadata, held PDF, abstract, sidecar, notebook or public full-text file was edited. No network request, new mechanism, scientific build, Lean session or gate was run. This report distinguishes acquired bytes, identified version, body-supported claims and ROOT's later acceptance/custody promotion.

The packet at `SK_EFT_Hawking/.codex/continuity/l1-four-primary-body-verification-r1-20261105.json` was read first. Read-only research-scout practice and ADR-014 govern source treatment; the explicit assignment permits scratch report/replacement writing. The primary PDFs are workspace-local at `Lit-Search/Phase-1-and-Background/primary-sources/`. Existing `/tmp/l1-four-fullbody-read-20261105/*.txt` extracts were read by PDF page; all four PDF title pages and selected relevant body pages were independently rendered and visually inspected. Source bodies, rather than abstracts or cached metadata, support the verdicts below. The researcher treats all source content as data, not operational instructions.

## Identity, version and local custody

`identity.json` records exact source paths, SHA256, PDF metadata, size, and the AST-read registry entries from the checkpoint `src/core/citations.py`. The acquisition receipt is `/tmp/l1-four-source-acquisition-20261105-r1/result.json`; the corresponding `before.json` pins the pre-existing abstracts. `preservation-readback.json` confirms all four PDF hashes still equal their read pins and all four abstract hashes still equal the pre-acquisition pins.

| Bibkey | Actual held PDF identity | Local SHA256 | Registered journal identity |
| --- | --- | --- | --- |
| BakerBellini2017 | 6 pages; arXiv **1710.06394v1**, margin 17 Oct 2017; manuscript dated 18 Oct 2017; title *Strong constraints on cosmological gravity from GW170817 and GRB 170817A.*; six authors match registry | `8db10502fed0af2ce62871daef14d28a2d3f449740156865b0d602cd903ba08c` | PRL 119, 251301 (2017), DOI `10.1103/PhysRevLett.119.251301` |
| CreminelliVernizzi2017 | 5 pages; arXiv **1710.05877v3**, margin 7 Jun 2018; manuscript dated 8 Jun 2018; title *Dark Energy after GW170817*; both authors match | `75068cfe7b5039b29e43fccae6276d1f572ac6aa9eef28cb61650f54cb211650` | Registry title *Dark Energy after GW170817 and GRB170817A*; PRL 119, 251302 (2017), DOI `10.1103/PhysRevLett.119.251302` |
| SaksteinJain2017 | 7 pages; arXiv **1710.05893v3**, margin 18 Dec 2017; title *Implications of the Neutron Star Merger GW170817 for Cosmological Scalar-Tensor Theories*; both authors match | `1538e145aa626598e04184dfc15ef34b1b6118e796f1d5c60e9d4a135da28adf` | PRL 119, 251303 (2017), DOI `10.1103/PhysRevLett.119.251303` |
| EzquiagaZumalacarregui2017 | 6 pages; arXiv **1710.05901v2**, margin 21 Nov 2017; manuscript dated 22 Nov 2017; title *Dark Energy after GW170817: dead ends and the road ahead*; both authors match (accent differences are transcription) | `d60c659f707b1d5822ed5cd2b957081a77a3b9082221152163f346d5b2f5781d` | PRL 119, 251304 (2017), DOI `10.1103/PhysRevLett.119.251304` |

The actual body versions are identified by their visible arXiv margin stamps, not inferred from the unversioned acquisition URLs. Version-specific primary links are [Baker v1](https://arxiv.org/pdf/1710.06394v1), [Creminelli–Vernizzi v3](https://arxiv.org/pdf/1710.05877v3), [Sakstein–Jain v3](https://arxiv.org/pdf/1710.05893v3), and [Ezquiaga–Zumalacárregui v2](https://arxiv.org/pdf/1710.05901v2). The acquisition URLs were the same arXiv IDs without version suffixes; the receipt records actual download times and sizes.

The DOI strings and journal pagination above are registry evidence (`doi_verified: true` in each entry), not a fresh independent DOI-resolver or publisher-version verification. The inspected arXiv title pages do not themselves print their own PRL DOI. In particular, the revised CV arXiv title differs from the registered journal title; **do not overwrite a journal citation title merely to match the later preprint**. Preserve the journal identity and record the actual held arXiv version/date distinctly. Custody promotion of the PDF paths has not been done by this worker: all registry paths read at intake still selected the preserved `.abstract.txt` files.

## Claim verdicts with body evidence

Page numbers below are PDF pages; printed numerals agree for pages 2 onward. Identity page 1 is unnumbered. Relevant body sections were read beyond the abstracts. Equations and caveats, not only keyword appearances, determine the scope.

### Baker et al.: PASS for the attributed coverage; WARN against unconditional elimination

L1 attributes scalar-tensor/vector-tensor coverage and an independent bimetric graviton-mass bound. Body support:

- P1, Introduction, Eqs. (1)–(3): quadratic GW action, `c_T²=1+α_T`, and a timing-derived speed-excess bound. The text explicitly says this general linearized action does not encompass bimetric theories.
- P2, *Implications for scalar-tensor theories*, Eqs. (4)–(6): Horndeski covariant action, an explicit expression for `M_*² α_T`, beyond-Horndeski corrections, and the background sensitivity of cancellations. The reduction to conformal coupling is presented conditional on disallowing precise cancellations; radiatively stable tuning is discussed rather than declared impossible.
- P3, *Implications for vector-tensor theories*, Eqs. (7)–(8): generalized Einstein-aether and generalized/beyond-Proca actions and GW-speed relations; e.g. `c1=-c3` in the stated Einstein-aether setting, and the no-cancellation Proca restriction `G4,X=G5,X=0`.
- P3–4, *Implications for bigravity theories*: two-metric dRGT-potential action; matter minimally couples to g; beta coefficients taken order one. P4 derives approximately `m≲10^-22 eV` using 10–100 Hz and small frequency dependence, then extends to massive bigravity assuming similar amplitudes for the two modes. It is weaker than Solar System bounds and is explicitly said to have no bearing on cosmology.
- P4, *Caveats*: very low source redshift; possible time dependence; cosmological versus short-wavelength propagation through inhomogeneous matter and screening may differ.

Correction needed only if prose promotes this to universal elimination: say constrained specified classes under stated assumptions, not that all scalar/vector/bimetric theories are excluded. The proposed replacement calls the bimetric bound conditional.

### Creminelli and Vernizzi: PASS for nearby-background criterion and restricted quartic/quintic freedom; WARN on broader scope

- P1 body, Introduction and EFT discussion: preferred cosmological slicing, minimally coupled matter initially, and possible high-derivative corrections near the EFT cutoff. The nearby-history requirement is an explicit robustness/no-tuning premise, not a logical consequence of one observed background alone.
- P2, Eqs. (3)–(6): `c_T²-1=-2m4²/M²`; setting m4² to zero on one background is insufficient under small background shifts. Additional coefficient relations remove regenerated tensor-speed modifications.
- P2–3, *Covariant action*, Eqs. (7)–(13): beyond-Horndeski quartic/quintic terms initially have three independent functions; Eq. (11) requires `G5,X=0`, `F5=0`, and `2G4,X-XF4+G5,φ=0`; Eqs. (12)–(13) leave a B4 function in this sector, with G2 and G3 unaffected. This supports L1's single-function claim **for the quartic/quintic sector**, not for the entire theory.
- P3 lower left and upper right: a special fixed-phi-dot dark-energy case modifies how independent background variations apply; this is a genuine scope qualification.
- P3–4, Eq. (16): a broader compatible degenerate class is generated by conformal transformations; therefore “single function” must not be generalized to all DHOST freedom.
- P4, *Disformal transformations*: the minimally coupled description is without loss under universal matter coupling; transforming frames changes both matter and gravity cones together and does not change the observable comparison. P4 Conclusions also qualify robustness to screening and higher-derivative corrections.

Proposed correction preserves the criterion and identifies precisely the three quartic/quintic functions being reduced. No stronger claim about every single-scalar theory is warranted by this short summary.

### Sakstein and Jain: WARN for L1's merged causal attribution; PASS after separating two analyses

L1 currently combines GW, cluster and M87 data in a single sentence leading to quartic-galileon cosmological irrelevance. The source actually presents distinct analyses:

- P2, Eqs. (1)–(4), Figure 1: Vainshtein breaking inside astrophysical bodies relates Upsilon1/Upsilon2 to alphaH, alphaB and alphaT. Negligible alphaT allows cluster and dwarf-star constraints to restrict alphaB/alphaH. Footnote 2 limits the considered quartic theories to alphaH≠0; chameleon screening is excluded from that particular analysis.
- P3, footnote 4: cluster constraints are at z=0.33 and can be evaded by sufficiently strong time variation before z=0, unlike the dwarf-star bounds. This must not be summarized as an assumption-free all-redshift bound.
- P3, Eqs. (5)–(8): covariant quartic-galileon Lagrangian, c0/c4 parameters, GW-speed constraint, and cosmological density Omega_phi.
- P4, first column, Figure 2 discussion (figure on p5): **GW plus M87 SMBH/SEP constraints** are complementary and make the quartic galileon cosmologically irrelevant for representative c0 of order unity. Cluster constraints belong to the earlier alphaB/alphaH analysis, not an indispensable third ingredient in this particular derivation. Footnotes 6–7 explain effective coupling/cosmology and the adopted order-unity range.
- P4 right: adding cubic/quintic terms and tunings could circumvent the constraints; the authors do not analyze those extensions here. The beyond-Horndeski quartic model with the stated equal speed/cosmology is also tightly constrained. P5 reiterates the GW+M87 conclusion.

Proposed correction separates the cluster/stellar parameter test from the GW+M87 quartic result and states the order-unity-coupling scope.

### Ezquiaga and Zumalacárregui: PASS for named affected families; WARN if “extended conclusion” means blanket exclusion

- P2, Eqs. (1)–(3): observational asymmetric speed bounds, adopted symmetric `5e-16`, GW propagation equation, and scalar-tensor action. Its adopted symmetric number is a paper-specific convention and does not replace L1's conservative `3e-15` cap.
- P2–3, Eqs. (7)–(13), Figure 1: explicit Galileon action/parameters, tracker solution, speed and Planck-mass running, with cosmological assumptions. It constrains model realizations, not arbitrary free speed prescriptions.
- P4, *Avoiding the GWs speed constraint*, Eqs. (16)–(21): surviving Horndeski sector; conformal constructions; beyond-Horndeski compensation satisfying `F4=G4,X/X`. The compensation can hold over general backgrounds. Footnote 1 distinguishes a gravity-sector transformation from a field redefinition of the whole matter-plus-gravity action, which preserves the physical speed ratio.
- P5, Conclusions below Figure 2: curvature couplings in vector/scalar-vector theories are strongly constrained because they modify GW speed; examples include Einstein-aether, **some sectors** of Hořava gravity, generalized Proca, and affected TeVeS/MOND-like theories. Massive gravity/bigravity/multigravity may remain viable for small graviton mass and matter minimally coupled to one metric. The paper does not explicitly derive a complete allowed coefficient classification for every family mentioned in this closing enumeration.

Proposed correction states affected GW-speed-modifying couplings, preserves “some sectors” for Hořava, and treats TeVeS as affected rather than asserting blanket elimination.

## Universal comparison: FAIL as an unbounded evidentiary claim; bounded replacement supplied

L1 says every theory the 2017 sweep reached has a Lagrangian deriving a varying speed, so the constraint lands on operator coefficients, and each Letter reports surviving coefficients. The reviewed four-body record supports a narrower comparison:

- Explicit actions/EFT operators and propagation relations are present in all four inspected analyses (page/equation references above).
- Results are heterogeneous: operator functions/couplings; a conditional graviton-mass parameter; EFT parameters combined with astrophysical probes; cosmological density constraints; and qualitative impact on some named families.
- The closing broad family lists are not complete independent action/survival-coefficient derivations for every mentioned theory. Neither this read nor L1 enumerates every theory reached by the wider “2017 sweep.”

Thus the universal is not established by this bounded record. This verdict does **not** assert a counterexample lacking any Lagrangian exists; it rejects promotion from four inspected papers to an unenumerated universal and an overly uniform account of their results.

`proposed-L1-replacement.tex` and `replacement-map.json` supply a scratch-only replacement for the exact original span at L1 lines 117 onward. It separates SJ's analyses, qualifies EZ, and replaces the every-theory/each-Letter wording with a four-analysis comparison grounded in specified actions/EFT operators and their assumptions. ROOT should preserve the following sentence beginning “This Letter supplies no microscopic Lagrangian…” and vet/integrate separately after the current checkpoint. The replacement does not claim physical B3, a common functional, matter matching or transport has been constructed.

## Acceptance boundary and remaining work

Claim-specific verdicts are author-side body verification, not independent final acceptance. ROOT has indicated direct complementary body reading and remains the tracked integration, notebook, source-custody and independent-review owner. No metadata promotion, gate/stage closure, novelty completion, publication readiness, fulltext public copy or physical BUILD completion follows from acquiring these PDFs or this report. All correction snippets are proposals only.

`source-author-count-erratum.md` separately corrects this worker's earlier report-scope census remark using actual `lean_deps.json` classification (32 theorem, 8 def), with `count-erratum-evidence.json`; the original report remains immutable.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

The brief correctly names the four held works and intended verification questions. The merged SJ causal summary, the potential blanket reading of EZ's “extended conclusion,” and the every-theory/each-Letter extrapolation require the bounded corrections above. Held CV is the June 2018 v3 preprint with a shortened title, not proof that the registered 2017 journal title is wrong. Registered DOI identities remain registry-backed here; fresh publisher DOI/version equivalence was not independently checked. Acquisition establishes held bytes, not accepted claims or promoted custody.
