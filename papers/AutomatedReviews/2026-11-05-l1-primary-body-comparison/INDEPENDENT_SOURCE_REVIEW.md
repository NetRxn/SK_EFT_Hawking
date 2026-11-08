# Independent primary-body review: ACCEPT

Scope: proposed four-source L1 comparison, four registry records, and four acquisition records only. Base candidate 97018780963e5d9c328cae29e6187b5f9fcda088. Continuity check returned fresh=true, changed=[] before review. ROOT remains sole tracked/notebook writer and formal closer. No tracked/Git/Lean/slot/build changes made.

## Actual source reading

I independently ran pdftotext on each actual held Lit-Search PDF, verified the resulting full extracts byte-for-byte against the supplied extracts, read the relevant body sections, and rendered/inspected actual printed pages Baker p4, CV p3, SJ p4 and EZ p5. Identity stamps were read in the full extracts, not inferred from registry metadata. Scratch evidence is /tmp/l1-primary-body-independent-evidence-20261105-r1/; it must not be copied wholesale into public artifacts because it contains full-body extracts/page images.

- Baker et al., arXiv:1710.06394v1, stamp 17 October 2017 (internal dated line October 18). Body p2 Eqs.(5)–(6) analyzes scalar-tensor speed and cancellations; p3 Eqs.(7)–(8) analyzes generalized Proca, and the preceding Einstein-aether analysis restricts c1+c3. The conclusions p4 explicitly assume no finely tuned cancellations. Bimetric derivation pp3–4 assumes matter minimally coupled to g, order-one beta coefficients, and similar amplitudes of massive/massless modes. The resulting mass restriction is separate from scalar/vector speed restrictions and does not by itself constrain cosmology. Proposed “conditional graviton-mass bound” and registry assumptions are faithful; no universal exclusion is warranted.
- Creminelli–Vernizzi, arXiv:1710.05877v3, stamp 7 June 2018 (internal dated June 8), titled Dark Energy after GW170817. Body p2 Eqs.(3)–(6): cT^2−1=−2m4^2/M^2, m4=0, tilde-m4^2=m5^2, and m6=tilde-m6=m7=0 under nearby-background robustness. Covariant degeneracy Eq.(9) leaves three independent quartic/quintic functions; p3 Eq.(11) gives G5,X=0, F5=0, 2G4,X−XF4+G5,phi=0. Eqs.(12)–(13) leave B4 with G2 and G3 free, not a one-function full theory. The fixed-phi-dot special case on p3 is explicitly discussed; p4 Eq.(16) and disformal discussion qualify DHOST and universal matter-coupling/frame assumptions. Proposed wording limits the one-function claim to the quartic/quintic functions and notes the free lower functions; accepted. It does not establish identity of all v3 details with the originally published 2017 text.
- Sakstein–Jain, arXiv:1710.05893v3, stamp 18 December 2017. Body p2 Eqs.(1)–(4), Fig.1 constrain alphaB/alphaH using alphaT near zero plus dwarf-star and lensing/X-ray cluster tests; footnote2 specifies quartic alphaH nonzero/Vainshtein regime, footnote4 p3 gives cluster redshift/time-variation caveat. Separate covariant quartic-galileon model p3 Eqs.(5)–(8) combines speed with M87 SMBH SEP constraints on pp3–4. P4 explicitly uses representative c0 of order one; Fig.2 p5 shows c0=1 and 3. The cosmological irrelevance conclusion concerns this combination and regime, not cluster data alone or arbitrary matter coupling. Proposed text separates exactly these inferences and keeps the matter-coupling scope. Registry disformal-photon statement is supported by p4 Eq.(9), p5 Eqs.(10)–(11) under its stated simplest coupling scenario.
- Ezquiaga–Zumalacarregui, arXiv:1710.05901v2, stamp 21 November 2017 (internal dated November 22). Body p2 Eq.(1) first reports the asymmetric conservative speed interval, then explicitly adopts symmetric 5e−16 for its analysis. P3 Eqs.(11)–(13) give Galileon parameter bounds under no-cancellation/tracker assumptions; the text disclaims their universality. P3 Eq.(14), p4 Eqs.(16)–(21) analyze the effective metric, surviving simple Horndeski sectors, conformal transformations and compensating beyond-Horndeski couplings. Gravity-only disformal transformations differ from transforming the whole matter action (p4 footnote1). P5 closing paragraph identifies constrained curvature couplings, Einstein-aether, some Horava sectors, generalized Proca and effects on TeVeS/MOND-like theories, not blanket elimination of each family. Proposed text and notes faithfully retain this scope.

All four analyses support the bounded summary that they connect propagation with specified actions/EFT operators and restrict functions, couplings, masses or cosmologies under assumptions. They do not justify the original unenumerated “Every theory” / “each Letter” assertions. The proposal removes those assertions without claiming a microscopic Lagrangian or prediction for L1.

## Independent exact-byte/invariant verification

Executable scratch readback is /tmp/l1-primary-body-independent-20261105-r1.json. It verifies original/proposed hashes against SOURCE_PINS.json, CITATION_DATA_DIFF.json and CUSTODY_DIFF.json; actual PDF magic, byte lengths and SHA against tracked identity and actual fetch receipts; unchanged original abstract hashes; and independently regenerated extracts.

Actual PDF SHA256 / size:

- Baker: 8db10502fed0af2ce62871daef14d28a2d3f449740156865b0d602cd903ba08c / 156600 bytes.
- CV: 75068cfe7b5039b29e43fccae6276d1f572ac6aa9eef28cb61650f54cb211650 / 130147 bytes.
- SJ: 1538e145aa626598e04184dfc15ef34b1b6118e796f1d5c60e9d4a135da28adf / 1016046 bytes.
- EZ: d60c659f707b1d5822ed5cd2b957081a77a3b9082221152163f346d5b2f5781d / 884307 bytes.

AST-derived registry comparison confirms exactly these four entries change, only primary_source_path/notes/provides (CV provides unchanged). All other entries, bibliographic identities, DOI-verification/inprep flags, and any other fields are preserved. No fitted value changes. Sidecar comparison confirms exactly four entries change and each equals its actual acquisition receipt, including actual fetch time/URL and size; only generated_at changes at top level. I imported the existing back_fill_primary_sources module using primary .venv Python and independently reproduced proposal entries through Sidecar.put(FetchRecord) in scratch. The writer is reproducible; I did not independently observe the preceding fetch network operations or author process. Unversioned url_used is retained as the actual receipt URL; versioned identity and hashes remain available in the identity/recovery evidence. Historical original abstracts remain byte-identical.

Proposed full-file pins accepted:

- paper_draft.tex: 82d5682f890baf32f663ca2779353416c6770e81081b721ea99f24e19f3f30ac
- citations.py: 8fefe95dfe535168509cf1dbc4607ff40fa82bc1eda7a70b0ac01a7db6a2a3bd
- primary_sources_state.json: 4ac41ae39e0d37b4f53df6e377ed77a3ef998e81556d613385193177268ac849

The focused canonical finding has an actual original RED AssertionError control. This independent source audit is substantive corroboration, not merely the syntactic control turning green. Eventual integrated GREEN, canonical claim refresh, compilation and closure remain ROOT-owned.

## Boundaries

ACCEPT requires no substantive correction to these proposed files. It establishes external attribution fidelity and the stated bounded custody invariants only. No physical B3/common-functional realization, physical state, denominator/range, tensor/matter identification, transport construction, native build, novelty search, full-stage/main/human/publication acceptance follows. Original L1 scientific target remains unchanged.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

None for the proposed bounded correction. The held CV body is a June 2018 arXiv revision with a shorter title, not the 2017 journal version itself; the proposed notes correctly disclose both version and title distinction. The original manuscript/registry, unlike the proposed correction, contradicted SJ's separation of astrophysical inferences and EZ's qualified affected-sector enumeration.
