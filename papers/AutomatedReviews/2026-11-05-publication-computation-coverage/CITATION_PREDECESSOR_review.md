# Citation predecessor — independent read-only reuse review

Recommendation: REUSE THE REVIEWED FOCUSED SOURCE PATCH, WITH FRESH EXISTING-WRITER STATE AND CURRENT RATCHET EVIDENCE. Do not merge the whole f28 ancestry or e34029-file package, copy historical success JSON, or treat registry resolution as source-content/scientific acceptance. Current implementation/adoption acceptance is not granted by this history review.

## Authority and exact pins

First action checked publication-citation-predecessor-review-r1.json: fresh=true, changed=[]. Read primary notebook and relevant ADR-014/source-writer contracts. Current immutable base56fe8172f695ad664461c6e6517a8913413abbc6; donor f28cc370f9907419773c5325fe70a838881fe3d8, parent0b6012549428b3a5b40c3e51e0c8a787defaf812. Older broader accepted composition e340bf425756c0c69aa80b79e207d93a2f2ba61b carries whole24 source review and checkpoint readback. There are13 donor-lineage commits outside current HEAD: normal merging f28 is not a one-commit adoption.

No candidate/primary/notebook/Git/state writer action, tests, project/kernel imports, source fetching or research performed. Source population was measured through immutable Git text, stdlib AST-literal parsing and the documented citation/comment/bibitem syntax; local held files were only read/hashed. Only reviewer-owned /tmp artifacts written.

## Independently reconciled populations — identities, not arithmetic

Current64 immediate paper drafts have516 distinct cited keys and664 registry entries. Independently enumerate all cited-but-unregistered keys, then separately inventory actual bibitem blocks as the extractor does. Exact13 missing:

- Barcelo2011; cited E1; bibitem in E1; external identity
- CompanionCompilation; cited D9; bibitem in D9; internal inprep companion
- CompanionFaultTolerance; cited D9; bibitem in D9; internal inprep companion
- CompanionStochastic; cited D9; bibitem in D9; internal inprep companion
- FinazziLiberatiSindoni2012; cited D3; bibitem in D3; external identity
- Kitaev2006; cited D2; bibitem in D2; external identity
- Roehm2026TQC; cited D3; bibitem in D3; internal inprep companion
- RoehmD4Topological; cited D8; no bibitem block; internal inprep companion
- RoehmD6FaultTolerant; cited D8; no bibitem block; internal inprep companion
- RoehmD8Compilation; cited D4; bibitem in D4; internal inprep companion
- RoehmD9Certification; cited D8; no bibitem block; internal inprep companion
- Verlinde1988; cited D4; bibitem in D4,paper11_quantum_group; external identity
- Wang2026TMDPolariton; cited D1; bibitem in D1; external identity

The ten actual stub-backed keys are Barcelo2011, CompanionCompilation, CompanionFaultTolerance, CompanionStochastic, FinazziLiberatiSindoni2012, Kitaev2006, Roehm2026TQC, RoehmD8Compilation, Verlinde1988, Wang2026TMDPolariton. Three orphan keys are RoehmD4Topological, RoehmD6FaultTolerant, RoehmD9Certification, each cited inD8. Set equality/disjointness is checked by actual keys, not inferred from13=10+3. D8 already has BibTeX entries for those three; it lacks inline bibitem blocks. Registering their real identities makes the existing extractor skip them as registered, without inserting fake bibitems or reducing scope.

The donor adds EXACT those13 records and changes only existing BarceloLRR2005. All13 added record values are AST-identical to e340's accepted whole24 source. Current registry exactly equals donor preimage. The eight internal records match current companion title/author sources D4,D6,D8,D9,I3, allowing TeX linebreak/accent/spacing conventions; inprep=true and null external DOI/arXiv/cache remain. No public deposit or publication is fabricated. Detailed key/source records: /tmp/l1-citation-predecessor-populations.json and /tmp/l1-citation-predecessor-companion-identities.json.

## Coherent minimal adoption boundary and conflicts

The focused source consists of eight paths:

- src/core/citations.py — exact13 identities plus honest oldBarcelo edition qualification, with every other existing record conserved.
- papers/D1/paper_draft.tex — Wang published bibliography metadata, retaining author-preprint distinction.
- papers/D3/paper_draft.tex — actual internal D4 companion title/author.
- papers/D8/bibliography.bib — actual internal D4/D6/D9 metadata, explicitly in preparation.
- papers/D9/paper_draft.tex — actual D8/D6/I3 internal companion metadata.
- papers/E1/paper_draft.tex — correct2011 Barcelo edition/DOI/pinned preprint.
- src/core/constants.py — down-only undeclared ceiling, contingent on CURRENT canonical measurement.
- tests/test_d5_citations.py — only replace stale79th-entry docstring with one-new-entry language; assertions/seed strength remain unchanged.

All these eight whole-file preimages exactly match current56fe; there is no present manuscript/source conflict. All five manuscript changes are bibliography-only; no scientific body, theorem/physics statement, numerical result, human state, SOURCE137/physical BUILD or claims verdict should change. Reuse exact selected historical source changes, not e340's additional Anderson/CHHK/Crossno/source/manuscript repairs. Hold the constants76 postimage until current measurement supports that exact number. Current78, f28 historical76 and e340 historical75 are not interchangeable facts: e340 review records actual slack at76 and restored declaration-removal sensitivity at75 on its different corpus, with the population cause UNKNOWN.

The ninth substantive donor path docs/primary_sources_state.json also has an exact current preimage, but MUST NOT be transplanted: its five success rows are dated historical acquisition receipts. Recreate current rows only via the existing writer against actual held files. The tenth donor path is an absent-current focused render/readback dossier; copying its whole solver/render/old-fast narrative as current acceptance would be misleading. Retain it as explicitly historical Git evidence or quote/link its focused citation paragraph in a new current adoption record with fresh commands/hashes. No new infrastructure or source-acquisition mechanism is required.

## Actual held-source fidelity and missing current receipt

All five selected key-named artifacts exist now and match the exact sizes/hashes in the tracked historical source review. Four carry PDF magic. Finazzi/Kitaev/Wang alias files are independently byte-identical to the existing canonical artifact. This is current byte identity plus inherited reviewed version/content evidence, not a fresh whole-paper reading. Detailed receipts in /tmp/l1-citation-predecessor-held-and-preimages.json.

- Barcelo2011: 2172677 bytes; SHA256 b1cad9c9c9511d0e912820c8f1d583fefdb622ff6331936f07649f2447d5581d; held2011v3 preprint; distinct from2005/2024 editions.
- FinazziLiberatiSindoni2012: 318882 bytes; SHA256 61c4da4e5f21112acee522fedbfd65bede2e567fea53eed8ac0e47e3b7c75f3e; byte-identical canonical FinazziLiberatiSindoni2012PRL.
- Kitaev2006: 1533535 bytes; SHA256 eb99541ee61044a6028edc53aad19dd80afed7e96778350a38420f36269e93ba; byte-identical canonical KitaevHonest2006.
- Verlinde1988: 12945 bytes; SHA256 010f971d637b39e3e596f40a5d9fa326fbfff713e7b1a35cc79149f34a34e20e; Crossref metadata only; no abstract/body.
- Wang2026TMDPolariton: 1152746 bytes; SHA256 88f4a4eda6a956ab29554730908d916891933379fc7594c3f0a674b4f055bded; byte-identical canonical WangKimBZHe2026PennTMDPolariton.

Barcelo2011 is the2011v3 author preprint, not the published journal body or2005/2024 edition. The old BarceloLRR2005 artifact is preserved; donor sets its declared path toNone and documents that its file is2024v4. Current64drafts contain no literal BarceloLRR2005 mention. Filename fallback may still discover that historical wrong-edition file if the old key returns; f28's tracked readback explicitly leaves edition-aware discovery owed. Do not claim this identity patch repairs that general discovery limitation.

Finazzi is the exact1103.4841v2 body, not the separate proceedings1204.3039. Kitaev's heldv3 is2008 while publication metadata is2006. Wang heldv1 is2024 with different author order from published2026 metadata; old whole24 review reports reading published linewidths online, but that published body is not the cached artifact and no all-parameter revision equivalence follows. Those distinctions stay in registry notes and bibliography metadata.

Verlinde actual heldJSON has Crossref work metadata, title/author/DOI300/360-376/1988, no abstract/body. Under ADR-014 it supports bibliographic identity ONLY; it cannot back fusion-rule/source-content attribution. Its unresolved full-body/load-bearing obligation remains visible; no exemption is added.

CURRENT receipt gap: allfive alias keys are absent from current primary_sources_state, even though held files exist. Historical five success rows are not current receipts. Existing scripts/back_fill_primary_sources.py supports the needed path: load registry entries, --no-stubs/--bibkey selection, no --force, find_on_disk recognizes a nonempty existing key file and Sidecar.put records NOW with url_used=None and note 'pre-existing on disk; recorded without re-fetch'. Check active SK_ROOT/state path and real workspace routing first. Future ROOT may invoke the existing writer's selected pre-existing-file branch after source adoption, preserving every old sidecar entry; dry-run/byte/hash preflight must prevent accidental fallback fetching. No new network acquisition is needed or authorized by this review. New records should acknowledge existing held bytes, not claim fresh downloads, source reading or stronger fidelity. Do not copy old URLs/fetched_at as fresh observations.

## Accepted historical evidence and remaining current acceptance

The tracked f28 focused readback reports independent held-hash/active-corpus acceptance, canonical516cited/zero missing/zero required-cache, undeclared76 and78 citation/Wave1 passes with one deselection. It contains no standalone raw/current receipt here. e340 whole24 review independently checks the exact thirteen record bodies/source distinctions and broader221pass/1skip, but that older package includes separate citation/scientific propagation and ratchet derivatives. Neither receipt is a current test or source-fidelity certificate. Original source/content MAJOR R1 and SOURCE137/physical obligations remain open.

Next substantive current acceptance, ROOT-owned after deliberate adoption allocation:

1. Freeze selected eight source postimages/current state, preserve complete current ledger, IMPORTS, planner/G4, manuscript scientific bodies and all human/claims data. Use no blind normal merge of f28 ancestry or old29-filecheckpoint. Reconcile current diff independently.
2. Produce the five CURRENT existing-writer local-file receipts with no refetch and full old-entry conservation. Keep artifact bytes/modes/mtime fixed and fidelity/version qualifications intact.
3. Run existing canonical `python scripts/validate.py --check citation_primary_sources_present --no-memo` from the prepared current environment, inspect COMPLETE details rather than only passed. Require missing keys0 and required cache0; retain metadata/abstract warnings. Measure actual undeclared residue before tightening78 to measured76 or a different justified DOWNWARD value; no upward bound/exemption/blanked metadata. Re-run both zero-headroom and actual declaration-removal seed controls on a green baseline with existing seed_journal restoration; missing-key reds cannot stand in for those guards.
4. Run full tests/test_d5_citations.py plus tests/test_phase6i_wave1.py and tests/test_workspace_resolver.py; explicitly include slow extraction (`-m ''`) once, retaining zero-stub/zero-orphan assertions and tmp_path isolation. Reconcile exact thirteen identities, ten originalstubs/threeorphans after registration, existing metadata/title/edition checks and SOURCE137/scientific scope. Run current declared cache1.2 Verify unchanged: `python -B -m pytest -q -p no:cacheprovider tests/test_phase6i_wave1.py tests/test_workspace_resolver.py`.
5. Obtain independent current complete source/state/fidelity/control review, canonical derived-writer/freshness readback and reviewed source checkpoint; only then use existing writer for `review:2026-10-19-managed-worktree-paths:infra:1.2` if its full declared command is actually green. No new check/alias resolver/indexing registry/service.

This report identifies a buildable previously accepted source boundary and current receipt obligations. It does not certify current fullcache, body fidelity/publication, scientific BUILD, main/full/native/security/human acceptance or resolve other frozen broad failures. No source/state mutation or tests executed by reviewer.

## Exact preimages and donor hashes

- docs/audits/2026-10-25-njl-qualification-dependencies/NJL_FOCUSED_RENDER_READBACK_20261103.md; current None; donor e736b4636bed1d06e8c543a48feafa95ce771bb9cc645ecc5259ccb454a817a2; exact preimage False
- docs/primary_sources_state.json; current b3e7f4e33d3304f6512cfc5450ecf7f8bfe155ddf79b8df82039cc978c07929d; donor a84ad2f17c77a347eb80ebd49c5c0d2501009fa0b69779c75a4546b549565df2; exact preimage True
- papers/D1/paper_draft.tex; current 0e0ae1be8970816add86ed9491f53f0975660bb02b917f9ecb1ff87c403d1138; donor badd7db66a368bc0a80620e10e552e2a56d52ac0fc65f63f60b9651b6a1ee614; exact preimage True
- papers/D3/paper_draft.tex; current 55642bb6be98c68f2feb6cece25b1d7ce405a4f336aeb2807fc206c2a66fac22; donor e60c583110b8de5884a62b67ad21aa268da718632528b178a6b519224ce4b15c; exact preimage True
- papers/D8/bibliography.bib; current 859f72ecf366bfdf78153db56478847fcefa003d861d3368d6042d66e1ceece2; donor 709d0a92da6689ca54e331c18c6e0758582f07512fa9293e586b8e6f784dd4ab; exact preimage True
- papers/D9/paper_draft.tex; current d14aa1a4dfa7d8a41923700a179b8925626a2114ebb368a451c69c1e58524fab; donor c2514912b42cb7eb615791f4030e0dfca5f4d58b8d3ca1263e99834e930d690d; exact preimage True
- papers/E1/paper_draft.tex; current 42480eb34627c37ecda4ebdace02ad243d8776e451fcef23d4e1bca5faf30233; donor 3570323f966b0bdd488c0af6de76d1e27006fdd848409c47a4412d81796996b1; exact preimage True
- src/core/citations.py; current d0d2720d845ce9fee73bf2ba8b3c3c01b45df41c1212327a5c737c997fb56210; donor 3b42687dec73ff6d147bb8b72fae261aed285f706373f95845b74b0322b3d608; exact preimage True
- src/core/constants.py; current 0efa3ffd37d57cec4a942f922d0717024398d70ec33049f57a5e19a06fc32c15; donor b91f65926d7a5190834352e757f25ebaed9b03895901acc632875e2c55f05b2d; exact preimage True
- tests/test_d5_citations.py; current bab2e802e8a4bfc948209fa00da1b441bc67c83373d042f55b22a0bbb4040a2e; donor c020863fedcf33c9d21527530c7108e3d2c429d7ddf31428a0bb63422f99633b; exact preimage True
