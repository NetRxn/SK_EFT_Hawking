# Citation identity, acquisition and validation evidence

Evidence assessment against `7f788810`. This report records the lead's actual acquisition/validation receipt, current source changes and the preceding independent identity assessments. Final independent acceptance and the subsequent exact-25053c00 FLS qualification are recorded in SCOPED_REVIEW.md; the separate ledger audit accepted the supported closure. No source, acquisition, test, metadata or ledger changes were made by this evidence author.

## Twelve cited identities

Eight keys are internal manuscript references, registered manually under their existing citing keys with explicit inprep=True, no external DOI/arXiv/cache, no exemption class, empty provides, actual citing paths and target-manuscript identity notes. The year 2026 comes from existing bibliography/draft dates, not an invented external publication date. Actual authors are John Roehm except D6's John G. Roehm.

| Existing key | Citing bundle | Actual target |
|---|---|---|
| CompanionCompilation | D9 | D8, universal gate compilation / alphabet-agnostic Solovay–Kitaev |
| CompanionFaultTolerance | D9 | D6, minimal hypotheses for the AGP threshold recursion |
| CompanionStochastic | D9 | I3, stochastic-calculus and large-deviation predicate-substrate library |
| Roehm2026TQC | D3 | D4, Fibonacci braid universality and graded modular-tensor-category verification |
| RoehmD8Compilation | D4 | D8, same actual compilation manuscript |
| RoehmD4Topological | D8 | D4, same actual Fibonacci manuscript |
| RoehmD6FaultTolerant | D8 | D6, same actual AGP-recursion manuscript |
| RoehmD9Certification | D8 | D9, quantum-network/device-characterization certification substrate |

Registry titles follow complete current manuscript titles, not stale short metadata. D8's three entries already existed in `papers/D8/bibliography.bib`; their titles/authors/status were reconciled there without parallel inline bibitems or extractor changes. D9's three companion bibliography entries and D3/D4 companion identities were aligned. All 666 prior registry entry values, including older companion keys and historical titles, are preserved; exactly twelve new entries were added, for 678 total. These identities do not certify the targets' mathematical claims or external publication status.

Four external keys retain their existing cited spelling:

- **FinazziLiberatiSindoni2012:** Finazzi, Liberati and Sindoni, *Cosmological Constant: A Lesson from Bose-Einstein Condensates*, PRL 108, 071101 (2012), [DOI 10.1103/PhysRevLett.108.071101](https://doi.org/10.1103/PhysRevLett.108.071101). Held author preprint 1103.4841v2, not an asserted publisher PDF.
- **Kitaev2006:** Kitaev, *Anyons in an exactly solved model and beyond*, Annals of Physics 321 (2006), [DOI 10.1016/j.aop.2005.10.005](https://doi.org/10.1016/j.aop.2005.10.005). Held preprint cond-mat/0506438v3 is dated 2008, distinct from the 2006 journal body.
- **Wang2026TMDPolariton:** published title *Strongly Nonlinear Nanocavity Exciton Polaritons in Gate-Tunable Monolayer Semiconductors*, author order Wang/Kim/Zhen/He, [DOI 10.1103/gc15-qsvf](https://doi.org/10.1103/gc15-qsvf). Held 2411.16635v1 is dated 2024 and orders authors Wang/He/Kim/Zhen. The independent source reviewer read the final seven-page publisher PDF pp.1–3 for D1's 2.3/1.8 meV linewidths; that final PDF is not cached, and not every device parameter is claimed identical across editions.
- **Verlinde1988:** Erik Verlinde, *Fusion rules and modular transformations in 2D conformal field theory*, [DOI 10.1016/0550-3213(88)90603-7](https://doi.org/10.1016/0550-3213(88)90603-7). Only Crossref metadata was acquired; no abstract or body reading is claimed. D4 preserves its name-attribution-only/body-unread limitation. No exemption class was added.

## Actual key-based cache resolution and fetched artifacts

Initial shared-path aliases were insufficient for the existing key/phase filename lookup and introduced three new cache-resolution faults. These were this package's failures. Independent design reconciliation retained the existing reader/writer contract and required real pinned fetches under the new key filenames; no cache copying, fabricated fetch records or checker change was used.

| Key / workspace-relative artifact under Lit-Search/Phase-1-and-Background/primary-sources/ | Actual pinned URL | Header / pages / bytes | SHA256 |
|---|---|---|---|
| FinazziLiberatiSindoni2012.pdf | [Pinned preprint](https://arxiv.org/pdf/1103.4841v2) | 28 February 2012 / 5 / 318882 | `61c4da4e5f21112acee522fedbfd65bede2e567fea53eed8ac0e47e3b7c75f3e` |
| Kitaev2006.pdf | [Pinned preprint](https://arxiv.org/pdf/cond-mat/0506438v3) | 1 January 2008 / 113 / 1533535 | `eb99541ee61044a6028edc53aad19dd80afed7e96778350a38420f36269e93ba` |
| Wang2026TMDPolariton.pdf | [Pinned preprint](https://arxiv.org/pdf/2411.16635v1) | 25 November 2024 / 6 / 1152746 | `88f4a4eda6a956ab29554730908d916891933379fc7594c3f0a674b4f055bded` |
| Verlinde1988.json | Crossref DOI metadata for 10.1016/0550-3213(88)90603-7 | metadata only / 12945 bytes | `010f971d637b39e3e596f40a5d9fa326fbfff713e7b1a35cc79149f34a34e20e` |

The existing acquisition writer made all four fetch records. The three new PDF hashes exactly equal the corresponding old canonical held-body hashes; old canonical artifacts are unchanged. All 651 old acquisition-state entry values are preserved, with exactly four new actual-fetch entries, for 655 total. Writer path resolution was reconciled to the workspace at the callsite for the linked checkout; no writer implementation or fidelity policy changed. Existing fidelity inspection identifies Verlinde's JSON as metadata, not full text.

## Directly cited scientific precision

The independent FLS assessment and lead's actual held p.2 read establish the acoustic-geometric regime at wavelengths larger than the healing length, with quartic-dispersion breakdown for k>xi^-1. D3's reversed wavelength statement was corrected without changing equations or numerical inputs. The earlier assessment of the pp.2–4 depletion comparison missed a retained attribution error, subsequently returned by ROOT: Eq. (14) is the condensate's total ground-state energy density, compared alongside its grand-canonical density h on p.4. It is not the total ground-state energy of the phonon effective theory. The separate phonon-EFT vacuum-energy statement does not identify either condensate quantity. D3 now names both condensate energy densities; fresh follow-up review is recorded separately.

Kitaev's held v3 pp.42–44 distinguish anyon statistics modulo 16 from additional robust chiral-central-charge data. D2 now qualifies both its item 4 attribution and later discussion; existing period arithmetic remains unchanged and is not promoted into a full physical-phase classification.

D4's actual introduction and scope paragraph explicitly provide no recovery map or scrambling dynamics. D3's link now points to an assessment of that categorical/error-correction interpretation rather than claiming developed recovery dynamics. D6's narrower AGP-recursion title is preserved instead of implying a complete fault-tolerance proof. These corrections repair citation support; they do not create new mathematical results.

## Actual checks, rendering and preserved boundaries

Actual base coverage: 517 cited / 505 registered, nine stubs plus three apparent orphans; both existing targeted tests failed in 1.23 seconds. Final coverage reports 517 registered, zero stubs and zero orphans. The two coverage tests plus twelve existing BibitemTitlePrimarySource/MetadataIsNotFullText tests passed together: **14 passed in 12.55 seconds**. Assertions and test files are unchanged.

After the real pinned fetches, existing citation_primary_sources_present reports **passed**, with zero missing registry keys and zero needed cache artifacts. Its actual census remains fidelity-qualified: 364 cached cited keys comprise 241 full, 59 abstract-only and 64 metadata-only; 33 internal in-preparation and 43 declared-class references are separate, with 77 undeclared against the unchanged ceiling 78. This is not full-body coverage or publication acceptance. The one declared finding Verify includes both coverage tests and this complete citation-check result, guarding against registration-only closure with unresolved cache faults.

The existing isolated compiler produced all six manuscripts with zero TeX errors, unresolved PDF references and dropped class options:

| Bundle | Pages | Overfull boxes, unwaived |
|---|---:|---:|
| D1 |21 |15 |
| D2 |18 |5 |
| D3 |65 |12 |
| D4 |30 |2 |
| D8 |12 |7 |
| D9 |14 |9 |

The lead inspected eight actual changed-page PNGs: D1 p.21; D2 p.14; D3 pp.31/37/64; D4 p.30; D8 p.12; D9 p.14. Changed passages and bibliography identities were legible; existing long-citation/identifier overflow remains unwaived. The first D8 BibTeX rendering downcased proper names; case protection was applied to its three companion titles, followed by actual recompilation and pixel review. No zero-overflow or whole-layout acceptance is claimed.

Only measured metadata delta is D4 compiled_pages 32→30 through the existing compiler, replacing a stale recorded metric. No exact baseline compilation comparison establishes that citation edits removed two pages; no such causal claim is made. Other metadata, stages, last_lift and manifests are unchanged. Shared numerical evaluators and constants, all Lean statements/proofs and formal counts remain unchanged; the existing closure ledger is untouched at this authoring boundary. No new tests, checkers, runners, exemption classes or raised ceilings were introduced. Broad/seeded, Lean and canonical integration gates remain separately controlled. Final independent scientific/source/artifact review is accepted and the separate closure audit is accepted; no merge or external-publication readiness is asserted.
