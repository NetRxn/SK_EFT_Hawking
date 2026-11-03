# D8 primary source intake

Three version-pinned arXiv PDFs were verified readable and cached under the existing workspace Lit-Search primary-source path. The cache holds the full text. This repo records the publication work and source readback.

| Cache key | Primary version | Pages | SHA-256 |
| --- | --- | ---: | --- |
| RossSelinger2016 | [1403.2975v3](https://arxiv.org/abs/1403.2975v3) | 40 | `4792f897a1326cb5e039e167d13620d5d7d8c0ef82a3de6ce891a9ab4ed74a70` |
| KMM2013 | [1206.5236v4](https://arxiv.org/abs/1206.5236v4) | 23 | `0946f767e7120ce6526b5e235b00a5cc8d5ded827920cdf5589422458c3d55c5` |
| Mukhopadhyay2024 | [2401.08950v1](https://arxiv.org/abs/2401.08950v1) | 55 | `16b5c2c30086a872f9584f7a7f324c84d7e01c4936f16be172eb5d665c5ebdbd` |

The author versions contain Ross–Selinger Hypothesis 8.3 and Mukhopadhyay Fact 3.9, Lemma 3.10 and Conjecture 4.8 at the expected anchors. Section-by-section claim comparison remains open. In particular, Ross–Selinger Hypothesis 8.3 concerns the asymptotic likelihood that an algorithm-generated integer is prime. D8 must distinguish that role from its own bounded residual realization hypothesis. D8 finding 1.5 stays open pending the full attribution comparison and paraphrase-cache classification.

## Appendix C and cache readback

Ross–Selinger C.2 describes the unit group and its doubly positive squares. Definition C.15 permits a relative norm up to a unit. C.16 removes that unit under the positivity condition in the dyadic rings. D8's Lean theorem is the integral-ring version, and C.17's denominator-clearing reduction is outside that version. C.19 combines coprime factors. The manuscript now separates C.20's prime-case gcd construction and the norm-power obstruction, stating the hypotheses used by each Lean theorem. Its C.21 special case takes the norm `±p` with `p ≡ 7 mod 8` as input. The bounded finder does not implement the source's general factorization procedure.

Nine existing caches were explicitly relabelled as project-authored summaries while preserving their bodies: AaronsonGottesman2004, BMPRV1999, Brylinski2002, Hietala2020VOQC, KMM2013, Lewis2021VerifQC, Mukhopadhyay2024, ReadRezayi1999, and RossSelinger2016. The historical Dawson–Nielsen mislabel is documented separately in D8_ATTRIBUTION_SOURCE_READBACK.md. The declared three-file existence command passed from the canonical repository root. Independent manuscript and cache verification remains required before recording finding 1.5 fixed.
