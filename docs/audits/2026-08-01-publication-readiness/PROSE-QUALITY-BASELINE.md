# Prose quality — corpus baseline

**What this measures.** Mechanical readability properties of all 21 publication-bundle drafts.
Body text only: math environments, figures, tables and the bibliography are stripped, and
dotted identifiers are protected so `SPTClassification.lean` does not split a sentence.

**Why it exists.** No validation check, no reviewer agent, and no stage of
`WAVE_EXECUTION_PIPELINE.md` assesses whether prose serves a reader. Verified at audit time:
zero checks matching readability/style, zero of the reviewer agents briefed on it, and zero
mentions of readability in the process law. This is the first measurement of the dimension.

---

## The table

`sent` = body sentences · `med`/`p90`/`max` = sentence length in words ·
`>60w` = sentences over 60 words · `em—/k` = em-dashes per 1000 sentences ·
`(` = open-parens per sentence.

| bundle | sent | med | p90 | max | >60w | em—/k | ( |
|---|---:|---:|---:|---:|---:|---:|---:|
| `D9` | 128 | 34 | 63 | 95 | 14 | **391** | 1.61 |
| `D10` | 63 | 30 | 50 | 85 | 1 | **349** | 0.83 |
| `D6` | 238 | 21 | 45 | 95 | 6 | **345** | 1.17 |
| `D12` | 240 | 22 | 39 | 81 | 3 | **317** | 0.2 |
| `D11` | 175 | 23 | 40 | 66 | 3 | **297** | 0.18 |
| `D8` | 130 | 27 | 56 | 123 | 12 | **285** | 1.0 |
| `E2` | 63 | 22 | 58 | 99 | 5 | **270** | 0.56 |
| `I1` | 356 | 22 | 51 | 171 | 24 | **216** | 0.59 |
| `D7` | 33 | 31 | 74 | 179 | 4 | **182** | 1.09 |
| `D3` | 459 | 20 | 40 | 100 | 16 | **172** | 0.74 |
| `L2` | 54 | 23 | 49 | 76 | 3 | **167** | 0.44 |
| `D5` | 224 | 22 | 42 | 95 | 5 | **161** | 1.07 |
| `E1` | 76 | 24 | 43 | 98 | 3 | **158** | 0.61 |
| `D2` | 229 | 21 | 50 | 106 | 12 | **153** | 0.79 |
| `D4` | 255 | 24 | 51 | 125 | 17 | **125** | 1.0 |
| `I2` | 152 | 20 | 46 | 91 | 7 | **125** | 0.8 |
| `F` | 444 | 21 | 40 | 108 | 14 | **115** | 0.87 |
| `I3` | 211 | 22 | 45 | 143 | 10 | **114** | 0.63 |
| `D1` | 165 | 19 | 44 | 100 | 11 | **109** | 0.73 |
| `L3` | 47 | 26 | 52 | 59 | 0 | **106** | 0.83 |
| `L1` | 56 | 16 | 40 | 89 | 1 | **36** | 0.39 |

**Corpus median-of-medians: 22 words** — normal for physics prose. The problem is not average
density.

## What the numbers say

**1. The tail, not the mean.** 171 sentences exceed 60 words. Seven bundles contain a sentence
over 100 words; D7 peaks at **179**, I1 at **171**, I3 at **143**. A 179-word sentence is not a
stylistic preference, it is an unfinished edit.

**2. Em-dash density spans 11× within the corpus** — L1 at 36 per 1000 sentences, D9 at 391.
Both ends are this project's own output, which makes the low end a calibration target rather
than an external ideal. No appeal to outside style guidance is needed to say 391 is wrong: L1
demonstrates the same author and substrate at 36.

**3. The gradient tracks recency.** The newest bundles occupy the top of the table
(D9 391, D10 349, D6 345, D12 317, D11 297); the oldest occupy the bottom (D1 109, L3 106,
L1 36). Prose became more machine-shaped as the corpus grew.

**4. D9 is worst on every axis simultaneously** — highest em-dash density, median sentence 34
words against a corpus norm of 22, p90 of 63, and 11% of its sentences over 60 words. It is also
the least-reviewed bundle and the only GREEN one. See
[`PROMOTION-PATH-AND-SIGNAL.md`](PROMOTION-PATH-AND-SIGNAL.md).

## Interpretation

The corpus optimized exactly what it measured. Stage 10 produces a draft; Stages 9/10/13 verify
**truth** — figures render, claims trace to theorems, citations support their sentences. The
claims reviewer walks every sentence asking *is this backed?* Nothing asks *does this land?*

The result is a corpus of individually defensible sentences assembled without an authorial pass.
D9's abstract — one sentence, five layers, ~250 words — is the pure case: every clause true, the
whole unreadable.

⚠️ **This is a missing control, not a capability limit.** The same project produced a
1,123-theorem kernel-pure Lean corpus, because the kernel refuses bad proofs. It produced
unreadable prose because nothing refuses bad prose. The distinguishing variable is the presence
of a decider, not the author.

## Remediation — NOT built (per audit constraint)

Filed for `ARCHITECTURE_TODOs.MD`:

1. **A readability ratchet check**, house idiom: p90 sentence length, >60-word count, em-dash and
   parenthetical density per bundle; ceiling set to the live measured value; shrink-only.
   Calibrate against L1/D1, which are in-corpus evidence of the achievable end.
2. **A `prose-reviewer` agent** — the missing fourth reviewer. `claims-reviewer` asks *is it
   backed*, `adversarial-reviewer` asks *is it wrong*, `figure-reviewer` asks *does it render*.
   Brief: read as a referee for the target venue; mark where you would stop reading, where the
   argument fails to carry, whether the abstract states the result in its first sentence.
3. **A gate before Stage 13.** Sending an unreadable draft to adversarial review spends the most
   expensive reviewer in the pipeline on prose defects.
4. ⚠️ **The decider must not be the generator.** An LLM rewriting LLM prose can converge on a
   different bad attractor. Metrics computed independently of the rewriter, an adversarial reader
   with a distinct brief, and human calibration on a *sample* — not on all 21.
