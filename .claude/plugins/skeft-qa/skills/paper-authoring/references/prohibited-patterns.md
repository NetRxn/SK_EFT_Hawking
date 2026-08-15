# Prohibited patterns in manuscript prose

**Shared reference. Read on drafting, and read again on review.** The `paper-authoring`
skill and the `prose-reviewer` agent both consume this file, so a rule cannot mean one
thing while writing and another while reviewing.

⚠️ **This is the shared FLOOR, not the whole review.** The reviewer additionally carries
reader-outcome questions that do not appear here and that an author must never be given as
a checklist: a generator optimises against any list it can see. See the skill's §"Why the
reviewer knows things this file does not".

Every rule below was derived from a measured sweep of the 21-bundle corpus, not from a
style guide. Where a number appears, it is what was counted.

---

## 1. The em-dash: prohibited outright, including in headings

**Never write `---` or a literal `—`.** Two forms exist and both are banned.

**Why this one is absolute.** An em-dash reads as machine-authored to a 2026 reader and
costs trust before the physics is evaluated. One is as disqualifying as forty, so there is
no acceptable density. Enforced by `validate.py --check bundle_prose_em_dash_free`, target
zero. Measured before the corpus was swept: **741 of them, and 0 of 21 bundles clean.**

### ⚠️ The en-dash `--` is MANDATORY and must never be touched

`--` (exactly two hyphens) is a different character doing a different job, and the corpus
carries **1,121** of them:

- compound eponyms: `Bose--Einstein`, `Bekenstein--Hawking`, `Schwinger--Keldysh`,
  `Kaul--Majumdar`, `Chowdhury--Hartnoll--Hebbar--Khondaker`, `SK--EFT`
- numeric ranges: `pp. 10--15`, `$2$--$3$ K`

**An author over-correcting to "no dashes at all" breaks every compound name in the
program, and the check cannot see it** because it counts exactly three hyphens. This is the
single highest-cost mistake available here. One live line contained both:
`observables---also drives the SK--EFT`.

A third variant exists in the wild: the literal Unicode en-dash `–` (U+2013), found as
`Kaul–Majumdar` and `Chowdhury–Hartnoll–Hebbar–Khondaker`. Write `--` instead; D3 once
spelled the same name both ways.

### Replacing an em-dash is a REWRITE, not a substitution

A mechanical swap produces comma splices. Identify the job the dash was doing, then use the
punctuation that already exists for that job. Frequencies below are from six independent
readings of all 741 occurrences.

| The dash was doing | Frequency | Write instead |
|---|---|---|
| Paired aside interrupting a clause | ~45–55% | parentheses; a comma pair when the aside is short and contains no commas of its own |
| Introducing an explanation, expansion or list | ~30–45% | a colon |
| Separating a label from its gloss in `\item`, `\subsection{}`, `\paragraph{}` | ~15% | a colon, always |
| Contrastive "X, not Y" interjection | ~7% | a comma pair (parentheses would demote a correction to an aside) |
| Joining two independent clauses | ~3–15% | a semicolon, or a full stop and a new sentence |
| Trailing appositive glossing a number's significance | common in E1/E2 | a comma |

### The four hard cases, each of which defeats a mechanical fix

1. **The aside contains its own parenthetical or citation.** Converting the outer dash to
   parentheses yields stacked or nested parens that read as a stutter:
   `(\lean{diamondDist_eq_choiSDP}) (the Watrous semidefinite program~\cite{Watrous2018}) is proven`.
   **Merge the tag and the aside into ONE parenthetical** with an internal comma or
   semicolon. Do not nest.
2. **The aside contains a comma-separated list.** Comma-punctuating it makes the reader
   parse the inner items as continuing the outer sentence's list. Use parentheses.
3. **The sentence already has a colon later on.** Adding a second colon reads as a nested
   label. Restructure with a copula: `X is the headline theorem: Y`.
4. **Three levels of subordination.** An aside inside an aside inside a main clause is a
   sentence trying to be three sentences. Split it.

### The generative habits behind them: prohibit these, not just the symbol

All six readers converged on the same root, so treat it as the rule that matters:

> **Do not interrupt a main clause to insert a clarification.** Write the clarification as
> its own sentence, before or after.

The dominant shape was *claim, dash, restatement-with-a-twist, dash, continuation*: draft a
clean declarative, then, worried a reader will misattribute a convention or miss a caveat,
splice the qualifier into the middle. It concentrated in exactly the paragraphs doing the
heaviest epistemic hedging (novelty disclaimers, provenance caveats, convention-pinning),
which is where this project's prose is densest.

Four more shapes, each of which reliably produces an em-dash:

- **Name-then-gloss in itemised lists.** `\item \verb|foo_bar|: the substantive witness`.
  Use the colon from the start; this was the single most common pattern in the Lean-heavy
  bundles.
- **Label-then-gloss in headings.** `\subsection{Pillar 1: Golterman--Shamir}`. A dash in a
  heading also reads as a tic when scanning the table of contents.
- **Tag-stacking.** A claim ending in a `\lean{...}` identifier in parens, then a dash
  glossing that identifier. This is an appositive that got dash-punctuated only because the
  sentence had already spent its parentheses.
- **Claim-then-immediately-re-scope.** `T_H \approx 2.4$ K --- nine orders of magnitude
  above atomic BEC --- with adiabaticity...`. A defensible instinct for a rigorous program,
  executed with the wrong punctuation: pick the syntax that matches the qualifier's
  grammatical role.

---

## 2. A fix may not narrate itself

**Never tell the reader what an earlier draft of this paper said, when it was corrected, or
which review round caught it.** A referee has no access to that process and cannot act on
it; the text reads as a changelog pasted into a manuscript.

Enforced by `validate.py --check bundle_reader_facing_voice`, target zero. Banned forms:

- a correction stamped with a date: `(corrected 2026-08-01)`
- an account of an earlier draft: `three earlier drafts of this paragraph asserted...`
- a first-person superseded claim: `We previously shipped a theorem asserting...`
- an internal review reference: `(D11 Stage-13 round-14 finding 6.2)`
- the project's own planning documents: `Our earlier planning documents described...`
- review rounds cast as actors: `rounds 7 and 10 both rated this cosmetic`
- a claim about the paper's own drafting: `typeset unconditionally in every draft`

**And never tell the reader that you did not read a source you cite.** Same rule, second
shape (added 2026-08-15): it is an account of your process, and it leaves the citation
standing as support for a claim while the prose says nobody read it. Banned forms:

- an unread cited source: `we have not inspected its text`
- a citation held as metadata: `we hold that source only as a resolved DOI record`
- a citation read off its abstract: `we have read \cite{X} in abstract only`

**The fix is to acquire the source, never to delete the sentence.** Dropping the hedge while
keeping the citation converts a visible gap into an invisible one (ADR-014). If the source
cannot be acquired, the claim must stand without it or not stand.

⚠️ **Three shapes look alike and only one is prohibited.** Keep the other two:

- ✓ **the cited source is itself preliminary** — *"presents itself as an ongoing project…so
  we do not read it as establishing how much of that layer is finished"*. You are
  characterising the work's maturity, not confessing that you skipped it.
- ✓ **a novelty search states its scope** — *"HOL Light was not among the ecosystems we
  assessed and we do not assert absence there"*. This is REQUIRED on an absence claim.

The line is the noun: not reading *its text* is prohibited; not having surveyed *that
development* is the scope statement a priority claim owes its reader.

**The history is not lost, it moves.** `papers/<X>/change_log.md` and
`docs/review_finding_supersessions.json` are where a later reader can actually check it, and
the ledger entry is required by the lift procedure anyway.

### ⚠️ Removing narration is not deleting content

Most of these passages wrap something real, and the substance must survive:

- **A retraction is a scientific disclosure.** Restate it as a present-tense negative
  result: what is *not* claimed and why it fails. Do not delete the paragraph.
- **A scope correction states the correct scope.** Keep every factual statement about what
  a module does and does not contain, including file:line references. Drop only "earlier
  drafts called it X" and the date/round/finding tag.
- **A completeness disclaimer is a real caveat.** Keep it; drop the account of what two
  earlier drafts asserted.

### What is NOT prohibited

Reporting that *the literature* corrected something is ordinary scholarship: `Smith
corrected this coefficient in 2019` is correct and stays.

Describing the verification pipeline is legitimate **when the pipeline is the paper's
subject matter** (I1, and I2/I3 for library conventions). Addressing the paper's own
referees is legitimate anywhere: `lets Mathlib4 reviewers calibrate expectations`.

This distinction is why the rule targets the *act* of self-narration rather than a
vocabulary. A word list banning `Stage 13`, `reviewer` and `adversarial review` scores 90
hits on this corpus, of which 48 are legitimate uses in the methodology paper alone.

---

## 3. Claim discipline

These are enforced elsewhere in the pipeline; they are repeated here because they are
cheaper to satisfy while drafting than to repair at review.

- **Never hedge a count or numerical literal with "alt convention" or "+N depending on
  convention" without proving the convention sensitivity.** If counts disagree across
  tools, find the truth. Convention-drift framing masks actual content drift: a "161 ± 3
  alt convention" was really 164, and the +3 was real drift.
- **Verify which registry a name lives in before citing it.** `AXIOM_METADATA`,
  `PLACEHOLDER_THEOREMS`, `HYPOTHESIS_REGISTRY` and `BORDISM_HYPOTHESES` are four different
  tables; a name found in one and attributed to another is a Stage-13 blocker.
- **Every cross-language prior-art claim must resolve to a verifiable URL or canonical
  ecosystem reference.** Hallucinated libraries have shipped before. When in doubt, cite
  the ecosystem (UniMath, Mathlib4) rather than naming a specific library.
- **When broadening an attribution, verify every addition belongs in the broadened
  category.** Surface code is abelian-stabiliser QEC, not non-Abelian-anyon TQC.
- **Numbers come from the pipeline.** Use `\input{tables/<spec>.tex}` and the `counts.tex`
  macros rather than typing a literal.

---

## 4. Structure

- **The abstract leads with the result**, not with the programme, the architecture, or what
  the paper will do.
- **The reader never sees the project's internal taxonomy.** Not `bundle`, `tier`, `wave`,
  `phase`, or `splash`. Companion papers are cited as papers, by title, in a normal
  reference list. This is what makes a manuscript read as a repository index: F's organising
  vocabulary was its own publication plan.
- **Section architecture is authored, not accumulated.** A bundle's sections come from its
  charter, written before any source is registered. Do not add a section because a source
  was registered: D3 has 37 sections against 31 sources, which is sedimentation.
- **Every figure is planned.** A bundle with no figures is a charter defect, not a style
  choice; 9 of 21 bundles shipped zero figures because the lift step only ever *migrated*
  figures that already existed.
