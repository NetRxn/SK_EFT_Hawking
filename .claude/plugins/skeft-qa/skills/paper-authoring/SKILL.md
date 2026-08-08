---
name: paper-authoring
description: This skill should be used when the user asks to "draft a paper section", "write the bundle draft", "author the manuscript", "lift content into a bundle", "write up this wave for publication", "draft the abstract", "revise the paper prose", or when editing any `papers/<bundle>/paper_draft.tex`. Provides the house voice, the prohibited-pattern floor, and venue conventions for SK-EFT Hawking publication bundles.
---

# Authoring a publication bundle

Guidance for writing manuscript prose in `papers/<bundle>/paper_draft.tex`. This is the
generative counterpart to the `prose-reviewer` agent; both read the same prohibited-pattern
reference so a rule cannot drift between writing and review.

**Read `references/prohibited-patterns.md` before drafting.** It is mandatory, not
background, and it is short.

---

## Why this skill exists

The pipeline had three reviewer agents and no authoring guidance. Everything about how to
write lived in `docs/BUNDLE_LIFT_PROCEDURE.md` §7 as a bookkeeping checklist consulted at
lift time. The measured result of that gap, across 21 bundles:

- **741 em-dashes**, with zero bundles clean
- **13 passages** narrating the paper's own correction history to a referee
- **9 of 21 bundles shipping zero figures**, because the lift step only migrated figures
  that already existed and no step ever planned one
- **D3 carrying 37 sections against 31 contributing sources**, which is sedimentation
  rather than architecture

None of that is a capability limit. It is what an unguided generator produces when the only
controls are downstream reviewers.

---

## Before writing a section

1. **Read the charter.** `papers/<X>/bundle_metadata.json` carries `target_journal` and
   `length_target`; the section belongs to a planned outline, not to a source paper that
   happened to be registered.
2. **Read the substrate directly.** Contributing per-paper drafts, the Lean modules, the
   roadmap. Do not write from a summary.
3. **Know the claim this section makes** and which apex theorem backs it. A section whose
   claim has no Lean witness is a finding waiting to happen.

## While writing

Write for a referee at the named venue who has never seen the repository, cannot run the
code, and will not read a second sentence to understand the first.

- **State the result, then support it.** Not the programme, not the architecture, not what
  the section will do.
- **One clause, one job.** Do not interrupt a main clause to insert a clarification; write
  the clarification as its own sentence. This single habit produced most of the corpus's
  em-dashes.
- **No em-dash, ever** (`---` or `—`). **`--` is mandatory** for compound eponyms and
  ranges and must never be touched. Both rules and every replacement case are in
  `references/prohibited-patterns.md` §1; read them before reaching for a dash.
- **A fix never narrates itself.** Correct silently in the manuscript and record the history
  in `change_log.md` and the supersession ledger (§2 of the reference).
- **Numbers come from the pipeline** via `\input{tables/<spec>.tex}` and the `counts.tex`
  macros, never typed as literals.
- **Cite companion work as papers**, by title. The reader never sees `bundle`, `tier`,
  `wave`, `phase` or `splash`.

## Before handing off

```bash
cd papers/<X> && pdflatex paper_draft.tex          # must be clean
uv run python scripts/validate.py \
    --check bundle_prose_em_dash_free \
    --check bundle_reader_facing_voice \
    --check bundle_manuscript_length
```

All three are deterministic and all three must pass. They are a floor, not a review: they
confirm nothing prohibited is present, and say nothing about whether the argument carries.

---

## Why the reviewer knows things this file does not

The `prose-reviewer` agent reads this same reference, so the two never disagree about a
rule. It also carries a brief that is deliberately **not** written down here, framed on
reader outcome rather than rule compliance: where a reader would stop, whether the abstract
leads with the result, whether each section advances a single argument.

That asymmetry is intentional. A generator optimises against any checklist it can see, so a
reviewer briefed entirely off the author's rules would pass anything the author produced.
Satisfying this file is necessary and not sufficient.

---

## Additional resources

### Reference files

- **`references/prohibited-patterns.md`** — mandatory read. The em-dash prohibition and its
  replacement cases, the self-narration ban, claim discipline, structure rules. Shared with
  the `prose-reviewer` agent.

### Related surfaces

- `docs/BUNDLE_LIFT_PROCEDURE.md` — the 14-step lift workflow this drafting sits inside
  (§7 authoring, §11 the BLOCKER loop, §12a the terminal de-scarring pass).
- `docs/WAVE_EXECUTION_PIPELINE.md` Stage 10 — the process law and its gates.
- `docs/BUNDLE_DIRECTORY_SCHEMA.md` — `length_target`, `apex_theorems`, and who writes what.
