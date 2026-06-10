# AI Disclosure Standard — Canonical Text for All 17 Publication Bundles

**Authority:** user decision 2026-06-10. One standard disclosure text for all 17
bundles, vendor-level generic. The Aristotle clause is conditional and
register-derived (see §2). This document is the single source of truth for the
disclosure block; the ad-hoc per-paper variants listed in §3 are superseded.

---

## 1. The standard LaTeX block

Placed as an **unnumbered section immediately before the bibliography**
(`\section*{...}` — after the conclusions/acknowledgments, before
`\begin{thebibliography}` or `\bibliography{...}`).

### Variant A — bundles whose content used Aristotle-proved theorems

```latex
\section*{Methods and tools disclosure}
The formal verification layer of this work was developed with
substantial machine assistance: Lean~4 proof drafting and iteration
used LLM-based agents (Anthropic Claude-family models) operating under
the project's staged validation pipeline. A subset of the underlying
library's theorems was closed by the Aristotle automated theorem
prover (Harmonic); every proof is ultimately certified by the Lean~4
kernel via \texttt{lake build} on the public repository, independently
of any AI tool. Manuscript prose was AI-assisted and human-reviewed;
all numerical claims trace to the repository's computation pipeline
through its automated validation checks.
```

### Variant B — bundles whose content did not use Aristotle-proved theorems

```latex
\section*{Methods and tools disclosure}
The formal verification layer of this work was developed with
substantial machine assistance: Lean~4 proof drafting and iteration
used LLM-based agents (Anthropic Claude-family models) operating under
the project's staged validation pipeline. Every proof is ultimately
certified by the Lean~4 kernel via \texttt{lake build} on the public
repository, independently of any AI tool. Manuscript prose was
AI-assisted and human-reviewed; all numerical claims trace to the
repository's computation pipeline through its automated validation
checks.
```

Assembly note: the two variants differ only in the conditional Aristotle
sentence. In Variant A the closing text follows the Aristotle clause after a
semicolon (hence lowercase "every"); in Variant B the closing text opens its
own sentence ("Every proof ..."). No other wording differences are permitted.

---

## 2. Applicability rule (register-derived)

Which variant a bundle carries is **not a judgment call**. It is derived
deterministically by `scripts/aristotle_usage_by_bundle.py` from the project's
canonical registers:

- `ARISTOTLE_THEOREMS` (`src/core/constants.py`) — the Aristotle run registry
  (Pipeline Invariant #2);
- `PAPER_DEPENDENCIES` (`src/core/provenance.py`) — per-paper declared Lean
  modules;
- `docs/PAPER_DRAFT_MAPPING.md` — per-paper → bundle assignment (Pipeline
  Invariant #14);
- `lean/lean_deps.json` — theorem → Lean-module resolution.

A bundle carries **Variant A** iff either deterministic signal fires:

- **S1 — declared-module intersection:** the union of Lean modules declared by
  the bundle's source papers (per `PAPER_DEPENDENCIES`, sources per
  `PAPER_DRAFT_MAPPING.md`) intersects the set of modules containing
  `ARISTOTLE_THEOREMS` entries; **or**
- **S2 — draft names an Aristotle-proved theorem:** the bundle's
  `papers/<bundle>/paper_draft.tex` (TeX comments stripped) names at least one
  `ARISTOTLE_THEOREMS` key as a whole word.

S2 exists because `PAPER_DEPENDENCIES` declares modules for only a subset of
mapped source papers (16 of 72 mapping rows as of 2026-06-10); a draft that
names an Aristotle-closed theorem uses it regardless of what its source papers
declared (live cases: I1 discusses `firstOrder_uniqueness` as methodology
subject matter; I2 names 8 Aristotle-closed estimator/fusion theorems).

Regenerate at any time:

```bash
uv run python scripts/aristotle_usage_by_bundle.py          # table
uv run python scripts/aristotle_usage_by_bundle.py --json   # machine-readable
```

### Live snapshot — 2026-06-10 (REGENERABLE; rerun the script before relying on this)

Registers at snapshot: 322 `ARISTOTLE_THEOREMS` entries, all 322 resolved to
52 Lean modules; 16 `PAPER_DEPENDENCIES` papers; 72 mapping rows.

| Bundle | aristotle_used | S1 (modules) | S2 (draft names) | Witness modules | Witness theorems | Draft "Aristotle" mentions |
|---|---|---|---|---:|---:|---:|
| F  | **yes** | yes | yes | 14 | 96 | 8 |
| D1 | **yes** | yes | yes | 6 | 41 | 16 |
| D2 | **yes** | yes | yes | 2 | 14 | 15 |
| D3 | **yes** | yes | yes | 7 | 57 | 0 |
| D4 | no | no | no | 0 | 0 | 0 |
| D5 | no | no | no | 0 | 0 | 0 |
| D6 | no | no | no | 0 | 0 | 0 |
| D7 | no | no | no | 0 | 0 | 0 |
| D8 | no | no | no | 0 | 0 | 0 |
| L1 | **yes** | yes | no | 2 | 32 | 0 |
| L2 | no | no | no | 0 | 0 | 1 |
| L3 | no | no | no | 0 | 0 | 0 |
| I1 | **yes** | no | yes | 0 | 0 | 46 |
| I2 | **yes** | no | yes | 0 | 0 | 0 |
| I3 | no | no | no | 0 | 0 | 0 |
| E1 | **yes** | yes | no | 1 | 5 | 0 |
| E2 | no | no | no | 0 | 0 | 0 |

**Variant A (8):** F, D1, D2, D3, L1, I1, I2, E1.
**Variant B (9):** D4, D5, D6, D7, D8, L2, L3, I3, E2.

Advisory at snapshot: L2's draft mentions Aristotle once — an acknowledgments
blurb ("Automated proofs by the Aristotle theorem prover (Harmonic).",
`papers/L2/paper_draft.tex` ~line 385) inherited from the project-wide
acknowledgment template, while L2's verdict is Variant B. The sweep visit
removes that blurb when installing the standard block (§3).

---

## 3. Application protocol

The standard block is applied **per bundle during the attribution-content
sweep's per-bundle visit** (`docs/roadmaps/AttributionContentSweep_Roadmap.md`
— it is part of that roadmap's exit criteria). At each bundle visit:

1. Run `scripts/aristotle_usage_by_bundle.py`; read the bundle's verdict.
2. Insert the matching variant (§1) as `\section*{Methods and tools
   disclosure}` immediately before the bibliography of
   `papers/<bundle>/paper_draft.tex`.
3. Normalize any pre-existing ad-hoc AI-disclosure text in that bundle to the
   standard (remove or rewrite so the standard block is the only
   manuscript-level disclosure; methodology *content* that discusses AI
   tooling as subject matter — e.g. I1's QA-agent sections — stays).
4. LaTeX-compile gate per `docs/BUNDLE_LIFT_PROCEDURE.md`.

### Superseded ad-hoc variants (locations recorded 2026-06-10)

This standard supersedes the three pre-existing ad-hoc disclosure variants.
They get normalized to the standard during their bundles' sweep visits:

| # | Location | Existing text |
|---|---|---|
| 1 | `papers/I2/paper_draft.tex:746` | `\subsection{The AI-tool-assistance disclosure protocol}` — Mathlib-PR disclosure protocol ("drafted with AI-tool assistance under human review and direction" + cover-memo gates R1/R2/R3). The subsection describes the *Mathlib upstream* protocol and may stay as content; the *manuscript-level* disclosure becomes the standard block. |
| 2 | `papers/I3/paper_draft.tex:1093` | `\subsection{AI-tool-assistance disclosure}` — per-PR tool-stack declaration (lean-lsp-mcp tool list). Same treatment as I2: upstream-PR protocol content may stay; manuscript-level disclosure becomes the standard block. |
| 3 | `papers/paper4_wkb_connection/paper_draft.tex:342` | Acknowledgments line "This work was conducted with the assistance of Claude Code (Anthropic)." — names a specific product; replaced by the vendor-level standard when paper4's content is lifted (per `PAPER_DRAFT_MAPPING.md` paper4 → D1; D1's standard block covers it). |

Additional location found by the 2026-06-10 register run (not one of the three
ad-hoc variants, but normalized the same way): `papers/L2/paper_draft.tex:385`
acknowledgments blurb crediting Aristotle in a Variant-B bundle (see §2
advisory).

---

## 4. Rationale — vendor-level naming (user decision 2026-06-10)

The disclosure names "Anthropic Claude-family models" and deliberately **does
not** name model versions. Development spanned varied models (multiple
Claude-family versions plus subagents); pinning version strings in 17
manuscripts would be both inaccurate (no single version produced any bundle)
and unmaintainable (every model change would require chasing and re-writing
17 disclosure blocks). **Do not add version strings** to the disclosure in any
bundle. The Aristotle clause names Harmonic's Aristotle because it is a
distinct external proving service whose runs are individually tracked in
`ARISTOTLE_THEOREMS` (auditable per run id), not a development-loop assistant.
