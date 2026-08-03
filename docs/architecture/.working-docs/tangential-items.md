# Tangential items — parked until the QA/QI remediation completes

Items surfaced during the 2026-08 publication-readiness / validation-infrastructure work that are **out of
scope** for it, recorded so they are not lost. None blocks ADR-009.

---

## T1 — Dual slot-management implementations (Claude vs Codex)

**Status: real duplication, confined, non-blocking.**

Two mechanisms manage the same three Lean worktree slots (`wt1`/`wt2`/`wt3`):

| | Claude path | Codex path |
|---|---|---|
| Entry point | `.claude/plugins/skeft-qa/scripts/reset_slot.py`, `/skeft-qa:reset-slot` | `scripts/slotctl.py` → `scripts/lean_slots/{cli,controller,proxy,state,supervisor}.py` |
| Governing doc | plugin skill | [ADR-008](../../adrs/ADR-008-shared-lean-slot-control-plane.md) |
| Build authority | lead-owned by convention | lease-enforced + hook-guarded (`.codex/hooks/pre_tool_use_policy.py` blocks raw `lake build`, git mutations, direct `slotctl` subcommands) |
| Live today | **yes** | Codex-first authorized; Claude activation deferred |

**Verified provenance (2026-08-03).** The Codex contribution is **7 commits, all dated 2026-07-22**, authored
as `NetRxn` with **no co-author trailer** — there are zero non-Anthropic `Co-Authored-By:` trailers in the
last 60 days, so trailers cannot discriminate Codex work. The discriminator is the artifact set:
`scripts/lean_slots/*`, `scripts/slotctl.py`, `.codex/*`, ADR-008. **No activity since 2026-07-22.**

**Verified non-overlap with ADR-009.** `grep` over `scripts/lean_slots/`, `.codex/`, and `scripts/slotctl.py`
for `validate.py`, `register_check`, `gate_precheck`, `bundle_readiness`, `build_graph` returns **nothing**.
The Codex work never touched the validation suite, the readiness stack, or the provenance graph. The single
non-Anthropic commit that did touch `scripts/validate.py` (`b7b91c81`, *"feat: harness enhancements (wip)"*)
is dated **2026-06-22**, predating Codex, and is an operator commit.

**When resumed, decide:** converge on one slot mechanism, or define which owns which client. Two mechanisms
over one resource is the ADR-004 single-writer concern applied to slots rather than artifacts.

---

## T2 — ADR-008's Claude-Code activation: DEFERRED BY DECISION

**Status: decided 2026-08-03. Not an open question; scheduled work.**

ADR-008 is ACCEPTED with *"CODEX-FIRST IMPLEMENTATION AUTHORIZED; CLAUDE CODE ACTIVATION DEFERRED… no
earlier than the week of 2026-07-27."* That window has passed, so the ADR is behind its own schedule.

**Operator ruling (2026-08-03):** *"You're right on ADR 8, we're behind schedule on that, but I want to get
our systems working first before we mess with onboarding claude-code into the new system. We'll circle back
to ADR-008 after we've completed all the infrastructure remediation and paper prose remediation."*

So the sequencing is explicit and deliberate:

1. Infrastructure remediation (ADR-009 Phases 0–3, and the T4 orphaned-enforcement items)
2. Paper-prose remediation (the publication-readiness audit's BUILD / CORRECT / FACTUAL queues)
3. **Then** ADR-008 Claude-Code activation

Until then the legacy Claude slot path (`reset_slot.py`) remains live and is the supported mechanism; the
Codex control plane stays Codex-only. ADR-008's own status line should be amended to record this
re-deferral when it is next touched — the current text implies the window merely elapsed rather than being
deliberately re-scheduled behind two named workstreams.

---

## T3 — The MCP-efficiency claim is UNVERIFIED

ADR-008 argues the streamable-HTTP deployment lets both products share **one server process per
project/worktree** instead of one stdio server per client *and per subagent* — plausibly the structural fix
for the ENFILE/vnode-exhaustion class that motivated the three-slot posture.

**This has not been vetted.** No one has confirmed it runs, that both clients connect cleanly, or that the
resource claim holds under three concurrent workers. Do not quote the efficiency gain as fact until someone
does. Note ADR-008's own recorded constraints: HTTP deployments are single-project and reject project
switching, and REPL objects remain session-scoped, so separate client sessions can still spawn separate REPL
subprocesses — the sharing is of the LSP client, not necessarily of every subprocess.

---

## T4 — Orphaned enforcement, found while mapping (not Codex-related)

Recorded here because each is a standalone fix outside ADR-009's scope:

1. **`docs/AI-DEFECT-DEFENSE-LAYER.md` describes a Tier 1 that does not exist.** It names
   `scripts/pre_commit_hook.sh` and `scripts/install_pre_commit.sh` as the implementation at `:5`, `:50`,
   `:205`, `:253`. **Both files are absent** (verified by absolute path). Every Tier-1 token-class and
   structural check it specifies is enforced by nothing. Of its 9 named Tier-2 checks, **1 is registered**
   (`axiom_closure_allowlist`); 8 are absent. Pipeline Invariant #16 cites this document as canonical — via
   a filename that is also wrong (`AI_DEFECT_DEFENSE.md`).
2. **Stage 9 has no machine reader.** `figure-reviewer` writes `figures/figure_review_report.json`; the only
   consumer (`provenance_dashboard.py:2495`) reads `papers/<paper>/figures/figure_review_report.json`.
3. **`scripts/lint_native_decide_comments.py` is orphaned** — a full CLI with ERROR/WARN tiers, wired into
   no hook, no check, no skill, though ADR-002 treats it as mandatory after a file-wide replace.
4. **`stage9_status` / `stage10_status` are read by nothing.** The 2026-08-03 guard covered
   `stage13_status` only. Extending it requires stage-attributed findings first — `blocker_count` aggregates
   across all stages, so "stage9 green with blockers open" is not necessarily wrong. Do not guess.
5. **`figures/provenance_graph.json` is ~4 months stale**, git-tracked, regenerated by nothing, read by
   nothing in code.
