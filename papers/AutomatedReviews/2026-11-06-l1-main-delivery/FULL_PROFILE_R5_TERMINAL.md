# Exact L1 delivery candidate: completed merge profile

The existing full merge profile on `5a5d36fed74a83dcf4746e95b8f7673309e11d27`
finished on 6 November 2026 at 10:29:20 UTC with exit code 1.

- Lean library and ExtractDeps build: **PASS**, 10,834 jobs.
- Full Python suite: **FAIL**, 7,053 passed, 63 failed, 52 errors, 46 skipped.
- CI validation: **FAIL**, 76 of the required 85 checks measured.
- Four explicitly selected CI-skip checks: **FAIL** as a combined phase;
  the wrapper summary does not establish each individual check outcome.
- Working-tree conservation: **FAIL**. The existing checks regenerated
  `docs/counts.json` and `papers/paper15_methodology/tables/table2_checks.tex`.
  Scientific source HEAD remained unchanged. Those generated edits require
  their own verification and are not accepted merely because a check wrote them.

The linked archive preserves the invocation, terminal result, actual wrapper
stdout/stderr and generated diff. Its readback records member hashes. Full
child-process test tracebacks were not retained; the earlier failure cache is
only diagnostic. Do not attribute all failures to missing native prerequisites.

Next: use the now-built exact candidate to refresh its canonical declaration
extraction, reproduce graph-dependent failures with full output, and repair
confirmed publication source defects through the existing planner and review
writers. Preserve existing scientific obligations, numerical ceilings and human
approval. This is not a successful merge gate, fresh portfolio gate snapshot,
qualified main integration or publication acceptance. L1 remains the lead.

Evidence: [archive](FULL_PROFILE_R5_TERMINAL_EVIDENCE.zip),
[hash readback](FULL_PROFILE_R5_TERMINAL_READBACK.json).
