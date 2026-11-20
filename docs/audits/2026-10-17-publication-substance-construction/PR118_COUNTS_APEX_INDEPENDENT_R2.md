# Independent review of the PR118 count and apex repair

**ACCEPT at scoped source and test level.** The frozen patch applies to
`68e4310a6e4c5a371402b5e202d50e076296b184` and touches six paths.
I verified the author manifest. The existing three-test XML receipts for
immediate parent `ddc320ec365a1f42fd5d8d81796ae07bc0bb029c` and the draft
both reproduce the same assertions: an extra seeded apex fails to trip
ratchets, D8 closure counts are stale, and a seeded counts test starts
with figures 170 versus live 171. Both controlled lanes included the
same refreshed Lean stamp. These observations place all three failures
before the table commit.

I applied the exact patch to a fresh detached clone and reran the same
four selected test classes. **43 passed in 17.73 seconds.** The existing
count and bundle-count generators were run with the read-only venv and
scratch UV cache. The four generated artifacts stayed byte-identical.
The scoped output changes default-collected pytest cases from 6,891 to
6,943 and figures from 170 to 171. D8's existing declared-apex closure
renders 1,877 theorems, 2,401 declarations and 305 modules. Source
provenance is the repository-relative `lean/lean_deps.json`; the
generator's input path and actual counting behavior are unchanged.

Independent Git-blob SHA replay reproduces the old source stamp
`be5f125717089b51` at the last index refresh `bf586aa77` and the
new stamp `fc377552dec9e27e` at both immediate table commits. Across
2,058 module files plus the aggregate, seven FKLW files changed since
the refresh. Non-comment source lines in all seven are identical, and
the declaration JSON blob is unchanged. The stamp correction tracks
that documented source drift. This was an index provenance check
rather than native re-extraction.

The apex floor increases from 634 to the observed 640. Content-free
and undisclosed ceilings tighten from 20/15 to 19/14. The exact patch
edits no apex identity, claim, detection or exemption. The selected
tests include the real corpus adverse insertion, name reporting,
both zero-headroom checks and both population-floor checks. The
post-test binary patch remains byte-identical to the frozen proposal.
Terminal continuity is fresh. Full merge qualification remains separate.
