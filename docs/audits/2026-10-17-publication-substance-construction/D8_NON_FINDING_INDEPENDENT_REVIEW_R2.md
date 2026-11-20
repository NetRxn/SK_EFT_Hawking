# D8 1.7 independent exact protection review R2

**ACCEPT** the exact R1 donor and canonical Verify with R2 protection
patch SHA256 `b97ebb23081a65465d3e9c83ec697c9803fc54ae462683d96c6e47d018233b21`
on frozen base `3f9461f0f2d1f4ba3edb433ceedebf28d3cdaa18`.
R2 modifies the parser's conflict recognition and extends the existing
regression fixture by the two measured fail-closed cases.

I independently applied the test hunk to the R1 scratch candidate.
The focused test failed for both missing actionable IDs. Applying
the parser hunk made the exact test pass. My separate scratch probe
again reproduced silent loss of both bare bold labels on R1. On R2,
both remain findings and emit conflict warnings. The four filled
or colon-bearing controls also remain findings. The original
fixture's valid non-finding still suppresses, and its dependency,
duplicate and ledger-protected controls still pass.

The R2 corpus replay was byte-identical to the independent R1 green
snapshot, including all 1,817 retained records, all seven active
blocked-by edges, the ledger hash and its existing dangling references.
The exact Verify ran with PYTHONPATH unset and exited 0. Eight artifact
IDs are excluded and all nine required findings remain. D8 1.7
remains open and major pending canonical closure.

First and final continuity are fresh and byte-identical. The independent
red/green logs, direct probes and corpus replay are in `/tmp/d8-non-finding-independent-r2.k9srfs`.
The scratch pytest invocation emitted five unknown slow-mark warnings
because the reduced scratch tree lacks the repository pytest settings.
No real checkout, ledger, slot or remote writes were made.
