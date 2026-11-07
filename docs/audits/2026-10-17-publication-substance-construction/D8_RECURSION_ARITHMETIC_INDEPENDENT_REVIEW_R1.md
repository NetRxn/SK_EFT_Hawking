# Independent review of D8 recursion arithmetic R1

**REVISE before landing.** Both proposed arithmetic edits agree with the
pinned Lean definitions. The same worked example is repeated on rendered
page 11 in the Trust Boundary and still says depth zero. Correct that
occurrence and add it to the finding's exact verification before closure.

The continuity packet matched at intake and after independent replay.
The base was 74c5ad099b6800ebf41581e1909110d7c3cc94ca. The exact two-hunk
patch SHA256 was fe2fa17e6cd06206d9d2db46624926e1bec459cd6b825e4ebb67f78043339d09.
The finding SHA256 was 64e27ffb8f7e751f2628ee6b8b3bef8d8130e8805dd7dd76ba785e423924d377.
Reconstructed both snapshots with Git archive, checked and applied the
patch in scratch, matched the supplied candidate bytes, and verified
unchanged metadata bytes. The finding marker validator passed and the
declared commands returned 1 and 1 on baseline, 0 and 0 on the candidate.
The second command misses the Trust Boundary occurrence at TeX lines
1190–1193.

The successor formula in EpsilonSeq.lean:50–59 multiplies by K.
The closed form in EpsilonSeq.lean:237–248 uses K squared in the
rescaling. The unchanged contraction condition follows from the latter.
The worked proof is CliffordTCompiler.lean:129–141, which instantiates
the existing theorem at identity and epsilon0. Substituting epsilon0
from SolovayKitaevRecursion.lean:107 into its depth definition at
lines 672–674 gives the natural ceiling of log base 3/2 of
log base 4 of 8. The inner value is 3/2 and the depth is exactly one.

Both independent builds via compile_bundle_pdf.py returned 13 pages,
four overfull notices, zero TeX errors, zero unresolved rendered
references, and zero dropped class options. Raster inspection confirmed
the recurrence on page 3 and the depth-one worked instance on page 8,
and exposed the depth-zero contradiction on page 11. The separate
depth-zero initialization statements remain valid. The tighter initial
budget invariant remains a separate BUILD. No repo, slot, or remote
writes occurred.
