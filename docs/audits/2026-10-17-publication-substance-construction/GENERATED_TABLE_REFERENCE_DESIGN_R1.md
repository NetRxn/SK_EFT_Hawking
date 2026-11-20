# Proposed ADR-009 clarification for generated-table theorem references

Exact PR118 ddc320ec and frozen all-eleven table patch f963e4a5. The
existing theorem-reference checker reads the raw bundle draft. The source
migration drops 32 distinct resolved names and 64 occurrences from that
population. An independent review reproduced the loss and recovered the
full token multiset with the TeX input population and draft macro context.
The direct-input pilot then measured the exact same expanded token
multisets before and after migration across all 21 bundles. Previously
generated direct table inputs add no tokens on this base. The live gate
result is not repaired by a smaller scan population.

## Proposed decisions

1. Extend the existing bundle leg of prose_theorem_reference_coverage to
   read direct canonical table inputs referenced in the draft. Reuse the
   shared TeX input token grammar and comment stripping to identify
   active direct input commands. Limit reads to the existing tables
   directory beneath the real bundle directory. Resolve only matching
   .tex targets, with the existing default extension convention. Fail on
   missing, unreadable or escaped referenced table files. Deduplicate
   identical physical file paths. The generic input dependency closure
   remains the freshness authority.
2. Reuse the existing verbatim tokenizer and resolution tiers. Supply
   the draft's macro declarations when scanning a generated table, while
   retaining each file's local offsets for diagnostics and disclaimers.
   Group by token across the draft and its table inputs as one bundle
   population. Preserve all existing waiver, severity, disclaimer and
   resolution rules. Leave the separate legacy leg unchanged.
3. Keep the check name, graph interfaces and thresholds. Use the existing
   ADR-009 and validation architecture documentation. The correction
   restores the checked population after the table migration and does
   not assert semantic theorem backing or change publication scope.

## Qualification

Add a red test on an actual generated D9 table using its inherited lean
alias. The existing checker must miss a deliberately unresolved name
there. The patched check must reject it and report the actual file and
line. Restore exact production bytes through the existing seed journal.
Also test missing input, comment decoy, symlink escape, inline legacy
behavior and context-local disclaimers. Compare complete baseline and
composed verdict and candidate identities on the same retained catalog.
Keep inherited faults visible. Use the existing registration audit and
independent source review before applying the composed table package.
