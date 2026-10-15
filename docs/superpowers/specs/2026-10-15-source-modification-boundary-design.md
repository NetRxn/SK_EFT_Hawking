# Source modification boundary design

Specification before code; governs ADR-018 D1–D3.

The production manifest reader computes a maximum over eligible files in a selected paper tree. Eligibility is: file, no relative component beginning with a dot, no relative component equal to `__pycache__`. Ancestors of that tree do not participate. The maximum starts at zero exactly as before; no eligible positive mtime gives None. UTC conversion remains unchanged: the manifest formats whole seconds; the freshness datetime retains fractional seconds. Pin both using a deterministic fractional mtime. Symlink behavior and generated-file eligibility are unchanged.

Implementation changes the predicate's input from absolute path parts to `p.relative_to(paper_dir).parts`. The writer and metadata lifecycle are reused. Add deterministic tests with different file times, not current-clock comparisons; make hidden/cache fixtures newer so accidentally including them fails. Assert the rendered source row contains the expected timestamp. Tests must not refresh production metadata or artifacts. A known existing source in the actual hidden checkout will also be measured read-only.

The separate freshness reader is explicitly assigned too: apply the same relative boundary using its `pdir`, preserving its existing bundle_metadata.json/append_log.json exclusions and datetime interface; tests must pin the distinction that the manifest reader includes those filenames. Exercise both readers in the same deterministic test matrix. No population-wide claims or pilot disposition counts are part of this design.
