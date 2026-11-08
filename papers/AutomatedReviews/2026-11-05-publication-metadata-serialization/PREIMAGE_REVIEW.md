# Canonical bundle metadata: preimage and history review

ACCEPT propagation of the existing normalization repair onto the current two-file population. This is reuse of the existing bundle_json writer, not a new serializer, infrastructure layer or semantic metadata revision. No candidate edit or runtime/test acceptance is claimed by this review.

Initial publication-metadata-serialization-preimage-review-r1 packet checked fresh/changed=[]. Current HEAD4b6408ce608b6138d903aaa96f787dda139394b6. Read scripts/bundle_json.py and all serializer tests, actual current D3/L2 metadata, scoped Git history, original TODO-D25 and prior frozen failure disposition. Other shared candidate artifacts belong to ROOT/scientific writers and were left untouched.

## Exact preimages, not an old semantic overwrite

Both current metadata blobs are BYTE-IDENTICAL to the parent preimages of BOTH6a6cd7ee6e3d927f5dea241bd046d6a1a32edd72 andb8f352bd82e4c46c562ea6033e9b80fb8fd4071b. Canonicalizing the current parsed objects with the exact current dump_bundle_json body produces BYTE-IDENTICAL postimages to both historical commits. b8f352bd8 explicitly records cherry-pick of6a6cd7ee6. Neither commit is an ancestor of current HEAD, so the existing repair has not been inherited here.

This unusually exact equality means no older claim/status/date/human field is being substituted for a changed current one. Prefer ROOT applying current write_bundle_json to the two current objects; propagating the reviewed two-file normalization is also source-compatible after rechecking these exact preimage hashes at application. Do not replace any blob merely because an old commit had the right formatting; the measured equality is the prerequisite that makes this particular reuse safe.

## Proposed bytes and preservation checks

- D3 sourceSHA256b0061743d9cdb4c89fd872f8f36e74699a13a5da30517102cb2ccf0b9fd7708d; proposedSHA256cdc8cec5040596b6eb950e07c8646c155f9137973950ecec4216422bdaaf075f. Only94 lines exchange escaped non-ASCII sequences for their exact UTF8 characters;25,983to25,273bytes. Existing final newline retained.
- L2 sourceSHA256f5231e903694eef7b637da53e759e728bfcc57da6ab158094b836c648c4bb341; proposedSHA256eb926f0fb30a8df77f38993ddb897441fe6f1aa95742c07d04811c7e7a363b0a. Only missing final newline is added;9,692to9,693bytes.

Drafts and reviewable standard Git no-index diffs are under /tmp/l1-serialization-preimage-proposals/. D3.bundle_metadata.json and L2.bundle_metadata.json are canonical proposed bytes; D3.diff and L2.diff represent95 total insertions/95 deletions across the two files, with zero semantic field changes. D3's line count is encoding visibility, not94 changed claims.

/tmp/l1-serialization-preimage.json contains exact source/proposal/history hashes, paths, byte counts and assertions. Strict UTF8 decoding and duplicate-rejecting JSON object parsing succeeded. Nonfinite literal tokens are rejected, and recursive numeric checks also establish no overflow-to-infinity float values. Recursive typed-tree and dictionary key-order equality hold before/after; every claim/status/date/human field, list order and scalar type is preserved. The serializer is idempotent on both proposals. No hidden field is dropped or assigned a new acceptance state.

Used only the exact existing dump_bundle_json AST body with stdlib json in scratch, not a candidate module import or alternate normalizer. The writer remains ensure_ascii=False, indent2, authored key order and one final newline. Its no-op behavior intentionally preserves mtime when bytes already canonical; ROOT should use that same existing writer for application and second-pass readback.

## Existing route and closure boundaries

Original TODO-D25 in docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD records the single writer as fixed on9August;3516569d5 introduced it. Current test guard already expresses canonical serialization and checks actual writer call sites. The current frozen failure package canonical_json is exactly three failures: escaped D3 plus D3/L2 fixed-point failures. The present owning route is the frozen37 disposition and REPAIR_DISPOSITION_MAP serializer predecessor package, not a new mechanism.

A bounded search of docs/review_finding_supersessions.json for either normalizer commit, serializer, bundle_json, escaped Unicode or TODO-D25 found no matching minted closure entry. Do not invent an old ADR-012 finding ID or claim its canonical closure has been propagated. Reuse the accepted source repair and record current propagation/qualification in the existing disposition/source-binding record. If ROOT requires a new formal canonical finding for bookkeeping, it must be a real narrowly scoped present formatting regression with its declared Verify, or a located real original finding; it must not manufacture scientific acceptance or a second serializer registry. A new defect/sidecar is not needed to authorize the already reviewed writer operation.

After application, ROOT should run the existing serializer suite and focused current source checks, inspect exact two-file bytes and semantic preservation, and obtain composition readback before checkpoint. Such tests were not run by reviewer. Do not imply all37 fixed or all manuscript claims correct from three serialization failures disappearing. The escaped strings include pre-existing substantive scientific wording; normalization does not endorse it. All existing scientific BUILD, human, full qualification/main and publication duties remain unchanged.

Reviewer wrote only /tmp/l1-serialization-preimage.json, /tmp/l1-serialization-preimage-review.md and the prefix-owned scratch proposal/diff directory. No candidate edit, tests, graph, database/native operation, Lean action or Git mutation. One optional TODO glob had no match; the actual tracked TODO-D25 path was then located through the original writer commit and read. No absent-glob result was used as evidence of missing policy.
