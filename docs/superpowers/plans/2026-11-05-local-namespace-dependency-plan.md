# Local namespace dependency repair plan

Specification and implementation independently accepted at source scope;
canonical closure and main qualification remain pending.

Global constraints: preserve the scientific exact-width regression, existing guard,
source-walk exclusions, declaration/alias policy, seed-journal restoration, one ROOT
candidate writer, independent review, and canonical closure. No Lean or DB action.

1. ROOT: reproduce current failure and record the actual affected import population.
2. Independent reviewer: adversarially assess ADR-018, specification and this plan;
   test intent against original finding1.4 and check existing machinery overlap.
3. ROOT: add meaningful namespace and negative tests; demonstrate the original red
   path. Extend only the existing local-name walk after specification acceptance.
4. ROOT: run the declared suite, production-seeded non-vacuity test and exact D3
   regression; inspect source diff and registration sites; update owning architecture
   description before shipping. Existing counts/freshness writers remain authoritative.
5. Independent reviewer: verify actual implementation, negative controls, restoration,
   population changes and unchanged scientific assertions. ROOT uses closure writer,
   updates the existing queue, commits and pushes. Main qualification remains owed.

Ownership: ROOT edits `tests/test_dependency_declaration.py` and its existing owning
architecture/finding records; reviewer writes scratch assessment only. Scientific
L1 source construction remains independently active and does not depend on this fix.
