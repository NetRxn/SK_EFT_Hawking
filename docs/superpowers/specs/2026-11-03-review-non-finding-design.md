# Explicit non-finding sections

This specification implements ADR-012 D28. It remains proposed until its
implementation and full differential have independent acceptance.

Use the exact standalone line `<!-- skeft: non-finding -->` as the first
nonblank line of a numbered review section. Annotate only independently
adjudicated sections. Preserve all other source bytes, including recap text
and later QI material.

Parse and mint normally first, keeping section boundaries, normalized IDs,
metadata, ordering and duplicate precedence. Collect suppression candidates
separately. Before returning nodes, retain candidates with a duplicate ID,
actionable heading or structured field, an outgoing dependency or operator
hold, an incoming active dependency, or a ledger identity or target. Use
existing field and dependency parsing. Declared severity and verification
conflicts include malformed field declarations. Log conflicts. Historical
prose references do not create active dependencies.

Implement tests first in the existing graph review tests. Exercise a valid
marker, an embedded or quoted marker, a conflict, duplicate precedence,
incoming and outgoing dependencies and ledger protection. Annotate the
reviewed corpus and compare the complete graph finding population and
dependency edges against the baseline by ID. Require byte-equivalent metadata
for every retained node and no dropped active dependency. Check actual
bundle aggregation and preserve the August D8 §1.7 major. Then use the
canonical metadata writer, run the original §1.7 Verify, and record any
closure through the existing closer after independent review.
