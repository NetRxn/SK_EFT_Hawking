# GAP-A proposal: substrate-shape review (a graduated pre-decision)

**Status:** DRAFT for `/debrief` sign-off. **Atlas-independent.**

**Mechanizes** the L2 tracer's **dominant** root cause: the L2 keystone's hardness was *self-inflicted*
by early substrate-shape choices — the cohomology connecting map built **Kronecker-defined** (no
cochain rep) → circularity rediscovered 4+ times; **doubly-nested-subtype carriers** → the
200k-heartbeat whnf wall. The math was shallow; the cost was formalization-architecture, decided at
W1–W2/W4 design time.

## What it does
A pre-decision + `goal-dev` discipline: when building a from-scratch substrate, **shape choices are a
reviewed decision**, and when a residual resists, **the shape is re-examined first** — re-architect
the shape, don't route-shop at the wrong altitude.

## Mechanism (graduate into `PRE_DECISIONS.md` Full)
> *When building a from-scratch substrate (a representation/carrier Mathlib lacks): treat the SHAPE —
> representation form (e.g. Kronecker-defined vs cochain-rep) and carrier types (abstract vs
> deeply-nested-subtype) — as load-bearing for downstream tractability; review it at design time. When
> a residual resists across >1 attempt, re-examine the shape BEFORE route-shopping: a self-inflicted
> whnf / circularity wall is re-architected at the shape, not ground at the wrong altitude.*

Pairs with PD-1 rung B (toehold-sweep) + the lemma-isolation-with-explicit-signatures Process Win.

## Where it lives (goal-safe)
`PRE_DECISIONS.md` Full (a `/debrief`-graduated pre-decision) + a one-line `goal-dev` note. No hook,
no gate.

## Sign-off ask
Approve graduating this as a Full pre-decision.
