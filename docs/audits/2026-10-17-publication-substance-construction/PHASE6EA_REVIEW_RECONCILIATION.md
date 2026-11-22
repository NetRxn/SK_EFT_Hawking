# Phase 6EA review reconciliation

The review inventory identified two original findings whose substantive
repairs are already present on main. This replay uses the existing Lean
declaration map and the committed independent review.

- **Round 1, finding 2.1.** `poissonMean_thinning` describes its limited
  mean algebra. The actual `thinnedMean_eq_eta_mul` proof calls
  `poisson_thinning`. The same-factor
  `shotPSD_thinnedMean_same_eta` combines that theorem with the
  shot-PSD transfer property at the same `eta`. The proof dependencies
  and absence of project axioms are checked against the underlying map.
  The weighted identity uses a nonnegative parameter. A probability
  interpretation of the thinning kernel also needs the usual upper
  bound on the thinning probability. The later construction is
  `3ff08bb4c8eb9f8530e3464843237a43207259e1`.
- **Round 1, finding 2.3.** The chosen notebook route and the original
  stale wave state were independently rechecked. The portable evidence
  is [round 2, section 4.5](../../../papers/AutomatedReviews/2026-07-28-1924-internal-adversarial/phase6EA_substrate_round2.md).
  The current declaration map still traces the square-root proof to
  `QuantumNetwork.posSemidef_eq_of_mul_self_eq`. Notebook contents
  remain in their existing custody.

The lead's per-wave audit, the broader novelty and non-vacuity claims, and
the remaining Phase 6EE findings require their own dispositions. The
original reviews are preserved. This reconciliation makes no new Lean
source change or kernel certification claim.
