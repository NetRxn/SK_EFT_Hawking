# Phase 6x Item L continuation (L.A / L.B / L.C) — Stage-13 adversarial review

**Date:** 2026-05-30  **Verdict:** ✅ **GREEN-WITH-RECOMMENDED** → advisories substantively closed → **GREEN**
**Reviewer:** fresh-context adversarial reviewer (read-only, no-web), per the Wave Pipeline Stage 13.

## Scope reviewed

The three new kernel-pure modules of the Item-L continuation (commits `952294e` → `62ccfd3`,
Stage-9/10 sync `8b5e795`, roadmap `aa81db8`):

1. `lean/SKEFTHawking/FKLW/MukhopadhyayChannelRep.lean` — **L.A** (channel representation Eq. 27 over
   the shipped 64-Pauli basis; monoid-homomorphism law; orthogonality; conjugation-action
   characterization; structural re-base of `IsExactlyCliffordCCZ` onto `channelGenMonoid`).
2. `lean/SKEFTHawking/FKLW/MukhopadhyaySde2.lean` — **L.B** (dyadic `sde₂`, Definition 3.13, via
   `padicValRat 2`; Fact 3.14 half-sum `+1` bound — the scalar core of Lemma 3.16).
3. `lean/SKEFTHawking/FKLW/MukhopadhyayToffoliBound.lean` — **L.C** (`toffoliCount` / `toffoliCost`;
   the telescoping mechanism `toffoliCount_ge_measure` / `toffoliCost_ge_measure` giving
   `T^of(U) ≥ sde₂(Û)` under the reading `μ = sde₂ ∘ channelRep`).

Against the curated DR dossier `Lit-Search/Phase-6x/Phase-6x — Mukhopadhyay 2024.md` and the MVP
`MukhopadhyayCCZ.lean`.

## Verdict: GREEN-WITH-RECOMMENDED (no blocking findings)

The three files are kernel-pure, compile cleanly (zero diagnostics), mathematically sound, and
honestly scoped. The reviewer specifically hunted for — and did **not** find — a tautological
telescoping bound, a vacuous `toffoliCost_ge_measure` (empty-`sInf` degeneracy is discharged; the
nonemptiness obligation is proved), a minimality/optimality overclaim, a `channelRep` that mismatches
Eq. 27, a dishonest "DR correction," or any kernel impurity.

**Central correctness check (the DR Q2.3 contradiction).** The docstrings assert `T^of(U) ≥ sde₂(Û)`
*does* follow by telescoping Lemma 3.16 from a Clifford base, contradicting the DR's stated "no lower
bound follows" (dossier lines 88–90, 227). The reviewer independently confirmed the docstrings are
**correct** and the DR's Q2.3 conclusion is the error: the DR conflates the **descent-existence**
direction (Conjecture 4.8 — whether a sde₂-*decreasing* generator always exists; genuinely unproven)
with the **growth-bound** direction (each `CCZ` raises `sde₂` by at most 1, Cliffords leave it fixed —
exactly Fact 3.14 + Fact 3.9). The telescoping uses only the latter, so `sde₂(Û) ≤ #CCZ ≤ T^of(U)` is
valid. The "secondary sources can err — verify mechanisms directly" guardrail fired correctly. The
bound is shipped **conditional** (`μ = sde₂ ∘ channelRep` is never instantiated; the per-generator
bridges remain abstract hypotheses), and the docstrings disclose this — so it is not overclaimed.

## Kernel purity — confirmed

All headline theorems close over exactly `{propext, Classical.choice, Quot.sound}` (verified by the
principal via `lean_verify`; reviewer source-scan confirms). Zero `sorry` / `axiom` / `native_decide` /
`maxHeartbeats` / `synthInstance.maxHeartbeats` / `unsafe` / `opaque` in proof bodies (the only
`maxHeartbeats`/`axiom` string hits are the invariant-statement docstring lines). Clean
`lean_diagnostic_messages` on all three files. No private-repo identifiers. Invariants #10 and #15
respected.

## Advisories (RECOMMENDED, non-blocking) — substantively closed

- **R1 — the two "headline" theorems are parametric skeletons.** `toffoliCount_ge_measure` /
  `toffoliCost_ge_measure` are unconditional telescoping inductions; all substantive Toffoli content
  lives in the un-discharged `μ = sde₂ ∘ channelRep` instantiation + the `hC`/`hCCZ` bridge hypotheses.
  **Closed:** added an explicit **PARAMETRIC** tag to both theorem docstrings naming the deferred
  instantiation as the documented follow-on.
- **R2 — `μ ≡ 0` trivially satisfies `(h1, hC, hCCZ)`.** The abstract lemmas have a trivial satisfying
  instance; the non-vacuous value is realized only by the intended (un-shipped) witness. **Closed:**
  the R1 PARAMETRIC tag explicitly states the `μ ≡ 0` vacuous case and that the non-vacuous value is
  un-shipped.
- **R3 — `sde2` is over all of `ℚ`, not `ℤ[1/2]`.** Strictly more general (and the proofs are correct
  on all `ℚ`); the eventual `sde₂(channelRep …)` reading additionally needs channel-rep entries to be
  genuinely dyadic (Lemma 3.10). **Closed:** added a note to the `sde2` docstring flagging the
  `ℚ`-generality and the Lemma-3.10 dependency of the intended instantiation.

(Advisory-closure docstring edits build clean; docstring-only, no statement changes.)

## Per-theorem substantiveness (summary)

Every shipped theorem is substantive (not P2–P5 tautology): `channelRep_mul` (the homomorphism law,
multi-step trace-linearity — most substantive of L.A); `channelRep_mulVec_repr` (the conjugation-action
characterization); `isExactlyCliffordCCZ_channelRep_mem` (honest NECESSARY-only re-base, not a `⟺`);
`sde2_half_sum_le` (Fact 3.14 — the `+1` bound, tight, via `padicValRat.min_le_padicValRat_add`);
`toffoliCount_ge_measure` / `toffoliCost_ge_measure` (genuine telescoping, non-empty `sInf`). The
`toffoliCount` simp lemmas are appropriately routine. Full per-declaration assessment in the reviewer
transcript.

## Disposition

**GREEN.** Item L's full PUBLIC math layer is closed at the achievable scope (channel-rep
characterization + structural re-base; dyadic `sde₂` + Lemma 3.16 core; the `sde₂` Toffoli lower
bound). The per-generator channel-rep entry analyses (Lemma 3.10 / Theorem 3.8 / the Fact 3.9 converse)
and full MITM minimality (Conjecture 4.8) are documented optional follow-ons, not required for Exit.
Notably, the work correctly identified and corrected an error in its own source-of-truth DR dossier
(the Q2.3 "no lower bound follows" verdict) without overclaiming the result as discharged.
