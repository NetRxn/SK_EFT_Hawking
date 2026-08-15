---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T00:00:00Z
readiness_gates_version: 1
kind: substantiation-audit
prior_reviews:
  - papers/AutomatedReviews/2026-08-15-l2-stage10-redraft/L2.md
  - docs/SIXTEEN_CONVERGENCE_STATUS.md
counts_snapshot: 40769 decls in lean/lean_deps.json; apex_claims_not_vacuous 20/20 flagged, 15/15 undisclosed
---

# infra — findings from the sixteen-convergence re-pointing audit

## Summary

**1 REQUIRED, 1 RECOMMENDED.** The audit was commissioned to re-point the
sixteen-convergence citations from the enumeration theorems onto stronger ones.
**The re-pointing was not performed, because the premise does not hold**: the
theorems nominated as "strong" rest on a carrier that the project's own
canonical status doc already classifies as a posited `ℤ/16ℤ`. Citing them for
the bordism-group identification would have introduced an overclaim into a
manuscript that is currently correct. Detail in §0; the findings below are the
two remediable items that surfaced.

## 0. Why no citation was re-pointed (context, not a finding)

`SKEFTHawking.SymTFT.Omega4PinPlusBordism` is
`Quotient PinPlusBordism4Setoid`, where `PinPlusManifold4` is a one-field
structure `⟨signature : ℤ⟩` (`lean/SKEFTHawking/SymTFT/PinPlusManifold4.lean:108`)
and the setoid relation is `16 ∣ (M.signature - N.signature)`
(`.../PinPlusBordism4.lean:76`). `PinPlusStructure` is a field-less `Prop`
class (`PinPlusManifold4.lean:92`), and `pinPlusRP4 := ⟨1⟩`,
`pinPlusK3Lift := ⟨-16⟩` are hand-chosen integers. The carrier is therefore
`ℤ` and the quotient is congruence mod 16.

Consequently `Nonempty (Omega4PinPlusBordism ≃+ ZMod 16)` — the first conjunct
of `PinPlusDischarge.sixteen_convergence_finite_discharge_substrate` and of
`PinPlusSmithDerived.sixteen_convergence_via_sandwich` — is
`ZMod 16 ≃+ ZMod 16` under a physics name, and `addOrderOf [pinPlusRP4] = 16`
is `addOrderOf (1 : ZMod 16) = 16`. These are kernel-pure and unconditional,
and they are *not* substantive. This is not a new discovery: it is recorded at
`docs/SIXTEEN_CONVERGENCE_STATUS.md:129-131`, which states that
`Omega4PinPlusBordism` is "a posited `ℤ/16ℤ` (a one-field `signature:ℤ`
quotient with a vacuous Pin⁺ `Prop`-class), **not** the smooth bordism group".
`lean/SKEFTHawking/PinPlusDischarge.lean:165-184` (§6 RETIREMENT) demotes the
same theorems in the module that defines them.

`papers/D2/paper_draft.tex:1000-1008` currently says that connecting the
Rokhlin sixteen to the anomaly sixteen "would require the Smith homomorphism
and the computed identification `Ω₄^{Pin⁺} ≅ ℤ₁₆`, neither of which is in the
library," and `:1054-1063` cites the two enumeration theorems explicitly as
indices that "do not assert a common origin". **Both statements are accurate.**
Re-pointing D2 onto `sixteen_convergence_finite_discharge_substrate` would have
made D2 assert as computed exactly the identification it correctly disclaims.

The strongest genuinely-unconditional statement in the family is
`PinPlusTangentialData.dataBordism_quotient_abk_equiv_zmod16`
(`lean/SKEFTHawking/PinPlusTangentialData.lean:283`), whose carrier is a real
`Quot` of Mathlib `SingularManifold`s. Its own §5b docstring is candid that it
is a quotient by `ker(abkGrade)` and that `ker = ⊥` is unreachable there. It is
still not the computed `Ω₄^{Pin⁺} ≅ ℤ₁₆`, so it does not license the D2 claim
either. No citation change was warranted.

---

## 1. The Phase 5q.E roadmap contradicts its own named status companion on the load-bearing framing

**Severity:** REQUIRED
**Lane:** docs
**Where:** `docs/roadmaps/Phase5qE_SixteenConvergence_Roadmap.md:18`, `:149`;
`docs/SIXTEEN_CONVERGENCE_STATUS.md:11`, `:186`

The roadmap concludes, twice, that "the convergence is now a **conditional
genuine unification**, no longer a bare enumeration" (`:18`, `:149`).

The status doc — which the roadmap itself names as its status companion at
`:7` and `:163` — carries the opposite, and is the later document. Its
standing rule for all papers and talks is to describe the convergence as a
formal enumeration and "never as a 'formally verified unification'" (`:11`),
and its §3.6.2 (dated 2026-06-15, one day after the roadmap's last update)
states "**The four-16 convergence of §3 remains an enumeration** connected by
spin-bordism ... NOT a 'formally verified unification'" (`:186`).

This is not a stylistic divergence. "Conditional genuine unification" is
precisely the phrasing a drafting agent would lift to license the overclaim
that `SIXTEEN_CONVERGENCE_STATUS.md:11` exists to forbid, and the roadmap is
the document a wave-planning agent reads first.

The roadmap is additionally stale on substance: it stops at W6 (2026-06-14)
and contains **zero** mentions of Phase 5q.F, `pin4_abutment`, `adamsAbutment`,
`DataBordismGrp`, or the genuine-carrier route — all of which the status doc
records in §3.6, §3.6.1 and §3.6.2. Its brick table at `:49` still describes
the genuine bordism group as "a tracked Prop (`IsKirbyTaylorPinPlusBordism`)".

Note that the roadmap's W5 row (`:73`) is *not* itself wrong:
`CommonOrigin.sixteen_convergence_common_origin` does bind `∀ S : SmithInflow`,
and `PinPlusDischarge`'s "SmithInflow is gone" describes a different theorem
(`sixteen_convergence_finite_discharge`, which binds `pin4_abutment` instead).
Those two statements do not conflict. The staleness is the framing sentence and
the missing 5q.F/W4–W6 absorption, not the W5 row.

**Verify (executed at HEAD on this branch; currently fails):**

```
grep -n "conditional genuine unification" docs/roadmaps/Phase5qE_SixteenConvergence_Roadmap.md
grep -n "remains an enumeration" docs/SIXTEEN_CONVERGENCE_STATUS.md
grep -c "5q\.F\|pin4_abutment\|DataBordismGrp\|genuine_carrier\|adamsAbutment" \
  docs/roadmaps/Phase5qE_SixteenConvergence_Roadmap.md
```

Executed 2026-08-15: the first returns lines 18 and 149; the second returns
line 186; the third returns `0`. The defect is present. A check that both
documents exist, that their links resolve, or that the roadmap's theorem names
resolve in `lean_deps.json` passes while the contradiction stands — the defect
is a disagreement in prose between two documents, so the check must compare the
two documents' framing verdicts against each other, keyed on the status doc as
authority.

---

## 2. The bare `SKEFTHawking.sixteen_convergence` is a pure enumeration with no consumer

**Severity:** RECOMMENDED
**Lane:** substrate
**Where:** `lean/SKEFTHawking/Z16AnomalyComputation.lean:217`

```
theorem sixteen_convergence :
    (Fintype.card (Fin 16) = 16) ∧ (16 = 0) ∧ (2*(4*2) = 16) ∧ (8 ∣ 16)
```

Every conjunct is a closed numeral fact; the second is a tautology in
`ZMod 16`. Unlike `sixteen_convergence_full` and
`sixteen_convergence_unconditional`, which D2 declares as apexes and treats
honestly as indices, this one is cited by **no** paper, bundle metadata, test,
doc or roadmap — verified by grep across `papers/ docs/ scripts/ src/ tests/`.

It is not currently flagged by `apex_claims_not_vacuous`, because it is not a
declared apex; it costs nothing today. It is listed here because it is the
weakest statement carrying the `sixteen_convergence` name, and a future agent
searching that name may cite it precisely because it is the shortest. Either
delete it or rename it to carry `enumeration` in the name.

**Verify (executed at HEAD; currently fails):**

```
grep -rn "SKEFTHawking\.sixteen_convergence\b" papers docs scripts src tests \
  | grep -v "_full\|_unconditional\|_of_HM\|_common\|_derived\|_finite\|_adams\|_genuine\|_via\|_faithful"
```

Executed 2026-08-15: returns nothing, confirming zero consumers while the
declaration remains in the library. A check that counts theorems, or that
verifies each apex resolves, cannot see an unreferenced weak declaration.

---

## Not filed — already open elsewhere

`wang_sixteen_convergence`'s `claims` string overstating its content is
**already filed**, today, at
`papers/AutomatedReviews/2026-08-15-l2-stage10-redraft/L2.md:216-235`
(REQUIRED, lane substrate). It is an **L2** apex
(`papers/L2/bundle_metadata.json` `apex_theorems[1]`), not a D2 one, and that
finding already records that the L2 redraft no longer cites it while the apex
declaration remains. Not duplicated here.
