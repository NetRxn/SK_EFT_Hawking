# H geometric-leg design pass (lead, 2026-07-20) — the three-lane decomposition

**Status: BINDING for completeness-lane dispatches.** Target: `H : ∀ p (brown-0, rank>0),
IsotropicSurgeryTrace prov p` (the §4-sharpened terminal form, `KTCompletenessProvider.lean:268`),
i.e. per arbitrary non-spin brown-0 representative: `{p', hrank, b, hT2, hBor}`. The algebraic head
{x, hx0, hxq} is DONE (absorbed, `kernelReducesToSpin_of_isotropicSurgeryTraceSupply :312`).

## The structural insight (code-verified 2026-07-20)

**The KT surgery does NOT change the 4-manifold — `p'.1.M = p.1.M`.** KT §5 surgery compresses the
characteristic SURFACE Σ ⊂ M along an embedded disk (genus/rank drop by 2); the trace bordism is
`W = M × I` with the membrane `Σ×[0,½] ∪ 2-handle ∪ Σ'×[½,1]` (`AmbientSurgeryDatum` docstring,
`PinPlusKTSurgeryTrace.lean:100`). So the generic supply splits cleanly: a SURFACE-topology core
(new) + a membrane/weld packaging (generalize the capstone) + a W-admissibility transfer (banked
provider atoms + MV across the handle).

Field classification of `CapstoneAmbientSupply` (`PinPlusTraceCapstoneInhabit.lean:276`, the 33-field
row): {x,hx0,hxq} = done · {p',hrank,hsT2} = Lane H-1 output (same M, compressed Σ') ·
{S,hS,φ,hφ,hφinj,cd,hseam,d + real/htaylor/hlag/HAQ/HAW/weld/hQ/hW/glueσ/glueτ/chartQ} = Lane H-2 ·
{hasClass, findimAbs/Rel 14/23, nondeg14/23, dimeq14/23, hwu} = Lane H-3.

## Lane H-1 — SUPERSEDED BY THE VETTED CODEX DOSSIER (2026-07-20; `scratchpad/codex_H1_scoping.md`, load-bearing claims lead-vetted against the KT extraction + BrownSurgeryReduction)

**Three corrections to the section below (which is retained as the original record):**
1. **Source attribution WRONG:** KT §5 **Thm 5.1 is the 3-dimensional Ω₃ computation**; the ℤ/16 target
   is **Thm 5.2**, proved via characteristic submanifolds + a bordism exact sequence (vetted against
   `Lit-Search/Phase-5qH/KT_LMS_Section5_completeness_proof_extracted.md:16-23`). The actual circle-surgery
   mechanism: an ALREADY-EMBEDDED framed circle with q = 0 has the bounding Spin structure ⟹ attach a
   disk bundle to M×I ⟹ a BORDISM to a possibly-DIFFERENT end M′. **No same-M embedded disk is produced
   or needed** — `AmbientSurgeryDatum`'s b : Bordism p'.1 p.1 is already end-agnostic, and the reduction
   only needs [p′] = [p] + rank drop. The "same-M compression" framing below overstates the source.
2. **The transvection route is DEAD** (vetted: `SurgeryReduction` fields z/pairing/κ/R/e/agree — `e`
   identifies the reduced space with the PAIR COMPLEMENT; no automorphism of the original space, no
   normalization of x, no q-isometry realization). Do not invest absent a deliberately-added
   q-isometry + mapping-class-realization + ambient-extension chain.
3. **Interface looseness (fix before H-2 binds):** `IsotropicSurgeryTrace` DROPS x — its assembly can
   pair an arbitrary algebraic x with an unrelated geometric trace (formally sound for consumption,
   but the algebra–geometry tether must be explicit for H-2's construction). Fix = the dossier's
   `IsotropicFramedAttachingDatum` (embedded framed circle + fund_generator + realizes_x tether +
   attaching + pin_extends) and the exact-`SurgeryReduction`-identification output form.

**THE ADOPTED H-1 SUMMIT (source-faithful):**
`BrownZeroHasIsotropicFramedAttachment : ∀ p, brown = 0 → 0 < n → ∃ x ≠ 0, q x = 0 ∧
Nonempty (IsotropicFramedAttachingDatum p x)` — ∃ per REPRESENTATIVE (the induction needs one x, not
all). The genuine geometric summit stack behind it (per the dossier + the in-tree honest record in
`CharSurfaceRealization.lean`): embedded-circle realization of a surface H₁ class · band-sum closure ·
framed tubular data · Pin-extension via the Taylor detection (currently a statement freeze in
`CharSurfaceTrace.lean:67`). The same-M `CompressionDiskDatum` variant requires NEW hypotheses
(null-homotopy in M + 4-dim disk-embedding control) — optional, NOT the default summit.

### (original section below, retained as the record — read with the corrections above)
## Lane H-1 — the compression disk (THE summit core; genuinely new)

Given `x ≠ 0` isotropic (`q x = 0`): represent `x` by an EMBEDDED circle `c ⊂ Σ`, then produce the
compressing disk `D ⊂ M` (∂D = c, interior pushed off Σ, correctly framed) — "embedded-surgery-disk
existence, KT §5 Thm 5.1" (the module's own named geometric input). Output: `Σ' ⊂ M` with the
compatible enhancement `q'` at rank `n−2` ⟹ `p'`.

**⚠ H is ∀-quantified over ALL representatives — per-instance discharge CANNOT close it.** The disk
existence must be proved GENERICALLY from the carrier's realized-membrane data, or the geometric
content isolated as ONE sharply-stated sub-Prop whose generic proof is the summit. Two sub-questions
to settle BEFORE any H-1 dispatch (lead deep-read owed):
1. What exactly does the KT §5 Thm 5.1 proof use for the disk? (Re-read the KT primary +
   `Lit-Search/Phase-5qH/` KT §5 material DIRECTLY — depth-read rule applies. If the mechanism is
   "characteristic-surface + Pin⁺ structure forces the framing", the carrier's pin data may carry it;
   if it needs immersed-curve surgery theory, scope honestly.)
2. What does the post-round-7 carrier (realized membranes, `GeoRealizationTied`) provide toward
   embedded-circle representation of a mod-2 H₁ class on Σ? (Surface topology — embedded
   representatives of primitive H₁ classes — is NOT in Mathlib; the carrier's Σ is however
   genus-g STANDARD, which may permit a basis-circle route: represent the enhancement BASIS by
   standard embedded circles, then reduce arbitrary isotropic x to a basis element by the
   symplectic-transvection normalization ALREADY banked in the algebra layer — check
   `exists_finReduction_of_brown_zero`'s normal form for exactly this.)

**Design recommendation:** pursue the basis-circle + transvection-normalization route first — it
converts "represent an arbitrary class" into "represent ONE standard basis circle on a standard
surface", which the carrier's standard-Σ data plausibly supplies. If it survives a scoping pass,
H-1 becomes bounded; if not, H-1 is the phase's true remaining summit and gets the Fable treatment.

## Lane H-2 — membrane/weld packaging parameterized by the disk (generalize #150–#178)

Mechanical-in-shape: re-run the capstone's `ktHandleAttachment`/`SeamCollarDatum`/`SurgeredEndDatum`/
`TraceMembraneLeaves` construction with the concrete S²-instance data replaced by the Lane-H-1 disk
data. The capstone modules were largely built GENERIC in `(p'.1, p.1, S, φ, cd, d)` (the supply
structure's own field types prove it — they elaborate at arbitrary `p`); the instance-specific parts
were the D⁵ chain/cycle witnesses (#163, #166, #191). Deliverable: `CapstoneAmbientSupply` inhabited
from `(disk data) × (Lane H-3 outputs)`. Dispatch-ready AFTER H-1's interface is frozen (the disk
datum's exact fields), not before — freezing the interface too early re-runs the hcompat mistake.

## Lane H-3 — W-admissibility transfer across the handle
### ⚠ PREMISE CORRECTED (2026-07-20 risk-1 audit, wt3 — the section below is superseded where it conflicts)

The provider's cylinder atoms (`WAdmPinned (reflCylinder s)`: full P14/P23 `LefschetzWuDatum` numerics)
are the right SHAPE on the WRONG SPACE — a 2-handle changes H₂/H₃, so W's duality numerics genuinely
differ from the cylinder's, and the W-side finiteness is already better-banked via
`CapstoneCohomologyMVDatum` + `PinPlusTraceCapstoneMVPieces §1` (all-degree piece finiteness). **The
W-side obligation is already reduced to CARRIER-GEOMETRIC MV residuals the cylinder atoms do not
feed.** Landed from the audit wave (`KTCompletenessTransfer.lean`, #print-pure):
`finiteDimensional_homology_sub_two_ends` (reusable two-closed-ends topology core) +
`capstone_boundary_hBd` (the MV datum's `hBd` for ARBITRARY attaching data from `SurgeredEndDatum`)
— `findimRel14/23`'s boundary input is OFF the list.

**H-3's true remaining increments (next dispatches, in order):**
1. The MV collar-thickened cover `A/B/hcov` + piece homeos `eA/eB/eAB` — Mathlib-absent collar
   thickening (`hcov` needs INTERIORS to cover; `HandleAttachment` banks only the closed-range
   union). Marked "deferred to Fable by #181" in MVPieces — **Fable-tier**.
2. The on-W two-sided Poincaré–Lefschetz `nondeg14/23` (+ flips) — deep.
3. `hwf14/hwf23` Steenrod–Kronecker vanishings + spin-cert transport across the cover glue — deep.
4. `hasClass` — BLOCKED on the settled fork `seam-transfer-open-support-uninhabitable` (#210,
   "dead AS SHIPPED"); the repair = the collar-pair split + `hasClass_ofTransferCorrector`
   (= the gate-pending task #212 COLLAR-PAIR REPAIR). Do not re-attempt the dead cSeam shape.

### (original section, superseded as noted)

The numerics/hasClass/hwu fields live on `W = capstoneB ≃ M×I ∪ D⁵-handle`. The provider
`CharPairWProviderPerOp` ALREADY supplies `WAdmPinned` for the plain cylinder `M×I` (reflCylinder —
that is its defining field). The handle is contractible and attached along a collar region ⟹ the
cylinder atoms should TRANSFER across the attachment by the banked MV/excision machinery
(the subdivision-to-cover engine #189, the excision bridge #141, the relative clopen-split #134,
the seam-split #194 `hasClass_ofTransfer`). Deliverable: generic transfer lemmas
`(provider cylinder atoms at p) → (the 11 W-admissibility fields at capstoneB p'.1 p.1 …)`,
quantified over the attachment data. **This is the next completeness-lane worker dispatch** — no
H-1 dependency (it consumes the attachment abstractly), high reuse, all-banked substrate.

## Sequencing

H-3 (worker, now) → H-1 scoping (lead deep-read: KT §5 Thm 5.1 mechanism + the transvection route;
then freeze the disk-datum interface) → H-2 (worker, after the interface freeze) → assemble
`IsotropicSurgeryTrace` supply → `kernelReducesToSpin_of_isotropicSurgeryTraceSupply` fires → H DONE.

Risks: (1) finite-dimensionality of H*(M;ℤ/2) for the ARBITRARY closed carrier M behind the cylinder
atoms — verify the provider's reflCylinder WAdm actually carries the finiteness (it should, it is
`WAdmPinned`); if it does not, that is a provider-strengthening brick, not an H-3 blocker per se.
(2) The transfer's boundary bookkeeping: W's boundary = M ⊔ M (cylinder) vs M ⊔ M with the membrane
seam — the #198 hvOut narrowing + closed-S collar bridge are the precedents.
