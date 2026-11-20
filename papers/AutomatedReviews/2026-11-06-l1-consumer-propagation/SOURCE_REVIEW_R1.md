# Independent applied consumer source review R1

Verdict: REQUIRED REPAIRS. Frozen candidate parent f86e4b37f99cb0d4e90ddad4f8bf0f99b50726d3, packet l1-consumer-source-review-20261106-r1.json. Canonical continuity check returned fresh=true, changed=[]. No repository, source, Git, ledger, notebook, native/controller/build/test mutation. Only this /tmp report was written. This is a scoped consumer source review, not complete D3/L1 gate acceptance or semantic closure.

## Required exact repairs

1. D3 paper_draft.tex 872–882 and adjacent transition1115: remaining physical derivation/branch language contradicts the repaired law. The opening still says “derives the propagation speed”, “datum admits the branch”, and “range naturalness allows”. Replace the opening with a statement that Volovik proposes an intermediate expectation-valued metric branch, this section assumes a spin-two interpretation and scalar law, and the cap constrains that law's free normalized response to a finite interval inside an adopted comparison interval. It does not establish existence/admission of the physical phase or derive the law. Replace “The vestigial branch having been confined” with “The assumed vestigial speed law having been conditionally constrained”. The opening also calls the metric a “fermion bilinear”; Eq19 in the primary is a quartet/four-fermion correlator of tetrad bilinears. Say “fermionic quartet correlator” or “correlator of fermion bilinears”. This is a retained residual, not an error in the newly repaired interval algebra.

2. D3917–938: physical equivalence-principle assertions outrun their actual carriers. VestigialGravity.has_equivalence_principle is a hand-declared Bool table (75–79); sees_gravity_as_boson/fermion are Bool tables (310ff); ep_only_in_full_tetrad113–118 is a match on that finite table; wep_distinguishes_vestigial_from_full363–368 compares those booleans. They do not derive matter actions, trajectories or universal physical EP restoration in every full-tetrad realization. Volovik2024 III Eq21–22 explicitly allows a connected metric contribution in ECSK/full tetrad, and says EP “can be violated”; it does not guarantee its disappearance merely because the tetrad becomes nonzero. Preserve the accepted finite classifier results, describe them as classifications under their assigned coupling flags, and distinguish Volovik's possible physical differential coupling from a constructed observable. State that physical full-tetrad WEP restoration requires control/absence of the connected contribution and actual matter/source correspondence. Avoid asserting trajectory differences as an unconditional computed observation or EP “there and nowhere else”. No theorem/proof absence claim is needed.

3. D3994–1003 and1104–1107: 26 Mpc is used as if the measured luminosity distance, and the arrival delay as sufficient for the cap. Abbott L13 §4.1 uses26 Mpc as the lower90% credible-distance bound, assumes simultaneous emission for the positive side and gamma emission10s after GW for the negative side, and explicitly discusses alternative histories broadening the velocity interval by two orders. Replace with “using the conservative lower90% distance bound26 Mpc and the collaboration's source-emission assumptions” and disclose that alternative histories can weaken the bound. In the lattice paragraph say “rests on the adopted speed law and the conditional propagation bound” instead of “propagation-speed datum alone”. This carries current L1's conditional premises through the complete D3 context.

4. Paper25 line238: replace “frame-independent form” with “reference-speed-independent form” (or “invariance under rescaling the reference c”). c_GW_relative_deviation_eq and natural_endpoints_violate_ligo_for_every_c quantify real scalar c≠0; they do not implement a Lorentz frame change. The actual c≠0 domain is correctly repaired and must be retained.

5. Paper25 bibliography498–499: arXiv1109.0091 is “Towards lattice-regularized Quantum Gravity”, as the held Diakonov PDF title page confirms; replace the incorrect “Towards a fermionic cosmological term”. At462–473, replace the imported/duplicated broad multi-messenger collaboration list with the actual L13 attribution “LIGO Scientific Collaboration and Virgo Collaboration, Fermi Gamma-ray Burst Monitor, and INTEGRAL” (or a correct concise equivalent). The held L13 title page provides the exact list; IceCube and the long optical/radio collaboration list are not the front-matter attribution of this article. Preserve L13/arXiv1710.05834 and the correct §4.1 Eq1 locator.

## Accepted content at this bounded source scope

The actual revised D3 speed-law paragraphs, adopted endpoint interpretation, finite-compatible-interval conclusion and future-event scope are correct in their own paragraphs. All three changed metadata strings correctly distinguish scalar classification/luminal anchor from a physical mode or exclusion. The ancillary D3 QEC wording-only diff at1363–1367 preserves its previous positivity-of-logarithm claim and does not expand it.

The revised Paper25 abstract/setup accurately distinguishes Volovik2024's metric quartet from Volovik2026's de Sitter two-fluid sound. The latter's complete abstract and §§I–V show s2=c in Eq9 and explicitly leave spin/helicity interpretation open (including spin0/helicity0 possibilities); no spin-two susceptibility-dependent law follows from it. The repaired conditional RPA form correctly leaves bare susceptibility/coupling unevaluated and distinguishes dimensionless normalized response from a dimensionful bubble. Vergeles does not supply the asserted numerical response interval in the sections carrying its result; its fixed-degree-of-freedom Minkowski/gauge premises remain important to any physical use.

Read actual GravitationalWaves definitions/statements/proofs, not only docstrings: c_GW=c*sqrt(chi), deviation=sqrt(chi)-1; nonnegative-domain finite-interval theorem; all endpoint and width/nesting/nonempty witnesses; c≠0 bridge; actual three-clause Prop and four counterexamples; actual product definition and correction-only biconditional/placeholder theorem. The finite interval, center1+tau², half-width2tau, width4tau, nonempty intersection, endpoint factors, prior-dependence and nonexclusive counterexamples remain accepted. P2 implies P3 at the fixed tolerance and the compatible interval supplies positivity. No new kernel-purity or absence claim was made.

Paper25's revised dispersion section is mathematically correct: unmatched gamma=GammaH/cGW² is disclosed, physical inverse-frequency units and frequency convention are owed, real100 is not100Hz, placeholder1e-30 is neither measured nor derived. With |d_disp|≤B the reverse-triangle exclusion |d0|>tau+B is correct; the signed near-boundary witness restores exactly s*tau. It makes no physical existence claim for that correction. SecondOrderSK.GammaH's actual definition is (gamma1+gamma2)*(kappa/cs)^2; its acoustic identification is distinct from metric response. Companion Planck matching alpha*=Nf/(12pi) is conditional algebra; the revised Weyl/Dirac species and coefficient caveats agree with canonical L1. The original physical regulator, species and coefficient normalizations remain owed.

No source regression found in the accepted caption interval/anchor/prior language. Figures' actual rendering is not certified by this source review. Numeric table inputs and accepted mathematical claims were preserved, not re-gated or closed here.

## Read scopes and hashes

Full Paper25 TeX (including title/abstract, all sections/caption and bibliography); complete D3 vestigial section from opening869 through lattice1107, preceding850–868 and following1112–1125, affected QEC1355–1380, complete affected Scope subsections2400–2565; every actual three-file source/metadata diff; D3 metadata; original SOURCE_ASSESSMENT. Canonical L1 TeX read across opening, relevant complete sections and appendix/captions/bibliography. GravitationalWaves.lean1–678 complete; VestigialSusceptibility1–215 and270–383 including entire actual RPA section; SecondOrderSK395–415 definition/adjacent statements; VestigialGravity64–118 and310–368 actual classifier definitions/statements. Primary Volovik2026 extracted body1–245 complete; Volovik2024 III and V plus references (the initial full-file request was output-truncated before early unrelated superfluid material); Vergeles1–130 and350–710 covering introduction and the complete relevant evolution/unitarity/discussion/conclusion result spans; Abbott title page and complete §4.1 with adjacent §4.2; Diakonov title page/abstract. Process authorities/roles, current roadmap opening and designated notebook current tail were read; some large bulk output was truncated, so no claim to full historical-notebook reading is made.

SHA256 frozen source:
- D3 TeX a8887aba59cf2ea16ad8a0505ef8544b1420d6a4ac81190639f1a47969a0027c
- D3 metadata69771c9a28d4ad46cc90abf7e92c56a8d09c2010ffdb2b4770aad99688b17c17
- Paper25 TeX e70adab5df808dc5e8bd7247b245381ec7b2b3452fe058ee1678d2fb6e24de0b
- L1 TeX29f926fef642a352ffb24b2d1fb0d851c1fb58d5c2a50ba7ffaf3083e3c1c5a2
- GravitationalWaves eab4cd660adb486d6b057e8036d2d952bdea55e7ab7686e568cb79ae6a02285d
- VestigialSusceptibility cf5a4584ad51f44a232c7da2d4fe9300ea14c322a416b2843e7ef3c2032bf721
- SecondOrderSK393179be9e2a27660e5c0e5ad53ffe9089633f5f397e85c35bd7ae55048f8bb4
- VestigialGravity4c057448a02f8dc0a55f6048bd5b9521cc08c66ee8aa6c3fc7359610cf240f47

Held primary PDF SHA256:
- Abbott Phase-6a bf06bd2ae6a23cf7f7092307677c2b681ce02abab3b5bbe37bbce76a8960140a
- Diakonov Phase-5d132d63150a678ef17bfbbc04978a8cab9c9801f03556982a6aa67c11d3fbc4da
- Volovik2026 Phase-1-and-Background392649cf58b98b03957e11f95beb01b9e204b398219e6ffde067c181d26a5c17
- Volovik2024 Phase-6a e882f606f37d56c6111ea9ab3fc16ecba4d41001186ade32d9ccb7221224c2ed
- Vergeles Phase-5d daa334f1ad59ace58aba5afe68ec5d4909e717e626ba6fa7c0d7237c8df43eac

Extracted bodies supplied by ROOT:
- /tmp/volovik-second-sound-root.txt975ba208c5bfa0b01b9859b23d9632c4861347b87d39ca879508572238617d18
- /tmp/2312.09435v2-root-intake.txt66ec0262a7ead3dea16f6840a1bf6a85eac6776a05bf4f346b6a8952b1041fcc
- /tmp/2506.00036v2-root-intake.txt97138211cd522b7de771334be2250fd5f887eac6790d0f9eae36f583828ddedb

## Execution record

All commands were read-only, except the final heredoc writing this permitted report. No evaluations, tests, builds, proof/native tools, Git writes, controller calls or external web access were run. The following records every exec shell command group (semicolon-separated independent reads in the original calls); cwd was assigned checkout except workspace-orientation commands and absolute-primary-source reads. Abbreviations P=assigned checkout, S=primary SK_EFT_Hawking, W=workspace, M=Lit-Search. Paths identify exact originals above.

1. python3 scripts/continuity_check.py <S/.codex/continuity/l1-consumer-source-review-20261106-r1.json> from P: exit2 (wrong nonexistent adapter spelling); no state changed.
2. cat <same packet>: exit0.
3. rg -n 'continuity.*check|check.*continuity' S/docs/dev-loops/CODEX_CONTINUITY.md S/AGENTS.md; cat W/CLAUDE.md; cat /Users/johnroehm/.codex/skills/../plugins/cache/openai-curated-remote/superpowers/7.0.1/skills/using-superpowers/SKILL.md. The skill explicitly exempts dispatched subagents.
4. python3 scripts/codex_continuity.py check <packet> from P: exit0, fresh=true.
5. cat AGENTS.md CLAUDE.md; cat docs/dev-loops/CODEX_CONTINUITY.md; cat .claude/agents/claims-reviewer.md .claude/agents/adversarial-reviewer.md: final cat exit1 because role paths live under plugin, subsequently resolved.
6. cat docs/WAVE_EXECUTION_PIPELINE.md; cat <S/.codex/continuity/publication-remediation-notebook.md>; cat papers/AutomatedReviews/2026-11-06-l1-consumer-propagation/SOURCE_ASSESSMENT.md; rg --files .claude | rg '(claims-reviewer|adversarial-reviewer)'. Large combined output truncated.
7. git diff -- papers/D3/paper_draft.tex papers/D3/bundle_metadata.json papers/paper25_gravitational_waves/paper_draft.tex; cat .claude/plugins/skeft-qa/agents/claims-reviewer.md .claude/plugins/skeft-qa/agents/adversarial-reviewer.md; cat papers/paper25_gravitational_waves/paper_draft.tex. Large combined output truncated; later reads recover source text.
8. cat <same two role paths>; sed -n '900,1100p' papers/D3/paper_draft.tex; cat papers/D3/bundle_metadata.json; rg -n 'second.sound|RPA|dispersion|matching locus|Weyl|species|chi_0|chi.*vest|Planck' papers/L1/paper_draft.tex. Combined output truncated.
9. sed -n '900,1090p' papers/D3/paper_draft.tex; sed -n '2400,2560p' papers/D3/paper_draft.tex; cat papers/L1/paper_draft.tex. Later small reads recover affected sections.
10. wc -l <three supplied extracted bodies> lean/SKEFTHawking/GravitationalWaves.lean lean/SKEFTHawking/VestigialSusceptibility.lean; cat <Volovik2026 body>; cat <Volovik2024 body>. Output truncated in early unrelated Volovik2024 material, relevant III/V present.
11. sed -n '1,260p' lean/SKEFTHawking/GravitationalWaves.lean.
12. sed -n '260,678p' <GW Lean>; sed -n '1,215p' <VestigialSusceptibility Lean>; rg -n -A14 -B6 'def GammaH' lean/SKEFTHawking/SecondOrderSK.lean.
13. sed -n '270,383p' <VestigialSusceptibility Lean>; sed -n '1080,1125p' papers/D3/paper_draft.tex; sed -n '1,150p' papers/L1/paper_draft.tex; sed -n '1,130p' <Vergeles extracted body>; rg -n '^ *[IVX]+\.|unitar|positiv|suscept|conclu' <Vergeles extracted body>.
14. rg --files M | rg '(Abbott2017|1710.05834|Diakonov2011|1109.0091|Volovik2026SecondSound|Volovik2024Vestigial|Vergeles2025)'; sed -n '350,710p' <Vergeles body>. Combined output truncated a small mid-unitarity segment; the complete actual premises/conclusion and §V discussed physical limits were visible.
15. pdftotext -layout <Abbott PDF> - | sed -n '1,20p;560,690p'; pdftotext -layout <Diakonov PDF> - | head -35; sed -n '850,905p' papers/D3/paper_draft.tex; git diff --numstat; shasum -a256 <D3 TeX/metadata, Paper25 TeX, L1 TeX, GW/VestigialSusceptibility/SecondOrderSK Lean, three extracted bodies>. Hash syntax actually used '-a 256'.
16. sed -n '1,220p' Paper25 TeX; rg -n -A20 -B12 'wep_distinguishes|ep_only_in_full|def.*[Ee]quivalence|def.*[Cc]oupling|vestigial_has_metric' <VestigialGravity Lean>; pdftotext -layout <Abbott PDF> - | rg -n -A50 -B12 '26 Mpc|4.1. Speed|10 s|10 seconds'. Abbott material recovered in command18.
17. sed -n '220,440p' Paper25 TeX; sed -n '440,570p' Paper25 TeX; sed -n '310,350p' <VestigialGravity Lean>; pdftotext -layout <Abbott PDF> - | sed -n '302,370p'. Overlap at440 repeats one displayed line only; source does not contain a duplicate conclusion sentence.
18. rg -n 'L1|B3|consumer|physical|GW170817' <S/docs/roadmaps/Phase6a_Roadmap.md> | tail -45; cat docs/adrs/ADR-008-shared-lean-slot-control-plane.md docs/adrs/ADR-017-codex-continuity.md; sed -n '1,160p' <adversarial-reviewer role>; nl -ba D3 TeX | sed -n '866,885p;914,940p;990,1007p;1106,1116p'; nl -ba Paper25 TeX | sed -n '236,258p;460,510p'; shasum -a 256 <five held primary PDFs listed above> <VestigialGravity Lean>. Combined authority output truncated; quoted source anchors/hashes visible.
19. sed -n '2520,2565p' D3 TeX; sed -n '1355,1380p' D3 TeX; sed -n '1,27p' <primary roadmap>; git diff -- Paper25 TeX | sed -n '160,380p'.
20. cat > /tmp/l1-consumer-source-review-r1.md <<'EOF' (this report).

ROOT must reissue a reconciled packet and obtain scoped R2 applied-source review after repair. Original full B3 normalization/domain/window, positive physical state, constrained tensor/matter construction and matched causal transport acceptance remain OPEN; this report preserves their original requirements and all previously accepted mathematical results.

## Final R1 abstract propagation check

D3 abstract55–58 independently read after ROOT's pointer: “GW170817 confines the substrate's own vestigial phase to a susceptibility interval more than14 orders of magnitude narrower than its natural range.” Required repair: describe a conditional constraint on the assumed scalar speed law within the adopted comparison range. This statement must not admit or confine a physically constructed substrate phase. The abstract otherwise remains outside any new general scientific acceptance.

Additional commands actually run after initial report writing: sed -n '45,65p' papers/D3/paper_draft.tex; shasum -a 256 /tmp/l1-consumer-source-review-r1.md (pre-addendum report hash only); cat >> /tmp/l1-consumer-source-review-r1.md <<'EOF' (this final addendum). R1 report is frozen after this addendum.
