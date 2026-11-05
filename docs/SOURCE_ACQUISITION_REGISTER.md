# Source Acquisition Register

**Auto-generated** by `scripts/source_acquisition_register.py`. Do not hand-edit —
curated verdicts belong in `docs/source_acquisition_overlay.json`, which survives
regeneration.

Sources cited in the **21 submission bundles** that we do not hold in full text.
Legacy `paperNN` drafts are excluded: they are not the submission surface.

## Priority

| | meaning | budget |
|---|---|---|
| **P0** | load-bearing — a claim, parameter or formula depends on it | buy only if `route` is not free |
| **P1** | cited by 2+ bundles, not load-bearing | do not buy; verify the citation earns its place |
| **P2** | single bundle, not load-bearing | do not buy; likely droppable |
| **—** | our own companion papers | never a budget item |

⚠️ **The load-bearing signal is a FLOOR, not a census.** It fires on sources that
supply a registered parameter value or are named in `formulas.py`. A source
supplying a *closed form*, theorem or convention is invisible to it —
`IrwinHilton2005` is the measured example. Curate those in the overlay; a P1/P2
row is 'not detected as load-bearing', never 'confirmed decorative'.

⚠️ **An unchecked paywall is a guess, not a cost.** `route: paywalled` is honest
only once the free routes named in `route_note` have actually been tried.

## Spend list — P0, not free

_None._

**Candidate spend: 0 source(s).**

## P0 — load-bearing

| source | held | bundles | route | why it is load-bearing |
|---|---|---|---|---|
| `Sen2013` | none | D3, F | open | Supplies BH.LOG_CORRECTION_SEN_4D_SCHWARZSCHILD; cited by both D3 and F. |
| `BB84` | none | D9 | open | Referenced by formulas.py. |
| `IrwinHilton2005` | abstract | D12 | repository | Attributed source of D12's diffuse-conduction closed form for the thermal-link gradient factor gamma (F_link). D12:474-475 currently discloses in reader-facing prose that we hold it only as a resolved DOI record -- a non-starter for submission. Either the attribution is verified or it must be re-sourced. |
| `Mather1982` | abstract | D12 | repository | Supplies MATHER_1982_GRADIENT_REDUCTION (0.30). The convention -- whether the quoted 30% is a PSD or an amplitude reduction -- is UNRESOLVED because the body has never been read, and D12:498 discloses that in prose. The body settles it; the abstract cannot. |
| `PDG2024` | abstract | D3 | open | Supplies EW.M_H_GEV and EW.M_TOP_GEV. |
| `Rokhlin1952` | none | L2 | repository | Has a bibitem in D2 but NO cached text. D2's section 5.5 quotes the statement of Rokhlin's theorem (16 | sigma for closed smooth spin 4-manifolds) from its standard formulation, unverified against the original. The theorem is universally standard, so the risk is attribution fidelity rather than correctness. |

## P1 — cross-cutting, not detected as load-bearing (30)

`Sakharov1968`, `Volovik2024Vestigial`, `ABP1967`, `Adams1974`, `Adler1980`, `AndersonBFP2013`, `BardeenCarterHawking1973`, `CorleyJacobson1996`, `Coutant2014`, `DawsonNielsen2006`, `FreedmanLarsenWang2002`, `Hawking1971`, `Hawking1972`, `Hawking1975`, `Hietala2020VOQC`, `Israel1986`, `KSS2005`, `KitaevShenVyalyi2002`, `Lewis2021VerifQC`, `Majumdar2025`, `NayakSimonSternFreedmanDasSarma2008`, `PastawskiYoshidaHarlowPreskill2015`, `PretkoRadzihovsky2018`, `ReshetikhinTuraev1991`, `Stepanov2019`, `Weinberg1989`, `Wen2003`, `Will2014`, `Witten1989`, `coqq2022`

## P2 — single bundle, not detected as load-bearing (122)

`ADM1962`, `AaronsonGottesman2004`, `AharonovArad2011`, `Alberti1983`, `AnantramDatta1996`, `ArnoldMcLerran1987`, `BakerBellini2017`, `Balbinot2005`, `Berry1984`, `Berry1989`, `Bhatia1997`, `Bilic1999`, `Blanter2000`, `BlochSiegert1940`, `BoldoLaxMilgram2016`, `Brylinski2002`, `Buballa2005`, `CallenWelton1951`, `Carter1971`, `Caves1982`, `Choi1975`, `ChristensenDuff1978`, `CompanionCompilation`, `CompanionFaultTolerance`, `CompanionStochastic`, `CoutantParentani2012`, `CreminelliVernizzi2017`, `Davies1990`, `Degenne2025Kernels`, `DemboZeitouni1998LDT`, `DolanGrady1982`, `EchenimMhalla2021`, `Eddington1919`, `EzquiagaZumalacarregui2017`, `FordFulkerson1956`, `FouresBruhat1952`, `FriedrichRendall2000`, `FukuiHatsugaiSuzuki2005`, `Gabor1946`, `GellMannOakesRenner1968`, `GrossJackiw1972`, `Haldane1988`, `HashinShtrikman1962`, `HashinShtrikman1963`, `HawkingPenrose1970`, `Heading1962`, `Helstrom1976`, `InonuWigner1953`, `Irwin1995`, `Israel1967`, `Jacquet2022`, `KMM2013`, `Kailath1967`, `KaratzasShreve1991BMSC`, `KehleUnger2024`, `Kitaev1997`, `KlinkhamerManton1984`, `KobayashiNomizu1963`, `LeCam1986`, `Lean4`, `LeanLJ2025`, `LiPaulson2018`, `LjungstromMortberg2024`, `LuccioliDegenne2024`, `Maldacena1997`, `MaxwellGarnett1904`, `MeiburgLessaSoldati2025`, `Milton2002`, `Mukhopadhyay2024`, `Nielsen1981a`, `Nielsen1981b`, `Niemeier1973`, `Onsager1944`, `Penrose1965`, `RashidHasan2017`, `ReadRezayi1999`, `Reuss1929`, `RevuzYor1999CMSM`, `RobertsonParentani2015`, `Robinson1975`, `RoehmD4Topological`, `RoehmD6FaultTolerant`, `RoehmD8Compilation`, `RoehmD9Certification`, `Romatschke2010`, `RossSelinger2016`, `SaksteinJain2017`, `Son2002`, `Stelle1977`, `TKNN1982`, `Uhlmann1976`, `UnruhCBO2025`, `Voigt1889`, `Volovik2022Counting`, `Volovik2024VacuumDecay`, `Volovik2026SecondSound`, `Watrous2018`, `WernerState1989`, `Witten1982`, `Zaremba1999`, `bakalov2001`, `buttiker1986`, `datta1995`, `denHollander2000LDPs`, `diFrancesco1997`, `efron1982`, `egno2015`, `gksl1976`, `hohenbergKohn1964`, `isabelleCBO`, `kassel1995`, `kato1995`, `landauer1957`, `leanQI2025`, `levy1979`, `lieb1983`, `lindblad1976`, `mathlib4_2020`, `meirWingreen1992`, `reedSimon2`, `survey2021`, `turaev2010`

## Our own companion papers (16) — not purchasable

`Roehm2026D2`, `Roehm2026D3`, `Roehm2026D4`, `Roehm2026E1`, `Roehm2026E2`, `Roehm2026I1`, `Roehm2026Modular`, `Roehm2026Strategy`, `Roehm2026D1`, `Roehm2026D5`, `Roehm2026GrapheneDeep`, `Roehm2026I2`, `Roehm2026L2`, `Roehm2026LinearizedEFE`, `Roehm2026TQC`, `Roehm2026Wave16`

---

*174 bundle-cited sources not held in full text: 6 P0, 30 P1, 122 P2, 16 internal.*
