# Primary-Sources Cache — Backfill Report

External bibkeys: 211
Already cached (any tier): 4 (1.9%)
Phase-6a legacy aliases needing migration: 4

## Per-phase tier distribution

| Phase | Total | Cached | arxiv-pdf | arxiv-tex | abstract | crossref-json | Needs fetch | Has arXiv ID | Has DOI |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Phase-1-and-Background | 20 | 0 | 0 | 0 | 0 | 0 | 20 | 9 | 18 |
| Phase-3 | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 1 |
| Phase-5d | 5 | 0 | 0 | 0 | 0 | 0 | 5 | 4 | 3 |
| Phase-5e | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 0 |
| Phase-5q | 6 | 0 | 0 | 0 | 0 | 0 | 6 | 4 | 5 |
| Phase-5w | 15 | 0 | 0 | 0 | 0 | 0 | 15 | 3 | 13 |
| Phase-5x | 29 | 0 | 0 | 0 | 0 | 0 | 29 | 23 | 20 |
| Phase-5z | 32 | 0 | 0 | 0 | 0 | 0 | 32 | 24 | 30 |
| Phase-6a | 54 | 0 | 0 | 0 | 0 | 0 | 54 | 40 | 47 |
| Phase-6c | 17 | 0 | 0 | 0 | 0 | 0 | 17 | 16 | 16 |
| Phase-6d | 17 | 0 | 0 | 0 | 0 | 0 | 17 | 12 | 17 |
| Phase-6e | 14 | 4 | 1 | 0 | 2 | 1 | 10 | 5 | 12 |

## Fetchability projection (per phase)

Tier-1 reachability: bibkeys that have an arXiv ID can fetch arxiv-pdf or arxiv-tex.
Tier-5 fallback: bibkeys without arXiv but with DOI fall to abstract.txt or JSON.
Tier-6 floor: bibkeys without DOI nor arXiv need manual fill.

| Phase | Tier-1 reach | Tier-5 reach | Manual-fill required |
|---|---:|---:|---:|
| Phase-1-and-Background | 9 | 11 | 0 |
| Phase-3 | 1 | 0 | 0 |
| Phase-5d | 4 | 1 | 0 |
| Phase-5e | 1 | 0 | 0 |
| Phase-5q | 4 | 2 | 0 |
| Phase-5w | 3 | 12 | 0 |
| Phase-5x | 23 | 5 | 1 |
| Phase-5z | 24 | 7 | 1 |
| Phase-6a | 40 | 11 | 3 |
| Phase-6c | 16 | 1 | 0 |
| Phase-6d | 12 | 5 | 0 |
| Phase-6e | 4 | 4 | 2 |

## Manual-fill backlog (no arXiv, no DOI)

These bibkeys need manual primary-source acquisition:

- **Sola2023** [Phase-5x] — Sol{\`a} Peracaula, J. (2023)
- **PeskinSchroeder** [Phase-5z] — Peskin, M. E., Schroeder, D. V. (1995)
- **Carroll2004** [Phase-6a] — Carroll, S. M. (2004)
- **MTW1973** [Phase-6a] — Misner, C. W., Thorne, K. S., Wheeler, J. A. (1973)
- **Sakharov1968** [Phase-6a] — Sakharov, A. D. (1968)
- **Gilkey1995** [Phase-6e] — Gilkey, P. B. (1995)
- **Trautman1973** [Phase-6e] — Trautman, A. (1973)

## Phase-6a legacy migration (arXiv-ID → bibkey)

- `balbinot/` → `Balbinot2025.{tex,pdf,json}`
- `jv9801308/` → `JacobsonVolovik1998.{tex,pdf,json}`
- `jk0205174/` → `JacobsonKoike2002.{tex,pdf,json}`
- `v0301043/` → `Volovik2003BraneBH.{tex,pdf,json}`
