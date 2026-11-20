---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: publication-chat-lead
review_date: 2026-10-15T00:00:00Z
kind: focused-polariton-notebook-qualification
---

# Polariton notebook qualifications and saved outputs

Base: `0b984829c70f52841717ba879bac4cbbe0ea4b0e`. Independent whole-notebook source, output and pixel review accepted the bounded correction; see SCOPED_REVIEW.md. The separate ledger audit accepted the exact two closures; see SCOPED_REVIEW.md. The report author inspected all current cell sources and saved text/MIME structure but did not execute a kernel, acquire sources or alter the notebook.

### 1.1 — REQUIRED — Propagate accepted device, model and noise-budget qualifications into the technical notebook

- **Severity:** required
- **Lane:** `pyrust`
- **Target:** `notebooks/Phase5d_Polariton_Technical.ipynb`
- **Location:** `notebooks/Phase5d_Polariton_Technical.ipynb`, complete 15-cell notebook, especially parameter status, stimulated response/SNR, dispersive-model and mean-field sections and their saved outputs.
- **Gate:** none
- **Verify:** `cd "$REPO" && python3 -c 'import json; n=json.load(open("notebooks/Phase5d_Polariton_Technical.ipynb")); m=" ".join(" ".join("".join(c.get("source",[])) for c in n["cells"] if c["cell_type"]=="markdown").split()); assert "spectrally featureless" not in m; assert "3 independent measurements" not in m; assert "phenomenological" in m; assert "measured in-band noise budget" in m'`
- **Observed at base:** The notebook retains an unmatched reservoir rescaling, stale parameter/output values, unsupported spontaneous repetition and featureless-noise claims, and treats the adopted quadratic law and ideal readout as physical predictions without the accepted qualifications. A numerical illustration can consequently read as measured sensitivity or controlled dispersion.
- **Expected:** Use canonical reservoir-inclusive Paris inputs and distinguish the measured 8 ps device from projected 100/300 ps lifetimes. Identify the entire quadratic law as phenomenological, normalize conditional gain/SNR consistently with kappa_eff, and require independent greybody/transfer calibration and a measured in-band noise budget. Treat mean-field energy as energy units, not inferred occupation or detected PSD. Distinguish a reported 4 K cryostat from the hypothetical equilibrium mode population. Regenerate actual saved outputs through the existing project execution route and inspect both actual saved plots.
- **Baseline:** The lead executed this qualification guard at the base and observed its assertion failure on the old featureless-noise claim. The report author did not rerun it. The lead and independent reviewer executed the exact final declared Verify with REPO set to the candidate root; both passed.
- **Evidence:** SOURCE_ASSESSMENT.md records the verified existing kernel/source context, actual nbconvert execution of all eight code cells, current saved model outputs, two generated PNG/Plotly bundles and hashes, actual lead pixel inspection, and eleven passing focused tests. No output payload was authored by hand.
- **Limits:** This content guard cannot certify scientific fidelity, successful execution, current saved numerics, accessible HTML layout or apparatus performance. Independent review of the full notebook, source evidence and actual saved outputs remains required. The separate ratio-arithmetic defect remains owned by original `2026-08-15-dispersive-coefficient-normalization/infra.md` finding 1.1; it is not duplicated here. Its closure requires correct arithmetic and actual regenerated outputs, not merely a negative string guard. No source caches, metadata, formal proof counts or runner implementation change is claimed.
