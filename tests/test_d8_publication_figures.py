"""Check D8's manuscript bindings and theorem-backed figure data."""

from pathlib import Path

import numpy as np
from PIL import Image

from scripts.review_figures import FIGURE_REGISTRY
from src.core.visualizations import (
    bundle_figure_typeset_pt,
    fig_d8_alphabet_dimension_map,
    fig_d8_length_comparison,
)


def test_d8_figure_bindings_and_typeset_floor():
    paper = Path(__file__).resolve().parents[1] / "papers" / "D8"
    draft = (paper / "paper_draft.tex").read_text()
    for label, name, producer in (
        ("coverage", "d8_fig1_alphabet_dimension_map", fig_d8_alphabet_dimension_map),
        ("length-comparison", "d8_fig4_length_comparison", fig_d8_length_comparison),
    ):
        figure_label = rf"\label{{fig:d8-{label}}}"
        assert draft.count(figure_label) == 1
        block = draft.split(figure_label)[0].rsplit(r"\begin{figure*}", 1)[1]
        assert rf"\includegraphics[width=\textwidth]{{figures/{name}.png}}" in block
        assert rf"\figuredeferred{{fig:d8-{label}}}" not in draft
        assert any(spec.name == name and spec.function == producer.__name__
                   for spec in FIGURE_REGISTRY)
        fig = producer()
        assert bundle_figure_typeset_pt(fig) >= 8
        with Image.open(paper / "figures" / f"{name}.png") as png:
            assert png.format == "PNG"
            assert png.size == (2 * fig.layout.width, 2 * fig.layout.height)
            png.verify()


def test_d8_coverage_matches_manuscript_roster():
    fig = fig_d8_alphabet_dimension_map()
    assert [item.text for item in fig.layout.annotations] == [
        "Clifford+T", "Read–Rezayi SU(2)₅", "Read–Rezayi SU(2)₇",
        "Trapped-ion (MS)", "Clifford+CCZ (with T)", "Clifford+CCZ (T-free)",
    ]
    assert [trace.x[0] for trace in fig.data[:6]] == [0, 0, 0, 1, 2, 2]


def test_d8_length_bounds_preserve_distinct_error_contracts():
    fig = fig_d8_length_comparison()
    balanced, grid, kmm = fig.data
    eps = np.asarray(balanced.x)
    assert np.all((eps > 0) & (eps <= 1 / 8388608))
    np.testing.assert_allclose(balanced.y, 1000 * np.log(1 / eps)**(np.log(5) / np.log(1.5)))

    k = np.arange(16, 97, dtype=float)
    np.testing.assert_allclose(grid.x, (1 + np.sqrt(2)) / np.sqrt(2)**k, atol=0)
    np.testing.assert_array_equal(grid.y, 8 * k)
    np.testing.assert_allclose(kmm.x, 9 * (2 / 4**k + 2 * np.sqrt(2) / 2**k), atol=0)
    np.testing.assert_array_equal(kmm.y, 50400 * k + 812)

    assert fig.layout.xaxis.title.text == "Target ε"
    assert fig.layout.xaxis2.title.text == "Column precision δ"
    assert fig.layout.yaxis2.title.text == "Bound − N₃"
    assert fig.layout.xaxis3.title.text == "Squared state error"
