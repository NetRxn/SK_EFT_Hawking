"""Experimental prediction package for BEC analog Hawking radiation.

Provides platform-specific spectral predictions, detector sensitivity
requirements, and measurement strategy guidance for three experimental
programs: Steinhauer (87Rb), Heidelberg (39K), and Trento (23Na).

This package synthesizes results from Papers 1-4 into concrete,
experimentally actionable predictions.
"""

from src.experimental.predictions import (
    PredictionTable,
    PlatformComparison,
    DetectorRequirements,
    compute_prediction_table,
    compute_all_predictions,
    compute_detector_requirements,
    compare_platforms,
    measurement_strategy,
)

__all__ = [
    'PredictionTable',
    'PlatformComparison',
    'DetectorRequirements',
    'compute_prediction_table',
    'compute_all_predictions',
    'compute_detector_requirements',
    'compare_platforms',
    'measurement_strategy',
]
