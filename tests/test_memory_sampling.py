"""Exact decision checks and finite null enumeration, not experimental validation."""
from decimal import Decimal
from fractions import Fraction as F
from math import comb

import pytest

from src.core.formulas import memory_sampling_certificate


def certificate(**updates):
    args = dict(n0=4096, n1=4096, count0=0, count1=1280,
                rho0=F(1, 32), rho1=F(1, 32), eps1=F(1, 8), alpha=F(1, 64))
    return memory_sampling_certificate(**(args | updates))


def test_exact_partial_model_count_example():
    r = certificate()
    assert r["proportion1"] == F(5, 16)
    assert r["failure_bound"] == F(1, 64)
    assert r["memoryless_bound"] == F(1, 8)
    assert r["rejection_threshold"] == F(3, 16)
    assert r["strict_margin"] == F(1, 8)
    assert r["exponent0"] == r["used_exponent0"] == 8
    assert r["confidence_sufficient"] and r["positive_margin"]
    assert r["reject_common_channel"]
    assert not r["exponent_capped0"]
    for key in ("proportion0", "proportion1", "failure_bound", "memoryless_bound",
                "empirical_gap", "rejection_threshold", "strict_margin"):
        assert type(r[key]) is F


def test_strict_margin_and_confidence_boundaries_are_separate():
    # Equality at the empirical threshold is inconclusive, including beta=alpha.
    boundary = certificate(count1=768)
    assert boundary["strict_margin"] == 0
    assert boundary["confidence_sufficient"] and not boundary["positive_margin"]
    assert not boundary["reject_common_channel"]
    assert certificate(count1=769)["reject_common_channel"]
    assert certificate(count1=767)["strict_margin"] < 0
    insufficient = certificate(alpha=F(1, 64)-F(1, 10**100))
    assert insufficient["positive_margin"] and not insufficient["confidence_sufficient"]
    assert not insufficient["reject_common_channel"]


def test_unequal_groups_radii_and_observation_bias():
    r = certificate(n0=25, n1=40, count0=5, count1=32, rho0=F(1, 5),
                    rho1=F(1, 4), eps0=F(1, 20), eps1=F(1, 40),
                    delta0=F(1, 100), delta1=F(1, 50), alpha=F(3, 4))
    assert (r["exponent0"], r["exponent1"]) == (2, 5)
    assert r["failure_bound"] == F(9, 16)
    assert r["memoryless_bound"] == F(21, 200)
    assert r["empirical_gap"] == F(3, 5)
    assert r["strict_margin"] == F(9, 200)
    assert r["reject_common_channel"]
    swapped = certificate(n0=40, n1=25, count0=32, count1=5, rho0=F(1, 4),
                          rho1=F(1, 5), eps0=F(1, 40), eps1=F(1, 20),
                          delta0=F(1, 50), delta1=F(1, 100), alpha=F(3, 4))
    for key in ("failure_bound", "memoryless_bound", "strict_margin"):
        assert swapped[key] == r[key]


def test_only_reset_budget_sum_is_capped():
    r = certificate(eps0=2, eps1=3, delta0=F(1, 4), delta1=F(1, 8))
    assert r["memoryless_bound"] == F(11, 8)
    assert not r["positive_margin"]


def test_downward_resource_cap_cannot_strengthen_confidence():
    capped = certificate(exponent_cap=7)
    assert capped["exponent0"] == 8 and capped["used_exponent0"] == 7
    assert capped["exponent_capped0"] and capped["exponent_capped1"]
    assert capped["failure_bound"] == F(1, 32)
    assert capped["positive_margin"] and not capped["confidence_sufficient"]
    assert not capped["reject_common_channel"]
    assert certificate(exponent_cap=0)["failure_bound"] == 1
    huge = certificate(n0=10**100, n1=10**100)
    assert huge["used_exponent0"] == 4096
    assert huge["exponent_capped0"]
    assert huge["failure_bound"].denominator.bit_length() <= 4097


def test_exact_floor_just_below_integer_and_probability_cap():
    # 2*25*(1/5)^2=2; move strictly below without floating-point rounding.
    r = certificate(n0=25, rho0=F(1, 5)-F(1, 10**100))
    assert r["exponent0"] == 1
    assert r["failure_bound"] == 1
    assert not r["confidence_sufficient"]


@pytest.mark.parametrize("field", ["n0", "n1", "count0", "count1", "exponent_cap"])
@pytest.mark.parametrize("bad", [True, False, 4.0, F(4), "4", Decimal(4), None])
def test_integer_types_rejected(field, bad):
    with pytest.raises(TypeError):
        certificate(**{field: bad})


@pytest.mark.parametrize("field", ["rho0", "rho1", "eps0", "eps1", "delta0", "delta1", "alpha"])
@pytest.mark.parametrize("bad", [True, False, 0.25, float("nan"), float("inf"),
                                 "1/4", Decimal("0.25"), None, 1j])
def test_inexact_or_ambiguous_rational_inputs_rejected(field, bad):
    with pytest.raises(TypeError):
        certificate(**{field: bad})


@pytest.mark.parametrize("updates", [dict(n0=0), dict(n1=-1), dict(count0=-1),
    dict(count1=4097), dict(rho0=0), dict(rho1=-1), dict(eps0=-1), dict(eps1=-1),
    dict(delta0=-1), dict(delta1=-1), dict(alpha=0), dict(alpha=1),
    dict(alpha=2), dict(exponent_cap=-1), dict(exponent_cap=4097)])
def test_domain_validation(updates):
    with pytest.raises(ValueError):
        certificate(**updates)


@pytest.mark.parametrize("q0,q1,budget", [(F(1, 2), F(1, 2), F(0)),
                                         (F(1, 2), F(3, 8), F(1, 8))])
def test_exact_nontrivial_null_count_enumeration(q0, q1, budget):
    # Independent binomial groups are one admissible IID null. Enumerate all
    # count pairs with rational masses, including actual false rejections.
    n0, n1 = 24, 32
    pmf0 = [comb(n0, c)*q0**c*(1-q0)**(n0-c) for c in range(n0+1)]
    pmf1 = [comb(n1, c)*q1**c*(1-q1)**(n1-c) for c in range(n1+1)]
    rejected_mass, total_mass, failed_coverage_mass = F(0), F(0), F(0)
    for c0, p0 in enumerate(pmf0):
        for c1, p1 in enumerate(pmf1):
            r = certificate(n0=n0, n1=n1, count0=c0, count1=c1,
                            rho0=F(1, 3), rho1=F(1, 4), eps1=budget,
                            alpha=F(3, 16))
            mass = p0*p1
            total_mass += mass
            covered = (abs(F(c0, n0)-q0) <= F(1, 3)
                       and abs(F(c1, n1)-q1) <= F(1, 4))
            if not covered:
                failed_coverage_mass += mass
            if r["reject_common_channel"]:
                assert not covered
                rejected_mass += mass
    assert total_mass == 1
    assert r["failure_bound"] == F(3, 16) < 1
    assert 0 < rejected_mass <= failed_coverage_mass <= r["failure_bound"]


def test_eight_trial_null_has_exact_rejection_and_equality_masses():
    rejected, equality_mass = {}, F(0)
    for c0 in range(9):
        for c1 in range(9):
            r = certificate(n0=8, n1=8, count0=c0, count1=c1,
                            rho0=F(7, 16), rho1=F(7, 16), eps1=0, alpha=F(1, 2))
            mass = F(comb(8, c0)*comb(8, c1), 2**16)
            assert r["exponent0"] == r["exponent1"] == 3
            assert r["failure_bound"] == F(1, 2)
            if r["strict_margin"] == 0:
                equality_mass += mass
                assert not r["reject_common_channel"]
            if r["reject_common_channel"]:
                rejected[c0, c1] = mass
    assert set(rejected) == {(0, 8), (8, 0)}
    assert sum(rejected.values()) == F(1, 32768)
    assert equality_mass == F(1, 2048)
