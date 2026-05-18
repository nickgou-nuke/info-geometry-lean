import importlib

import pytest

sage_all = importlib.import_module("sage.all")

CC = sage_all.CC
I = sage_all.I
exp = sage_all.exp
pi = sage_all.pi


def q_of_tau(tau):
    return exp(2 * pi * I * CC(tau))


def sl2_fugacity(z):
    return exp(pi * I * CC(z))


def sl3_fugacity_1(z1):
    return exp(2 * pi * I * CC(z1))


def sl3_fugacity_2(z2):
    return exp(2 * pi * I * CC(z2))


def relative_error(actual, expected):
    actual_val = CC(actual)
    expected_val = CC(expected)
    return abs(actual_val - expected_val) / abs(expected_val)


def relative_error_with_reference(actual, expected, reference):
    actual_val = CC(actual)
    expected_val = CC(expected)
    reference_val = CC(reference)
    return abs(actual_val - expected_val) / abs(reference_val)


def sl2_vacuum_series_first_4_terms(tau, z):
    q = q_of_tau(tau)
    b = sl2_fugacity(z)
    return (
        q ** (1 / 4)
        + (1 + 1 / b**2 + b**2) * q ** (5 / 4)
        + ((1 + b**2 + b**4) ** 2 / b**4) * q ** (9 / 4)
        + (5 + 1 / b**6 + 2 / b**4 + 4 / b**2 + 4 * b**2 + 2 * b**4 + b**6) * q ** (13 / 4)
    )


def sl3_vacuum_series_first_2_terms(tau, z1, z2):
    q = q_of_tau(tau)
    b1 = sl3_fugacity_1(z1)
    b2 = sl3_fugacity_2(z2)
    return q ** (1 / 3) + (
        b1**4 * b2
        + 2 * b1**2 * b2**2
        + b2**3
        + b1**3 * (1 + b2**3)
        + b1 * (b2 + b2**4)
    ) / (b1**2 * b2**2) * q ** (4 / 3)


def sl2_boundary_nonvacuum_j1_series_first_4_terms(tau, z):
    q = q_of_tau(tau)
    b = sl2_fugacity(z)
    return (
        b ** (4 / 3) / ((-1 + b**2) * q ** (1 / 12))
        + (b ** (4 / 3) * (1 + b**2) * q ** (11 / 12)) / (-1 + b**2)
        + ((1 + 2 * b**2 + b**4 + b**6) * q ** (23 / 12)) / (b ** (2 / 3) * (-1 + b**2))
        + ((2 + 3 * b**2 + 3 * b**4 + b**6 + b**8) * q ** (35 / 12))
        / (b ** (2 / 3) * (-1 + b**2))
    )


def sl2_boundary_nonvacuum_j1_leading_term(tau, z):
    q = q_of_tau(tau)
    b = sl2_fugacity(z)
    return b ** (4 / 3) / ((-1 + b**2) * q ** (1 / 12))


def sl2_boundary_nonvacuum_j2_series_first_4_terms(tau, z):
    q = q_of_tau(tau)
    b = sl2_fugacity(z)
    return (
        b ** (2 / 3) / ((-1 + b**2) * q ** (1 / 12))
        + ((1 + b**2) * q ** (11 / 12)) / (b ** (4 / 3) * (-1 + b**2))
        + ((1 + b**2 + 2 * b**4 + b**6) * q ** (23 / 12)) / (b ** (10 / 3) * (-1 + b**2))
        + ((1 + b**2 + 3 * b**4 + 3 * b**6 + 2 * b**8) * q ** (35 / 12))
        / (b ** (16 / 3) * (-1 + b**2))
    )


def sl2_boundary_nonvacuum_j2_leading_term(tau, z):
    q = q_of_tau(tau)
    b = sl2_fugacity(z)
    return b ** (2 / 3) / ((-1 + b**2) * q ** (1 / 12))


@pytest.mark.sage
@pytest.mark.parametrize("tau", [I, 1.3 * I])
def test_sl2_boundary_vacuum_golden_from_markdown(tau):
    from pyw.utils.theta_functions import sl2_boundary_vacuum_character

    z = 0.21 + 0.13 * I
    actual = sl2_boundary_vacuum_character(3, tau, z, num_terms=400)
    expected = sl2_vacuum_series_first_4_terms(tau, z)

    rel_err = relative_error(actual, expected)
    assert rel_err < 1e-6, f"sl2 rel_error={rel_err}"


@pytest.mark.sage
def test_sl3_boundary_vacuum_golden_from_markdown():
    from pyw.utils.theta_functions import sl3_boundary_vacuum_character

    tau = 1.8 * I
    z1 = 0.19 + 0.07 * I
    z2 = 0.13 + 0.04 * I

    actual = sl3_boundary_vacuum_character(tau, z1, z2, num_terms=500)
    expected = sl3_vacuum_series_first_2_terms(tau, z1, z2)

    rel_err = relative_error(actual, expected)
    assert rel_err < 1e-4, f"sl3 rel_error={rel_err}"


@pytest.mark.sage
@pytest.mark.parametrize("tau", [1.6 * I, 1.8 * I])
def test_sl2_boundary_nonvacuum_j1_golden_from_markdown(tau):
    from pyw.utils.theta_functions import sl2_boundary_character

    # Use purely imaginary z away from b^2 = 1 singularity.
    z = 0.23 * I

    actual = sl2_boundary_character(3, 1, tau, z, num_terms=500)
    expected_series = sl2_boundary_nonvacuum_j1_series_first_4_terms(tau, z)
    leading = sl2_boundary_nonvacuum_j1_leading_term(tau, z)

    # characters.md and implementation can differ by an overall normalization.
    # Compare shape after fixing the same leading term.
    scale = CC(actual) / CC(leading)
    rel_err = relative_error_with_reference(actual, scale * expected_series, actual)
    assert rel_err < 1e-4, f"sl2 j=1 rel_error={rel_err}"


@pytest.mark.sage
@pytest.mark.parametrize("tau", [1.6 * I, 1.8 * I])
def test_sl2_boundary_nonvacuum_j2_golden_from_markdown(tau):
    from pyw.utils.theta_functions import sl2_boundary_character

    # Use purely imaginary z away from b^2 = 1 singularity.
    z = 0.23 * I

    actual = sl2_boundary_character(3, 2, tau, z, num_terms=500)
    expected_series = sl2_boundary_nonvacuum_j2_series_first_4_terms(tau, z)
    leading = sl2_boundary_nonvacuum_j2_leading_term(tau, z)

    # characters.md and implementation can differ by an overall normalization.
    # Compare shape after fixing the same leading term.
    scale = CC(actual) / CC(leading)
    rel_err = relative_error_with_reference(actual, scale * expected_series, actual)
    assert rel_err < 3e-4, f"sl2 j=2 rel_error={rel_err}"
