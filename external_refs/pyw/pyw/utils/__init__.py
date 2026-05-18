"""
Utilities module - Helper functions for LaTeX rendering and visualization.

Includes:
- theta_functions: Jacobi theta functions and Dedekind eta for character formulas
"""

from .theta_functions import (
    dedekind_eta,
    eta_ratio,
    sl2_boundary_character,
    sl2_boundary_vacuum_character,
    sl3_boundary_vacuum_character,
    theta_01,
    theta_11,
    theta_11_product,
    theta_ratio,
    verify_theta_properties,
)

__all__ = [
    "dedekind_eta",
    "eta_ratio",
    "theta_11",
    "theta_11_product",
    "theta_01",
    "theta_ratio",
    "sl2_boundary_character",
    "sl2_boundary_vacuum_character",
    "sl3_boundary_vacuum_character",
    "verify_theta_properties",
]
