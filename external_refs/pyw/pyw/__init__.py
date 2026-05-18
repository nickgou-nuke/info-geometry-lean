"""
pyw - Kac-Moody & W-Algebra Computation Library

A Python library for computing with Kac-Moody algebras, affine Lie algebras,
and W-algebras, with special support for fractional level/weights.

Based on SageMath's root system and Lie algebra implementations.
"""

__version__ = "0.1.0"
__author__ = "pyw contributors"

from pyw.core.root_system import AffineRootSystem
from pyw.core.weyl_group import AffineWeylGroup
from pyw.core.weight_space import FractionalWeightSpace
from pyw.fractional.level import FractionalLevel
from pyw.fractional.admissible import AdmissibleWeight
from pyw.fractional.principal import PrincipalAdmissibleWeight
from pyw.fractional.nondegenerate import NondegenerateChecker

__all__ = [
    "AffineRootSystem",
    "AffineWeylGroup",
    "FractionalWeightSpace",
    "FractionalLevel",
    "AdmissibleWeight",
    "PrincipalAdmissibleWeight",
    "NondegenerateChecker",
]
