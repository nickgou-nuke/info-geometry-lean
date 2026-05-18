"""
Test configuration for pyw library.
"""

import pytest

# SageMath import - skip tests if not available
try:
    from sage.all import RootSystem, WeylGroup, Integer

    SAGEMATH_AVAILABLE = True
except ImportError:
    SAGEMATH_AVAILABLE = False

# Skip all tests if SageMath is not available
if not SAGEMATH_AVAILABLE:
    pytest.skip("SageMath not available", allow_module_level=True)
