"""
Test suite for pyw.core.root_system module
"""

import pytest

from sage.all import RootSystem

from pyw.core.root_system import AffineRootSystem


class TestAffineRootSystem:
    """Test AffineRootSystem class."""

    def test_init_a2_affine(self):
        """Test initialization with A2 affine type."""
        rs = AffineRootSystem(["A", 2, 1])
        assert rs.cartan_type == ["A", 2, 1]

    def test_init_a2_finite(self):
        """Test initialization with A2 finite type."""
        rs = AffineRootSystem(["A", 2])
        assert rs.cartan_type == ["A", 2]

    def test_init_tuple_type(self):
        """Test initialization with tuple type."""
        rs = AffineRootSystem(("A", 2, 1))
        assert rs.cartan_type == ("A", 2, 1)

    def test_cartan_matrix(self):
        """Test cartan_matrix property."""
        rs = AffineRootSystem(["A", 2, 1])
        cm = rs.cartan_matrix
        # Cartan matrix should be a square matrix
        assert cm.ncols() == cm.nrows()
        # A2 affine is 3x3
        assert cm.ncols() == 3

    def test_simple_roots(self):
        """Test simple_roots property."""
        rs = AffineRootSystem(["A", 2, 1])
        roots = rs.simple_roots
        # Should have roots indexed by the Cartan matrix size
        assert len(roots) >= 2

    def test_simple_coroots(self):
        """Test simple_coroots property."""
        rs = AffineRootSystem(["A", 2, 1])
        coroots = rs.simple_coroots
        # Should have coroots indexed by the Cartan matrix size
        assert len(coroots) >= 2

    def test_dual_coxeter_number_a2(self):
        """Test dual_coxeter_number for A2."""
        rs = AffineRootSystem(["A", 2])
        # For A2, h^∨ = 3
        assert rs.dual_coxeter_number == 3

    def test_dual_coxeter_number_b2(self):
        """Test dual_coxeter_number for B2."""
        rs = AffineRootSystem(["B", 2])
        # For B2, h^∨ = 3
        assert rs.dual_coxeter_number == 3

    def test_dual_coxeter_number_g2(self):
        """Test dual_coxeter_number for G2."""
        rs = AffineRootSystem(["G", 2])
        # For G2, h^∨ = 4
        assert rs.dual_coxeter_number == 4

    def test_roots_property(self):
        """Test roots property."""
        rs = AffineRootSystem(["A", 2])
        roots = rs.roots
        # Finite A2 has 6 roots (3 positive, 3 negative)
        assert len(roots) >= 6

    def test_coroots_property(self):
        """Test coroots property."""
        rs = AffineRootSystem(["A", 2])
        coroots = rs.coroots
        # Should have same number as roots
        assert len(coroots) >= 6

    def test_root_system_property(self):
        """Test root_system property."""
        rs = AffineRootSystem(["A", 2, 1])
        sage_rs = rs.root_system
        # Should be a SageMath RootSystem object
        assert hasattr(sage_rs, "cartan_type")
        assert hasattr(sage_rs, "cartan_matrix")

    def test_repr(self):
        """Test string representation."""
        rs = AffineRootSystem(["A", 2, 1])
        s = repr(rs)
        assert "AffineRootSystem" in s
        assert "A" in s
