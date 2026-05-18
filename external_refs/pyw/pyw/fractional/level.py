"""
Fractional level representation for Kac-Moody algebras.

This module provides the FractionalLevel class which represents fractional levels
of the form k = -h^∨ + p/u, where h^∨ is the dual Coxeter number and p, u are
coprime positive integers satisfying specific constraints.
"""

from sage.all import RootSystem, Integer, Rational
from fractions import Fraction
from typing import Union


def _to_python_int(n: Integer) -> int:
    """Convert SageMath Integer to Python int."""
    return int(n)


class FractionalLevel:
    """
    Represents a fractional level k = -h^∨ + p/u for affine Kac-Moody algebras.

    The fractional level is parameterized by coprime positive integers p and u
    that satisfy the following constraints:
        - (p, u) = 1 (coprime)
        - (u, ℓ) = 1 where ℓ is the lacety of the underlying Cartan type
        - p ≥ h^∨ where h^∨ is the dual Coxeter number

    Parameters:
        cartan_type: Cartan type specification, e.g., ['A', 2, 1] for affine A₂
        p: Numerator of the fractional part (positive integer)
        u: Denominator of the fractional part (positive integer)

    Raises:
        ValueError: If the constraints are not satisfied

    Example:
        >>> from pyw.fractional import FractionalLevel
        >>> level = FractionalLevel(['A', 2, 1], p=4, u=3)
        >>> print(f"Level k = {level.level}")  # k = -3 + 4/3 = -5/3
        >>> print(f"k + h^∨ = {level.k_plus_h_vee}")  # 4/3
        >>> print(f"ℓ = {level.lacety}")  # 1

    Notes:
        The lacety ℓ depends on the Cartan type:
            - ADE types: ℓ = 1
            - BCF types: ℓ = 2
            - G₂ type: ℓ = 3
    """

    def __init__(self, cartan_type: Union[list, tuple], p: int, u: int) -> None:
        """
        Initialize a FractionalLevel instance.

        Args:
            cartan_type: Cartan type in the format ['X', n, 1] for affine Xₙ
            p: Positive integer numerator
            u: Positive integer denominator

        Raises:
            ValueError: If the constraints (p, u) = 1, (u, ℓ) = 1, or p ≥ h^∨ fail
        """
        self.cartan_type = cartan_type
        self.p = Integer(p)
        self.u = Integer(u)
        self._h_vee: Integer | None = None
        self._lacety: int | None = None
        self._validate()

    def _validate(self) -> None:
        """
        Validate that the fractional level satisfies all required constraints.

        This method checks:
            1. (p, u) = 1 (coprime)
            2. (u, ℓ) = 1 where ℓ is the lacety
            3. p ≥ h^∨ where h^∨ is the dual Coxeter number

        Raises:
            ValueError: If any constraint is violated
        """
        from math import gcd as python_gcd

        # Get dual Coxeter number
        R = RootSystem(self.cartan_type)
        ct = R.cartan_type()
        # Try different methods for dual Coxeter number
        if hasattr(ct, "dual_coxeter_number"):
            self._h_vee = Integer(ct.dual_coxeter_number())
        elif hasattr(ct, "coxiceter_number"):
            self._h_vee = Integer(ct.coxeter_number())
        else:
            # Use a lookup table for common types
            self._h_vee = self.lookup_dual_coxeter_number()

        # Get lacety
        self._lacety = self.compute_lacety()

        # Check that p and u are positive
        if self.p <= 0:
            raise ValueError(f"p={self.p} must be positive")
        if self.u <= 0:
            raise ValueError(f"u={self.u} must be positive")

        # Check coprime constraint: (p, u) = 1
        if python_gcd(self.p, self.u) != 1:
            raise ValueError(f"p={self.p} and u={self.u} must be coprime (gcd = 1)")

        # Check lacety constraint: (u, ℓ) = 1
        if python_gcd(self.u, self._lacety) != 1:
            raise ValueError(f"u={self.u} and lacety={self._lacety} must be coprime (gcd = 1)")

        # Check lower bound constraint: p ≥ h^∨
        if self.p < self._h_vee:
            raise ValueError(f"p={self.p} must be >= h^∨={self._h_vee}")

    def compute_lacety(self) -> int:
        """
        Determine the lacety ℓ based on the Cartan type.

        The lacety is defined as:
            - ℓ = 1 for ADE Cartan types (simply-laced)
            - ℓ = 2 for BCF Cartan types (twice-laced)
            - ℓ = 3 for G₂ Cartan type (triple-laced)

        Returns:
            int: The lacety value (1, 2, or 3)

        Raises:
            ValueError: If the Cartan type is not recognized
        """
        ct = self.cartan_type[0]

        if ct in ["A", "D", "E"]:
            return 1
        elif ct in ["B", "C", "F"]:
            return 2
        elif ct == "G":
            return 3
        else:
            raise ValueError(f"Unknown Cartan type: {ct}. Expected A, B, C, D, E, F, or G")

    def lookup_dual_coxeter_number(self) -> Integer:
        """
        Fallback method to get dual Coxeter number using a lookup table.

        This is used when the SageMath CartanType object doesn't have
        the dual_coxeter_number method.

        Returns:
            Integer: The dual Coxeter number h^∨

        Raises:
            ValueError: If the Cartan type is not in the lookup table
        """
        # Dual Coxeter numbers for finite simple Lie algebras
        # Format: (type, rank) -> h^∨
        dual_coxeter_numbers = {
            ("A", 1): 2,
            ("A", 2): 3,
            ("A", 3): 4,
            ("A", 4): 5,
            ("A", 5): 6,
            ("A", 6): 7,
            ("A", 7): 8,
            ("A", 8): 9,
            ("A", 9): 10,
            ("A", 10): 11,
            ("B", 1): 2,
            ("B", 2): 3,
            ("B", 3): 4,
            ("B", 4): 5,
            ("B", 5): 6,
            ("B", 6): 7,
            ("B", 7): 8,
            ("B", 8): 9,
            ("B", 9): 10,
            ("B", 10): 11,
            ("C", 1): 2,
            ("C", 2): 3,
            ("C", 3): 4,
            ("C", 4): 5,
            ("C", 5): 6,
            ("C", 6): 7,
            ("C", 7): 8,
            ("C", 8): 9,
            ("C", 9): 10,
            ("C", 10): 11,
            ("D", 4): 4,
            ("D", 5): 5,
            ("D", 6): 6,
            ("D", 7): 7,
            ("D", 8): 8,
            ("D", 9): 9,
            ("D", 10): 10,
            ("D", 11): 11,
            ("D", 12): 12,
            ("E", 6): 6,
            ("E", 7): 8,
            ("E", 8): 12,
            ("F", 4): 6,
            ("G", 2): 4,
        }

        ct_letter = self.cartan_type[0]
        ct_rank = self.cartan_type[1]

        key = (ct_letter, ct_rank)
        if key in dual_coxeter_numbers:
            return Integer(dual_coxeter_numbers[key])

        raise ValueError(
            f"Dual Coxeter number not found for Cartan type {self.cartan_type}. "
            f"Please add ({ct_letter}, {ct_rank}) to the lookup table."
        )

    @property
    def level(self) -> Fraction:
        """
        Return the fractional level k = -h^∨ + p/u.

        Returns:
            Fraction: The level as a rational number

        Example:
            >>> level = FractionalLevel(['A', 2, 1], p=4, u=3)
            >>> level.level
            Fraction(-5, 3)  # -3 + 4/3 = -5/3
        """
        # Use SageMath Rational for arithmetic, then convert to Fraction
        h_vee_int = _to_python_int(self.h_vee)
        p_int = _to_python_int(self.p)
        u_int = _to_python_int(self.u)
        return Fraction(-h_vee_int * u_int + p_int, u_int)

    @property
    def k_plus_h_vee(self) -> Fraction:
        """
        Return k + h^∨ = p/u.

        This is the shifted level, often used in representation theory.

        Returns:
            Fraction: The shifted level p/u

        Example:
            >>> level = FractionalLevel(['A', 2, 1], p=4, u=3)
            >>> level.k_plus_h_vee
            Fraction(4, 3)
        """
        return Fraction(_to_python_int(self.p), _to_python_int(self.u))

    @property
    def h_vee(self) -> Integer:
        """
        Return the dual Coxeter number h^∨.

        Returns:
            Integer: The dual Coxeter number

        Example:
            >>> level = FractionalLevel(['A', 2, 1], p=4, u=3)
            >>> level.h_vee
            3
        """
        if self._h_vee is None:
            raise RuntimeError("h_vee not initialized. Validation failed.")
        return Integer(self._h_vee)

    @property
    def lacety(self) -> int:
        """
        Return the lacety ℓ of the underlying Cartan type.

        Returns:
            int: The lacety value (1, 2, or 3)

        Example:
            >>> level = FractionalLevel(['A', 2, 1], p=4, u=3)
            >>> level.lacety
            1
        """
        if self._lacety is None:
            raise RuntimeError("lacety not initialized. Validation failed.")
        return self._lacety

    def __repr__(self) -> str:
        """
        Return a string representation of the FractionalLevel.

        Returns:
            str: String representation showing the level parameters
        """
        return f"FractionalLevel(cartan_type={self.cartan_type}, p={self.p}, u={self.u})"

    def __str__(self) -> str:
        """
        Return a human-readable string representation.

        Returns:
            str: String showing the level value
        """
        return f"k = {self.level} (h^∨={self.h_vee}, p={self.p}, u={self.u})"


def to_python_int(sage_int: Integer) -> int:
    """Convert a SageMath Integer to a Python int."""
    return int(sage_int)
