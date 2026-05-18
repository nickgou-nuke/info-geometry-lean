"""
Nondegeneracy checker for weights in Kac-Moody algebras.

This module provides the NondegenerateChecker class which determines whether
a weight is nondegenerate, i.e., the pairing (λ|α) is not an integer for all
coroots α ∈ Δ^∨ (or for a relevant subset).

Nondegeneracy is crucial for character formulas in the Kac-Wakimoto theory
of admissible representations.
"""

from typing import List, Tuple, Union

from sage.all import Integer, QQ, RootSystem


class NondegenerateChecker:
    """
    Checker for nondegeneracy of weights in Kac-Moody algebras.

    A weight λ is called nondegenerate if the natural pairing (λ|α) is not
    an integer for all coroots α ∈ Δ^∨ (the set of simple coroots).

    In the context of Kac-Wakimoto admissible representations, this condition
    ensures that the denominator of the rational level is coprime with certain
    indices, which is necessary for character formulas to hold.

    Parameters:
        cartan_type: Cartan type specification
            - Finite: ['A', n], ['D', n], ['E', 6/7/8], ['B', n], ['C', n], ['F', 4], ['G', 2]
            - Affine: ['A', n, 1], ['D', n, 1], ['E', 6/7/8, 1], etc.

    Example:
        >>> from pyw.fractional import NondegenerateChecker
        >>> from sage.all import RootSystem
        >>> checker = NondegenerateChecker(['A', 2, 1])
        >>> W = RootSystem(['A', 2, 1]).weight_lattice()
        >>> weight = W.gen(0) / 2 + W.gen(1) / 3  # Lambda[0]/2 + Lambda[1]/3
        >>> checker.is_nondegenerate(weight)
        True

    Notes:
        - For affine algebras, we typically check against all simple coroots
        - For finite algebras, we check against all simple coroots
        - The pairing is computed using the natural pairing between weights and coroots
          from the root system's coroot lattice

    References:
        - Kac, V. G., Wakimoto, M. "On rationality of W-algebras", Adv. Math. 1993
        - Kac, V. G. "Infinite-dimensional Lie algebras", 3rd ed., Section 12.10
    """

    def __init__(self, cartan_type: Union[list, tuple]) -> None:
        """
        Initialize the NondegenerateChecker.

        Args:
            cartan_type: Cartan type specification for the root system

        Raises:
            ValueError: If the Cartan type is not supported
        """
        self._cartan_type = cartan_type
        self._setup()

    def _setup(self) -> None:
        """
        Initialize the root system and related data structures.

        This method sets up the root system, weight lattice, and coroot lattice
        for both finite and affine cases.
        """
        try:
            # Create the root system
            self._root_system = RootSystem(self._cartan_type)

            # Get the weight lattice
            self._weight_lattice = self._root_system.weight_lattice()

            # Get the coroot lattice
            self._coroot_lattice = self._root_system.coroot_lattice()

            # Get the set of simple coroots
            self._simple_coroots = self._coroot_lattice.simple_roots()

            # Determine if this is an affine type
            self._is_affine = len(self._cartan_type) == 3

        except Exception as e:
            raise ValueError(
                f"Failed to initialize root system for type {self._cartan_type}: {e}"
            ) from e

    def is_nondegenerate(self, weight) -> bool:
        """
        Check whether a weight is nondegenerate.

        A weight λ is nondegenerate if (λ|α) ∉ ℤ for all simple coroots α ∈ Δ^∨.

        Args:
            weight: A weight in the weight lattice

        Returns:
            True if the weight is nondegenerate, False otherwise

        Example:
            >>> checker = NondegenerateChecker(['A', 2, 1])
            >>> W = checker._weight_lattice
            >>> weight = W.gen(0) / 2 + W.gen(1) / 3
            >>> checker.is_nondegenerate(weight)
            True
        """
        # Check against all simple coroots
        return self.has_nondegenerate_pairings_on_coroots(
            weight, list(self._simple_coroots.values())
        )

    def has_nondegenerate_pairings_on_coroots(self, weight, coroots: List) -> bool:
        """
        Check nondegeneracy against a specific list of coroots.

        This method checks whether (λ|α) ∉ ℤ for all coroots in the given list.

        Args:
            weight: A weight in the weight lattice
            coroots: List of coroots to check against

        Returns:
            True if (weight|coroot) ∉ ℤ for all coroots in the list, False otherwise

        Example:
            >>> checker = NondegenerateChecker(['A', 2, 1])
            >>> W = checker._weight_lattice
            >>> weight = W.gen(0) / 2
            >>> coroots = [checker._coroot_lattice.simple_roots()[0]]
            >>> checker.has_nondegenerate_pairings_on_coroots(weight, coroots)
            True
        """
        try:
            for coroot in coroots:
                # Compute the pairing (λ|α) using the natural pairing
                pairing = self.compute_weight_coroot_pairing(weight, coroot)

                # Check if the pairing is an integer
                if self._is_integer(pairing):
                    return False

            return True
        except (AttributeError, TypeError) as e:
            raise ValueError(f"Invalid weight or coroot type: {e}") from e

    def compute_weight_coroot_pairing(self, weight, coroot) -> Union[Integer, float]:
        """
        Compute the natural pairing (λ|α) between a weight and a coroot.

        The pairing is computed using the dot product representation,
        which is the standard pairing in SageMath's root systems.

        Args:
            weight: A weight in the weight lattice
            coroot: A coroot in the coroot lattice

        Returns:
            The pairing value (λ|α) as a rational or float
        """
        # Convert to appropriate representation if needed
        # SageMath weights have a dot method that computes pairing with coroots
        try:
            # Try the direct dot method first
            pairing = weight.dot(coroot)
        except AttributeError:
            # Fallback: use the inner product from the root system
            try:
                # Get the coefficients and compute manually
                weight_coeffs = weight.to_vector()
                coroot_coeffs = coroot.to_vector()
                pairing = sum(
                    weight_coeffs[i] * coroot_coeffs[i] for i in range(len(weight_coeffs))
                )
            except (AttributeError, IndexError):
                # Convert to QQ for rational arithmetic
                pairing = QQ(weight).coefficient * QQ(coroot).coefficient

        # Ensure we're working with a rational number
        try:
            return QQ(pairing)
        except (TypeError, ValueError):
            return pairing

    def _is_integer(self, value: Union[Integer, float, int]) -> bool:
        """
        Check if a value is an integer.

        This handles both SageMath Integer and Python int types.

        Args:
            value: Value to check

        Returns:
            True if the value is an integer, False otherwise
        """
        if isinstance(value, Integer):
            return True

        try:
            return value == int(value)
        except (TypeError, ValueError):
            return False

    def get_failing_coroots(self, weight) -> List[Tuple[int, Union[Integer, float]]]:
        """
        Get the list of coroots that fail the nondegeneracy condition.

        For a given weight, this returns a list of indices and coroots
        such that (λ|α_i) ∈ ℤ.

        Args:
            weight: A weight in the weight lattice

        Returns:
            List of tuples (index, coroot, pairing) for failing coroots

        Example:
            >>> checker = NondegenerateChecker(['A', 2, 1])
            >>> W = checker._weight_lattice
            >>> weight = W.gen(0)  # Lambda[0]
            >>> failing = checker.get_failing_coroots(weight)
            >>> print(f"Failing coroots: {len(failing)}")
        """
        failing = []
        simple_coroots = self._simple_coroots

        for idx, coroot in simple_coroots.items():
            pairing = self.compute_weight_coroot_pairing(weight, coroot)
            if self._is_integer(pairing):
                failing.append((idx, coroot, pairing))

        return failing

    def has_integral_pairing(self, weight, coroot) -> bool:
        """
        Check if the pairing (λ|α) is an integer.

        This is a convenience method for checking a single coroot.

        Args:
            weight: A weight in the weight lattice
            coroot: A coroot in the coroot lattice

        Returns:
            True if (weight|coroot) ∈ ℤ, False otherwise
        """
        pairing = self.compute_weight_coroot_pairing(weight, coroot)
        return self._is_integer(pairing)

    @property
    def cartan_type(self) -> Union[list, tuple]:
        """Get the Cartan type."""
        return self._cartan_type

    @property
    def is_affine(self) -> bool:
        """Check if this is an affine type."""
        return self._is_affine

    @property
    def weight_lattice(self):
        """Get the weight lattice."""
        return self._weight_lattice

    @property
    def coroot_lattice(self):
        """Get the coroot lattice."""
        return self._coroot_lattice

    @property
    def simple_coroots(self):
        """Get the dictionary of simple coroots."""
        return self._simple_coroots
