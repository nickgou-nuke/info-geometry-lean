"""
Weight space implementation with support for fractional coefficients.

This module provides the FractionalWeightSpace class for creating and manipulating
weights in the extended weight space, supporting fractional coefficients beyond
the integer weight lattice.
"""

from fractions import Fraction
from typing import TYPE_CHECKING, Dict, Union

from sage.all import Integer, RootSystem, ZZ

if TYPE_CHECKING:
    from .affine_weight import AffineWeight


def is_integral_affine_weight(weight: "AffineWeight") -> bool:
    """Return whether an affine weight has integral Dynkin labels."""

    labels = weight.dynkin_labels()
    return all(value in ZZ for value in labels.values())


class FractionalWeightSpace:
    """
    A wrapper around SageMath's weight space with extended=True to support fractional weights.

    This class allows creation and manipulation of weights with fractional coefficients,
    using the extended weight space (weight_space(extended=True)) rather than the
    restricted weight lattice (weight_lattice()).

    The extended weight space supports weights of the form:
        λ = Σ (p_i/q_i) Λ_i

    where Λ_i are fundamental weights and p_i/q_i are rational coefficients.

    Parameters
    ----------
    cartan_type : str or CartanType
        The Cartan type of the root system (e.g., "A2", "B3", "E8")

    Attributes
    ----------
    cartan_type : CartanType
        The Cartan type of the root system
    root_system : RootSystem
        The underlying SageMath root system
    weight_space : sage.combinat.root_system.weight_space.WeightSpace
        The extended weight space with support for fractional coefficients

    Examples
    --------
    >>> from pyw.core.weight_space import FractionalWeightSpace
    >>> W = FractionalWeightSpace("A2")
    >>> lambda_1 = W.fundamental_weights[1]
    >>> lambda_2 = W.fundamental_weights[2]
    >>> half_weight = W.create_fractional_weight({1: Fraction(1, 2)})
    >>> zero = W.zero()
    """

    def __init__(self, cartan_type: Union[str, object]) -> None:
        """
        Initialize the fractional weight space for a given Cartan type.

        Parameters
        ----------
        cartan_type : str or CartanType
            The Cartan type of the root system (e.g., "A2", "B3", "E8")

        Raises
        ------
        ValueError
            If the Cartan type is invalid
        """
        self.cartan_type = cartan_type

        self.root_system: RootSystem = RootSystem(cartan_type)

        # Use weight_space(extended=True) to support fractional coefficients,
        # not weight_lattice() which is restricted to integer weights
        self.weight_space = self.root_system.weight_space(extended=True)

    @property
    def fundamental_weights(self) -> Dict[int, object]:
        """
        Return the fundamental weights of the weight space.

        Returns
        -------
        dict
            Dictionary mapping indices to fundamental weights, where
            fundamental_weights[i] gives the i-th fundamental weight Λ_i

        Examples
        --------
        >>> W = FractionalWeightSpace("A2")
        >>> Lambda = W.fundamental_weights
        >>> Lambda[1]  # First fundamental weight
        >>> Lambda[2]  # Second fundamental weight
        """
        Lambda = self.weight_space.fundamental_weights()

        return {i: Lambda[i] for i in range(1, self.root_system.rank() + 1)}

    def create_fractional_weight(
        self, coefficients: Dict[int, Union[Fraction, tuple[int, int], int, float]]
    ) -> object:
        """
        Create a weight with fractional coefficients.

        This method supports multiple input formats for coefficients:
        - Fraction objects: {i: Fraction(p, q)}
        - Tuple format: {i: (p, q)} equivalent to Fraction(p, q)
        - Integer values: {i: n} equivalent to Fraction(n, 1)
        - Float values: {i: x} converted to Fraction

        Parameters
        ----------
        coefficients : dict
            Dictionary mapping weight indices to their coefficients.
            Indices should be 1-based (e.g., {1: Fraction(1, 2), 2: (3, 4)})

        Returns
        -------
        Weight
            A weight in the extended weight space with the specified fractional
            coefficients

        Raises
        ------
        ValueError
            If coefficient format is invalid

        Examples
        --------
        >>> W = FractionalWeightSpace("A2")
        >>> # Using Fraction objects
        >>> w1 = W.create_fractional_weight({1: Fraction(1, 2), 2: Fraction(3, 4)})
        >>> # Using tuple format
        >>> w2 = W.create_fractional_weight({1: (1, 2), 2: (3, 4)})
        >>> # Using integers
        >>> w3 = W.create_fractional_weight({1: 1, 2: 2})
        """
        Lambda = self.fundamental_weights
        weight = self.weight_space.zero()

        for idx, coeff in coefficients.items():
            if isinstance(coeff, Fraction):
                frac = coeff
            elif isinstance(coeff, tuple) and len(coeff) == 2:
                frac = Fraction(coeff[0], coeff[1])
            elif isinstance(coeff, int):
                frac = Fraction(coeff, 1)
            elif isinstance(coeff, float):
                frac = Fraction(coeff).limit_denominator()
            else:
                raise ValueError(
                    f"Invalid coefficient format: {coeff}. "
                    f"Use Fraction, tuple (p, q), int, or float."
                )

            numerator = Integer(frac.numerator)
            denominator = Integer(frac.denominator)
            weight += (numerator / denominator) * Lambda[idx]

        return weight

    def zero(self) -> object:
        """
        Create the zero weight in the extended weight space.

        Returns
        -------
        Weight
            The zero weight element (all coefficients are zero)

        Examples
        --------
        >>> W = FractionalWeightSpace("A2")
        >>> zero_w = W.zero()
        """
        return self.weight_space.zero()
