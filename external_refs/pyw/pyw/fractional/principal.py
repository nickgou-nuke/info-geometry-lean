"""
Principal admissible weights for fractional level Kac-Moody algebras.

This module provides the PrincipalAdmissibleWeight class which constructs the
set of principal admissible weights P̂_{u,y}^k for a given fractional level k
and extended affine Weyl group element y.

The principal admissible weights are defined as:
    P̂_{u,y}^k = {y.(Λ + (k + h^∨ - p)D) | Λ ∈ P̂_+^{p-h^∨}}

where:
    - k = -h^∨ + p/u is the fractional level
    - y is an element of the extended affine Weyl group
    - Λ ∈ P̂_+^{p-h^∨} are dominant integral weights of level p - h^∨
    - D is the null root (or derivation operator)
    - The dot action is: w.λ = w(λ + ρ̂) - ρ̂

References:
    - Kac, V. G., Wakimoto, M. "On rationality of W-algebras"
    - Shan, D., Xie, D., Yan, W. "Mirror symmetry for circle compactified 4d N=2 SCFTs"
"""

from typing import Any, List, Union
from fractions import Fraction
from sage.all import RootSystem, Integer

from pyw.fractional.level import FractionalLevel
from pyw.core.weyl_group import AffineWeylGroup


class PrincipalAdmissibleWeight:
    """
    Construct and verify principal admissible weights for fractional level Kac-Moody algebras.

    The principal admissible weights form a set P̂_{u,y}^k defined by:
        P̂_{u,y}^k = {y.(Λ + (k + h^∨ - p)D) | Λ ∈ P̂_+^{p-h^∨}}

    where k = -h^∨ + p/u is the fractional level, y is an element of the extended
    affine Weyl group, and Λ ranges over dominant integral weights of level p - h^∨.

    Parameters
    ----------
    fractional_level : FractionalLevel
        The fractional level k = -h^∨ + p/u. Contains the Cartan type, p, u values,
        and derived quantities like h^∨ (dual Coxeter number) and lacety.
    y : Any
        An element y of the extended affine Weyl group. This should be a Weyl
        group element obtained from AffineWeylGroup.

    Attributes
    ----------
    level : FractionalLevel
        The fractional level object containing all level-related information.
    y : Any
        The extended affine Weyl group element used to construct the principal
        admissible weight set.
    cartan_type : tuple
        The Cartan type specification (e.g., ['A', 2, 1] for affine A₂).
    p : Integer
        The numerator p from the fractional level k = -h^∨ + p/u.
    u : Integer
        The denominator u from the fractional level k = -h^∨ + p/u.
    h_vee : Integer
        The dual Coxeter number h^∨ of the underlying Cartan type.
    weight_space : Any
        The extended weight space for the affine Kac-Moody algebra.
    fundamental_weights : Any
        The fundamental weights Λ₀, Λ₁, ..., Λₙ in the extended weight space.
    rho_hat : Any
        The affine Weyl vector ρ̂ used in the dot action.

    Examples
    --------
    >>> from pyw.fractional import FractionalLevel, PrincipalAdmissibleWeight
    >>> from pyw.core.weyl_group import AffineWeylGroup
    >>> from sage.all import RootSystem
    >>>
    >>> # Create a fractional level
    >>> level = FractionalLevel(['A', 2, 1], p=4, u=3)
    >>> print(f"Level: {level.level}")  # k = -5/3
    >>>
    >>> # Get a Weyl group element (identity for simplicity)
    >>> W = AffineWeylGroup(['A', 2, 1])
    >>> y = W.weyl_group.one()  # Identity element
    >>>
    >>> # Construct principal admissible weight set
    >>> paw = PrincipalAdmissibleWeight(level, y)
    >>> principal_set = paw.construct_principal_weights()
    >>> print(f"Principal admissible weights: {len(principal_set)} elements")
    >>>
    >>> # Create a test weight
    >>> R = RootSystem(['A', 2, 1])
    >>> P = R.weight_space(extended=True)
    >>> Lambda = P.fundamental_weights()
    >>> test_weight = Lambda[0]
    >>>
    >>> # Check if it's principal admissible
    >>> is_allowed = paw.is_principal_admissible(test_weight)
    >>> print(f"Is principal admissible: {is_allowed}")

    Notes
    -----
    The dot action w.λ = w(λ + ρ̂) - ρ̂ is central to the definition of
    principal admissible weights. This action preserves integrality and
    positivity properties essential for representation theory.

    For non-degenerate principal admissible weights, the additional condition
    (λ|α) ∉ Z must hold for all α ∈ Δ^∨.
    """

    def __init__(self, fractional_level: FractionalLevel, y: Any) -> None:
        """
        Initialize a PrincipalAdmissibleWeight instance.

        Parameters
        ----------
        fractional_level : FractionalLevel
            The fractional level k = -h^∨ + p/u. Must satisfy constraints:
                - (p, u) = 1 (coprime)
                - (u, ℓ) = 1 where ℓ is the lacety
                - p ≥ h^∨
        y : Any
            An element y of the extended affine Weyl group. This should be
            a Weyl group element from AffineWeylGroup.weyl_group.

        Raises
        ------
        TypeError
            If fractional_level is not a FractionalLevel instance.
        """
        # Validate fractional_level type
        if not isinstance(fractional_level, FractionalLevel):
            raise TypeError(
                f"fractional_level must be a FractionalLevel instance, got {type(fractional_level)}"
            )

        self.level = fractional_level
        self.y = y

        # Extract Cartan type and level parameters
        self.cartan_type = self.level.cartan_type
        self.p = self.level.p
        self.u = self.level.u
        self.h_vee = self.level.h_vee

        # Initialize weight space structures
        self._setup()

    def _setup(self) -> None:
        """
        Initialize the weight space and related structures.

        This method creates the extended weight space, fundamental weights,
        and affine Weyl vector needed for dot action calculations.
        """
        # Create extended weight space (essential for fractional weights)
        R = RootSystem(self.cartan_type)
        self.weight_space = R.weight_space(extended=True)

        # Get fundamental weights Λ₀, Λ₁, ..., Λₙ
        self.fundamental_weights = self.weight_space.fundamental_weights()

        # Get affine Weyl vector ρ̂ = Σ Λ_i (sum of all fundamental weights)
        self.rho_hat = self.weight_space.rho()

    def construct_principal_weights(self, max_fundamental_coeff: int = 5) -> List[Any]:
        """
        Construct the set P̂_{u,y}^k of principal admissible weights.

        The set is defined as:
            P̂_{u,y}^k = {y.(Λ + (k + h^∨ - p)D) | Λ ∈ P̂_+^{p-h^∨}}

        where Λ ∈ P̂_+^{p-h^∨} are dominant integral weights of level p - h^∨.
        Since computing all such weights is infinite, we restrict to weights
        where each fundamental weight coefficient ≤ max_fundamental_coeff.

        Parameters
        ----------
        max_fundamental_coeff : int, optional (default=5)
            Maximum coefficient for each fundamental weight when constructing
            Λ. This bounds the number of weights generated, as the set P̂_+^{p-h^∨}
            is infinite. Increase this value for more comprehensive construction.

        Returns
        -------
        List[Any]
            A list of principal admissible weights y.(Λ + (k + h^∨ - p)D)
            computed from the bounded subset of dominant integral weights.

        Examples
        --------
        >>> from pyw.fractional import FractionalLevel, PrincipalAdmissibleWeight
        >>> from pyw.core.weyl_group import AffineWeylGroup
        >>>
        >>> level = FractionalLevel(['A', 2, 1], p=4, u=3)
        >>> W = AffineWeylGroup(['A', 2, 1])
        >>> y = W.weyl_group.one()
        >>> paw = PrincipalAdmissibleWeight(level, y)
        >>>
        >>> # Construct set with small bound for demonstration
        >>> principal_set = paw.construct_principal_weights(max_fundamental_coeff=2)
        >>> print(f"Found {len(principal_set)} principal admissible weights")

        Notes
        -----
        The term (k + h^∨ - p)D in the formula represents a null direction.
        Since k + h^∨ = p/u, this becomes (p/u - p)D = p(1/u - 1)D.

        For actual computation with SageMath, the null root D is typically
        handled implicitly through the extended weight space structure.
        """
        principal_weights = []

        # The level for Λ ∈ P̂_+^{p-h^∨}
        lambda_level = self.p - self.h_vee

        # Compute the coefficient for the null direction: (k + h^∨ - p) = p/u - p
        null_coeff = Fraction(to_python_int(self.p), to_python_int(self.u)) - to_python_int(self.p)

        # Generate dominant integral weights of level p - h^∨
        # This is a bounded subset of the infinite set
        dominant_weights = self._generate_dominant_weights(
            lambda_level, max_coeff=max_fundamental_coeff
        )

        # Apply y using dot action to each weight
        for lambda_weight in dominant_weights:
            # Construct Λ + (k + h^∨ - p)D
            # The null direction D is Λ_0 (the affine fundamental weight)
            weight_with_null = lambda_weight + null_coeff * self.fundamental_weights[0]

            # Apply dot action: y.weight = y(weight + ρ̂) - ρ̂
            principal_weight = self.apply_y_dot_action(weight_with_null)

            principal_weights.append(principal_weight)

        return principal_weights

    def _generate_dominant_weights(self, level: int, max_coeff: int = 5) -> List[Any]:
        """
        Generate dominant integral weights of specified level.

        Parameters
        ----------
        level : int
            The level constraint: Σ a_i Λ_i must satisfy Σ a_i = level.
        max_coeff : int, optional (default=5)
            Maximum coefficient for each fundamental weight.

        Returns
        -------
        List[Any]
            List of dominant integral weights满足 the level constraint.

        Notes
        -----
        This generates a finite subset of the infinite set P̂_+^{level}.
        For practical computation, we use a bounding parameter.
        """
        # Get the index set (0, 1, ..., n for affine type X_n^(1))
        index_set = list(self.weight_space.index_set())
        n = max(index_set)

        dominant_weights = []

        # Simple recursive generation of partitions
        # This is a basic implementation; for production use, consider
        # more sophisticated algorithms or SageMath built-ins
        def generate(coefficients, remaining_level, position):
            """
            Recursively generate weight coefficients.

            Parameters
            ----------
            coefficients : List[int]
                Current coefficients being built.
            remaining_level : int
                Remaining level to distribute.
            position : int
                Current position in the index set.
            """
            if position == n:
                # Last coefficient is forced by level constraint
                if 0 <= remaining_level <= max_coeff:
                    final_coefficients = coefficients + [remaining_level]
                    weight = self.weight_space.zero()
                    for i, coef in enumerate(final_coefficients):
                        weight += coef * self.fundamental_weights[i]
                    dominant_weights.append(weight)
                return

            # Try all valid coefficients for current position
            for coef in range(0, min(max_coeff, remaining_level) + 1):
                generate(coefficients + [coef], remaining_level - coef, position + 1)

        # Start generation
        generate([], level, 0)

        return dominant_weights

    def apply_y_dot_action(self, weight: Any) -> Any:
        """
        Apply the dot action of y to a weight.

        The dot action is defined as:
            y.λ = y(λ + ρ̂) - ρ̂

        This action is essential for principal admissible weight construction
        and appears throughout the Kac-Wakimoto theory.

        Parameters
        ----------
        weight : Any
            A weight in the extended weight space.

        Returns
        -------
        Any
            The result of the dot action y.weight.

        Examples
        --------
        >>> from pyw.fractional import FractionalLevel, PrincipalAdmissibleWeight
        >>> from pyw.core.weyl_group import AffineWeylGroup
        >>> from sage.all import RootSystem
        >>>
        >>> level = FractionalLevel(['A', 2, 1], p=4, u=3)
        >>> W = AffineWeylGroup(['A', 2, 1])
        >>> y = W.weyl_group.simple_reflection(0)
        >>>
        >>> paw = PrincipalAdmissibleWeight(level, y)
        >>>
        >>> R = RootSystem(['A', 2, 1])
        >>> P = R.weight_space(extended=True)
        >>> Lambda = P.fundamental_weights()
        >>> test_weight = Lambda[0]
        >>>
        >>> result = paw.apply_y_dot_action(test_weight)
        >>> print(f"y.{test_weight} = {result}")

        Notes
        -----
        The dot action differs from the standard Weyl group action:
            - Standard action: w(λ)
            - Dot action: w.λ = w(λ + ρ̂) - ρ̂

        The dot action has better integrality properties and is used
        throughout representation theory of Kac-Moody algebras.
        """
        # Compute λ + ρ̂
        shifted_weight = weight + self.rho_hat

        # Apply y to (λ + ρ̂)
        y_shifted = self.y.action(shifted_weight)

        # Compute y.λ = y(λ + ρ̂) - ρ̂
        result = y_shifted - self.rho_hat

        return result

    def is_principal_admissible(self, weight: Any) -> bool:
        """
        Check if a weight is in the principal admissible weight set P̂_{u,y}^k.

        A weight λ is principal admissible if there exists Λ ∈ P̂_+^{p-h^∨}
        such that λ = y.(Λ + (k + h^∨ - p)D).

        Parameters
        ----------
        weight : Any
            A weight in the extended weight space to test for principal
            admissibility.

        Returns
        -------
        bool
            True if the weight is principal admissible, False otherwise.

        Examples
        --------
        >>> from pyw.fractional import FractionalLevel, PrincipalAdmissibleWeight
        >>> from pyw.core.weyl_group import AffineWeylGroup
        >>> from sage.all import RootSystem
        >>>
        >>> level = FractionalLevel(['A', 2, 1], p=4, u=3)
        >>> W = AffineWeylGroup(['A', 2, 1])
        >>> y = W.weyl_group.one()
        >>>
        >>> paw = PrincipalAdmissibleWeight(level, y)
        >>>
        >>> R = RootSystem(['A', 2, 1])
        >>> P = R.weight_space(extended=True)
        >>> Lambda = P.fundamental_weights()
        >>>
        >>> # Check a weight from the set
        >>> test_weight = paw.apply_y_dot_action(Lambda[0])
        >>> is_admissible = paw.is_principal_admissible(test_weight)
        >>> print(f"Is principal admissible: {is_admissible}")

        Notes
        -----
        This method requires computing the inverse of the dot action.
        In practice, this involves solving y^(-1).λ ∈ {Λ + (k + h^∨ - p)D}.

        Since P̂_+^{p-h^∨} is infinite, we use a bounded search with
        a reasonable coefficient bound. Increase max_fundamental_coeff
        for more thorough checking.
        """
        # Apply inverse dot action: y^(-1).λ = y^(-1)(λ + ρ̂) - ρ̂
        y_inverse = self.y.inverse()

        shifted_weight = weight + self.rho_hat
        y_inv_shifted = y_inverse.action(shifted_weight)
        lambda_candidate = y_inv_shifted - self.rho_hat

        # Compute the coefficient for the null direction: (k + h^∨ - p) = p/u - p
        null_coeff = Fraction(to_python_int(self.p), to_python_int(self.u)) - to_python_int(self.p)

        # Remove null component: λ' = λ - (k + h^∨ - p)D
        # This should give a dominant integral weight of level p - h^∨
        lambda_without_null = lambda_candidate - null_coeff * self.fundamental_weights[0]

        # Check if λ_without_null is dominant and has level p - h^∨
        # For simplicity, we check if coefficients are non-negative integers
        # and sum to p - h^∨ (within floating-point tolerance)

        try:
            # Get coefficients
            coefficients = []
            for i in range(len(self.fundamental_weights)):
                # Extract coefficient for Λ_i
                coef_i = lambda_without_null.coefficient(self.fundamental_weights[i])
                coefficients.append(coef_i)

            # Check if all coefficients are non-negative integers
            lambda_level = to_python_int(self.p) - to_python_int(self.h_vee)
            sum_coeff = sum(coef_i for coef_i in coefficients)

            # Verify conditions:
            # 1. All coefficients are non-negative integers
            # 2. Sum equals p - h^∨
            if all(coef >= 0 and coef == int(coef) for coef in coefficients):
                if sum_coeff == lambda_level:
                    return True

        except (AttributeError, TypeError, ValueError):
            # If we can't extract coefficients, it's not admissible
            pass

        return False

    def __repr__(self) -> str:
        """
        Return a string representation of PrincipalAdmissibleWeight.

        Returns
        -------
        str
            String representation showing the level and Weyl group element.
        """
        return f"PrincipalAdmissibleWeight(fractional_level={self.level}, y={self.y})"

    def __str__(self) -> str:
        """
        Return a user-friendly string representation.

        Returns
        -------
        str
            Detailed string showing level parameters and Cartan type.
        """
        return (
            f"Principal admissible weights for {self.level.level} "
            f"({self.level.cartan_type}, p={self.p}, u={self.u})"
        )


def to_python_int(sage_int: Integer) -> int:
    """
    Convert a SageMath Integer to a Python int.

    Parameters
    ----------
    sage_int : Integer
        A SageMath Integer object.

    Returns
    -------
    int
        The corresponding Python integer.
    """
    return int(sage_int)
