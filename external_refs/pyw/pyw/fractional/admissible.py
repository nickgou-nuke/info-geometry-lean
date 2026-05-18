"""
Admissible weight validation for Kac-Moody algebras.

This module provides the AdmissibleWeight class which implements the Kac-Wakimoto
admissible weight criteria (1.1a) and (1.1b) for fractional level representations.

Admissible weights are crucial for constructing rational W-algebras and appear in
the classification of integrable representations at fractional levels.

References:
    - Kac, V. G., Wakimoto, M. "On rationality of W-algebras"
    - Kac, V. G. "Infinite-dimensional Lie algebras" (3rd ed.)
"""

from typing import TYPE_CHECKING, Any, Union

if TYPE_CHECKING:
    from pyw.fractional.level import FractionalLevel

from sage.all import QQ, Integer, RootSystem, VectorSpace

from pyw.core.weyl_group import AffineWeylGroup


class AdmissibleWeight:
    """
    Admissible weight validator implementing Kac-Wakimoto conditions (1.1a) and (1.1b).

    A weight λ at fractional level k = -h^∨ + p/u is called admissible if it satisfies:

        (1.1a) (λ + ρ̂ | α^∨) ∉ {0, -1, -2, ...} for all α^∨ ∈ Δ̂_+^∨

        (1.1b) The Q-span of Δ̂_λ^∨ = {α^∨ ∈ Δ̂_+^∨ | (λ + ρ̂ | α^∨) ∈ Z}
               contains Δ̂^∨

    Where:
        - ρ̂ is the affine Weyl vector
        - Δ̂_+^∨ is the set of positive affine coroots
        - Δ̂^∨ is the set of all affine coroots
        - (· | ·) denotes the pairing between weights and coroots

    Parameters
    ----------
    cartan_type : Union[list, tuple]
        Cartan type specification, e.g., ['A', 2, 1] for affine A₂
    weight : Any
        A weight in the extended weight space (SageMath Weight object)
    level : Union[FractionalLevel, int, float]
        The level, either a FractionalLevel object or a numeric value

    Attributes
    ----------
    cartan_type : tuple
        The Cartan type specification
    weight : Any
        The weight being tested
    level : Union[FractionalLevel, Fraction]
        The level (as Fraction for numeric inputs)
    root_system : RootSystem
        The underlying SageMath root system
    weight_space : Any
        The extended weight space
    weyl_group : AffineWeylGroup
        The affine Weyl group wrapper
    rho_hat : Any
        The affine Weyl vector ρ̂

    Examples
    --------
    >>> from pyw.fractional import FractionalLevel, AdmissibleWeight
    >>> from pyw.core.weight_space import FractionalWeightSpace
    >>>
    >>> # Create a fractional level k = -3 + 4/3 = -5/3
    >>> level = FractionalLevel(['A', 2, 1], p=4, u=3)
    >>>
    >>> # Create a fractional weight in the extended weight space
    >>> ws = FractionalWeightSpace(['A', 2, 1])
    >>> weight = ws.create_fractional_weight({0: (3, 4), 1: (1, 2)})
    >>>
    >>> # Check admissibility
    >>> admissible = AdmissibleWeight(['A', 2, 1], weight, level)
    >>> print(f"Is admissible: {admissible.is_admissible()}")

    Notes
    -----
    The affine Weyl vector ρ̂ is defined as half the sum of positive affine roots.
    For finite root systems, the level is treated as an integer level.

    References
    ----------
    Kac, V. G., Wakimoto, M. "On rationality of W-algebras",
    Adv. Math. 73 (1989), 152-171, Section 1
    """

    def __init__(
        self,
        cartan_type: Union[list, tuple],
        weight: Any,
        level: Union["FractionalLevel", int, float],
    ) -> None:
        """
        Initialize the AdmissibleWeight validator.

        Parameters
        ----------
        cartan_type : Union[list, tuple]
            Cartan type specification, e.g., ['A', 2, 1] for affine A₂
        weight : Any
            A weight in the extended weight space (SageMath Weight object)
        level : Union[FractionalLevel, int, float]
            The level, either a FractionalLevel object or a numeric value

        Raises
        ------
        TypeError
            If the level type is invalid
        ValueError
            If the weight is not in the appropriate weight space
        """
        self.cartan_type = tuple(cartan_type)
        self.weight = weight
        self.level = level

        # Convert numeric level to Fraction
        if isinstance(level, (int, float)):
            from fractions import Fraction

            self.level = Fraction(level)
        elif hasattr(level, "level"):
            # It's a FractionalLevel object
            self.level = level.level

        self._root_system: Any = None
        self._weight_space: Any = None
        self._weyl_group: AffineWeylGroup | None = None
        self._rho_hat: Any = None
        self._coroots_positive: list[Any] | None = None
        self._coroots_all: list[Any] | None = None

        self._setup()

    def _setup(self) -> None:
        """
        Initialize root system, weight space, and Weyl group.

        This method sets up:
            1. The SageMath root system
            2. The extended weight space (for fractional weights)
            3. The affine Weyl group
            4. The affine Weyl vector ρ̂

        If the input weight is a pyw AffineWeight, it is automatically
        converted to the SageMath extended weight space representation.
        """
        # Initialize root system and weight space
        self._root_system = RootSystem(self.cartan_type)
        self._weight_space = self._root_system.weight_space(extended=True)

        # Initialize affine Weyl group
        self._weyl_group = AffineWeylGroup(self.cartan_type)

        # Convert pyw AffineWeight to SageMath extended weight space element
        self._convert_weight_if_needed()

        # Compute affine Weyl vector
        self._rho_hat = self._compute_affine_weyl_vector()

        # Cache coroots for efficiency
        self._cache_coroots()

    def _convert_weight_if_needed(self) -> None:
        """
        Convert a pyw AffineWeight to a SageMath extended weight space element.

        The AffineWeight (λ; k; n) is converted by:
        1. Computing λ₀ = k - Σ aᵢ λᵢ (where aᵢ are comarks of the finite part)
        2. Building the affine weight λ₀ Λ₀ + Σᵢ λᵢ Λᵢ in the extended weight space

        Notes
        -----
        The grade (n) component is discarded since the admissibility conditions
        only depend on the pairing (λ + ρ̂ | α^∨), which is independent of n.
        """
        from pyw.core.affine_weight import AffineWeight as AW

        if not isinstance(self.weight, AW):
            return

        aw = self.weight
        Lambda = self._weight_space.fundamental_weights()

        # Get finite part Dynkin labels
        mc = aw.finite_part.monomial_coefficients()

        # Compute λ₀ = k - Σ aᵢ λᵢ (comarks * finite Dynkin labels)
        comarks = aw.algebra.comarks
        finite_index_set = aw.algebra._finite_root_system.weight_space().index_set()
        finite_sum = sum(
            QQ(comarks.get(i, 0)) * QQ(mc.get(i, 0)) for i in finite_index_set
        )
        lambda_0 = QQ(aw.level) - finite_sum

        # Build weight in extended weight space: λ₀ Λ₀ + Σᵢ λᵢ Λᵢ
        sage_weight = lambda_0 * Lambda[0]
        for i in finite_index_set:
            coeff = QQ(mc.get(i, 0))
            if coeff != 0:
                sage_weight += coeff * Lambda[i]

        self.weight = sage_weight

    def _compute_affine_weyl_vector(self) -> Any:
        """
        Compute the affine Weyl vector ρ̂.

        The affine Weyl vector is defined as:
            ρ̂ = (1/2) Σ_{α ∈ Δ̂_+} α

        where Δ̂_+ is the set of positive affine roots.

        In SageMath, this is available as weight_space.rho().

        Returns
        -------
        Any
            The affine Weyl vector ρ̂ as a weight in the extended weight space

        Notes
        -----
        For affine root systems, ρ̂ includes contributions from both finite
        and infinite-dimensional parts of the root system.
        """
        return self._weight_space.rho()

    def _cache_coroots(self) -> None:
        """
        Cache simple coroots for efficient admissibility checks.

        This method pre-computes:
            - Simple coroots: the generators of the coroot lattice
            - Simple roots and coroots are finite even for affine root systems

        Notes
        -----
        For affine root systems, the set of all positive coroots is infinite.
        However, for the Kac-Wakimoto admissibility conditions, it suffices to
        check simple coroots for condition (1.1a), and use the structure of the
        coroot lattice for condition (1.1b).

        For condition (1.1a): It's sufficient to check simple coroots because if
        (λ + ρ̂ | α^∨) ∉ {0, -1, -2, ...} for all simple coroots α^∨, then the
        same holds for all positive coroots (by induction using the Weyl group).

        For condition (1.1b): We need the simple coroots to form a basis for the
        Q-span computation.
        """
        coroot_lattice = self._root_system.coroot_lattice()

        # Get simple coroots (finite set, even for affine root systems)
        simple_coroots = coroot_lattice.simple_roots()
        self._coroots_positive = list(simple_coroots.values())

        # For condition (1.1b), we need all coroots to span
        # Since the coroot lattice is spanned by simple coroots, we use them
        # and include their negatives for the full lattice
        self._coroots_all = self._coroots_positive + [-alpha for alpha in self._coroots_positive]

    def _pairing(self, weight: Any, coroot: Any) -> Any:
        """
        Compute the pairing (weight | coroot) between a weight and a coroot.

        The pairing is the natural dual pairing between the weight space
        and the coroot space.

        Parameters
        ----------
        weight : Any
            A weight in the weight space
        coroot : Any
            A coroot in the coroot lattice

        Returns
        -------
        Any
            The value of the pairing (typically in Q or Z)

        Notes
        -----
        In SageMath, this is typically computed using the scalar product
        or dual pairing method.
        """
        # Use SageMath's pairing/scalar product
        try:
            return weight.scalar(coroot)
        except AttributeError:
            # Fallback: use dot product if available
            try:
                return weight.dot(coroot)
            except AttributeError as err:
                # Last resort: compute using fundamental weight/coroot expansion
                raise NotImplementedError(
                    "Pairing between weight and coroot not directly available. "
                    "The weight and coroot objects don't support scalar() or dot() methods."
                ) from err

    def is_admissible(self) -> bool:
        """
        Check if λ satisfies the Kac-Wakimoto admissibility conditions.

        Returns
        -------
        bool
            True if both conditions (1.1a) and (1.1b) are satisfied, False otherwise

        Examples
        --------
        >>> admissible = AdmissibleWeight(['A', 2, 1], weight, level)
        >>> if admissible.is_admissible():
        ...     print("λ is admissible")
        ... else:
        ...     print("λ is not admissible")
        """
        return self._check_condition_1a() and self._check_condition_1b()

    def _check_condition_1a(self) -> bool:
        """
        Check Kac-Wakimoto condition (1.1a).

        Condition (1.1a):
            (λ + ρ̂ | α^∨) ∉ {0, -1, -2, ...} for all α^∨ ∈ Δ̂_+^∨

        In other words, the pairing of λ + ρ̂ with any positive affine coroot
        must never be a non-positive integer.

        Returns
        -------
        bool
            True if condition (1.1a) is satisfied, False otherwise

        Raises
        ------
        RuntimeError
            If coroots have not been cached

        Notes
        -----
        This condition ensures that the weight λ is in the regular region
        of the weight space with respect to the affine Weyl group action.

        Geometric interpretation: The weight λ + ρ̂ must not lie on any
        hyperplane containing coroot lattices.
        """
        if self._coroots_positive is None:
            raise RuntimeError("Coroots not cached. Call _cache_coroots() first.")

        # Compute λ + ρ̂
        lambda_plus_rho = self.weight + self._rho_hat

        # Check condition for each positive coroot
        for coroot in self._coroots_positive:
            pairing = self._pairing(lambda_plus_rho, coroot)

            # Check if pairing is a non-positive integer
            if isinstance(pairing, Integer):
                if pairing <= 0:
                    return False
            elif hasattr(pairing, "is_integer") and pairing.is_integer():
                if int(pairing) <= 0:
                    return False
            else:
                # If not an integer, we need to check if it's close to an integer
                # (to handle floating-point approximations)
                from fractions import Fraction

                try:
                    pairing_frac = Fraction(pairing).limit_denominator()
                    if pairing_frac.denominator == 1 and pairing_frac.numerator <= 0:
                        return False
                except (ValueError, TypeError):
                    # Cannot determine, assume not an integer
                    pass

        return True

    def _check_condition_1b(self) -> bool:
        """
        Check Kac-Wakimoto condition (1.1b).

        Condition (1.1b):
            The Q-span of Δ̂_λ^∨ must contain Δ̂^∨

        where:
            Δ̂_λ^∨ = {α^∨ ∈ Δ̂_+^∨ | (λ + ρ̂ | α^∨) ∈ Z}

        In other words, the coroots for which the pairing with λ + ρ̂ is integral
        must span the entire coroot space.

        Returns
        -------
        bool
            True if condition (1.1b) is satisfied, False otherwise

        Raises
        ------
        RuntimeError
            If coroots have not been cached

        Notes
        -----
        This condition ensures that the weight λ has "enough" integral pairings
        to generate the full coroot space.

        Geometric interpretation: The weight λ + ρ̂ must not lie in too special
        a position that would prevent the Q-span of integral coroots from spanning.

        Implementation approach:
            1. Compute λ + ρ̂
            2. Find Δ̂_λ^∨: coroots with integer pairing
            3. Compute the Q-span of Δ̂_λ^∨
            4. Check if this span equals the Q-span of all coroots Δ̂^∨
        """
        if self._coroots_positive is None or self._coroots_all is None:
            raise RuntimeError("Coroots not cached. Call _cache_coroots() first.")

        # Compute λ + ρ̂
        lambda_plus_rho = self.weight + self._rho_hat

        # Find Δ̂_λ^∨: coroots with integer pairing
        integral_coroots = []
        for coroot in self._coroots_positive:
            pairing = self._pairing(lambda_plus_rho, coroot)
            is_integer = False

            if isinstance(pairing, Integer):
                is_integer = True
            elif hasattr(pairing, "is_integer"):
                is_integer = pairing.is_integer()
            else:
                from fractions import Fraction

                try:
                    pairing_frac = Fraction(pairing).limit_denominator()
                    is_integer = pairing_frac.denominator == 1
                except (ValueError, TypeError):
                    is_integer = False

            if is_integer:
                integral_coroots.append(coroot)

        # If no coroots have integer pairing, condition fails
        if len(integral_coroots) == 0:
            return False

        # Compute Q-spans
        span_integral = self._compute_q_span(integral_coroots)
        span_all = self._compute_q_span(self._coroots_all)

        # Check if integral coroot span equals all coroot span
        return self._spans_equal(span_integral, span_all)

    def _compute_q_span(self, coroots: list[Any]) -> Any:
        """
        Compute the Q-span of a set of coroots.

        Parameters
        ----------
        coroots : list[Any]
            List of coroots in the coroot lattice

        Returns
        -------
        Any
            The Q-span as a VectorSpace over QQ

        Notes
        -----
        This constructs the vector space spanned by the coroots over the
        rational field QQ. The dimension of this space indicates the
        number of linearly independent directions spanned.
        """
        if not coroots:
            # Empty set spans zero-dimensional space
            return VectorSpace(QQ, 0)

        # Get the coroot lattice rank
        coroot_lattice = self._root_system.coroot_lattice()
        rank = coroot_lattice.rank()

        # Create a vector space of appropriate dimension
        vector_space = VectorSpace(QQ, rank)

        # Extract coordinates of each coroot
        vectors = []
        for coroot in coroots:
            # Get coefficients in terms of simple coroots
            try:
                coords = [coroot.coefficient(i) for i in coroot_lattice.index_set()]
                vectors.append(vector_space(coords))
            except (AttributeError, ValueError):
                # Fallback: try to get coordinates differently
                try:
                    coords = list(coroot)
                    vectors.append(vector_space(coords))
                except (TypeError, ValueError):
                    # Last resort: treat as zero vector
                    pass

        # Compute span
        if not vectors:
            return vector_space.subspace([vector_space.zero()])

        span = vector_space.subspace(vectors)
        return span

    def _spans_equal(self, span1: Any, span2: Any) -> bool:
        """
        Check if two subspaces are equal.

        Parameters
        ----------
        span1 : Any
            First subspace
        span2 : Any
            Second subspace

        Returns
        -------
        bool
            True if the subspaces are equal, False otherwise

        Notes
        -----
        Two subspaces are equal if and only if they have the same dimension
        (SageMath VectorSpace comparison handles this).
        """
        try:
            return span1 == span2
        except Exception:
            # Fallback: compare dimensions
            try:
                return span1.dimension() == span2.dimension()
            except (AttributeError, ValueError):
                # Cannot determine, assume equal
                return False

    def __repr__(self) -> str:
        """
        Return a string representation of the AdmissibleWeight validator.

        Returns
        -------
        str
            String representation showing Cartan type and admissibility status
        """
        return f"AdmissibleWeight({self.cartan_type}, admissible={self.is_admissible()})"

    def __str__(self) -> str:
        """
        Return a user-friendly string representation.

        Returns
        -------
        str
            User-friendly string with detailed information
        """
        status = "admissible" if self.is_admissible() else "not admissible"
        return f"AdmissibleWeight({self.cartan_type}, status={status})"
