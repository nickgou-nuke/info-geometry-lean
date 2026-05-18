"""
Affine Weight Class with Di Francesco Convention

This module provides the AffineWeight class for representing and manipulating
affine weights using the Di Francesco notation system:

    ̂λ = (λ; k_λ; n_λ)

where:
    - λ is the finite part (a weight in the finite weight space)
    - k_λ is the level (grade with respect to the central element k̂)
    - n_λ is the L₀ eigenvalue (grade with respect to -L₀)

This notation corresponds to Di Francesco, Mathieu, Sénéchal - "Conformal Field Theory"
Chapter 14, particularly Eq. (14.22)-(14.23).

Notation Systems
----------------
1. **Di Francesco (DFrancesco)**: ̂λ = (λ; k; n)
   - Used in CFT literature
   - Explicit finite/level/L₀ decomposition
   - Affine fundamental weights: ̂Λ_i = (Λ_i; 1; 0)

2. **SageMath (Standard)**: λ = Σ λ_i Λ_i
   - Uses affine weight lattice directly
   - Level computed from Dynkin labels: k = Σ a_i^∨ λ_i
   - No explicit L₀ eigenvalue tracking

Conversion Methods
------------------
- from_sagemath(): Convert SageMath affine weight to AffineWeight (with n=0 default)
- to_sagemath(): Convert AffineWeight back to SageMath weight (ignoring n)

References
----------
- Di Francesco et al., Chapter 14, Eqs. (14.22), (14.23), (14.63), (14.64), (14.69)
- Kac, V. G., "Infinite-dimensional Lie algebras" (3rd ed.), Chapter 6
"""

from __future__ import annotations
from typing import TYPE_CHECKING, Union, Optional, Dict, Any, Tuple
from fractions import Fraction
from sage.all import RootSystem, QQ, ZZ, Integer

if TYPE_CHECKING:
    from .affine_lie_algebra import AffineLieAlgebra


# =============================================================================
# LaTeX Formatting Helpers
# =============================================================================


def _rational_to_latex(value: Any) -> str:
    """
    Convert a rational number to LaTeX representation.

    Parameters
    ----------
    value : Rational or int
        The value to convert

    Returns
    -------
    str
        LaTeX representation (e.g., "1", "-2", "\\frac{1}{2}")
    """
    if hasattr(value, "numerator") and hasattr(value, "denominator"):
        num = value.numerator()
        den = value.denominator()
        if den == 1:
            return str(num)
        else:
            sign = "-" if num < 0 else ""
            return f"{sign}\\frac{{{abs(num)}}}{{{den}}}"
    return str(value)


def _rational_to_legacy(value: Any) -> str:
    if hasattr(value, "numerator") and hasattr(value, "denominator"):
        num = value.numerator()
        den = value.denominator()
        if den == 1:
            return str(num)
        return f"{num}/{den}"
    return str(value)


def _weight_to_latex(weight: Any) -> str:
    """
    Convert a SageMath weight to LaTeX representation.

    Converts "Lambda[1]" to "\\Lambda_1", handles linear combinations,
    and properly formats coefficients.

    Parameters
    ----------
    weight : SageMath weight element
        The weight to convert (from weight_space or weight_lattice)

    Returns
    -------
    str
        LaTeX representation (e.g., "\\Lambda_1", "2\\Lambda_1 + \\Lambda_2")
    """
    if weight == 0 or (hasattr(weight, "is_zero") and weight.is_zero()):
        return "0"

    # Get monomial coefficients: {index: coefficient}
    mc = weight.monomial_coefficients()

    if not mc:
        return "0"

    # Determine the symbol based on parent type
    # Check the parent class name, not the string representation
    parent = weight.parent()
    parent_class_name = type(parent).__name__.lower()

    # Root space/lattice uses alpha, weight space/lattice uses Lambda
    if "root" in parent_class_name:
        symbol = "\\alpha"
    else:
        symbol = "\\Lambda"

    # Build LaTeX terms
    terms = []
    for idx in sorted(mc.keys()):
        coeff = mc[idx]
        if coeff == 0:
            continue

        # Format coefficient
        coeff_latex = _rational_to_latex(coeff)

        # Build term
        if coeff == 1:
            term = f"{symbol}_{{{idx}}}"
        elif coeff == -1:
            term = f"-{symbol}_{{{idx}}}"
        else:
            # Handle fractional coefficients
            if hasattr(coeff, "denominator") and coeff.denominator() != 1:
                term = f"{coeff_latex}{symbol}_{{{idx}}}"
            else:
                term = f"{coeff_latex}{symbol}_{{{idx}}}"

        terms.append(term)

    if not terms:
        return "0"

    # Join terms with proper signs
    result = terms[0]
    for term in terms[1:]:
        if term.startswith("-"):
            result += f" {term}"
        else:
            result += f" + {term}"

    return result


class AffineWeight:
    """
    An affine weight in Di Francesco notation: ̂λ = (λ; k; n).

    This class encapsulates an affine weight with its three components:
    - finite_part: The finite weight λ (in the finite weight lattice/space)
    - level: The level k = ̂λ(k̂)
    - grade: The L₀ eigenvalue n = ̂λ(-L₀)

    The class supports:
    - Arithmetic operations (+, -, scalar multiplication)
    - Affine scalar product using Di Francesco Eq. (14.23)
    - Conversion to/from SageMath affine weights
    - Weyl reflections and translations

    Parameters
    ----------
    algebra : AffineLieAlgebra
        The affine Lie algebra context
    finite_part : weight
        The finite part λ of the affine weight
    level : number
        The level k (default: 0)
    grade : number
        The L₀ eigenvalue n (default: 0)

    Examples
    --------
    >>> from pyw.core.affine_lie_algebra import AffineLieAlgebra
    >>> from pyw.core.affine_weight import AffineWeight
    >>> ala = AffineLieAlgebra(['A', 2, 1])
    >>> Lambda = ala.fundamental_weights()
    >>> # Create Di Francesco affine weight ̂Λ₁ = (Λ₁; 1; 0)
    >>> w = AffineWeight(ala, Lambda[1], level=1, grade=0)
    >>> print(w)  # Shows Di Francesco notation

    Attributes
    ----------
    algebra : AffineLieAlgebra
        The affine Lie algebra context
    finite_part : weight
        The finite part λ
    level : Rational
        The level k
    grade : Rational
        The L₀ eigenvalue n
    """

    def __init__(
        self,
        algebra: "AffineLieAlgebra",
        finite_part: Any,
        level: Union[int, Fraction, Any] = 0,
        grade: Union[int, Fraction, Any] = 0,
    ) -> None:
        """
        Initialize an AffineWeight in Di Francesco notation.

        Parameters
        ----------
        algebra : AffineLieAlgebra
            The affine Lie algebra providing context
        finite_part : weight
            The finite part λ (SageMath weight or zero)
        level : number, optional
            The level k (default: 0)
        grade : number, optional
            The L₀ eigenvalue n (default: 0)
        """
        self.algebra = algebra
        self.finite_part = finite_part
        self.level = QQ(level)
        self.grade = QQ(grade)

    # =========================================================================
    # Properties
    # =========================================================================

    # NOTE: 压平属性，不需要 ._XXXX 属性，留 .XXXX 就可以了
    @property
    def k(self) -> Any:
        """Alias for level (Di Francesco notation)."""
        return self.level

    @property
    def n(self) -> Any:
        """Alias for grade (Di Francesco notation)."""
        return self.grade

    # =========================================================================
    # Representation
    # =========================================================================

    def __repr__(self) -> str:
        """Return a string representation in Di Francesco notation."""
        return f"AffineWeight({self.finite_part}; {self.level}; {self.grade})"

    def __str__(self) -> str:
        """Return a human-readable string in Di Francesco notation."""
        return f"({self.finite_part}; {self.level}; {self.grade})"

    def _repr_latex_(self) -> str:
        """LaTeX representation for Jupyter notebooks."""
        finite_latex = _weight_to_latex(self.finite_part)
        level_latex = _rational_to_latex(self.level)
        grade_latex = _rational_to_latex(self.grade)
        return f"$({finite_latex};\\ {level_latex};\\ {grade_latex})$"

    def to_tuple(self) -> Tuple[Any, Any, Any]:
        """
        Return the weight as a tuple (λ, k, n).

        Returns
        -------
        tuple
            (finite_part, level, grade)
        """
        return (self.finite_part, self.level, self.grade)

    # =========================================================================
    # Arithmetic Operations
    # =========================================================================

    def __add__(self, other: "AffineWeight") -> "AffineWeight":
        """
        Add two affine weights.

        (λ₁; k₁; n₁) + (λ₂; k₂; n₂) = (λ₁ + λ₂; k₁ + k₂; n₁ + n₂)

        Parameters
        ----------
        other : AffineWeight
            The weight to add

        Returns
        -------
        AffineWeight
            The sum
        """
        if not isinstance(other, AffineWeight):
            return NotImplemented
        if self.algebra != other.algebra:
            raise ValueError("Cannot add weights from different algebras")

        return AffineWeight(
            self.algebra,
            self.finite_part + other.finite_part,
            self.level + other.level,
            self.grade + other.grade,
        )

    def __sub__(self, other: "AffineWeight") -> "AffineWeight":
        """
        Subtract two affine weights.

        (λ₁; k₁; n₁) - (λ₂; k₂; n₂) = (λ₁ - λ₂; k₁ - k₂; n₁ - n₂)

        Parameters
        ----------
        other : AffineWeight
            The weight to subtract

        Returns
        -------
        AffineWeight
            The difference
        """
        if not isinstance(other, AffineWeight):
            return NotImplemented
        if self.algebra != other.algebra:
            raise ValueError("Cannot subtract weights from different algebras")

        return AffineWeight(
            self.algebra,
            self.finite_part - other.finite_part,
            self.level - other.level,
            self.grade - other.grade,
        )

    def __neg__(self) -> "AffineWeight":
        """
        Negate an affine weight.

        -(λ; k; n) = (-λ; -k; -n)

        Returns
        -------
        AffineWeight
            The negation
        """
        return AffineWeight(self.algebra, -self.finite_part, -self.level, -self.grade)

    def __mul__(self, scalar: Union[int, Fraction, Any]) -> "AffineWeight":
        """
        Scalar multiplication.

        c * (λ; k; n) = (cλ; ck; cn)

        Parameters
        ----------
        scalar : number
            The scalar to multiply by

        Returns
        -------
        AffineWeight
            The scaled weight
        """
        c = QQ(scalar)
        # For SageMath weight lattice/space elements, need to use Integer ratio form
        # to ensure proper coercion
        if hasattr(self.finite_part, "parent"):
            # Use c directly - SageMath handles Integer/Integer ratios correctly
            new_finite = c * self.finite_part
        else:
            new_finite = self.finite_part * c
        return AffineWeight(self.algebra, new_finite, self.level * c, self.grade * c)

    def __rmul__(self, scalar: Union[int, Fraction, Any]) -> "AffineWeight":
        """Right multiplication by scalar."""
        return self.__mul__(scalar)

    def __truediv__(self, scalar: Union[int, Fraction, Any]) -> "AffineWeight":
        """
        Scalar division.

        (λ; k; n) / c = (λ/c; k/c; n/c)

        Parameters
        ----------
        scalar : number
            The scalar to divide by

        Returns
        -------
        AffineWeight
            The scaled weight
        """
        c = QQ(scalar)
        if c == 0:
            raise ZeroDivisionError("Cannot divide by zero")
        return AffineWeight(self.algebra, self.finite_part / c, self.level / c, self.grade / c)

    # =========================================================================
    # Equality and Hashing
    # =========================================================================

    def __eq__(self, other: object) -> bool:
        """Check equality of two affine weights."""
        if not isinstance(other, AffineWeight):
            return False
        return (
            self.algebra == other.algebra
            and self.finite_part == other.finite_part
            and self.level == other.level
            and self.grade == other.grade
        )

    def __hash__(self) -> int:
        """Hash for use in sets and dicts."""
        return hash((str(self.finite_part), float(self.level), float(self.grade)))

    # =========================================================================
    # Scalar Product (Di Francesco Eq. 14.23)
    # =========================================================================

    def scalar_product(self, other: "AffineWeight") -> Any:
        """
        Compute the affine scalar product (̂λ, ̂μ).

        Following Di Francesco Eq. (14.23):
            (̂λ, ̂μ) = (λ, μ) + k_λ n_μ + k_μ n_λ

        Parameters
        ----------
        other : AffineWeight
            The other affine weight

        Returns
        -------
        Rational
            The affine scalar product

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> Lambda = ala.fundamental_weights()
        >>> w1 = AffineWeight(ala, Lambda[1], level=1, grade=0)
        >>> w2 = AffineWeight(ala, Lambda[2], level=1, grade=0)
        >>> w1.scalar_product(w2)
        1/3

        Notes
        -----
        The formula (̂λ, ̂μ) = (λ, μ) + k_λ n_μ + k_μ n_λ ensures:
        - (δ, δ) = 0 where δ = (0; 0; 1)
        - (δ, ̂λ) = k_λ for any affine weight ̂λ
        - Reduces to finite scalar product when k = n = 0
        """
        if not isinstance(other, AffineWeight):
            raise TypeError("Expected AffineWeight")

        # Compute finite part scalar product
        finite_scalar = self.algebra.scalar_product(self.finite_part, other.finite_part)

        # Add cross terms
        cross_terms = self.level * other.grade + other.level * self.grade

        return finite_scalar + cross_terms

    def norm_squared(self) -> Any:
        """
        Compute |̂λ|² = (̂λ, ̂λ).

        Returns
        -------
        Rational
            The squared norm

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> Lambda = ala.fundamental_weights()
        >>> w = AffineWeight(ala, Lambda[1], level=1, grade=0)
        >>> w.norm_squared()  # |Λ₁|²
        """
        return self.scalar_product(self)

    # =========================================================================
    # Conversion Methods
    # =========================================================================

    @classmethod
    def from_sagemath(
        cls, algebra: "AffineLieAlgebra", sage_weight: Any, grade: Union[int, Fraction, Any] = 0
    ) -> "AffineWeight":
        """
        Create an AffineWeight from a SageMath affine weight.

        The SageMath weight is decomposed into:
        - Finite part: projection onto the finite weight sublattice
        - Level: computed from Dynkin labels using k = Σ a_i^∨ λ_i
        - Grade: provided explicitly (SageMath doesn't track this)

        Parameters
        ----------
        algebra : AffineLieAlgebra
            The affine Lie algebra
        sage_weight : weight
            A SageMath weight from the affine weight lattice
        grade : number, optional
            The L₀ eigenvalue (default: 0)

        Returns
        -------
        AffineWeight
            The corresponding Di Francesco affine weight

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> Lambda = ala.fundamental_weights()
        >>> # SageMath affine weight Λ₁
        >>> w = AffineWeight.from_sagemath(ala, Lambda[1])
        >>> print(w)  # Should show (Λ₁_finite; 1; 0)

        Notes
        -----
        The grade n is not tracked by SageMath and defaults to 0.
        This is correct for highest weight modules where the highest
        weight has n = 0.
        """
        if not algebra.is_affine:
            raise ValueError("Algebra must be affine type for this conversion")

        # Get Dynkin labels from the weight
        mc = sage_weight.monomial_coefficients()

        # Compute level from Dynkin labels: k = Σ a_i^∨ λ_i
        comarks = algebra.comarks
        level = sum(comarks.get(i, 0) * mc.get(i, 0) for i in comarks.keys())

        # Extract finite part: project onto finite weight space (indices > 0)
        # The finite part is Σ_{i>0} λ_i Λ_i where Λ_i are finite fundamental weights
        finite_rs = algebra._finite_root_system
        finite_ws = finite_rs.weight_space()
        finite_Lambda = finite_ws.fundamental_weights()

        # Build finite weight
        finite_part = finite_ws.zero()
        for i in finite_ws.index_set():
            coeff = mc.get(i, 0)
            if coeff != 0:
                finite_part += coeff * finite_Lambda[i]

        return cls(algebra, finite_part, level=level, grade=grade)

    def to_sagemath(self) -> Any:
        """
        Convert to a SageMath affine weight.

        The Di Francesco weight (λ; k; n) is converted to a SageMath
        affine weight by:
        1. Computing λ₀ from level and finite Dynkin labels
        2. Constructing Σ λ_i Λ_i in the affine weight lattice

        Note: The grade n is lost in this conversion as SageMath
        affine weights don't track L₀ eigenvalues.

        Returns
        -------
        weight
            The SageMath affine weight

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> Lambda_finite = ala._finite_root_system.weight_lattice().fundamental_weights()
        >>> w = AffineWeight(ala, Lambda_finite[1], level=1, grade=0)
        >>> sage_w = w.to_sagemath()
        >>> # sage_w should be the affine Λ₁

        Notes
        -----
        This uses the formula λ₀ = k - (λ, θ) = k - Σ a_i λ_i
        from Di Francesco Eq. (14.57).
        """
        if not self.algebra.is_affine:
            raise ValueError("Algebra must be affine type for this conversion")

        # Get finite Dynkin labels from finite_part
        mc = self.finite_part.monomial_coefficients()

        # Convert to dict with integer keys
        finite_labels = {i: mc.get(i, 0) for i in mc.keys()}

        # Compute λ₀ = k - (λ, θ) = k - Σ a_i λ_i
        lambda0 = self.algebra.lambda0_from_level(int(self.level), finite_labels)

        # Build affine weight using integer coefficients
        # Use fundamental_weights_sage() to get SageMath native weights
        affine_Lambda = self.algebra.fundamental_weights_sage()
        result = int(lambda0) * affine_Lambda[0]
        for i, coeff in finite_labels.items():
            if coeff != 0 and i in affine_Lambda:
                result += int(coeff) * affine_Lambda[i]

        return result

    def to_legacy_expression(self) -> str:
        if not self.algebra.is_affine:
            raise ValueError("Legacy affine expression export requires an affine algebra")

        finite_mc = self.finite_part.monomial_coefficients()
        finite_index_set = self.algebra._finite_root_system.weight_space().index_set()
        comarks = self.algebra.comarks
        finite_sum = sum(QQ(comarks.get(i, 0)) * QQ(finite_mc.get(i, 0)) for i in finite_index_set)
        lambda_0 = QQ(self.level) - finite_sum

        signed_terms: list[tuple[str, str]] = []

        def append_symbol(coeff: Any, symbol: str) -> None:
            coeff = QQ(coeff)
            if coeff == 0:
                return
            sign = "-" if coeff < 0 else "+"
            abs_coeff = -coeff if coeff < 0 else coeff
            magnitude = _rational_to_legacy(abs_coeff)
            if abs_coeff == 1:
                term = symbol
            else:
                term = f"{magnitude}*{symbol}"
            signed_terms.append((sign, term))

        append_symbol(lambda_0, "Lambda[0]")
        for idx in sorted(finite_index_set):
            append_symbol(finite_mc.get(idx, 0), f"Lambda[{idx}]")
        append_symbol(QQ(self.grade), "delta")

        if not signed_terms:
            return "0"

        first_sign, first_term = signed_terms[0]
        pieces = [first_term if first_sign == "+" else f"-{first_term}"]
        for sign, term in signed_terms[1:]:
            pieces.append(f" {sign} {term}")
        return "".join(pieces)

    def finite_part_in_fundamental_weight_basis(self) -> Any:
        """Return the finite part rewritten in the fundamental-weight basis."""
        if self.algebra.is_affine:
            finite_ws = self.algebra._finite_root_system.weight_space()
        else:
            finite_ws = self.algebra.root_system().weight_space()
        return finite_ws(self.finite_part)

    def finite_part_in_simple_root_basis(self) -> Any:
        """Return the finite part rewritten in the simple-root basis."""
        return self.algebra.weight_to_root(self.finite_part_in_fundamental_weight_basis(), finite=True)

    def to_fundamental_weight_basis(self) -> Tuple[Any, Any, Any]:
        """Return ``(finite_part, level, grade)`` with finite part in weight basis."""
        return (self.finite_part_in_fundamental_weight_basis(), self.level, self.grade)

    def to_simple_root_basis(self) -> Tuple[Any, Any, Any]:
        """Return ``(finite_part, level, grade)`` with finite part in root basis."""
        return (self.finite_part_in_simple_root_basis(), self.level, self.grade)

    # =========================================================================
    # Weyl Group Actions (Di Francesco Eq. 14.64)
    # =========================================================================

    def weyl_reflect(self, alpha: "AffineWeight") -> "AffineWeight":
        """
        Apply Weyl reflection s_̂α to this weight.

        Following Di Francesco Eq. (14.64):
            s_̂α(̂λ) = (λ - [(λ, α) + k_λ m_α] α^∨;
                       k_λ;
                       n_λ - [(λ, α) + k_λ m_α] 2m_α/|α|²)

        where ̂α = (α; 0; m_α) is an affine root.

        Parameters
        ----------
        alpha : AffineWeight
            The affine root ̂α = (α; 0; m) defining the reflection

        Returns
        -------
        AffineWeight
            The reflected weight s_̂α(̂λ)

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> Lambda = ala.fundamental_weights()
        >>> alpha = ala.simple_roots()
        >>> w = AffineWeight(ala, Lambda[1], level=1, grade=0)
        >>> # Create affine simple root ̂α₁ = (α₁; 0; 0)
        >>> a = AffineWeight.affine_simple_root(ala, 1)
        >>> w.weyl_reflect(a)  # s_α₁(̂Λ₁)

        Notes
        -----
        For simple roots α_i (with m = 0), this reduces to the finite
        Weyl reflection on the finite part, leaving k and n unchanged.
        """
        # Extract components
        alpha_finite = alpha.finite_part
        m_alpha = alpha.grade  # m for affine root (α; 0; m)

        # Compute (λ, α) - finite scalar product
        lambda_dot_alpha = self.algebra.scalar_product(self.finite_part, alpha_finite)

        # Get |α|²
        alpha_norm_sq = self.algebra.scalar_product(alpha_finite, alpha_finite)

        if alpha_norm_sq == 0:
            # Imaginary root - no reflection
            return self

        # Compute coefficient: (λ, α) + k_λ m_α
        coeff = lambda_dot_alpha + self.level * m_alpha

        # α^∨ = (2/|α|²) α
        alpha_vee_factor = 2 / alpha_norm_sq

        # New finite part: λ - coeff * α^∨
        new_finite = self.finite_part - alpha_finite * (coeff * alpha_vee_factor)

        # Level unchanged
        new_level = self.level

        # New grade: n - coeff * 2m/|α|²
        n_correction = coeff * (2 * m_alpha / alpha_norm_sq)
        new_grade = self.grade - n_correction

        return AffineWeight(self.algebra, new_finite, new_level, new_grade)

    def simple_reflection(self, i: int) -> "AffineWeight":
        """
        Apply simple reflection s_i to this weight.

        For the simple root α_i with i > 0, this is a finite reflection.
        For i = 0, this uses α₀ = -θ + δ.

        Parameters
        ----------
        i : int
            Index of the simple root

        Returns
        -------
        AffineWeight
            The reflected weight s_i(̂λ)

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> Lambda = ala.fundamental_weights()
        >>> w = AffineWeight(ala, Lambda[1], level=1, grade=0)
        >>> w.simple_reflection(1)  # s_1(̂Λ₁)
        """
        affine_root = AffineWeight.affine_simple_root(self.algebra, i)
        return self.weyl_reflect(affine_root)

    def associated_reflection(self) -> tuple[int, ...]:
        return self.algebra.affine_weyl_group().associated_reflection_word(self)

    def translate(self, beta: Any) -> "AffineWeight":
        """
        Apply translation t_β to this weight.

        Following Di Francesco Eq. (14.69):
            t_β(λ; k; n) = (λ + kβ; k;
                           n + [|λ|² - |λ + kβ|²]/(2k))

        where β is a coroot (or vector in the root lattice).

        Parameters
        ----------
        beta : weight/coroot
            The translation vector (typically a coroot)

        Returns
        -------
        AffineWeight
            The translated weight t_β(̂λ)

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> alpha_vee = ala.simple_coroots()[1]
        >>> w = AffineWeight(ala, ala._finite_root_system.weight_lattice().zero(), level=1, grade=0)
        >>> w.translate(alpha_vee)

        Notes
        -----
        This is the Di Francesco convention. Kac-Wakimoto uses the opposite
        sign: t_β^{KW} = t_{-β}^{DF}.
        """
        if self.level == 0:
            raise ValueError("Cannot translate at level k = 0")

        # Convert beta to the same space as finite_part if needed
        # Beta (coroot) is typically in coroot_space, but we need to add it to weight_space
        beta_coeffs = beta.monomial_coefficients()
        if hasattr(self.finite_part, "parent"):
            parent = self.finite_part.parent()
            # Reconstruct beta in the weight space using simple roots/weights
            # For simply-laced algebras, this is straightforward
            simple_elements = (
                parent.simple_roots()
                if hasattr(parent, "simple_roots")
                else parent.fundamental_weights()
            )
            beta_in_parent = parent.zero()
            for idx, coeff in beta_coeffs.items():
                if idx in simple_elements.keys():
                    beta_in_parent += coeff * simple_elements[idx]
        else:
            beta_in_parent = beta

        # New finite part: λ + kβ
        new_finite = self.finite_part + beta_in_parent * self.level

        # Compute grade correction
        lambda_norm_sq = self.algebra.scalar_product(self.finite_part, self.finite_part)
        new_lambda_norm_sq = self.algebra.scalar_product(new_finite, new_finite)

        n_correction = (lambda_norm_sq - new_lambda_norm_sq) / (2 * self.level)
        new_grade = self.grade + n_correction

        return AffineWeight(self.algebra, new_finite, self.level, new_grade)

    # =========================================================================
    # Factory Methods for Special Elements
    # =========================================================================

    @classmethod
    def delta(cls, algebra: "AffineLieAlgebra") -> "AffineWeight":
        """
        Create the imaginary root δ = (0; 0; 1).

        The imaginary root has (δ, δ) = 0 and (δ, ̂λ) = k_λ.

        Parameters
        ----------
        algebra : AffineLieAlgebra
            The affine Lie algebra

        Returns
        -------
        AffineWeight
            The imaginary root δ

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> delta = AffineWeight.delta(ala)
        >>> delta.norm_squared()  # Should be 0
        0
        """
        # Zero in the finite weight space
        if algebra._finite_root_system is not None:
            zero = algebra._finite_root_system.weight_space().zero()
        else:
            zero = algebra._weight_lattice.zero()

        return cls(algebra, zero, level=0, grade=1)

    @classmethod
    def affine_fundamental_weight(cls, algebra: "AffineLieAlgebra", i: int) -> "AffineWeight":
        """
        Create affine fundamental weight ̂Λ_i in Di Francesco notation.

        For i = 0: ̂Λ₀ = (0; 1; 0)
        For i > 0: ̂Λ_i = (Λ_i; 1; 0)

        Parameters
        ----------
        algebra : AffineLieAlgebra
            The affine Lie algebra
        i : int
            Index of the fundamental weight (0, 1, ..., r)

        Returns
        -------
        AffineWeight
            The affine fundamental weight ̂Λ_i

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> Lambda_hat_0 = AffineWeight.affine_fundamental_weight(ala, 0)
        >>> Lambda_hat_1 = AffineWeight.affine_fundamental_weight(ala, 1)
        >>> print(Lambda_hat_0)  # (0; 1; 0)
        >>> print(Lambda_hat_1)  # (Λ₁; 1; 0)

        Notes
        -----
        The affine fundamental weights satisfy:
        - ̂Λ_i(α_j^∨) = δ_{ij} for j = 0, 1, ..., r
        - k(̂Λ_i) = a_i^∨ (level equals comark)
        - For highest weight representations at level k, use weight k·̂Λ₀ + ...
        """
        if not algebra.is_affine:
            raise ValueError("Algebra must be affine type")

        # Use weight space (not lattice) to support fractional coefficients
        finite_ws = algebra._finite_root_system.weight_space()

        if i == 0:
            # ̂Λ₀ = (0; 1; 0)
            finite_part = finite_ws.zero()
        else:
            # ̂Λ_i = (Λ_i; 1; 0) for i > 0
            finite_Lambda = finite_ws.fundamental_weights()
            if i not in finite_ws.index_set():
                raise ValueError(f"Index {i} not in range 1..{algebra.rank}")
            finite_part = finite_Lambda[i]

        # Level for fundamental weights is the comark
        comarks = algebra.comarks
        level = comarks.get(i, 1)

        return cls(algebra, finite_part, level=level, grade=0)

    @classmethod
    def affine_simple_root(cls, algebra: "AffineLieAlgebra", i: int) -> "AffineWeight":
        """
        Create affine simple root ̂α_i in Di Francesco notation.

        For i > 0: ̂α_i = (α_i; 0; 0)
        For i = 0: ̂α₀ = (-θ; 0; 1) = -θ + δ

        Parameters
        ----------
        algebra : AffineLieAlgebra
            The affine Lie algebra
        i : int
            Index of the simple root (0, 1, ..., r)

        Returns
        -------
        AffineWeight
            The affine simple root ̂α_i

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> alpha_hat_0 = AffineWeight.affine_simple_root(ala, 0)
        >>> alpha_hat_1 = AffineWeight.affine_simple_root(ala, 1)
        >>> print(alpha_hat_0)  # (-θ; 0; 1)
        >>> print(alpha_hat_1)  # (α₁; 0; 0)

        Notes
        -----
        The affine simple roots satisfy:
        - Σ a_i α_i = δ (null root relation)
        - α₀ = δ - θ where θ is the highest root

        The finite part is expressed in terms of fundamental weights using:
            α_i = Σ_j C_ij Λ_j
        where C is the Cartan matrix.
        """
        if not algebra.is_affine:
            raise ValueError("Algebra must be affine type")

        if i == 0:
            # ̂α₀ = (-θ; 0; 1) where θ is highest root
            theta_lattice = algebra._finite_root_system.root_lattice().highest_root()
            theta_in_ws = algebra.root_to_weight(theta_lattice, finite=True)
            return cls(algebra, -theta_in_ws, level=0, grade=1)
        else:
            # ̂α_i = (α_i; 0; 0) for i > 0
            finite_indices = [int(idx) for idx in algebra._finite_root_system.index_set()]
            if i not in finite_indices:
                raise ValueError(f"Index {i} not in range 1..{algebra.rank}")
            alpha_i = algebra._finite_root_system.root_lattice().simple_roots()[i]
            alpha_i_in_ws = algebra.root_to_weight(alpha_i, finite=True)
            return cls(algebra, alpha_i_in_ws, level=0, grade=0)

    @classmethod
    def rho_hat(cls, algebra: "AffineLieAlgebra") -> "AffineWeight":
        """
        Create the affine Weyl vector ρ̂.

        In Dynkin labels, ρ̂ = [1, 1, ..., 1], which means:
        ρ̂ = Σ_{i=0}^{r} ̂Λ_i

        In Di Francesco notation:
        ρ̂ = (ρ; g; 0) where ρ is the finite Weyl vector and g is the dual Coxeter number

        Parameters
        ----------
        algebra : AffineLieAlgebra
            The affine Lie algebra

        Returns
        -------
        AffineWeight
            The affine Weyl vector ρ̂

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> rho = AffineWeight.rho_hat(ala)
        >>> rho.level  # Should be g = 3 for A₂^(1)
        3

        Notes
        -----
        Di Francesco Eq. (14.62): ρ̂ = Σ ω̂_i = [1, 1, ..., 1]
        The level of ρ̂ equals the dual Coxeter number g.
        """
        if not algebra.is_affine:
            raise ValueError("Algebra must be affine type")

        # Finite Weyl vector ρ = Σ Λ_i (use weight space for fractional support)
        finite_ws = algebra._finite_root_system.weight_space()
        finite_Lambda = finite_ws.fundamental_weights()
        rho_finite = sum(finite_Lambda.values())

        # Level = dual Coxeter number = Σ a_i^∨
        g = algebra.dual_coxeter_number

        return cls(algebra, rho_finite, level=g, grade=0)

    @classmethod
    def theta_hat(cls, algebra: "AffineLieAlgebra") -> "AffineWeight":
        """
        Create the affine highest root θ̂ = (θ; 0; 0).

        The highest root θ of the finite Lie algebra, extended to an affine
        weight with level=0 and grade=0.

        Parameters
        ----------
        algebra : AffineLieAlgebra
            The affine Lie algebra

        Returns
        -------
        AffineWeight
            The affine highest root θ̂ = (θ; 0; 0)

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> theta = AffineWeight.theta_hat(ala)
        >>> theta.level  # 0
        0
        >>> theta.grade  # 0
        0
        >>> # For A₂, θ = α₁ + α₂ in root lattice
        >>> # In weight space: θ = 2Λ₁ - Λ₂ + 2Λ₂ - Λ₁ = Λ₁ + Λ₂

        Notes
        -----
        The highest root θ satisfies:
        - θ = Σ a_i α_i where a_i are the marks (i > 0)
        - α₀ = -θ + δ (Di Francesco Eq. 14.32)
        - (θ, θ) = 2 for simply-laced algebras (long root normalization)

        The finite part is expressed in the weight space using:
            α_i = Σ_j C_ij Λ_j
        where C is the Cartan matrix.
        """
        if not algebra.is_affine:
            raise ValueError("Algebra must be affine type")

        # Get highest root from finite root lattice
        theta_lattice = algebra._finite_root_system.root_lattice().highest_root()
        theta_in_ws = algebra.root_to_weight(theta_lattice, finite=True)
        return cls(algebra, theta_in_ws, level=0, grade=0)

    @classmethod
    def zero(cls, algebra: "AffineLieAlgebra") -> "AffineWeight":
        """
        Create the zero affine weight (0; 0; 0).

        Parameters
        ----------
        algebra : AffineLieAlgebra
            The affine Lie algebra

        Returns
        -------
        AffineWeight
            The zero weight
        """
        if algebra._finite_root_system is not None:
            zero = algebra._finite_root_system.weight_space().zero()
        else:
            zero = algebra._weight_lattice.zero()

        return cls(algebra, zero, level=0, grade=0)

    # =========================================================================
    # Dominance and Integrability
    # =========================================================================

    def is_dominant(self) -> bool:
        """
        Check if this weight is dominant (non-negative Dynkin labels).

        For an affine weight to be dominant, all Dynkin labels
        λ_i = ̂λ(α_i^∨) ≥ 0 must hold.

        Returns
        -------
        bool
            True if dominant

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> w = AffineWeight.affine_fundamental_weight(ala, 1)
        >>> w.is_dominant()  # True
        """
        # Compute Dynkin labels and check non-negativity
        dynkin = self.dynkin_labels()
        return all(l >= 0 for l in dynkin.values())

    def dynkin_labels(self) -> Dict[int, Any]:
        """
        Compute the affine Dynkin labels [λ₀, λ₁, ..., λ_r].

        The Dynkin label λ_i = ̂λ(α_i^∨) is the pairing with
        the simple coroot α_i^∨.

        Returns
        -------
        dict
            Dictionary mapping indices to Dynkin labels

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> w = AffineWeight.affine_fundamental_weight(ala, 1)
        >>> w.dynkin_labels()  # {0: 0, 1: 1, 2: 0}
        """
        if not self.algebra.is_affine:
            raise ValueError("Algebra must be affine type")

        # Get finite Dynkin labels from finite_part
        finite_mc = self.finite_part.monomial_coefficients()

        # Get marks for computing λ₀
        marks = self.algebra.marks

        # λ₀ = k - (λ, θ) = k - Σ a_i λ_i (where a_i are marks for i > 0)
        theta_dot_lambda = sum(
            marks.get(i, 0) * finite_mc.get(i, 0) for i in marks.keys() if i != 0
        )
        lambda_0 = self.level - theta_dot_lambda

        # Build full Dynkin labels
        result = {0: lambda_0}
        for i in self.algebra._finite_root_system.weight_space().index_set():
            result[i] = finite_mc.get(i, 0)

        return result

    def dynkin_label(self, index: int) -> Any:
        """
        Return the affine Dynkin label λ_i at a given node index.

        Parameters
        ----------
        index : int
            Dynkin node index.

        Returns
        -------
        number
            The Dynkin label λ_i = ̂λ(α_i^∨).

        Raises
        ------
        KeyError
            If ``index`` is not a valid affine Dynkin node.

        Examples
        --------
        >>> ala = AffineLieAlgebra(['A', 2, 1])
        >>> w = AffineWeight.affine_fundamental_weight(ala, 1)
        >>> w.dynkin_label(1)
        1
        >>> w.dynkin_label(0)
        0
        """
        labels = self.dynkin_labels()
        if index not in labels:
            raise KeyError(f"Invalid affine Dynkin node index: {index}")
        return labels[index]


# =============================================================================
# Convenience Functions
# =============================================================================


def affine_weight(
    algebra: "AffineLieAlgebra",
    finite_part: Any,
    level: Union[int, Fraction, Any] = 0,
    grade: Union[int, Fraction, Any] = 0,
) -> AffineWeight:
    """
    Create an AffineWeight (convenience function).

    Parameters
    ----------
    algebra : AffineLieAlgebra
        The affine Lie algebra
    finite_part : weight
        The finite part λ
    level : number, optional
        The level k (default: 0)
    grade : number, optional
        The grade n (default: 0)

    Returns
    -------
    AffineWeight
        The affine weight (λ; k; n)
    """
    return AffineWeight(algebra, finite_part, level, grade)


def from_dynkin_labels(
    algebra: "AffineLieAlgebra", labels: Dict[int, int], grade: Union[int, Fraction, Any] = 0
) -> AffineWeight:
    """
    Create an AffineWeight from Dynkin labels [λ₀, λ₁, ..., λ_r].

    Parameters
    ----------
    algebra : AffineLieAlgebra
        The affine Lie algebra
    labels : dict
        Dictionary mapping indices to Dynkin labels
    grade : number, optional
        The grade n (default: 0)

    Returns
    -------
    AffineWeight
        The corresponding affine weight

    Examples
    --------
    >>> ala = AffineLieAlgebra(['A', 2, 1])
    >>> w = from_dynkin_labels(ala, {0: 1, 1: 0, 2: 0})  # ̂Λ₀
    >>> print(w)  # (0; 1; 0)
    """
    if not algebra.is_affine:
        raise ValueError("Algebra must be affine type")

    # Compute level from labels
    comarks = algebra.comarks
    level = sum(comarks.get(i, 0) * labels.get(i, 0) for i in comarks.keys())

    # Build finite part from finite labels (use weight space for fractional support)
    finite_ws = algebra._finite_root_system.weight_space()
    finite_Lambda = finite_ws.fundamental_weights()
    finite_part = finite_ws.zero()

    for i in finite_ws.index_set():
        if labels.get(i, 0) != 0:
            finite_part += labels[i] * finite_Lambda[i]

    return AffineWeight(algebra, finite_part, level=level, grade=grade)
