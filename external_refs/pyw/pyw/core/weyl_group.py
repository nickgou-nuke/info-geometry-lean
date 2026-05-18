"""
Affine Weyl Group Wrapper Module

This module provides a clean wrapper around SageMath's Weyl group implementation
for affine types, including support for finite, affine, and extended affine Weyl groups.

Key Features:
    - Finite Weyl groups (e.g., type A2)
    - Affine Weyl groups (e.g., type A2^(1))
    - Extended affine Weyl groups
    - Dot action: w.λ = w(λ + ρ̂) - ρ̂
    - Translation operators: t_α

References:
    - Kac, V. G., "Infinite-dimensional Lie algebras" (3rd ed.)
    - Kac, V. G., Wakimoto, M. "On rationality of W-algebras"
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Any, Iterable, Iterator, Mapping, Sequence, Union

from sage.all import QQ, RootSystem, WeylGroup


class AffineWeylGroup:
    """
    Wrapper class for SageMath's Weyl group with special support for affine types.

    This class provides a convenient interface for working with finite, affine,
    and extended affine Weyl groups, including the dot action and translation
    operators essential for admissible weight calculations.

    Parameters
    ----------
    cartan_type : Union[str, tuple]
        Cartan type specification. Examples:
        - 'A2' for finite type A2
        - ['A', 2, 1] for affine type A2^(1)
        - ('A', 2, 1) for affine type A2^(1)
    extended : bool, optional (default=False)
        If True, use the extended affine Weyl group (Ŵ = W ⋉ t_Q*).
        If False, use the standard affine Weyl group (Ŵ = W ⋉ t_Q∨).
        For finite types, this parameter has no effect.

    Attributes
    ----------
    cartan_type : tuple
        The Cartan type specification.
    extended : bool
        Whether the extended affine Weyl group is used.

    Examples
    --------
    >>> from pyw.core.weyl_group import AffineWeylGroup
    >>>
    >>> # Finite Weyl group
    >>> W_finite = AffineWeylGroup('A2')
    >>> print(W_finite.weyl_group)
    Weyl Group of type ['A', 2]
    >>>
    >>> # Affine Weyl group
    >>> W_affine = AffineWeylGroup(['A', 2, 1])
    >>> print(W_affine.weyl_group)
    Weyl Group of type ['A', 2, 1]
    >>>
    >>> # Extended affine Weyl group
    >>> W_extended = AffineWeylGroup(['A', 2, 1], extended=True)
    >>>
    >>> # Dot action
    >>> w = W_affine.weyl_group.simple_reflection(0)
    >>> weight = W_affine.weyl_group.domain().fundamental_weights()[0]
    >>> rho = W_affine.weyl_group.domain().rho()
    >>> result = W_affine.dot_action(w, weight, rho)
    """

    def __init__(self, cartan_type: Union[str, tuple, list], extended: bool = False) -> None:
        """
        Initialize the AffineWeylGroup wrapper.

        Parameters
        ----------
        cartan_type : Union[str, tuple, list]
            Cartan type specification.
        extended : bool, optional (default=False)
            Whether to use extended affine Weyl group.

        Raises
        ------
        ValueError
            If the cartan_type is not recognized by SageMath.
        """
        self.cartan_type = cartan_type
        self.extended = extended
        self._weyl_group: Any = None
        self._simple_reflections: dict[int, Any] = {}
        self._setup()

    def _setup(self) -> None:
        """
        Initialize the SageMath Weyl group and related structures.

        This method creates the underlying SageMath WeylGroup object
        and caches the simple reflections for efficient access.
        """
        # Create the Weyl group using SageMath
        self._weyl_group = WeylGroup(self.cartan_type)

        # Cache simple reflections
        for i in self._weyl_group.index_set():
            self._simple_reflections[i] = self._weyl_group.simple_reflection(i)

    @property
    def weyl_group(self) -> Any:
        """
        Get the underlying SageMath WeylGroup object.

        Returns
        -------
        WeylGroup
            The SageMath WeylGroup object for the specified Cartan type.

        Examples
        --------
        >>> W = AffineWeylGroup(['A', 2, 1])
        >>> wg = W.weyl_group
        >>> print(wg)
        Weyl Group of type ['A', 2, 1]
        """
        return self._weyl_group

    @property
    def simple_reflections(self) -> dict[int, Any]:
        """
        Get the simple reflections of the Weyl group.

        Returns
        -------
        dict[int, Any]
            Dictionary mapping node indices to simple reflections.
            For affine types, the mapping includes the affine node (index -1 or len-1).

        Examples
        --------
        >>> W = AffineWeylGroup(['A', 2, 1])
        >>> s0 = W.simple_reflections[0]
        >>> s1 = W.simple_reflections[1]
        >>> s2 = W.simple_reflections[2]
        """
        return self._simple_reflections

    def dot_action(self, w: Any, weight: Any, rho: Any) -> Any:
        """
        Compute the dot action of a Weyl group element on a weight.

        The dot action is defined as:
            w.λ = w(λ + ρ̂) - ρ̂

        This action is essential for admissible weight calculations and
        appears in the Kac-Wakimoto theory of fractional levels.

        Parameters
        ----------
        w : Any
            A Weyl group element (from `self.weyl_group`).
        weight : Any
            A weight in the weight lattice or weight space.
        rho : Any
            The Weyl vector (ρ̂). For affine types, this is the affine Weyl vector.

        Returns
        -------
        Any
            The result of the dot action w.λ.

        Examples
        --------
        >>> from pyw.core.weyl_group import AffineWeylGroup
        >>> from sage.all import RootSystem
        >>>
        >>> W = AffineWeylGroup(['A', 2, 1])
        >>> R = RootSystem(['A', 2, 1])
        >>> P = R.weight_space(extended=True)
        >>> Lambda = P.fundamental_weights()
        >>>
        >>> # Get a Weyl group element and weight
        >>> s0 = W.simple_reflections[0]
        >>> lambda_weight = Lambda[0]
        >>> rho_hat = P.rho()
        >>>
        >>> # Compute dot action
        >>> result = W.dot_action(s0, lambda_weight, rho_hat)
        >>> print(result)
        """
        # Compute w(λ + ρ)
        shifted_weight = weight + rho
        w_shifted = w.action(shifted_weight)

        # Compute w.λ = w(λ + ρ) - ρ
        result = w_shifted - rho

        return result

    def translation_operator(self, alpha: Any) -> Any:
        """
        Create a translation operator t_α in the extended affine Weyl group.

        Translation operators are elements of the extended affine Weyl group
        that act by translation on the weight lattice. For the affine Weyl
        group Ŵ = W ⋉ t_Q∨, translations are by coroots. For the extended
        affine Weyl group Ŵ = W ⋉ t_Q*, translations are by weights.

        Parameters
        ----------
        alpha : Any
            A root or weight defining the translation direction.
            For standard affine groups: α ∈ Q∨ (coroot lattice)
            For extended affine groups: α ∈ Q* (weight lattice)

        Returns
        -------
        Any
            The translation operator t_α in the Weyl group.

        Raises
        ------
        NotImplementedError
            If translation operators are not directly available for the
            specified Cartan type.

        Examples
        --------
        >>> from pyw.core.weyl_group import AffineWeylGroup
        >>> from sage.all import RootSystem
        >>>
        >>> W = AffineWeylGroup(['A', 2, 1])
        >>> R = RootSystem(['A', 2, 1])
        >>> simple_roots = R.root_lattice().simple_roots()
        >>>
        >>> # Create translation operator (note: implementation depends on SageMath)
        >>> try:
        ...     t_alpha = W.translation_operator(simple_roots[0])
        ...     print(f"Translation: {t_alpha}")
        ... except NotImplementedError:
        ...     print("Translation not directly available")
        """
        # For affine Weyl groups, translation operators are part of the semidirect product
        # The exact implementation depends on SageMath's internal representation

        # Check if we can construct translation using the weight/weight lattice
        if hasattr(self._weyl_group, "translation"):
            # SageMath may provide a translation method
            return self._weyl_group.translation(alpha)
        else:
            # Alternative: Construct translation using the algebraic group structure
            # This requires more advanced SageMath operations
            raise NotImplementedError(
                f"Translation operators for Cartan type {self.cartan_type} "
                "require specialized construction. "
                "Use the underlying SageMath WeylGroup directly for advanced operations."
            )

    def __repr__(self) -> str:
        """
        Return a string representation of the AffineWeylGroup.

        Returns
        -------
        str
            String representation showing Cartan type and extended status.
        """
        extended_str = "extended" if self.extended else "standard"
        return f"AffineWeylGroup({self.cartan_type}, {extended_str})"

    def __str__(self) -> str:
        """
        Return a user-friendly string representation.

        Returns
        -------
        str
            User-friendly string showing the underlying Weyl group.
        """
        return str(self._weyl_group)


def _reduced_word_str(word: Sequence[int]) -> str:
    if not word:
        return "1"
    return " * ".join(f"s_{i}" for i in word)


def _sage_element_length(w: Any) -> int:
    if hasattr(w, "length"):
        try:
            return int(w.length())
        except Exception:
            pass
    if hasattr(w, "reduced_word"):
        try:
            return len(w.reduced_word())
        except Exception:
            pass
    return 0


def _sorted_weyl_elements(elements: Iterable[Any]) -> list[Any]:
    return sorted(elements, key=lambda w: (_sage_element_length(w), tuple(w.reduced_word())))


def _coerce_word_element(parent: Any, coeff: Any, basis_element: Any) -> Any:
    coeff_int = int(coeff)
    if coeff_int == 0:
        return parent.zero()
    return coeff_int * basis_element


def _affine_weight_to_extended_sage_root(root: Any) -> Any:
    from .affine_weight import AffineWeight

    if not isinstance(root, AffineWeight):
        raise TypeError("Expected an AffineWeight affine root")
    if root.level != 0:
        raise ValueError("associated_reflection is only defined for affine roots of level 0")

    algebra = root.algebra
    if not algebra.is_affine:
        raise ValueError("AffineWeight associated_reflection requires an affine algebra")

    root_system = algebra._root_system
    if root_system is None:
        raise ValueError("Affine algebra root system is not initialized")

    extended_weight_lattice = root_system.weight_lattice(extended=True)
    fundamental_weights = extended_weight_lattice.fundamental_weights()
    basis_extension = extended_weight_lattice.basis_extension()

    out = extended_weight_lattice.zero()
    finite_coeffs = root.finite_part.monomial_coefficients()
    comarks = algebra.comarks

    lambda_0 = -sum(comarks[i] * finite_coeffs.get(i, 0) for i in comarks.keys() if i != 0)
    if lambda_0:
        out += _coerce_word_element(extended_weight_lattice, lambda_0, fundamental_weights[0])

    for i, coeff in finite_coeffs.items():
        if coeff:
            out += _coerce_word_element(extended_weight_lattice, coeff, fundamental_weights[int(i)])

    if root.grade:
        delta_index = next(iter(basis_extension.keys()))
        out += _coerce_word_element(
            extended_weight_lattice, root.grade, basis_extension[delta_index]
        )

    return out


class FiniteWeylGroup:
    """Finite Weyl group wrapper with elements acting on AffineWeight.

    Notes
    -----
    This is intentionally minimal and only implements the surface used by:
    - pyw/core/affine_lie_algebra.py (finite_weyl_group)
    - debug notebooks/scripts in this repo.
    """

    def __init__(self, algebra: Any) -> None:
        self._algebra = algebra
        finite_rs = (
            algebra._finite_root_system
            if getattr(algebra, "is_affine", False)
            else algebra.root_system()
        )
        # Matrix Weyl group acting on finite weight space.
        self._weight_space = finite_rs.weight_space(QQ)
        self._groups_by_prefix: dict[str, Any] = {}
        self._W = self._weyl_group(prefix="s")

    def _weyl_group(self, prefix: str = "s") -> Any:
        if prefix not in self._groups_by_prefix:
            self._groups_by_prefix[prefix] = self._weight_space.weyl_group(prefix=prefix)
        return self._groups_by_prefix[prefix]

    def _sorted_elements(self, prefix: str = "s") -> list[Any]:
        return _sorted_weyl_elements(list(self._weyl_group(prefix=prefix)))

    @property
    def algebra(self) -> Any:
        return self._algebra

    def __len__(self) -> int:
        return len(self._W)

    def __iter__(self) -> Iterator[Any]:
        yield from self._sorted_elements()

    def list(self, prefix: str = "s") -> list[Any]:
        return self._sorted_elements(prefix=prefix)

    def identity(self) -> Any:
        return self._W.one()

    def longest_element(self) -> Any:
        # Sage uses long_element() for the longest element.
        return self._W.long_element()

    def simple_reflection(self, i: int) -> Any:
        return self._W.simple_reflection(i)

    def from_word(self, word: Sequence[int]) -> Any:
        return self._W.from_reduced_word(list(word))

    def associated_reflection_word(self, root: Any) -> tuple[int, ...]:
        return tuple(int(i) for i in root.associated_reflection())

    def associated_reflection(self, root: Any) -> Any:
        return self._W.from_reduced_word(list(self.associated_reflection_word(root)))


class AffineWeylGroupSemidirect:
    """Affine Weyl group implemented as a semidirect product W ⋉ Q^∨.

    Representation convention
    -------------------------
    An element is represented as (w, beta) meaning **w * t_beta**.
    Action on an AffineWeight is:
        (w, beta).action(λ) = w.action( t_beta(λ) )
    Multiplication is:
        (w1, b1) * (w2, b2) = (w1*w2, w2^{-1}(b1) + b2)
    """

    def __init__(self, algebra: Any):
        if not getattr(algebra, "is_affine", False):
            raise ValueError("AffineWeylGroupSemidirect requires an affine algebra")

        self._algebra = algebra
        finite_rs = algebra._finite_root_system

        self._finite_weight_space = finite_rs.weight_space(QQ)
        self._finite_root_lattice = finite_rs.root_lattice()
        self._finite_coroot_space = finite_rs.coroot_space(QQ)

        self._finite_weyl_group = self._finite_weight_space.weyl_group()
        self._W_root = self._finite_root_lattice.weyl_group()
        self._W_coroot = self._finite_coroot_space.weyl_group()

        self._zero_beta = self._finite_coroot_space.zero()

        self._theta_coroot = self._compute_theta_coroot()
        self._s_theta_weight = self._compute_s_theta_on_weight_space()
        self._simple_translation_word_list_cache: dict[tuple[int, bool, int], tuple[int, ...]] = {}

    def _coerce_to_affine_root(self, root: Any) -> Any:
        from .affine_weight import AffineWeight

        if isinstance(root, AffineWeight):
            if root.level != 0:
                raise ValueError("Affine reflection root must have level 0")
            return root

        return None

    def _affine_root_simple_index(self, root: Any) -> int | None:
        from .affine_weight import AffineWeight

        if not isinstance(root, AffineWeight):
            return None

        for i, alpha_hat in self._algebra.affine_simple_roots().items():
            if root == alpha_hat:
                return int(i)
        return None

    def _translate_affine_weight(self, beta: Any, weight: Any) -> Any:
        """Translate an AffineWeight by a coroot beta.

        We intentionally implement this here (instead of delegating to
        AffineLieAlgebra.translation) because that method uses the library's
        Kac–Moody scalar_product normalization, while the translation formula
        needs the *weight–coroot pairing* <λ, β> and the coroot norm |β|^2.

        The implementation below computes both via Sage's ambient space model,
        which satisfies <Λ_i, α_j^∨> = δ_{ij}.
        """

        from .affine_weight import AffineWeight

        if not isinstance(weight, AffineWeight):
            raise TypeError("Translation action expects an AffineWeight")

        lam = weight.finite_part
        k = weight.level
        n = weight.grade

        # Fast path via Sage ambient space.
        try:
            lam_amb = lam.to_ambient()
            beta_amb = beta.to_ambient()
            v_amb = lam_amb + k * beta_amb

            parent = lam.parent()
            if not hasattr(parent, "fundamental_weights"):
                raise AttributeError("finite_part parent has no fundamental_weights")
            Lambda = parent.fundamental_weights()

            A = beta_amb.parent()
            simple_coroots = A.simple_coroots()

            new_lam = parent.zero()
            for i, Lambda_i in Lambda.items():
                # Defensive: some parents may include index 0 in affine contexts.
                if int(i) == 0:
                    continue
                coeff = v_amb.inner_product(simple_coroots[int(i)])
                if coeff:
                    new_lam += coeff * Lambda_i

            pairing = lam_amb.inner_product(beta_amb)
            if hasattr(beta, "norm_squared"):
                beta_norm_sq = beta.norm_squared()
            else:
                beta_norm_sq = beta_amb.inner_product(beta_amb)

            new_n = n - pairing - k * QQ(beta_norm_sq) / 2
            return AffineWeight(weight.algebra, new_lam, k, new_n)
        except Exception:
            # Fallback to existing implementation if ambient conversions fail.
            return self._algebra.translation(beta, weight)

    @property
    def algebra(self) -> Any:
        return self._algebra

    def cartan_type(self) -> Any:
        return self._algebra._cartan_type

    def __repr__(self) -> str:
        return f"AffineWeylGroupSemidirect({self._algebra._cartan_type})"

    def identity(self) -> "AffineWeylGroupSemidirectElement":
        return AffineWeylGroupSemidirectElement(self, self._finite_weyl_group.one(), self._zero_beta)

    def theta_coroot(self) -> Any:
        return self._theta_coroot

    # obtain the t_β
    # .translation(β).action(affine_weight)
    def translation(self, beta: Any) -> "AffineWeylGroupSemidirectElement":
        beta_cs = self._coerce_to_coroot_space(beta)
        return AffineWeylGroupSemidirectElement(self, self._finite_weyl_group.one(), beta_cs)

    def from_word(self, word: Sequence[int]) -> "AffineWeylGroupSemidirectElement":
        element = self.identity()
        for i in word:
            element = element * self.simple_reflection(int(i))
        return element

    def associated_reflection_word(self, root: Any) -> tuple[int, ...]:
        affine_root = self._coerce_to_affine_root(root)
        if affine_root is not None:
            sage_root = _affine_weight_to_extended_sage_root(affine_root)
            return tuple(int(i) for i in sage_root.associated_reflection())

        root_rl = self._finite_root_lattice(root)
        return tuple(int(i) for i in root_rl.associated_reflection())

    def associated_reflection(self, root: Any) -> "AffineWeylGroupSemidirectElement":
        affine_root = self._coerce_to_affine_root(root)
        word = self.associated_reflection_word(root)
        if affine_root is not None:
            return AffineWeylGroupSemidirectElement(
                self,
                self._finite_weyl_group.one(),
                self._zero_beta,
                _display_order="st",
                _affine_root=affine_root,
                _abstract_word=word,
            )
        return self.from_word(word)

    # NOTE:
    # - 输出为 tuple[int, ...]（affine simple reflection indices）
    # - simple translation word 使用实例缓存，避免重复构造
    def translation_word_list(self, beta: Any, *, max_length: int = 6) -> tuple[int, ...]:
        beta_cs = self._coerce_to_coroot_space(beta)
        if beta_cs == self._zero_beta:
            return ()

        coeff_map = (
            beta_cs.monomial_coefficients() if hasattr(beta_cs, "monomial_coefficients") else {}
        )
        word: list[int] = []
        for i in self._finite_coroot_space.index_set():
            coeff = int(coeff_map.get(i, 0))
            if coeff == 0:
                continue
            piece = self.simple_translation_word_list(
                int(i), negative=(coeff < 0), max_length=max_length
            )
            for _ in range(abs(coeff)):
                word.extend(piece)

        return tuple(word)

    def simple_translation_word_list(
        self, i: int, *, negative: bool, max_length: int = 6
    ) -> tuple[int, ...]:
        key = (int(i), bool(negative), int(max_length))
        cached = self._simple_translation_word_list_cache.get(key)
        if cached is not None:
            return cached

        reflection_word = self.affine_plus_delta_reflection_word_list(int(i), max_length=max_length)
        word = tuple(list(reflection_word) + [int(i)]) if negative else tuple([int(i)] + list(reflection_word))
        self._simple_translation_word_list_cache[key] = word
        return word

    def affine_plus_delta_reflection_word_list(self, i: int, *, max_length: int = 6) -> tuple[int, ...]:
        alpha_i_plus_delta = (
            self._algebra.affine_simple_roots()[int(i)] + self._algebra.affine_delta()
        )
        return self.associated_reflection_word(alpha_i_plus_delta)

    def simple_reflection(self, i: int) -> "AffineWeylGroupSemidirectElement":
        if i == 0:
            # Convention used by our debug notebook/scripts:
            # s0 = s_theta * t_{-theta^vee}
            return AffineWeylGroupSemidirectElement(
                self,
                self._s_theta_weight,
                -self._theta_coroot,
                _abstract_word=(0,),
            )

        return AffineWeylGroupSemidirectElement(
            self,
            self._finite_weyl_group.simple_reflection(i),
            self._zero_beta,
            _abstract_word=(int(i),),
        )

    def elements_as_semi_direct_product(
        self,
        *,
        translation_bounds: Mapping[int, tuple[int, int]] | None = None,
        translations: Iterable[Any] | None = None,
        factor_order: str = "st",
    ) -> list["AffineWeylGroupSemidirectElement"]:
        """Enumerate a bounded subset of W ⋉ Q^∨.

        Parameters
        ----------
        translation_bounds:
            Dict mapping simple coroot indices (1..rank) to (min,max) coefficients.
            Unspecified indices default to (0,0).
        translations:
            Explicit coroot-lattice translations to enumerate. Entries may be
            coroot vectors or pure translation elements from this semidirect
            model. Cannot be combined with ``translation_bounds``.
        factor_order:
            Output convention for the semidirect-product factors. ``"st"``
            returns elements displayed as ``s... * t_beta``; ``"ts"`` returns
            the equivalent form ``t_beta * s...``.

        Returns
        -------
        list[AffineWeylGroupSemidirectElement]
            Deterministic ordering: first all finite elements with zero translation,
            then increasing translation (lexicographic coefficients) combined with
            finite elements sorted by (length, reduced_word).
        """

        if factor_order not in {"st", "ts"}:
            raise ValueError("factor_order must be either 'st' or 'ts'")

        # Avoid global (length, reduced_word) sorting here: for large finite
        # Weyl groups (e.g. D6 with 23040 elements) this dominates runtime.
        # Sage iteration order is deterministic and sufficient for bounded
        # affine KL workflows.
        finite_elts_sorted = list(self._finite_weyl_group)

        # translation_bounds 或者 translations 至少提供一个
        if translation_bounds is not None and translations is not None:
            raise ValueError("Provide either translation_bounds or translations, not both")

        # 用 translations 构建半直积元素
        if translations is not None:
            translation_vectors = self._translation_vectors_from_inputs(
                translations=translations,
            )
        else:
            bounds = {} if translation_bounds is None else translation_bounds
            idxs = list(self._finite_coroot_space.index_set())
            ranges: list[range] = []
            for i in idxs:
                lo, hi = bounds.get(int(i), (0, 0))
                ranges.append(range(int(lo), int(hi) + 1))

            basis = self._finite_coroot_space.simple_roots()
            generated_vectors: list[Any] = []
            for coeffs in product(*ranges):
                beta = self._zero_beta
                for i, c in zip(idxs, coeffs):
                    if c:
                        beta += int(c) * basis[int(i)]
                generated_vectors.append(beta)

            translation_vectors = self._translation_vectors_from_inputs(
                translations=generated_vectors,
            )

        result: list[AffineWeylGroupSemidirectElement] = []
        for beta in translation_vectors:
            for w in finite_elts_sorted:
                result.append(
                    AffineWeylGroupSemidirectElement(
                        self,
                        w,
                        beta,
                        _display_order=factor_order,
                    )
                )

        return result

    def _translation_vectors_from_inputs(
        self,
        *,
        translations: Iterable[Any] | None,
    ) -> list[Any]:
        vectors = [] if translations is None else [self._coerce_explicit_translation(beta) for beta in translations]

        by_key: dict[tuple[Any, ...], Any] = {}
        for beta in vectors:
            coerced = self._coerce_to_coroot_space(beta)
            by_key[self._translation_sort_key(coerced)] = coerced

        return [by_key[key] for key in sorted(by_key.keys())]

    def _coerce_explicit_translation(self, translation: Any) -> Any:
        if isinstance(translation, AffineWeylGroupSemidirectElement):
            if translation._group is not self:
                raise TypeError("Explicit affine translation element must belong to this group")
            if translation.finite_part.reduced_word():
                raise ValueError("Explicit affine translation element must have trivial finite part")
            return translation.translation_vector
        if hasattr(translation, "translation_vector") and hasattr(translation, "reduced_word"):
            if list(translation.reduced_word()):
                raise ValueError("Explicit affine translation element must have trivial finite part")
            return translation.translation_vector
        return translation

    def _translation_sort_key(self, beta: Any) -> tuple[Any, ...]:
        coeffs = beta.monomial_coefficients()
        idxs = [int(i) for i in self._finite_coroot_space.index_set()]
        coeff_tuple = tuple(coeffs.get(i, 0) for i in idxs)
        return (0 if all(c == 0 for c in coeff_tuple) else 1, coeff_tuple)

    def _coerce_to_coroot_space(self, beta: Any) -> Any:
        if beta in (0, None):
            return self._zero_beta
        if getattr(beta, "parent", lambda: None)() is self._finite_coroot_space:
            return beta
        try:
            return self._finite_coroot_space(beta)
        except Exception:
            # Best-effort reconstruction from monomial coefficients.
            if hasattr(beta, "monomial_coefficients"):
                coeffs = beta.monomial_coefficients()
                basis = self._finite_coroot_space.simple_roots()
                out = self._zero_beta
                for i, c in coeffs.items():
                    out += c * basis[int(i)]
                return out
            raise

    def _compute_theta_coroot(self) -> Any:
        theta = self._finite_root_lattice.highest_root()
        theta_vee = theta.associated_coroot()
        return self._finite_coroot_space(theta_vee)

    def _compute_s_theta_on_weight_space(self) -> Any:
        # Compute reflection s_theta in the finite Weyl group by conjugating
        # a simple reflection: if u(α_j) = θ, then s_θ = u s_j u^{-1}.
        theta = self._finite_root_lattice.highest_root()
        return self._reflection_on_weight_space(theta)

    def _reflection_on_weight_space(self, root: Any) -> Any:
        """Compute s_root in the finite Weyl group on weight space.

        Given a root α in the root lattice, construct the reflection s_α by
        conjugation: find u ∈ W and simple root α_j such that u(α_j) = α,
        then s_α = u · s_j · u⁻¹.

        Parameters
        ----------
        root : root lattice element
            A root (typically a positive root) in the finite root lattice.

        Returns
        -------
        Weyl group element on weight space.
        """
        # Ensure root is in the root lattice.
        root_rl = self._finite_root_lattice(root)
        simple_roots = self._finite_root_lattice.simple_roots()

        candidates = list(self._W_root)
        for j, alpha_j in simple_roots.items():
            for u in candidates:
                if u.action(alpha_j) == root_rl:
                    u_word = list(u.reduced_word())
                    u_weight = self._finite_weyl_group.from_reduced_word(u_word)
                    s_j_weight = self._finite_weyl_group.simple_reflection(int(j))
                    return u_weight * s_j_weight * u_weight.inverse()

        raise RuntimeError(f"Failed to construct s_({root}) in finite Weyl group")

    def reflection(self, root: Any) -> "AffineWeylGroupSemidirectElement":
        """Construct the Weyl reflection s_α for an arbitrary root α.

        Given any root α in the finite root system, returns the element
        (s_α, 0) of the semidirect product W ⋉ Q∨ — i.e., the pure finite
        reflection with zero translation.

        Parameters
        ----------
        root : root lattice element
            A root in the finite root lattice (e.g., ``alpha[1] + alpha[2]``
            for the highest root θ of A₂).

        Returns
        -------
        AffineWeylGroupSemidirectElement
            The reflection s_α as (s_α, 0).

        Example
        -------
        >>> ala = AffineLieAlgebra("A", 2, 1)
        >>> W = ala.affine_weyl_group()
        >>> alpha = W._finite_root_lattice.simple_roots()
        >>> s_theta = W.reflection(alpha[1] + alpha[2])  # highest root of A2
        """
        affine_root = self._coerce_to_affine_root(root)
        if affine_root is not None:
            return self.associated_reflection(affine_root)

        w = self._reflection_on_weight_space(root)
        return AffineWeylGroupSemidirectElement(self, w, self._zero_beta)


@dataclass(frozen=True)
class AffineWeylGroupSemidirectElement:
    _group: AffineWeylGroupSemidirect
    _w: Any  # finite Weyl element acting on finite weight space
    _beta: Any  # coroot-space element
    _display_order: str = "st"
    _affine_root: Any | None = None
    _abstract_word: tuple[int | None, ...] = ()
    _affine_word_override: tuple[int, ...] | None = None

    @property
    def finite_part(self) -> Any:
        return self._w

    @property
    def translation_vector(self) -> Any:
        return self._beta

    def word(self) -> tuple[int, ...]:
        if self._affine_word_override is not None:
            return self._affine_word_override
        if self._abstract_word:
            if any(i is None for i in self._abstract_word):
                raise TypeError(
                    "Word is unavailable for non-simple affine-root reflections"
                )
            out: list[int] = []
            for i in self._abstract_word:
                if i is None:
                    raise TypeError("Word is unavailable for non-simple affine-root reflections")
                out.append(int(i))
            return tuple(out)

        finite_word = tuple(int(i) for i in self._w.reduced_word())
        translation_word = self._group.translation_word_list(self._beta)
        return finite_word + translation_word

    # 返回 reduce_word 数组 [i, j, ...], 其中 i, j, ... = 0, 1, ..., r
    def reduced_word_list(self) -> list[int]:
        sage_element = self.reduced_word()
        return [int(i) for i in sage_element.reduced_word()]

    # 返回一串 sage weyl group simple reflection 的乘积，s_i * s_j * ...
    # 而不是数组 [i, j, ...]，其中 i, j, ... = 0, 1, ..., r
    def reduced_word(self) -> Any:
        sage_group = self._group.algebra.affine_weyl_group_sage()
        return sage_group.from_reduced_word(list(self.word()))

    def length(self) -> int:
        return int(self.reduced_word().length())

    def bruhat_le(self, other: Any) -> bool:
        sage_group = self._group.algebra.affine_weyl_group_sage()
        left = self.reduced_word()

        if isinstance(other, AffineWeylGroupSemidirectElement):
            right = other.reduced_word()
        elif isinstance(other, (list, tuple)):
            right = sage_group.from_reduced_word([int(i) for i in other])
        elif hasattr(other, "bruhat_le"):
            right = other
        elif hasattr(other, "reduced_word"):
            right_word = other.reduced_word()
            right = sage_group.from_reduced_word([int(i) for i in right_word])
        else:
            raise TypeError("Cannot compare Bruhat order with unsupported element type")

        return bool(left.bruhat_le(right))

    def semidirect_components(self, factor_order: str | None = None) -> tuple[Any, Any]:
        """Return semidirect components in ``st`` or ``ts`` convention."""
        order = self._display_order if factor_order is None else factor_order
        if order == "st":
            return self.finite_part, self._beta
        if order == "ts":
            w_coroot = self._group._W_coroot.from_reduced_word(list(self._w.reduced_word()))
            return w_coroot.action(self._beta), self.finite_part
        raise ValueError("factor_order must be either 'st' or 'ts'")

    def __str__(self) -> str:
        if self._affine_root is not None:
            return f"s_{{{self._affine_root}}}"
        if len(self._abstract_word) == 1 and self._abstract_word[0] is not None:
            return _reduced_word_str([int(self._abstract_word[0])])
        w_str = _reduced_word_str(list(self._w.reduced_word()))
        if self._beta == self._group._zero_beta:
            return _reduced_word_str(self.reduced_word_list())
        if self._display_order == "st":
            if not list(self._w.reduced_word()):
                return f"t_{{{self._beta}}}"
            return f"{w_str} * t_{{{self._beta}}}"
        beta_ts, finite_part = self.semidirect_components("ts")
        if not finite_part.reduced_word():
            return f"t_{{{beta_ts}}}"
        return f"t_{{{beta_ts}}} * {_reduced_word_str(finite_part.reduced_word())}"

    def __repr__(self) -> str:
        return f"AffineWeylGroupSemidirectElement({str(self)})"

    def __mul__(
        self, other: "AffineWeylGroupSemidirectElement"
    ) -> "AffineWeylGroupSemidirectElement":
        if self._group is not other._group:
            raise TypeError(
                "Cannot multiply elements from different AffineWeylGroupSemidirect instances"
            )

        if (
            self._abstract_word
            or other._abstract_word
            or self._affine_root is not None
            or other._affine_root is not None
        ):
            left = self._abstract_word if self._abstract_word else tuple(self._w.reduced_word())
            right = other._abstract_word if other._abstract_word else tuple(other._w.reduced_word())
            w_new = self._w * other._w
            word2 = list(other._w.reduced_word())
            w2_coroot = self._group._W_coroot.from_reduced_word(word2)
            b_new = w2_coroot.inverse().action(self._beta) + other._beta
            affine_left = self.word()
            affine_right = other.word()
            return AffineWeylGroupSemidirectElement(
                self._group,
                w_new,
                b_new,
                _display_order=self._display_order,
                _abstract_word=left + right,
                _affine_word_override=affine_left + affine_right,
            )

        # (w1, b1) * (w2, b2) = (w1*w2, w2^{-1}(b1) + b2)
        w_new = self._w * other._w
        word2 = list(other._w.reduced_word())
        w2_coroot = self._group._W_coroot.from_reduced_word(word2)
        b_new = w2_coroot.inverse().action(self._beta) + other._beta
        return AffineWeylGroupSemidirectElement(self._group, w_new, b_new)

    def inverse(self) -> "AffineWeylGroupSemidirectElement":
        w_inv = self._w.inverse()
        w_coroot = self._group._W_coroot.from_reduced_word(list(self._w.reduced_word()))
        beta_inv = -w_coroot.action(self._beta)
        return AffineWeylGroupSemidirectElement(
            self._group,
            w_inv,
            beta_inv,
            _display_order=self._display_order,
        )

    def action(self, weight: Any) -> Any:
        from .affine_weight import AffineWeight

        if not isinstance(weight, AffineWeight):
            # Fallback to Sage's action when possible.
            return self._w.action(weight)

        word = self._affine_word_override if self._affine_word_override is not None else self._abstract_word
        if word and len(word) > 1 and self._affine_root is None:
            if any(i is None for i in word):
                raise TypeError("Word is unavailable for non-simple affine-root reflections")
            word_ints = [int(j) for j in word if j is not None]
            current = weight
            for i in reversed(word_ints):
                current = self._group.simple_reflection(int(i)).action(current)
            return current

        if self._affine_root is not None:
            return self._group.algebra.affine_weyl_reflection(self._affine_root, weight)

        translated = self._group._translate_affine_weight(self._beta, weight)
        new_finite = self._w.action(translated.finite_part)
        return AffineWeight(weight.algebra, new_finite, translated.level, translated.grade)

    __call__ = action


class ExtendedAffineWeylGroup:
    """Extended affine Weyl group implemented as a semidirect product W ⋉ P^∨.

    This is the true extended affine Weyl group using the coweight lattice P^∨,
    which is larger than the coroot lattice Q^∨ used in AffineWeylGroupSemidirect.

    Mathematical Definition
    -----------------------
    - Affine Weyl group: W_aff = W ⋉ Q^∨ (coroot lattice)
    - Extended affine Weyl group: W_ext = W ⋉ P^∨ (coweight lattice)
    - Relationship: W_aff ⊆ W_ext, with quotient W_ext/W_aff ≅ P^∨/Q^∨ ≅ π₁(G)

    Representation convention
    -------------------------
    An element is represented as (w, lambda) meaning **w * t_lambda**.
    Action on an AffineWeight is:
        (w, lambda).action(μ) = w.action( t_lambda(μ) )
    Multiplication is:
        (w1, λ1) * (w2, λ2) = (w1*w2, w2^{-1}(λ1) + λ2)

    References
    ----------
    - Kac, V. G., "Infinite-dimensional Lie algebras" (3rd ed.), Chapter 6
    - The quotient P^∨/Q^∨ is the fundamental group of the corresponding Lie group
    """

    def __init__(self, algebra: Any):
        if not getattr(algebra, "is_affine", False):
            raise ValueError("ExtendedAffineWeylGroup requires an affine algebra")

        self._algebra = algebra
        finite_rs = algebra._finite_root_system

        self._finite_weight_space = finite_rs.weight_space(QQ)
        self._finite_root_lattice = finite_rs.root_lattice()
        self._finite_coweight_lattice = finite_rs.coweight_lattice()
        self._finite_coroot_space = finite_rs.coroot_space(QQ)

        self._finite_weyl_group = self._finite_weight_space.weyl_group()
        self._W_root = self._finite_root_lattice.weyl_group()
        self._W_coweight = self._finite_coweight_lattice.weyl_group()
        self._W_coroot = self._finite_coroot_space.weyl_group()

        self._zero_lambda = self._finite_coweight_lattice.zero()

        self._theta_coroot = self._compute_theta_coroot()
        self._s_theta_weight = self._compute_s_theta_on_weight_space()

    def _translate_affine_weight(self, lambda_cw: Any, weight: Any) -> Any:
        """Translate an AffineWeight by a coweight lambda.

        This uses the coweight lattice P^∨ instead of coroot space Q^∨.
        The translation formula is similar but uses coweights.
        """

        from .affine_weight import AffineWeight

        if not isinstance(weight, AffineWeight):
            raise TypeError("Translation action expects an AffineWeight")

        lam = weight.finite_part
        k = weight.level
        n = weight.grade

        # Convert coweight to ambient space for pairing computation
        try:
            lam_amb = lam.to_ambient()
            lambda_amb = lambda_cw.to_ambient()
            v_amb = lam_amb + k * lambda_amb

            parent = lam.parent()
            if not hasattr(parent, "fundamental_weights"):
                raise AttributeError("finite_part parent has no fundamental_weights")
            Lambda = parent.fundamental_weights()

            A = lambda_amb.parent()
            simple_coroots = A.simple_coroots()

            new_lam = parent.zero()
            for i, Lambda_i in Lambda.items():
                if int(i) == 0:
                    continue
                coeff = v_amb.inner_product(simple_coroots[int(i)])
                if coeff:
                    new_lam += coeff * Lambda_i

            pairing = lam_amb.inner_product(lambda_amb)
            if hasattr(lambda_cw, "norm_squared"):
                lambda_norm_sq = lambda_cw.norm_squared()
            else:
                lambda_norm_sq = lambda_amb.inner_product(lambda_amb)

            new_n = n - pairing - k * QQ(lambda_norm_sq) / 2
            return AffineWeight(weight.algebra, new_lam, k, new_n)
        except Exception:
            # Fallback
            return self._algebra.translation(lambda_cw, weight)

    @property
    def algebra(self) -> Any:
        return self._algebra

    def __repr__(self) -> str:
        return f"ExtendedAffineWeylGroup({self._algebra._cartan_type})"

    def identity(self) -> "ExtendedAffineWeylGroupElement":
        return ExtendedAffineWeylGroupElement(self, self._finite_weyl_group.one(), self._zero_lambda)

    def theta_coroot(self) -> Any:
        return self._theta_coroot

    def translation(self, lambda_cw: Any) -> "ExtendedAffineWeylGroupElement":
        """Create a translation element by a coweight.

        Parameters
        ----------
        lambda_cw : coweight element from P^∨
            The coweight to translate by.

        Returns
        -------
        ExtendedAffineWeylGroupElement
            Translation element t_lambda
        """
        lambda_cwl = self._coerce_to_coweight_lattice(lambda_cw)
        return ExtendedAffineWeylGroupElement(self, self._finite_weyl_group.one(), lambda_cwl)

    def from_word(self, word: Sequence[int]) -> "ExtendedAffineWeylGroupElement":
        element = self.identity()
        for i in word:
            element = element * self.simple_reflection(int(i))
        return element

    def associated_reflection_word(self, root: Any) -> tuple[int, ...]:
        from .affine_weight import AffineWeight

        if isinstance(root, AffineWeight):
            return self._algebra.affine_weyl_group().associated_reflection_word(root)

        root_rl = self._finite_root_lattice(root)
        return tuple(int(i) for i in root_rl.associated_reflection())

    def associated_reflection(self, root: Any) -> "ExtendedAffineWeylGroupElement":
        element = self.identity()
        for i in self.associated_reflection_word(root):
            element = element * self.simple_reflection(int(i))
        return element

    def simple_reflection(self, i: int) -> "ExtendedAffineWeylGroupElement":
        if i == 0:
            # s0 = s_theta * t_{-theta^vee}
            # theta^vee is in Q^∨, need to convert to P^∨ using Cartan matrix
            # α_i^∨ = Σ_j C_{ij} * Λ_j^∨ where C is the Cartan matrix

            theta_in_coweight = self._coroot_to_coweight(self._theta_coroot)
            return ExtendedAffineWeylGroupElement(
                self,
                self._s_theta_weight,
                -theta_in_coweight,
                _abstract_word=(0,),
            )

        return ExtendedAffineWeylGroupElement(
            self,
            self._finite_weyl_group.simple_reflection(i),
            self._zero_lambda,
            _abstract_word=(int(i),),
        )

    def _coroot_to_coweight(self, coroot: Any) -> Any:
        """Convert a coroot (element of Q^∨) to the coweight lattice (P^∨).

        Uses the relation: α_i^∨ = Σ_j C_{ij} * Λ_j^∨
        where C is the Cartan matrix.
        """
        # Get Cartan matrix
        C = self._algebra._finite_root_system.cartan_matrix()
        coroot_coeffs = coroot.monomial_coefficients()
        coweight_basis = self._finite_coweight_lattice.fundamental_weights()

        result = self._zero_lambda
        # For each simple coroot α_k^∨ with coefficient c_k in the input
        for k, c_k in coroot_coeffs.items():
            # α_k^∨ = Σ_j C_{kj} * Λ_j^∨
            for j in coweight_basis.keys():
                C_kj = C[int(k) - 1, int(j) - 1]  # Cartan matrix is 0-indexed
                if C_kj != 0:
                    result = result + coweight_basis[int(j)] * int(c_k * C_kj)
        return result

    def _coerce_to_coweight_lattice(self, lambda_cw: Any) -> Any:
        """Coerce an element to the coweight lattice P^∨."""
        if lambda_cw in (0, None):
            return self._zero_lambda
        if getattr(lambda_cw, "parent", lambda: None)() is self._finite_coweight_lattice:
            return lambda_cw
        try:
            return self._finite_coweight_lattice(lambda_cw)
        except Exception:
            # Best-effort reconstruction
            if hasattr(lambda_cw, "monomial_coefficients"):
                coeffs = lambda_cw.monomial_coefficients()
                basis = self._finite_coweight_lattice.fundamental_weights()
                out = self._zero_lambda
                for i, c in coeffs.items():
                    out += c * basis[int(i)]
                return out
            raise

    def _compute_theta_coroot(self) -> Any:
        """Compute the highest coroot theta^∨."""
        theta = self._finite_root_lattice.highest_root()
        theta_vee = theta.associated_coroot()
        return self._finite_coroot_space(theta_vee)

    def _compute_s_theta_on_weight_space(self) -> Any:
        """Compute reflection s_theta in the finite Weyl group."""
        theta = self._finite_root_lattice.highest_root()
        return self._reflection_on_weight_space(theta)

    def _reflection_on_weight_space(self, root: Any) -> Any:
        """Compute s_root in the finite Weyl group on weight space.

        Given a root α in the root lattice, construct the reflection s_α by
        conjugation: find u ∈ W and simple root α_j such that u(α_j) = α,
        then s_α = u · s_j · u⁻¹.
        """
        root_rl = self._finite_root_lattice(root)
        simple_roots = self._finite_root_lattice.simple_roots()

        candidates = list(self._W_root)
        for j, alpha_j in simple_roots.items():
            for u in candidates:
                if u.action(alpha_j) == root_rl:
                    u_word = list(u.reduced_word())
                    u_weight = self._finite_weyl_group.from_reduced_word(u_word)
                    s_j_weight = self._finite_weyl_group.simple_reflection(int(j))
                    return u_weight * s_j_weight * u_weight.inverse()

        raise RuntimeError(f"Failed to construct s_({root}) in finite Weyl group")

    def reflection(self, root: Any) -> "ExtendedAffineWeylGroupElement":
        """Construct the Weyl reflection s_α for an arbitrary root α.

        Given any root α in the finite root system, returns the element
        (s_α, 0) of the semidirect product W ⋉ P∨.

        Parameters
        ----------
        root : root lattice element
            A root in the finite root lattice.

        Returns
        -------
        ExtendedAffineWeylGroupElement
            The reflection s_α as (s_α, 0).
        """
        w = self._reflection_on_weight_space(root)
        return ExtendedAffineWeylGroupElement(self, w, self._zero_lambda)

    def elements_as_semi_direct_product(
        self,
        *,
        translation_bounds: Mapping[int, tuple[int, int]] | None = None,
        translations: Iterable[Any] | None = None,
        factor_order: str = "st",
    ) -> list["ExtendedAffineWeylGroupElement"]:
        """Enumerate a bounded subset of W ⋉ P^∨.

        Similar to AffineWeylGroupSemidirect.elements_as_semi_direct_product,
        but uses the coweight lattice P^∨ instead of the coroot lattice Q^∨.

        Parameters
        ----------
        translation_bounds:
            Dict mapping simple coroot indices (1..rank) to (min,max) coefficients
            for the fundamental coweights. Unspecified indices default to (0,0).
        translations:
            Explicit coweight-lattice translations to enumerate. Entries may be
            coweight vectors or pure translation elements from this semidirect
            model. Cannot be combined with ``translation_bounds``.
        factor_order:
            Output convention for the semidirect-product factors. ``"st"``
            returns elements displayed as ``s... * t_lambda``; ``"ts"`` returns
            the equivalent form ``t_lambda * s...``.

        Returns
        -------
        list[ExtendedAffineWeylGroupElement]
            Deterministic ordering: first all finite elements with zero translation,
            then increasing translation (lexicographic coefficients) combined with
            finite elements sorted by (length, reduced_word).
        """
        from itertools import product

        if factor_order not in {"st", "ts"}:
            raise ValueError("factor_order must be either 'st' or 'ts'")

        # Keep native deterministic iteration order instead of an expensive
        # global sort by (length, reduced_word) on large finite groups.
        finite_elts_sorted = list(self._finite_weyl_group)

        if translation_bounds is not None and translations is not None:
            raise ValueError("Provide either translation_bounds or translations, not both")

        if translations is not None:
            translation_vectors = self._translation_vectors_from_inputs(
                translations=translations,
            )
        else:
            bounds = {} if translation_bounds is None else translation_bounds
            idxs = list(self._finite_coweight_lattice.index_set())
            ranges: list[range] = []
            for i in idxs:
                lo, hi = bounds.get(int(i), (0, 0))
                ranges.append(range(int(lo), int(hi) + 1))

            basis = self._finite_coweight_lattice.fundamental_weights()
            generated_vectors: list[Any] = []
            for coeffs in product(*ranges):
                lam = self._zero_lambda
                for i, c in zip(idxs, coeffs):
                    if c:
                        lam += int(c) * basis[int(i)]
                generated_vectors.append(lam)

            translation_vectors = self._translation_vectors_from_inputs(
                translations=generated_vectors,
            )

        result: list[ExtendedAffineWeylGroupElement] = []
        for lam in translation_vectors:
            for w in finite_elts_sorted:
                result.append(
                    ExtendedAffineWeylGroupElement(self, w, lam, _display_order=factor_order)
                )

        return result

    def _translation_vectors_from_inputs(
        self,
        *,
        translations: Iterable[Any] | None,
    ) -> list[Any]:
        vectors = [] if translations is None else [self._coerce_explicit_translation(lam) for lam in translations]

        by_key: dict[tuple[Any, ...], Any] = {}
        for lam in vectors:
            coerced = self._coerce_to_coweight_lattice(lam)
            by_key[self._translation_sort_key(coerced)] = coerced

        return [by_key[key] for key in sorted(by_key.keys())]

    def _coerce_explicit_translation(self, translation: Any) -> Any:
        if isinstance(translation, ExtendedAffineWeylGroupElement):
            if translation._group is not self:
                raise TypeError("Explicit extended-affine translation element must belong to this group")
            if translation.finite_part.reduced_word():
                raise ValueError(
                    "Explicit extended-affine translation element must have trivial finite part"
                )
            return translation.translation_vector
        if hasattr(translation, "translation_vector") and hasattr(translation, "reduced_word"):
            if list(translation.reduced_word()):
                raise ValueError(
                    "Explicit extended-affine translation element must have trivial finite part"
                )
            return translation.translation_vector
        return translation

    def _translation_sort_key(self, lam: Any) -> tuple[Any, ...]:
        coeffs = lam.monomial_coefficients()
        idxs = [int(i) for i in self._finite_coweight_lattice.index_set()]
        coeff_tuple = tuple(coeffs.get(i, 0) for i in idxs)
        return (0 if all(c == 0 for c in coeff_tuple) else 1, coeff_tuple)


@dataclass(frozen=True)
class ExtendedAffineWeylGroupElement:
    """Element of the extended affine Weyl group W ⋉ P^∨."""

    _group: ExtendedAffineWeylGroup
    _w: Any  # finite Weyl element acting on finite weight space
    _lambda: Any  # coweight lattice element (P^∨)
    _display_order: str = "st"
    _abstract_word: tuple[int | None, ...] = ()

    @property
    def finite_part(self) -> Any:
        return self._w

    @property
    def translation_vector(self) -> Any:
        """Return the coweight translation vector (element of P^∨)."""
        return self._lambda

    def reduced_word(self) -> list[int]:
        return list(self._w.reduced_word())

    def semidirect_components(self, factor_order: str | None = None) -> tuple[Any, Any]:
        """Return semidirect components in ``st`` or ``ts`` convention."""
        order = self._display_order if factor_order is None else factor_order
        if order == "st":
            return self.finite_part, self._lambda
        if order == "ts":
            w_coweight = self._group._W_coweight.from_reduced_word(self.reduced_word())
            return w_coweight.action(self._lambda), self.finite_part
        raise ValueError("factor_order must be either 'st' or 'ts'")

    def __str__(self) -> str:
        if len(self._abstract_word) == 1 and self._abstract_word[0] is not None:
            return _reduced_word_str([int(self._abstract_word[0])])
        w_str = _reduced_word_str(self.reduced_word())
        if self._lambda == self._group._zero_lambda:
            return w_str
        if self._display_order == "st":
            if not self.reduced_word():
                return f"t_{{{self._lambda}}}"
            return f"{w_str} * t_{{{self._lambda}}}"
        lambda_ts, finite_part = self.semidirect_components("ts")
        if not finite_part.reduced_word():
            return f"t_{{{lambda_ts}}}"
        return f"t_{{{lambda_ts}}} * {_reduced_word_str(finite_part.reduced_word())}"

    def __repr__(self) -> str:
        return f"ExtendedAffineWeylGroupElement({str(self)})"

    def __mul__(self, other: "ExtendedAffineWeylGroupElement") -> "ExtendedAffineWeylGroupElement":
        if self._group is not other._group:
            raise TypeError(
                "Cannot multiply elements from different ExtendedAffineWeylGroup instances"
            )

        # (w1, λ1) * (w2, λ2) = (w1*w2, w2^{-1}(λ1) + λ2)
        w_new = self._w * other._w
        word2 = list(other._w.reduced_word())
        w2_coweight = self._group._W_coweight.from_reduced_word(word2)
        lambda_new = w2_coweight.inverse().action(self._lambda) + other._lambda
        return ExtendedAffineWeylGroupElement(self._group, w_new, lambda_new)

    def action(self, weight: Any) -> Any:
        from .affine_weight import AffineWeight

        if not isinstance(weight, AffineWeight):
            # Fallback to Sage's action when possible.
            return self._w.action(weight)

        translated = self._group._translate_affine_weight(self._lambda, weight)
        new_finite = self._w.action(translated.finite_part)
        return AffineWeight(weight.algebra, new_finite, translated.level, translated.grade)

    __call__ = action
