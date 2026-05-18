"""
Kazhdan-Lusztig Polynomials for Coxeter Groups

This module provides computation of Kazhdan-Lusztig polynomials and their
inverse/parabolic variants, essential for character formulas of admissible
representations.

Key features:
    - Standard KL polynomials P_{x,y}(q)
    - Inverse KL polynomials Q_{x,y}(q) on Weyl-group elements
    - Quotient/parabolic inverse KL polynomials Q̃_{[x],[y]}(q) on cosets
    - Integration with SageMath and coxeter3
    - Caching for expensive computations

The quotient inverse KL polynomial Q̃_{[x],[y]}(1) appears in the Kazhdan-Lusztig
character formula for admissible modules:

    ch(L_λ) = Σ Q̃_{[w],[w']}(1) · ch(M(w'·Λ))

References:
    - Kazhdan, D., Lusztig, G. "Representations of Coxeter groups..."
    - Soergel, W. "Kazhdan-Lusztig polynomials and a combinatoric for tilting modules"
    - Cordova, Gaiotto, Shao "Infrared Computations of Defect Schur Indices" (Eq. C.28)
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
from glob import glob
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Any, Dict, Iterable, List, Optional, Tuple, Union

from sage.all import QQ, SR, WeylGroup, matrix, var

if TYPE_CHECKING:
    from .bruhat import BruhatOrder, CosetRepresentative, ParabolicSubgroup
    from .affine_lie_algebra import AffineLieAlgebra


class KazhdanLusztigPolynomials:
    """
    Compute Kazhdan-Lusztig polynomials for Coxeter/Weyl groups.

    This class provides access to standard KL polynomials P_{x,y}(q),
    ordinary inverse KL polynomials Q_{x,y}(q) on Weyl-group elements,
    and quotient/parabolic inverse KL polynomials Q̃_{[x],[y]}(q) on cosets.

    The implementation uses multiple backends:
    1. SageMath's native KazhdanLusztigPolynomial (default)
    2. coxeter3 via invpol method (if available, faster for large groups)

    Parameters
    ----------
    coxeter_group : WeylGroup or CoxeterGroup
        The Coxeter group
    cache_dir : Path, optional
        Directory for caching computed polynomials

    Examples
    --------
    >>> from sage.all import WeylGroup
    >>> W = WeylGroup(['A', 2])
    >>> kl = KazhdanLusztigPolynomials(W)
    >>> s1 = W.simple_reflection(1)
    >>> s2 = W.simple_reflection(2)
    >>> kl.P(W.one(), s1 * s2)  # P_{e, s1s2}(q)
    1

    Notes
    -----
    The ordinary inverse KL polynomial Q_{x,y}(q) is related to P_{x,y}(q) by:
        Σ_z P_{x,z}(q) Q̃_{z,y}(q) = δ_{x,y}

    For the character formula on quotient data, we need Q̃_{[x],[y]}(1).
    """

    def __init__(
        self,
        coxeter_group: Any,
        cache_dir: Optional[Path] = None,
    ) -> None:
        """
        Initialize KL polynomial calculator.

        Parameters
        ----------
        coxeter_group : WeylGroup or CoxeterGroup
            The Coxeter group
        cache_dir : Path, optional
            Directory for caching (default: ~/.pyw/kl_cache)
        """
        self.weyl_group = coxeter_group
        self.cartan_type = coxeter_group.cartan_type()

        # Setup caching
        if cache_dir is None:
            cache_dir = Path.home() / ".pyw" / "kl_cache"
        self._cache_dir = cache_dir
        self._cache_dir.mkdir(parents=True, exist_ok=True)

        # In-memory cache
        self._P_cache: Dict[Tuple[Any, Any], Any] = {}
        self._Q_cache: Dict[Tuple[Any, Any], Any] = {}
        self._invpol_cache: Dict[Tuple[Any, Any], Any] = {}
        self._Q_at_one_cache: Dict[Tuple[Any, Any], Any] = {}
        self._legacy_Q_cache: Dict[Tuple[Tuple[int, ...], Tuple[int, ...]], Any] = {}

        # Initialize SageMath KL calculator
        self._sage_kl = None
        self._coxeter3 = None

        self._setup_backends()

    def _setup_backends(self) -> None:
        """Initialize computation backends."""
        # Try SageMath's native KL
        try:
            from sage.combinat.kazhdan_lusztig import KazhdanLusztigPolynomial
            from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

            # Use polynomial ring instead of symbolic variable to avoid subs() issues
            R = PolynomialRing(QQ, "q")
            q = R.gen()
            self._sage_kl = KazhdanLusztigPolynomial(self.weyl_group, q)
            self._q = q  # Store for substitution
        except ImportError:
            pass

        # Try coxeter3 backend (faster for large groups)
        try:
            from coxeter3_sage import Coxeter3

            command = self._discover_coxeter_command()
            self._coxeter3 = Coxeter3(self.weyl_group, self._q, command=command)
        except (ImportError, Exception):
            # coxeter3 not available or type not supported
            pass

    def _discover_coxeter_command(self) -> str:
        env_command = os.environ.get("PYW_COXETER_COMMAND")
        if env_command:
            return env_command

        direct = shutil.which("coxeter")
        if direct:
            return direct

        candidates = sorted(glob("/private/var/tmp/sage-*/local/bin/coxeter"), reverse=True)
        for candidate in candidates:
            if os.path.isfile(candidate) and os.access(candidate, os.X_OK):
                return candidate

        return "coxeter"

    # =========================================================================
    # Standard KL Polynomials P_{x,y}(q)
    # =========================================================================

    def P(self, x: Any, y: Any, at_one: bool = False) -> Any:
        """
        Compute the Kazhdan-Lusztig polynomial P_{x,y}(q).

        P_{x,y}(q) is defined for x ≤ y in Bruhat order and satisfies:
        - P_{x,x}(q) = 1
        - deg(P_{x,y}) ≤ (ℓ(y) - ℓ(x) - 1) / 2

        Parameters
        ----------
        x, y : Weyl group elements
            Elements with x ≤ y in Bruhat order
        at_one : bool
            If True, return P_{x,y}(1) instead of the polynomial

        Returns
        -------
        polynomial or int
            P_{x,y}(q) or P_{x,y}(1)

        Examples
        --------
        >>> W = WeylGroup(['A', 2])
        >>> kl = KazhdanLusztigPolynomials(W)
        >>> kl.P(W.one(), W.long_element())
        1
        """
        x = self._ensure_element(x)
        y = self._ensure_element(y)

        # Check cache
        cache_key = (self._element_key(x), self._element_key(y))
        if cache_key in self._P_cache:
            p = self._P_cache[cache_key]
            return p.subs({self._q: 1}) if at_one else p

        # Compute using SageMath
        if self._sage_kl is not None:
            p = self._sage_kl.P(x, y)
            self._P_cache[cache_key] = p
            return p.subs({self._q: 1}) if at_one else p

        # Fallback: P_{x,y} = 1 for x = y, need recursive formula otherwise
        raise NotImplementedError(
            "KL polynomial computation requires SageMath's KazhdanLusztigPolynomial"
        )

    # =========================================================================
    # Inverse KL Polynomials Q_{x,y}(q)
    # =========================================================================

    def Q(self, x: Any, y: Any, at_one: bool = False) -> Any:
        """
        Compute the ordinary inverse Kazhdan-Lusztig polynomial Q_{x,y}(q).

        Q_{x,y}(q) satisfies:
            Σ_z P_{x,z}(q) Q̃_{z,y}(q) = δ_{x,y}

        This is the Weyl-group-element-level inverse KL object. It is distinct
        from the quotient/parabolic quantity :meth:`Q_tilde`, whose arguments
        are coset representatives.

        Parameters
        ----------
        x, y : Weyl group elements
            Elements with x ≤ y in Bruhat order
        at_one : bool
            If True, return Q_{x,y}(1)

        Returns
        -------
        polynomial or int
            Q_{x,y}(q) or Q_{x,y}(1)

        Examples
        --------
        >>> W = WeylGroup(['A', 2])
        >>> kl = KazhdanLusztigPolynomials(W)
        >>> kl.Q(W.one(), W.long_element(), at_one=True)
        1
        """
        x = self._ensure_element(x)
        y = self._ensure_element(y)

        cache_key = (self._element_key(x), self._element_key(y))
        if at_one and cache_key in self._Q_at_one_cache:
            return self._Q_at_one_cache[cache_key]
        if not at_one and cache_key in self._Q_cache:
            return self._Q_cache[cache_key]

        if self._coxeter3 is not None and hasattr(self._coxeter3, "invpol"):
            try:
                result = self._coxeter3.invpol(x, y)
                self._Q_cache[cache_key] = result
                if at_one:
                    value_at_one = result.subs({self._q: 1}) if hasattr(result, "subs") else result
                    self._Q_at_one_cache[cache_key] = value_at_one
                    return value_at_one
                return result
            except Exception:
                pass

        if not at_one:
            result = self._compute_inverse_kl_by_matrix_inversion(x, y, at_one=False)
            self._Q_cache[cache_key] = result
            return result

        result = self._compute_inverse_kl_by_matrix_inversion(x, y, at_one=True)
        self._Q_at_one_cache[cache_key] = result
        return result

    def Q_tilde(
        self,
        coset_x: "CosetRepresentative",
        coset_y: "CosetRepresentative",
        at_one: bool = True,
    ) -> Any:
        """
        Compute the quotient/parabolic inverse KL polynomial Q̃_{[x],[y]}(q).

        This is the coset-level object attached to the quotient W / W_I. It is
        implemented by :meth:`parabolic_Q_tilde`, which currently supports
        right cosets in finite Weyl groups.
        """
        return self.parabolic_Q_tilde(coset_x, coset_y, at_one=at_one)

    def invpol(self, x: Any, y: Any) -> Any:
        """
        Compute inverse KL polynomial using coxeter3's invpol.

        This is a direct interface to coxeter3's invpol command,
        which computes the ordinary inverse KL polynomial Q_{x,y}(q)
        efficiently.

        Parameters
        ----------
        x, y : Weyl group elements
            Elements with x ≤ y in Bruhat order

        Returns
        -------
        polynomial
            Q_{x,y}(q) as a symbolic expression

        Raises
        ------
        RuntimeError
            If coxeter3 is not available
        """
        if self._coxeter3 is None:
            raise RuntimeError(
                "coxeter3 backend not available. "
                "Install coxeter3_sage and ensure invpol method is added."
            )

        x = self._ensure_element(x)
        y = self._ensure_element(y)

        # Check cache
        cache_key = (self._element_key(x), self._element_key(y))
        if cache_key in self._invpol_cache:
            return self._invpol_cache[cache_key]

        # Call coxeter3
        result = self._coxeter3.invpol(x, y)
        self._invpol_cache[cache_key] = result
        return result

    def _compute_inverse_kl_by_matrix_inversion(self, x: Any, y: Any, at_one: bool) -> Any:
        from .bruhat import BruhatOrder

        bruhat = BruhatOrder(self.weyl_group)

        if not bruhat.le(x, y):
            return 0

        interval = bruhat.interval(x, y)
        n = len(interval)

        if n == 1:
            return 1

        ring = QQ if at_one else self._q.parent()
        P_mat = matrix(ring, n, n)
        for i, w_i in enumerate(interval):
            for j, w_j in enumerate(interval):
                if bruhat.le(w_i, w_j):
                    P_mat[i, j] = self.P(w_i, w_j, at_one=at_one)

        try:
            Q_mat = P_mat.inverse()
        except Exception as e:
            raise RuntimeError(f"Failed to invert P-matrix: {e}")

        x_idx = interval.index(x)
        y_idx = interval.index(y)

        return Q_mat[x_idx, y_idx]

    # =========================================================================
    # Parabolic (Coset) KL Polynomials
    # =========================================================================

    def parabolic_Q_tilde(
        self,
        coset_x: "CosetRepresentative",
        coset_y: "CosetRepresentative",
        at_one: bool = True,
    ) -> Any:
        """
        Compute parabolic inverse KL polynomial Q̃_{[x],[y]}(q).

        For right cosets [x], [y] in W / W_I, the parabolic
        inverse KL polynomial is computed using the formula from
        Cordova-Gaiotto-Shao (Eq. C.28):

            Q̃_{[x],[y]} = Σ_{z ∈ [y]} Q_{x̄, z} · (-1)^{ℓ(x̄)} · (-1)^{ℓ(z)}

        where x̄ is the maximal representative of [x].

        Parameters
        ----------
        coset_x, coset_y : CosetRepresentative
            Coset representatives
        at_one : bool
            If True (default), evaluate at q=1

        Returns
        -------
        int or polynomial
            Q̃_{[x],[y]}(1) or Q̃_{[x],[y]}(q)

        Notes
        -----
        This formula is from Cordova, Gaiotto, Shao "Infrared Computations
        of Defect Schur Indices", Eq. (C.28).
        """
        from .bruhat import BruhatOrder

        bruhat = BruhatOrder(self.weyl_group)
        parabolic = coset_x._parabolic

        if parabolic != coset_y._parabolic:
            raise ValueError("Coset inputs must use the same parabolic subgroup")
        if coset_x._left != coset_y._left:
            raise ValueError("Coset inputs must use the same left/right convention")
        if coset_x._left:
            raise NotImplementedError("parabolic_Q_tilde currently supports right cosets only")
        if not self.weyl_group.is_finite():
            raise ValueError("parabolic_Q_tilde currently supports finite groups only")

        # Get minimal representatives
        x_min = coset_x.representative
        y_min = coset_y.representative

        # Check Bruhat order on cosets
        if not bruhat.le(x_min, y_min):
            return 0

        # Get maximal representative of [x]
        x_max = self._maximal_representative_in_coset(x_min, parabolic)

        # Sum over elements in coset [y]
        result = 0
        for z in self._enumerate_coset_elements(y_min, parabolic):
            if bruhat.le(x_max, z):
                q_val = self.Q(x_max, z, at_one=at_one)
                sign = (-1) ** (bruhat.length(x_max) + bruhat.length(z))
                result += sign * q_val

        return result

    def affine_bounded_interval(
        self,
        x: Any,
        y: Any,
        *,
        candidates: Iterable[Any],
    ) -> List[Any]:
        """Bruhat interval restricted to an explicit bounded affine candidate set."""
        from .bruhat import BruhatOrder

        bruhat = BruhatOrder(self.weyl_group)
        coerced = [self._ensure_element(w) for w in candidates]
        return bruhat.interval_from_candidates(self._ensure_element(x), self._ensure_element(y), coerced)

    def affine_bounded_Q(
        self,
        x: Any,
        y: Any,
        *,
        candidates: Iterable[Any],
        at_one: bool = True,
    ) -> Any:
        """Compute ordinary inverse KL polynomial on a bounded affine interval.

        For affine groups, direct interval enumeration is infinite globally but
        locally finite. This helper lets callers provide an explicit bounded
        candidate set coming from translation bounds, then performs the same
        matrix-inversion construction used by the finite fallback.
        """
        from .bruhat import BruhatOrder

        bruhat = BruhatOrder(self.weyl_group)
        x = self._ensure_element(x)
        y = self._ensure_element(y)

        if not bruhat.le(x, y):
            return 0

        interval = self.affine_bounded_interval(x, y, candidates=candidates)
        if x not in interval or y not in interval:
            raise ValueError("bounded candidate set must contain both interval endpoints")

        n = len(interval)
        if n == 1:
            return 1

        ring = QQ if at_one else self._q.parent()
        p_matrix = matrix(ring, n, n)
        for i, w_i in enumerate(interval):
            for j, w_j in enumerate(interval):
                if bruhat.le(w_i, w_j):
                    p_matrix[i, j] = self.P(w_i, w_j, at_one=at_one)

        q_matrix = p_matrix.inverse()
        return q_matrix[interval.index(x), interval.index(y)]

    def affine_bounded_Q_tilde(
        self,
        x: Any,
        y: Any,
        *,
        candidates: Iterable[Any],
        at_one: bool = True,
    ) -> Any:
        """Legacy alias for :meth:`affine_bounded_Q`.

        Historically this helper was misnamed as if it computed a quotient
        object. It actually computes the ordinary inverse KL polynomial Q on a
        bounded affine Bruhat interval.
        """
        return self.affine_bounded_Q(x, y, candidates=candidates, at_one=at_one)

    def affine_stabilizer(
        self,
        Lambda: Any,
        *,
        rho_hat: Any,
        candidates: Iterable[Any],
        algebra: Optional["AffineLieAlgebra"] = None,
    ) -> List[Any]:
        """Return the bounded affine stabilizer of ``Lambda`` under the dot action.

        When ``algebra`` is provided, candidate elements are interpreted through
        the semidirect-product affine Weyl wrapper so their action is evaluated
        on affine weights rather than Sage's default root-domain action.
        """
        from .affine_weight import AffineWeight

        result: List[Any] = []
        semidirect = algebra.affine_weyl_group() if algebra is not None else None
        target = Lambda + rho_hat
        target_affine = None
        rho_hat_affine = None
        Lambda_affine = None

        if algebra is not None:
            target_affine = AffineWeight.from_sagemath(algebra, target)
            rho_hat_affine = AffineWeight.from_sagemath(algebra, rho_hat)
            Lambda_affine = AffineWeight.from_sagemath(algebra, Lambda)

        for w in candidates:
            if semidirect is not None:
                if hasattr(w, "reduced_word"):
                    affine_word = w.word() if hasattr(w, "word") else tuple(int(i) for i in w.reduced_word())
                    element = semidirect.from_word(affine_word)
                    stabilized = element.action(target_affine)
                else:
                    element = w
                    stabilized = element.action(target_affine)

                if stabilized - rho_hat_affine == Lambda_affine:
                    if hasattr(w, "reduced_word"):
                        affine_word = w.word() if hasattr(w, "word") else tuple(int(i) for i in w.reduced_word())
                        result.append(self.weyl_group.from_reduced_word(affine_word))
                    else:
                        affine_word = element.word() if hasattr(element, "word") else tuple(int(i) for i in element.reduced_word())
                        result.append(self.weyl_group.from_reduced_word(affine_word))
                continue

            element = self._ensure_element(w)
            if element.action(target) - rho_hat == Lambda:
                result.append(element)

        identity = self.weyl_group.one()
        if all(self._element_key(w) != self._element_key(identity) for w in result):
            result.append(identity)

        return sorted(result, key=lambda w: (int(w.length()), tuple(w.reduced_word())))

    def affine_bounded_parabolic_Q_tilde(
        self,
        x_min: Any,
        y_min: Any,
        *,
        candidates: Iterable[Any],
        stabilizer_candidates: Iterable[Any],
        at_one: bool = True,
    ) -> Any:
        """Compute bounded affine coset-level Q̃ using an explicit stabilizer set."""
        from .bruhat import BruhatOrder

        bruhat = BruhatOrder(self.weyl_group)
        x_min = self._ensure_element(x_min)
        y_min = self._ensure_element(y_min)
        bounded_candidates = [self._ensure_element(w) for w in candidates]
        stabilizer = [self._ensure_element(w) for w in stabilizer_candidates]

        if not bruhat.le(x_min, y_min):
            return 0

        x_max = self._bounded_maximal_representative(x_min, stabilizer=stabilizer)
        result = 0
        for z in self._bounded_right_coset_elements(y_min, stabilizer=stabilizer, candidates=bounded_candidates):
            if bruhat.le(x_max, z):
                q_val = self.affine_bounded_Q(x_max, z, candidates=bounded_candidates, at_one=at_one)
                sign = (-1) ** (bruhat.length(x_max) + bruhat.length(z))
                result += sign * q_val

        return result

    def _bounded_maximal_representative(self, w_min: Any, *, stabilizer: Iterable[Any]) -> Any:
        """Find the maximal representative inside a bounded right coset."""
        current = self._ensure_element(w_min)
        current_length = int(current.length())
        for s in stabilizer:
            candidate = current * self._ensure_element(s)
            candidate_length = int(candidate.length())
            if candidate_length > current_length:
                current = candidate
                current_length = candidate_length
        return current

    def _bounded_right_coset_elements(
        self,
        w_min: Any,
        *,
        stabilizer: Iterable[Any],
        candidates: Iterable[Any],
    ) -> List[Any]:
        """Enumerate right-coset elements present in a bounded candidate set."""
        candidate_set = {
            self._element_key(self._ensure_element(w)): self._ensure_element(w) for w in candidates
        }
        result: Dict[Tuple[int, ...], Any] = {}
        base = self._ensure_element(w_min)
        for s in stabilizer:
            candidate = base * self._ensure_element(s)
            key = self._element_key(candidate)
            if key in candidate_set:
                result[key] = candidate_set[key]
        if self._element_key(base) not in result and self._element_key(base) in candidate_set:
            result[self._element_key(base)] = candidate_set[self._element_key(base)]
        return sorted(result.values(), key=lambda w: (int(w.length()), tuple(w.reduced_word())))

    def _maximal_representative_in_coset(self, w_min: Any, parabolic: "ParabolicSubgroup") -> Any:
        """Find the maximal length representative of a coset."""
        from .bruhat import BruhatOrder

        bruhat = BruhatOrder(self.weyl_group)

        # Start from minimal rep and multiply by longest element of W_I
        # The maximal rep is w_min * w_I^0 where w_I^0 is longest in W_I
        current = w_min
        changed = True
        while changed:
            changed = False
            for i in parabolic.generators:
                s_i = self.weyl_group.simple_reflection(i)
                product = current * s_i
                if bruhat.length(product) > bruhat.length(current):
                    current = product
                    changed = True
                    break
        return current

    def _enumerate_coset_elements(self, w_min: Any, parabolic: "ParabolicSubgroup") -> List[Any]:
        """Get all elements in the coset of w_min."""
        from .bruhat import BruhatOrder

        bruhat = BruhatOrder(self.weyl_group)

        # Generate coset by multiplying w_min by all elements of W_I
        result = [w_min]
        queue = [w_min]
        visited = {self._element_key(w_min)}

        while queue:
            current = queue.pop(0)
            for i in parabolic.generators:
                s_i = self.weyl_group.simple_reflection(i)
                # Right multiplication for right cosets
                new_elem = current * s_i
                key = self._element_key(new_elem)
                if key not in visited:
                    visited.add(key)
                    result.append(new_elem)
                    queue.append(new_elem)

        return result

    # =========================================================================
    # Caching and Persistence
    # =========================================================================

    def save_cache(self, filename: Optional[str] = None) -> Path:
        """
        Save computed polynomials to disk.

        Parameters
        ----------
        filename : str, optional
            Filename (default: based on Cartan type)

        Returns
        -------
        Path
            Path to saved cache file
        """
        if filename is None:
            ct_str = str(self.cartan_type).replace(" ", "_")
            filename = f"kl_cache_{ct_str}.json"

        filepath = self._cache_dir / filename

        # Convert cache to serializable format
        cache_data = {
            "cache_version": self.CACHE_VERSION,
            "cartan_type": str(self.cartan_type),
            "value_kind": "Q_at_one",
            "Q_at_one_cache": {
                self._cache_key_to_string(k): self._json_scalar(v)
                for k, v in self._Q_at_one_cache.items()
            },
        }

        with open(filepath, "w") as f:
            json.dump(cache_data, f, indent=2)

        return filepath

    def load_cache(self, filename: Optional[str] = None) -> bool:
        """
        Load cached polynomials from disk.

        Parameters
        ----------
        filename : str, optional
            Filename (default: based on Cartan type)

        Returns
        -------
        bool
            True if cache was loaded successfully
        """
        if filename is None:
            ct_str = str(self.cartan_type).replace(" ", "_")
            filename = f"kl_cache_{ct_str}.json"

        filepath = self._cache_dir / filename

        if not filepath.exists():
            return False

        try:
            with open(filepath) as f:
                cache_data = json.load(f)

            if cache_data.get("cache_version") != self.CACHE_VERSION:
                return False

            if cache_data.get("cartan_type") != str(self.cartan_type):
                return False

            if cache_data.get("value_kind") not in {"Q_at_one", "Q_tilde_at_one"}:
                return False

            for key_str, value in cache_data.get("Q_at_one_cache", {}).items():
                self._Q_at_one_cache[self._parse_cache_key(key_str)] = value

            return True
        except Exception:
            return False

    # =========================================================================
    # Internal Methods
    # =========================================================================

    def _ensure_element(self, w: Any) -> Any:
        """Ensure w is an element of self.weyl_group."""
        if hasattr(w, "parent") and w.parent() == self.weyl_group:
            return w
        if isinstance(w, (list, tuple)):
            return self.weyl_group.from_reduced_word(w)
        return w

    def _element_key(self, w: Any) -> Tuple[int, ...]:
        """Get a hashable key for a Weyl group element."""
        if hasattr(w, "reduced_word"):
            return tuple(w.reduced_word())
        return (0,)  # Identity

    def _cache_key_to_string(self, cache_key: Tuple[Tuple[int, ...], Tuple[int, ...]]) -> str:
        return json.dumps([list(cache_key[0]), list(cache_key[1])])

    def _parse_cache_key(self, key_str: str) -> Tuple[Tuple[int, ...], Tuple[int, ...]]:
        left, right = json.loads(key_str)
        return (tuple(left), tuple(right))

    def _json_scalar(self, value: Any) -> Any:
        if isinstance(value, (int, float, str, bool)) or value is None:
            return value
        if hasattr(value, "is_integer") and value.is_integer():
            return int(value)
        try:
            return int(value)
        except (TypeError, ValueError):
            try:
                return float(value)
            except (TypeError, ValueError):
                return str(value)

    CACHE_VERSION = 1
