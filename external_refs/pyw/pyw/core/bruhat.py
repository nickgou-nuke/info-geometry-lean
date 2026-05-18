"""
Bruhat Order for Coxeter Groups

This module provides Bruhat partial order utilities for finite and affine
Weyl groups, essential for Kazhdan-Lusztig theory and character computations.

The Bruhat order is a partial order on Coxeter groups defined by:
    w ≤ w' iff some reduced expression for w can be obtained by
    deleting simple reflections from some reduced expression for w'.

Key features:
    - Bruhat comparison for Weyl group elements
    - Bruhat intervals [w, w']
    - Parabolic coset representatives
    - Integration with SageMath's Coxeter group implementation

References:
    - Björner, A., Brenti, F. "Combinatorics of Coxeter Groups"
    - Humphreys, J. E. "Reflection Groups and Coxeter Groups"
    - Kazhdan, D., Lusztig, G. "Representations of Coxeter groups..."
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, Iterator, List, Optional, Set, Union

from sage.all import CoxeterGroup, WeylGroup, QQ

if TYPE_CHECKING:
    from .affine_lie_algebra import AffineLieAlgebra


class BruhatOrder:
    """
    Bruhat partial order utilities for Coxeter/Weyl groups.

    This class provides methods for comparing elements in Bruhat order,
    computing Bruhat intervals, and working with parabolic cosets.

    The implementation delegates to SageMath's built-in Bruhat order
    methods when available, with fallbacks for edge cases.

    Parameters
    ----------
    coxeter_group : CoxeterGroup or WeylGroup
        The Coxeter group (can be finite or affine type)

    Examples
    --------
    >>> from sage.all import WeylGroup
    >>> W = WeylGroup(['A', 2])
    >>> bruhat = BruhatOrder(W)
    >>> s1 = W.simple_reflection(1)
    >>> s2 = W.simple_reflection(2)
    >>> bruhat.le(s1, s1 * s2)  # True: s1 ≤ s1*s2
    True

    Notes
    -----
    For affine Weyl groups, the Bruhat order is infinite but locally finite:
    any Bruhat interval [w, w'] is finite.
    """

    def __init__(self, coxeter_group: Any) -> None:
        """
        Initialize BruhatOrder for a Coxeter group.

        Parameters
        ----------
        coxeter_group : CoxeterGroup or WeylGroup
            A SageMath Coxeter or Weyl group object
        """
        self.weyl_group = coxeter_group
        self.cartan_type = coxeter_group.cartan_type()

    @classmethod
    def from_cartan_type(cls, cartan_type: Union[str, list, tuple]) -> "BruhatOrder":
        """
        Create BruhatOrder from a Cartan type specification.

        Parameters
        ----------
        cartan_type : str, list, or tuple
            Cartan type, e.g., 'A2', ['A', 2], or ['A', 2, 1] for affine

        Returns
        -------
        BruhatOrder
            A new BruhatOrder instance

        Examples
        --------
        >>> bruhat = BruhatOrder.from_cartan_type(['A', 2, 1])
        >>> bruhat.cartan_type
        ['A', 2, 1]
        """
        W = WeylGroup(cartan_type)
        return cls(W)

    @classmethod
    def from_algebra(cls, algebra: "AffineLieAlgebra") -> "BruhatOrder":
        """
        Create BruhatOrder from an AffineLieAlgebra.

        Parameters
        ----------
        algebra : AffineLieAlgebra
            The affine Lie algebra

        Returns
        -------
        BruhatOrder
            A new BruhatOrder instance
        """
        return cls.from_cartan_type(algebra._cartan_type)

    # =========================================================================
    # Bruhat Order Comparison
    # =========================================================================

    def le(self, w1: Any, w2: Any) -> bool:
        """
        Check if w1 ≤ w2 in Bruhat order.

        Parameters
        ----------
        w1, w2 : Weyl group elements
            Elements to compare

        Returns
        -------
        bool
            True if w1 ≤ w2 in Bruhat order

        Examples
        --------
        >>> W = WeylGroup(['A', 2])
        >>> bruhat = BruhatOrder(W)
        >>> e = W.one()
        >>> s1 = W.simple_reflection(1)
        >>> bruhat.le(e, s1)  # Identity ≤ any element
        True
        """
        # Ensure elements are in the same group
        w1 = self._ensure_element(w1)
        w2 = self._ensure_element(w2)

        # Use SageMath's built-in bruhat_le if available
        if hasattr(w1, "bruhat_le"):
            return w1.bruhat_le(w2)

        # Fallback: use the subword property
        return self._bruhat_le_subword(w1, w2)

    def lt(self, w1: Any, w2: Any) -> bool:
        """
        Check if w1 < w2 in Bruhat order (strict).

        Parameters
        ----------
        w1, w2 : Weyl group elements
            Elements to compare

        Returns
        -------
        bool
            True if w1 < w2 (w1 ≤ w2 and w1 ≠ w2)
        """
        return self.le(w1, w2) and w1 != w2

    def ge(self, w1: Any, w2: Any) -> bool:
        """Check if w1 ≥ w2 in Bruhat order."""
        return self.le(w2, w1)

    def gt(self, w1: Any, w2: Any) -> bool:
        """Check if w1 > w2 in Bruhat order (strict)."""
        return self.lt(w2, w1)

    def comparable(self, w1: Any, w2: Any) -> bool:
        """
        Check if w1 and w2 are comparable in Bruhat order.

        Parameters
        ----------
        w1, w2 : Weyl group elements
            Elements to check

        Returns
        -------
        bool
            True if w1 ≤ w2 or w2 ≤ w1
        """
        return self.le(w1, w2) or self.le(w2, w1)

    # =========================================================================
    # Bruhat Intervals
    # =========================================================================

    def interval(self, w1: Any, w2: Any) -> List[Any]:
        """
        Compute the Bruhat interval [w1, w2].

        The Bruhat interval [w1, w2] is the set of all elements w
        such that w1 ≤ w ≤ w2.

        Parameters
        ----------
        w1, w2 : Weyl group elements
            Lower and upper bounds

        Returns
        -------
        list
            List of elements in [w1, w2], sorted by length

        Raises
        ------
        ValueError
            If w1 > w2 (empty interval)

        Examples
        --------
        >>> W = WeylGroup(['A', 2])
        >>> bruhat = BruhatOrder(W)
        >>> e = W.one()
        >>> s1s2 = W.simple_reflection(1) * W.simple_reflection(2)
        >>> interval = bruhat.interval(e, s1s2)
        >>> len(interval)  # e, s1, s2, s1*s2
        4
        """
        w1 = self._ensure_element(w1)
        w2 = self._ensure_element(w2)

        if not self.le(w1, w2):
            raise ValueError(f"Empty interval: {w1} is not ≤ {w2}")

        # Use SageMath's bruhat_interval if available
        if hasattr(self.weyl_group, "bruhat_interval"):
            interval = list(self.weyl_group.bruhat_interval(w1, w2))
            return sorted(interval, key=lambda w: (self.length(w), tuple(self.reduced_word(w))))

        # Fallback: enumerate by BFS from w1
        return self._bruhat_interval_bfs(w1, w2)

    def interval_size(self, w1: Any, w2: Any) -> int:
        """
        Compute the size of Bruhat interval [w1, w2].

        Parameters
        ----------
        w1, w2 : Weyl group elements
            Lower and upper bounds

        Returns
        -------
        int
            Number of elements in [w1, w2]
        """
        return len(self.interval(w1, w2))

    def interval_from_candidates(self, w1: Any, w2: Any, candidates: List[Any]) -> List[Any]:
        w1 = self._ensure_element(w1)
        w2 = self._ensure_element(w2)

        if not self.le(w1, w2):
            raise ValueError(f"Empty interval: {w1} is not ≤ {w2}")

        filtered = [w for w in candidates if self.le(w1, w) and self.le(w, w2)]
        return sorted(filtered, key=lambda w: (self.length(w), tuple(self.reduced_word(w))))

    # =========================================================================
    # Length Function
    # =========================================================================

    def length(self, w: Any) -> int:
        """
        Get the length of a Weyl group element.

        The length ℓ(w) is the minimum number of simple reflections
        needed to express w.

        Parameters
        ----------
        w : Weyl group element
            The element

        Returns
        -------
        int
            The length ℓ(w)
        """
        w = self._ensure_element(w)
        if hasattr(w, "length"):
            return int(w.length())
        if hasattr(w, "reduced_word_list"):
            return len(w.reduced_word_list())
        return len(w.reduced_word())

    def reduced_word(self, w: Any) -> List[int]:
        """
        Get a reduced word for a Weyl group element.

        Parameters
        ----------
        w : Weyl group element
            The element

        Returns
        -------
        list[int]
            A reduced word (list of simple reflection indices)
        """
        w = self._ensure_element(w)
        if hasattr(w, "reduced_word_list"):
            return list(w.reduced_word_list())
        return list(w.reduced_word())

    # =========================================================================
    # Parabolic Subgroups and Cosets
    # =========================================================================

    def parabolic_subgroup(self, generators: Set[int]) -> "ParabolicSubgroup":
        """
        Create a parabolic subgroup W_I generated by simple reflections in I.

        Parameters
        ----------
        generators : set[int]
            Set of simple reflection indices generating the parabolic subgroup

        Returns
        -------
        ParabolicSubgroup
            The parabolic subgroup W_I

        Examples
        --------
        >>> W = WeylGroup(['A', 3])
        >>> bruhat = BruhatOrder(W)
        >>> W_I = bruhat.parabolic_subgroup({1, 2})  # Generated by s1, s2
        """
        return ParabolicSubgroup(self, generators)

    # =========================================================================
    # Internal Methods
    # =========================================================================

    def _ensure_element(self, w: Any) -> Any:
        """Ensure w is an element of self.weyl_group."""
        if hasattr(w, "parent") and w.parent() == self.weyl_group:
            return w
        # Try to convert
        if isinstance(w, (list, tuple)):
            # Assume it's a reduced word
            return self.weyl_group.from_reduced_word(w)
        return w

    def _bruhat_le_subword(self, w1: Any, w2: Any) -> bool:
        """
        Check Bruhat order using the subword property.

        w1 ≤ w2 iff some reduced word for w1 is a subword of
        some reduced word for w2.

        This is a fallback when bruhat_le is not available.
        """
        word1 = self.reduced_word(w1)
        word2 = self.reduced_word(w2)

        # Quick length check
        if len(word1) > len(word2):
            return False

        # Check if word1 is a subword of word2
        return self._is_subword(word1, word2)

    def _is_subword(self, short: List[int], long: List[int]) -> bool:
        """Check if short is a subword of long."""
        if not short:
            return True
        if len(short) > len(long):
            return False

        j = 0
        for i in range(len(long)):
            if long[i] == short[j]:
                j += 1
                if j == len(short):
                    return True
        return False

    def _bruhat_interval_bfs(self, w1: Any, w2: Any) -> List[Any]:
        """
        Compute Bruhat interval using BFS.

        Start from w1 and explore upward in Bruhat order.
        """
        result = [w1]
        if w1 == w2:
            return result

        # BFS from w1
        visited = {w1}
        queue = [w1]
        target_length = self.length(w2)

        while queue:
            current = queue.pop(0)
            current_length = self.length(current)

            if current_length >= target_length:
                continue

            # Try multiplying by each simple reflection
            for i in self.weyl_group.index_set():
                s_i = self.weyl_group.simple_reflection(i)

                # Try right multiplication
                next_w = current * s_i
                if next_w not in visited:
                    if self.le(w1, next_w) and self.le(next_w, w2):
                        visited.add(next_w)
                        result.append(next_w)
                        queue.append(next_w)

        # Sort by length
        result.sort(key=lambda w: self.length(w))
        return result


@dataclass
class ParabolicSubgroup:
    """
    A parabolic subgroup W_I of a Coxeter group W.

    A parabolic subgroup is generated by a subset I of simple reflections.
    It is used for computing coset representatives and parabolic KL polynomials.

    Parameters
    ----------
    bruhat : BruhatOrder
        The parent Bruhat order
    generators : set[int]
        Set of simple reflection indices generating W_I

    Attributes
    ----------
    generators : set[int]
        The generating set I
    complement : set[int]
        The complement S \\ I of simple reflections

    Examples
    --------
    >>> W = WeylGroup(['A', 3])
    >>> bruhat = BruhatOrder(W)
    >>> W_I = bruhat.parabolic_subgroup({1, 2})
    >>> # W_I is generated by s1, s2 (isomorphic to S3)
    """

    bruhat: BruhatOrder
    generators: Set[int]

    def __post_init__(self):
        """Validate and compute complement."""
        self.weyl_group = self.bruhat.weyl_group
        self._all_indices = set(self.weyl_group.index_set())
        self.complement = self._all_indices - self.generators

    def contains(self, w: Any) -> bool:
        """
        Check if w is in the parabolic subgroup W_I.

        An element w is in W_I iff all simple reflections in any
        reduced word for w are in I.

        Parameters
        ----------
        w : Weyl group element
            The element to check

        Returns
        -------
        bool
            True if w ∈ W_I
        """
        word = self.bruhat.reduced_word(w)
        return all(s in self.generators for s in word)

    def minimal_coset_representative(self, w: Any, left: bool = True) -> Any:
        """
        Find the minimal length representative of w's coset.

        For left cosets W_I \\ W: find unique w^I with ℓ(w^I) minimal
        such that w = u * w^I for some u ∈ W_I.

        For right cosets W / W_I: find unique ^I w with ℓ(^I w) minimal
        such that w = ^I w * u for some u ∈ W_I.

        Parameters
        ----------
        w : Weyl group element
            The element
        left : bool
            If True, compute left coset representative (W_I \\ W)
            If False, compute right coset representative (W / W_I)

        Returns
        -------
        Weyl group element
            The minimal coset representative
        """
        w = self.bruhat._ensure_element(w)

        if left:
            # Left coset W_I \\ W: minimal rep has no left descent in I
            return self._minimal_left_coset_rep(w)
        else:
            # Right coset W / W_I: minimal rep has no right descent in I
            return self._minimal_right_coset_rep(w)

    def _minimal_left_coset_rep(self, w: Any) -> Any:
        """Find minimal representative for left coset W_I * w."""
        current = w
        changed = True
        while changed:
            changed = False
            for i in self.generators:
                s_i = self.weyl_group.simple_reflection(i)
                # Check if s_i * current has smaller length
                product = s_i * current
                if self.bruhat.length(product) < self.bruhat.length(current):
                    current = product
                    changed = True
                    break
        return current

    def _minimal_right_coset_rep(self, w: Any) -> Any:
        """Find minimal representative for right coset w * W_I."""
        current = w
        changed = True
        while changed:
            changed = False
            for i in self.generators:
                s_i = self.weyl_group.simple_reflection(i)
                # Check if current * s_i has smaller length
                product = current * s_i
                if self.bruhat.length(product) < self.bruhat.length(current):
                    current = product
                    changed = True
                    break
        return current

    def coset_representatives(
        self, max_length: Optional[int] = None, left: bool = True
    ) -> Iterator[Any]:
        """
        Iterate over minimal coset representatives.

        Parameters
        ----------
        max_length : int, optional
            Maximum length of representatives to return
        left : bool
            If True, iterate left coset reps (W_I \\ W)
            If False, iterate right coset reps (W / W_I)

        Yields
        ------
        Weyl group element
            Minimal coset representatives in order of increasing length
        """
        # For finite groups, enumerate all elements
        # For affine groups, need max_length bound
        if max_length is None:
            if self.weyl_group.is_finite():
                elements = list(self.weyl_group)
            else:
                raise ValueError("max_length required for infinite groups")
        else:
            elements = self._enumerate_up_to_length(max_length)

        seen_cosets: Set[Any] = set()
        for w in sorted(elements, key=lambda x: self.bruhat.length(x)):
            rep = self.minimal_coset_representative(w, left=left)
            rep_key = tuple(self.bruhat.reduced_word(rep))
            if rep_key not in seen_cosets:
                seen_cosets.add(rep_key)
                yield rep

    def _enumerate_up_to_length(self, max_length: int) -> List[Any]:
        """Enumerate Weyl group elements up to given length."""
        result = [self.weyl_group.one()]
        current_level = [self.weyl_group.one()]

        for _ in range(max_length):
            next_level = []
            for w in current_level:
                for i in self.weyl_group.index_set():
                    s_i = self.weyl_group.simple_reflection(i)
                    # Right multiplication
                    w_new = w * s_i
                    if self.bruhat.length(w_new) == self.bruhat.length(w) + 1:
                        if w_new not in result:
                            result.append(w_new)
                            next_level.append(w_new)
            current_level = next_level
            if not current_level:
                break

        return result


class CosetRepresentative:
    """
    A coset representative [w] in W / W_I or W_I \\ W.

    This class wraps a minimal-length representative and provides
    comparison methods using Bruhat order on representatives.

    Parameters
    ----------
    representative : Weyl group element
        The minimal-length coset representative
    parabolic : ParabolicSubgroup
        The parabolic subgroup defining the cosets
    left : bool
        True for left cosets (W_I \\ W), False for right (W / W_I)
    """

    def __init__(self, representative: Any, parabolic: ParabolicSubgroup, left: bool = True):
        self.representative = parabolic.minimal_coset_representative(representative, left=left)
        self._parabolic = parabolic
        self._left = left
        self._bruhat = parabolic.bruhat

    @property
    def length(self) -> int:
        """Length of the representative."""
        return self._bruhat.length(self.representative)

    def bruhat_le(self, other: "CosetRepresentative") -> bool:
        """
        Compare cosets in Bruhat order.

        [w] ≤ [w'] iff w_min ≤ w'_min where w_min, w'_min are
        the minimal representatives.

        Parameters
        ----------
        other : CosetRepresentative
            The other coset

        Returns
        -------
        bool
            True if self ≤ other in Bruhat order on cosets
        """
        if self._parabolic != other._parabolic or self._left != other._left:
            raise ValueError("Cannot compare cosets from different parabolic data")
        return self._bruhat.le(self.representative, other.representative)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CosetRepresentative):
            return False
        return (
            self.representative == other.representative
            and self._parabolic == other._parabolic
            and self._left == other._left
        )

    def __hash__(self) -> int:
        return hash(
            (
                tuple(sorted(self._parabolic.generators)),
                self._left,
                tuple(self._bruhat.reduced_word(self.representative)),
            )
        )

    def __repr__(self) -> str:
        word = self._bruhat.reduced_word(self.representative)
        if not word:
            return "[1]"
        return f"[{'*'.join(f's{i}' for i in word)}]"
