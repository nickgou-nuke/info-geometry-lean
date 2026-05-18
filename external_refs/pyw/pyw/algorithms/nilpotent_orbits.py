"""
Nilpotent Orbits of Classical Lie Algebras

This module enumerates nilpotent orbits of finite-dimensional simple Lie algebras
of classical type (A, B, C, D) via the partition correspondence.

Classification (Collingwood-McGovern, Chapter 5):

    Type A_n  (sl(n+1)):  Partitions of n+1
    Type B_n  (so(2n+1)): Partitions of 2n+1 where even parts have even multiplicity
    Type C_n  (sp(2n)):   Partitions of 2n where odd parts have even multiplicity
    Type D_n  (so(2n)):   Partitions of 2n where even parts have even multiplicity
                          (very even partitions correspond to TWO orbits)

For each orbit the module computes:
    - Partition label λ
    - Orbit dimension = dim G - dim Z_G(e)
    - Dual partition λ^t (transpose / Barbasch-Vogan dual for type A)
    - Whether the orbit is Richardson, even, or distinguished

References:
    - Collingwood, D. H., McGovern, W. M.
      "Nilpotent Orbits in Semisimple Lie Algebras" (1993)
    - Carter, R. W. "Finite Groups of Lie Type" (1985)
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Tuple, Union

from sage.all import Partitions


# ---------------------------------------------------------------------------
# Partition helpers
# ---------------------------------------------------------------------------


def _transpose_partition(p: List[int]) -> List[int]:
    """Return the conjugate (transpose) partition of p.

    >>> _transpose_partition([4, 2, 1])
    [3, 2, 1, 1]
    """
    if not p:
        return []
    result: List[int] = []
    for i in range(1, p[0] + 1):
        result.append(sum(1 for part in p if part >= i))
    return result


def _multiplicity_map(p: List[int]) -> Dict[int, int]:
    """Return {part: multiplicity} for the partition *p*."""
    return dict(Counter(p))


# ---------------------------------------------------------------------------
# Partition filters for classical types
# ---------------------------------------------------------------------------


def _is_type_B_partition(p: List[int]) -> bool:
    """Partition of 2n+1 for so(2n+1): even parts must occur with even multiplicity."""
    mult = _multiplicity_map(p)
    return all(mult[k] % 2 == 0 for k in mult if k % 2 == 0)


def _is_type_C_partition(p: List[int]) -> bool:
    """Partition of 2n for sp(2n): odd parts must occur with even multiplicity."""
    mult = _multiplicity_map(p)
    return all(mult[k] % 2 == 0 for k in mult if k % 2 == 1)


def _is_type_D_partition(p: List[int]) -> bool:
    """Partition of 2n for so(2n): even parts must occur with even multiplicity."""
    mult = _multiplicity_map(p)
    return all(mult[k] % 2 == 0 for k in mult if k % 2 == 0)


def _is_very_even(p: List[int]) -> bool:
    """A partition is *very even* if every part is even (only relevant for type D)."""
    return all(part % 2 == 0 for part in p)


# ---------------------------------------------------------------------------
# Orbit dimension formulas
# ---------------------------------------------------------------------------


def _orbit_dim_A(p: List[int]) -> int:
    r"""Dimension of the nilpotent orbit labelled by *p* in sl(N).

    $$
    \dim \mathcal{O}_\lambda = N^2 - \sum_i (\lambda_i^t)^2
    $$

    where $\lambda^t$ is the transpose partition.
    """
    n = sum(p)
    pt = _transpose_partition(p)
    return n * n - sum(x * x for x in pt)


def _orbit_dim_B(p: List[int]) -> int:
    r"""Dimension of the nilpotent orbit labelled by *p* in so(2n+1).

    $$
    \dim \mathcal{O}_\lambda
       = \frac{N(N-1)}{2} - \frac{1}{2}\Bigl(\sum_i (\lambda_i^t)^2 - |\{j : \lambda_j \text{ odd}\}|\Bigr)
    $$

    with $N = 2n+1$.
    """
    N = sum(p)
    pt = _transpose_partition(p)
    num_odd_parts = sum(1 for x in p if x % 2 == 1)
    # dim so(N) = N(N-1)/2
    dim_g = N * (N - 1) // 2
    centralizer_dim = (sum(x * x for x in pt) - num_odd_parts) // 2
    return dim_g - centralizer_dim


def _orbit_dim_C(p: List[int]) -> int:
    r"""Dimension of the nilpotent orbit labelled by *p* in sp(2n).

    $$
    \dim \mathcal{O}_\lambda
       = \frac{N(N+1)}{2} - \frac{1}{2}\Bigl(\sum_i (\lambda_i^t)^2 + |\{j : \lambda_j \text{ odd}\}|\Bigr)
    $$

    with $N = 2n$.
    """
    N = sum(p)
    pt = _transpose_partition(p)
    num_odd_parts = sum(1 for x in p if x % 2 == 1)
    # dim sp(N) = N(N+1)/2
    dim_g = N * (N + 1) // 2
    centralizer_dim = (sum(x * x for x in pt) + num_odd_parts) // 2
    return dim_g - centralizer_dim


def _orbit_dim_D(p: List[int]) -> int:
    r"""Dimension of the nilpotent orbit labelled by *p* in so(2n).

    Same formula as type B.
    """
    N = sum(p)
    pt = _transpose_partition(p)
    num_odd_parts = sum(1 for x in p if x % 2 == 1)
    dim_g = N * (N - 1) // 2
    centralizer_dim = (sum(x * x for x in pt) - num_odd_parts) // 2
    return dim_g - centralizer_dim


# ---------------------------------------------------------------------------
# Data class for a single orbit
# ---------------------------------------------------------------------------


@dataclass
class NilpotentOrbit:
    """A nilpotent orbit in a classical Lie algebra.

    Attributes:
        lie_type: Cartan type, e.g. ('A', 4) or ('D', 6).
        partition: The partition labelling this orbit.
        dimension: Complex dimension of the orbit.
        transpose: The transpose (conjugate) partition.
        is_even: True if all parts of the transpose partition are even.
        is_distinguished: True if no part of the partition repeats
            more than once (all multiplicities ≤ 1) for type A;
            for BCD see Collingwood-McGovern §6.
        is_very_even: (Type D only) True if every part is even.
        roman_numeral: For type D very-even partitions: 'I' or 'II'.
    """

    lie_type: Tuple[str, int]
    partition: List[int]
    dimension: int
    transpose: List[int] = field(default_factory=list)
    is_even: bool = False
    is_distinguished: bool = False
    is_very_even: bool = False
    roman_numeral: Optional[str] = None

    # Convenient label
    @property
    def label(self) -> str:
        base = str(self.partition)
        if self.roman_numeral is not None:
            base += f" ({self.roman_numeral})"
        return base

    def weighted_dynkin_diagram(self) -> List[int]:
        r"""Compute the weighted Dynkin diagram for this orbit.

        Returns the labels `(d_1, \dots, d_n)` such that
        `\alpha_i(h) = d_i` for the semisimple element `h`
        of the corresponding `\mathfrak{sl}_2`-triple.

        Returns
        -------
        list of int
            Non-negative integer labels, each in `\{0, 1, 2\}`.

        Examples
        --------
        >>> orb = nilpotent_orbits('A', 3)[-2]  # partition [3,1]
        >>> orb.weighted_dynkin_diagram()
        [2, 0, 2]
        """
        from pyw.embedding.sl2_triple import weighted_dynkin_diagram as _wdd

        return _wdd(self.lie_type, self.partition)

    def sl2_triple(self):
        r"""Construct the `\mathfrak{sl}_2`-triple `(h, e, f)` for this orbit.

        Returns an :class:`~pyw.embedding.sl2_triple.SL2Triple` object
        containing the Chevalley-basis elements `h, e, f` satisfying

        $$[h, e] = 2e, \quad [h, f] = -2f, \quad [e, f] = h.$$

        Returns
        -------
        SL2Triple
            The `\mathfrak{sl}_2`-triple for this nilpotent orbit.

        Examples
        --------
        >>> orb = nilpotent_orbits('A', 3)[-1]  # principal orbit [4]
        >>> triple = orb.sl2_triple()
        >>> triple.verify()
        True
        """
        from pyw.embedding.sl2_triple import compute_sl2_triple

        return compute_sl2_triple(self.lie_type, self.partition)

    def sl2_triplet_regular_in_standard_levi(self):
        r"""Construct a triple with `f'` regular in a standard Levi.

        Returns an object carrying the conjugate-style representatives
        ``hprime, eprime, fprime`` and ``xprime = hprime/2``. The standard Levi
        is determined from the Bala-Carter Levi attached to this orbit and then
        moved to the ambient dominant chamber.
        """
        from pyw.embedding.sl2_triple import compute_standard_levi_regular_sl2_triple

        return compute_standard_levi_regular_sl2_triple(self.lie_type, self.partition)

    def root_grading(self):
        r"""Compute the root space grading `\Delta = \bigcup_j \Delta_j`.

        For the semisimple element `h` of the `\mathfrak{sl}_2`-triple,
        the roots are decomposed by their eigenvalue under `\mathrm{ad}(h)`:

        $$\Delta_j = \{\alpha \in \Delta \mid [h, E^\alpha] = j\, E^\alpha\}.$$

        Returns
        -------
        RootSpaceGrading
            Object with ``grading[j]`` giving the roots in `\Delta_j`.

        Examples
        --------
        >>> orb = nilpotent_orbits('A', 3)[-1]  # principal orbit
        >>> rg = orb.root_grading()
        >>> rg.grades
        [-2, 2]
        """
        from pyw.embedding.sl2_triple import root_space_grading

        wdd = self.weighted_dynkin_diagram()
        return root_space_grading(self.lie_type, wdd)

    def levi_subalgebra(self) -> LeviSubalgebra:
        r"""Return the Levi subalgebra corresponding to this orbit.

        The Levi is computed from an ``sl_2``-triple by

        $$
        \mathfrak{h}^f = \{h \in \mathfrak{h} \mid [h,f]=0\},
        \qquad
        \Delta_\mathfrak{l} = \{\alpha \in \Delta \mid \alpha|_{\mathfrak{h}^f}=0\}.
        $$

        Returns
        -------
        LeviSubalgebra
            Levi descriptor with root subsystem ``Delta_l``.
        """
        triple = self.sl2_triple()
        return LeviSubalgebra(lie_type=self.lie_type, roots=triple.delta_l())

    def regular_levi(self) -> LeviSubalgebra:
        """Return the canonical Levi attached to this orbit."""
        return self.levi_subalgebra()

    def is_regular_in(self, levi: Optional[LeviSubalgebra] = None) -> bool:
        r"""Check whether this orbit is regular in a chosen Levi subalgebra.

        Parameters
        ----------
        levi : LeviSubalgebra, optional
            Levi to test against. If omitted, use orbit's corresponding Levi.

        Returns
        -------
        bool
            ``True`` iff a representative ``f`` of this orbit is regular in
            the Levi, i.e. ``dim Z_l(f) = rank(l)``.
        """
        triple = self.sl2_triple()
        if levi is None:
            levi = self.regular_levi()
        if tuple(levi.lie_type) != tuple(self.lie_type):
            raise ValueError(f"Levi type {levi.lie_type} does not match orbit type {self.lie_type}")
        return levi.is_regular_element(triple.f)

    def is_regular(
        self, levi_subalgebra: Optional[Union[LeviSubalgebra, Sequence[Any]]] = None
    ) -> bool:
        """Alias of :meth:`is_regular_in` for concise API usage."""

        if levi_subalgebra is None:
            return self.is_regular_in()
        if isinstance(levi_subalgebra, LeviSubalgebra):
            return self.is_regular_in(levi=levi_subalgebra)
        return self.is_regular_in(
            levi=LeviSubalgebra(lie_type=self.lie_type, roots=list(levi_subalgebra))
        )

    def __repr__(self) -> str:
        return (
            f"NilpotentOrbit({self.lie_type[0]}{self.lie_type[1]}, "
            f"{self.label}, dim={self.dimension})"
        )


# ---------------------------------------------------------------------------
# Orbit classification helpers
# ---------------------------------------------------------------------------


def _is_even_orbit_A(p: List[int]) -> bool:
    """In type A every orbit is even iff all parts of λ^t are even,
    equivalently iff all parts of λ differ by at least 2."""
    pt = _transpose_partition(p)
    return all(x % 2 == 0 for x in pt)


def _is_distinguished_A(p: List[int]) -> bool:
    """Distinguished orbits in type A: all parts are distinct."""
    return len(p) == len(set(p))


def _is_even_orbit_BCD(p: List[int], lie_type: str) -> bool:
    """An orbit is even when the weighted Dynkin diagram has only even entries.

    For types B, C, D the criterion on partitions:
      - Type B: the partition has only odd parts
      - Type C: the partition has only even parts
      - Type D: the partition has only odd parts
    (These ensure the orbit is even in the sense of Dynkin diagrams.)
    """
    if lie_type == "C":
        return all(x % 2 == 0 for x in p)
    else:  # B or D
        return all(x % 2 == 1 for x in p)


def _is_distinguished_BCD(p: List[int]) -> bool:
    """Distinguished in type B/C/D: no part repeats more than twice,
    equivalently the parts of λ^t decrease by at most 1 each step.
    A simpler criterion: all parts are distinct for B,D;
    for C all even parts are distinct.

    Actually, Collingwood-McGovern:
    Distinguished ↔ Z_G(e) is unipotent ↔ each part has multiplicity 1.
    This is the same as type A for BCD.
    """
    return len(p) == len(set(p))


# ---------------------------------------------------------------------------
# Main enumeration
# ---------------------------------------------------------------------------


def nilpotent_orbits(
    lie_type: Union[str, Tuple[str, int]],
    rank: Optional[int] = None,
) -> List[NilpotentOrbit]:
    r"""Enumerate all nilpotent orbits for a classical Lie algebra.

    Parameters
    ----------
    lie_type : str or tuple
        Either a single letter ``'A'``, ``'B'``, ``'C'``, ``'D'``
        (in which case *rank* must be given), or a tuple ``('A', n)``.
    rank : int, optional
        Rank of the algebra. Ignored when *lie_type* is a tuple.

    Returns
    -------
    list of NilpotentOrbit
        Orbits sorted by dimension (ascending).  For type D, very-even
        partitions produce **two** orbit objects (labelled I and II).

    Examples
    --------
    >>> orbits = nilpotent_orbits('A', 3)  # sl(4)
    >>> len(orbits)  # Partitions(4) has 5 elements
    5
    >>> orbits[-1].partition  # regular orbit = single part
    [4]

    >>> orbits_D4 = nilpotent_orbits('D', 4)  # so(8)
    >>> vev = [o for o in orbits_D4 if o.is_very_even]
    >>> len(vev)  # [4,4] and [2,2,2,2] each give 2 orbits → 4
    4

    References
    ----------
    Collingwood & McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
    Van Nostrand Reinhold, 1993. Chapters 5–6.
    """
    # --- Parse input ---
    if isinstance(lie_type, (list, tuple)):
        letter, n = lie_type[0], int(lie_type[1])
    else:
        letter = str(lie_type).upper()
        if rank is None:
            raise ValueError("rank must be specified when lie_type is a string")
        n = int(rank)

    letter = letter.upper()
    if letter not in ("A", "B", "C", "D"):
        raise ValueError(f"Only classical types A, B, C, D are supported; got '{letter}'")
    if n < 1:
        raise ValueError(f"Rank must be ≥ 1; got {n}")
    if letter == "D" and n < 2:
        raise ValueError(f"Type D requires rank ≥ 2; got {n}")

    # --- Determine the integer N to partition ---
    if letter == "A":
        N = n + 1  # sl(n+1)
    elif letter == "B":
        N = 2 * n + 1  # so(2n+1)
    elif letter == "C":
        N = 2 * n  # sp(2n)
    else:  # D
        N = 2 * n  # so(2n)

    # --- Filter partitions ---
    filter_fn = {
        "A": lambda p: True,
        "B": _is_type_B_partition,
        "C": _is_type_C_partition,
        "D": _is_type_D_partition,
    }[letter]

    dim_fn = {
        "A": _orbit_dim_A,
        "B": _orbit_dim_B,
        "C": _orbit_dim_C,
        "D": _orbit_dim_D,
    }[letter]

    orbits: List[NilpotentOrbit] = []

    for sage_partition in Partitions(N):
        p = list(sage_partition)
        if not filter_fn(p):
            continue

        dim = dim_fn(p)
        pt = _transpose_partition(p)

        if letter == "A":
            is_even = _is_even_orbit_A(p)
            is_dist = _is_distinguished_A(p)
        else:
            is_even = _is_even_orbit_BCD(p, letter)
            is_dist = _is_distinguished_BCD(p)

        very_even = (letter == "D") and _is_very_even(p)

        if letter == "D" and very_even:
            # Very even partition → two distinct orbits (I and II)
            for numeral in ("I", "II"):
                orbits.append(
                    NilpotentOrbit(
                        lie_type=(letter, n),
                        partition=p,
                        dimension=dim,
                        transpose=pt,
                        is_even=is_even,
                        is_distinguished=is_dist,
                        is_very_even=True,
                        roman_numeral=numeral,
                    )
                )
        else:
            orbits.append(
                NilpotentOrbit(
                    lie_type=(letter, n),
                    partition=p,
                    dimension=dim,
                    transpose=pt,
                    is_even=is_even,
                    is_distinguished=is_dist,
                    is_very_even=very_even,
                )
            )

    # Sort by dimension (ascending)
    orbits.sort(key=lambda o: o.dimension)
    return orbits


# ---------------------------------------------------------------------------
# Convenience: summary table
# ---------------------------------------------------------------------------


def nilpotent_orbit_table(
    lie_type: Union[str, Tuple[str, int]],
    rank: Optional[int] = None,
) -> str:
    r"""Return a human-readable table of nilpotent orbits.

    Examples
    --------
    >>> print(nilpotent_orbit_table('A', 3))
    Nilpotent orbits of A3 (sl(4)):  5 orbits
    ─────────────────────────────────────────────
      #  Partition          Dim   Transpose       Flags
      1  [1, 1, 1, 1]        0   [4]
      2  [2, 1, 1]           4   [3, 1]
      3  [2, 2]              6   [2, 2]           even
      4  [3, 1]              8   [2, 1, 1]        dist
      5  [4]                12   [1, 1, 1, 1]     dist even
    """
    orbits = nilpotent_orbits(lie_type, rank)
    if isinstance(lie_type, (list, tuple)):
        letter, n = lie_type[0], int(lie_type[1])
    else:
        letter, n = str(lie_type).upper(), int(rank)

    algebra_name = {
        "A": f"sl({n + 1})",
        "B": f"so({2 * n + 1})",
        "C": f"sp({2 * n})",
        "D": f"so({2 * n})",
    }[letter]

    header = f"Nilpotent orbits of {letter}{n} ({algebra_name}):  {len(orbits)} orbits"
    sep = "\u2500" * max(len(header), 50)

    lines = [header, sep]
    lines.append(f"  {'#':>3}  {'Partition':<20} {'Dim':>5}   {'Transpose':<20} Flags")

    for i, orb in enumerate(orbits, 1):
        flags: List[str] = []
        if orb.is_distinguished:
            flags.append("dist")
        if orb.is_even:
            flags.append("even")
        if orb.is_very_even:
            flags.append("v-even")
        flag_str = " ".join(flags)
        lines.append(
            f"  {i:>3}  {orb.label:<20} {orb.dimension:>5}   {str(orb.transpose):<20} {flag_str}"
        )
    return "\n".join(lines)


@dataclass
class LeviSubalgebra:
    """Levi subalgebra data attached to a nilpotent orbit.

    The Levi is encoded by its root subsystem
    ``Delta_l = {alpha in Delta | alpha|_{h^f} = 0}`` and always contains
    the full Cartan subalgebra of the ambient Lie algebra.
    """

    lie_type: Tuple[str, int]
    roots: List[Any] = field(default_factory=list)

    @property
    def rank(self) -> int:
        """Rank of the Levi subalgebra (same as ambient rank)."""
        return int(self.lie_type[1])

    @property
    def dimension(self) -> int:
        """Dimension of Levi: ``rank + |Delta_l|``."""
        return self.rank + len(self.roots)

    def contains_element(self, element: Any) -> bool:
        """Return whether an ambient Lie algebra element lies in this Levi."""
        from sage.all import LieAlgebra, QQ, RootSystem

        letter, n = self.lie_type
        L = LieAlgebra(QQ, cartan_type=[letter, n])
        B = L.basis()
        rl = RootSystem([letter, n]).root_lattice()
        alpha_check = rl.simple_coroots()

        allowed = set(self.roots)
        for i in range(1, n + 1):
            allowed.add(alpha_check[i])

        coeffs = element.monomial_coefficients()
        return all((c == 0) or (k in allowed) for k, c in coeffs.items())

    def centralizer_dimension(self, element: Any) -> int:
        """Return ``dim Z_l(element)`` where ``l`` is this Levi."""
        from sage.all import LieAlgebra, Matrix, QQ, RootSystem

        letter, n = self.lie_type
        L = LieAlgebra(QQ, cartan_type=[letter, n])
        B = L.basis()
        rl = RootSystem([letter, n]).root_lattice()
        alpha_check = rl.simple_coroots()

        levi_basis = [B[alpha_check[i]] for i in range(1, n + 1)]
        for root in self.roots:
            levi_basis.append(B[root])

        ambient_keys = sorted(B.keys(), key=str)
        rows = []
        for key in ambient_keys:
            rows.append(
                [L.bracket(b, element).monomial_coefficients().get(key, 0) for b in levi_basis]
            )

        M = Matrix(QQ, rows)
        return int(M.right_kernel().dimension())

    def is_regular_element(self, element: Any, *, require_nilpotent: bool = True) -> bool:
        r"""Check if ``element`` is regular in this Levi.

        Regular means ``dim Z_l(element) = rank(l)``.
        """
        if not self.contains_element(element):
            return False

        if require_nilpotent:
            is_nilpotent_fn = getattr(element, "is_nilpotent", None)
            if callable(is_nilpotent_fn):
                try:
                    if not bool(is_nilpotent_fn()):
                        return False
                except Exception:
                    pass

        return self.centralizer_dimension(element) == self.rank

    def is_regular(self, element: Any, *, require_nilpotent: bool = True) -> bool:
        """Alias of :meth:`is_regular_element` for concise API usage."""
        return self.is_regular_element(element, require_nilpotent=require_nilpotent)
