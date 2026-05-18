r"""
SL2 Triples and Root Space Grading for Nilpotent Orbits

Given a nilpotent orbit in a classical Lie algebra (type A, B, C, D),
this module constructs:

1. **Weighted Dynkin diagram** from the partition label.
2. **SL2 triple** `(h, e, f)` satisfying

   $$
   [h, e] = 2e, \quad [h, f] = -2f, \quad [e, f] = h
   $$

   (equivalently, `x = h/2` gives `[x,e]=e, [x,f]=-f, [e,f]=2x`).

3. **Root space grading** (ad-eigenspace decomposition):

   $$
   \Delta = \bigcup_j \Delta_j, \quad
   \Delta_j = \{\alpha \in \Delta \mid [h, E^\alpha] = j\, E^\alpha\}
   $$

References
----------
- Collingwood, D. H., McGovern, W. M.
  "Nilpotent Orbits in Semisimple Lie Algebras" (1993), Chapters 3--5.
- Dynkin, E. B. "Semisimple subalgebras of semisimple Lie algebras" (1952).
- Carter, R. W. "Finite Groups of Lie Type" (1985), Chapter 5.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
from itertools import combinations, product
from typing import Any, Dict, List, Optional, Sequence, Tuple, Union

from sage.all import (
    CartanType,
    LieAlgebra,
    Matrix,
    QQ,
    RootSystem,
    ZZ,
)


# ---------------------------------------------------------------------------
# Weighted Dynkin Diagram
# ---------------------------------------------------------------------------


def _partition_eigenvalues(partition: List[int]) -> List[int]:
    r"""Eigenvalues of the semisimple element `h` in the standard representation.

    For a block of size `p`, the eigenvalues are

    $$p-1,\; p-3,\; \dots,\; -(p-1).$$

    Returns the full list of eigenvalues, sorted in descending order.
    """
    eigenvalues: List[int] = []
    for p in partition:
        for i in range(p):
            eigenvalues.append(p - 1 - 2 * i)
    eigenvalues.sort(reverse=True)
    return eigenvalues


def weighted_dynkin_diagram(
    lie_type: Union[str, Tuple[str, int]],
    partition: List[int],
    rank: Optional[int] = None,
) -> List[int]:
    r"""Compute the weighted Dynkin diagram for a nilpotent orbit.

    The weighted Dynkin diagram `(d_1, \dots, d_n)` encodes the semisimple
    element `h` of the associated `sl_2`-triple via
    `\alpha_i(h) = d_i`.

    Parameters
    ----------
    lie_type : str or tuple
        Cartan type letter or ``(letter, rank)`` tuple.
    partition : list of int
        The partition labelling the nilpotent orbit.
    rank : int, optional
        Rank of the algebra; ignored if *lie_type* is a tuple.

    Returns
    -------
    list of int
        The Dynkin labels `[d_1, \dots, d_n]` (non-negative integers,
        each in `{0, 1, 2}`).

    Examples
    --------
    >>> weighted_dynkin_diagram('A', [3, 1], rank=3)
    [2, 0, 2]
    >>> weighted_dynkin_diagram(('B', 2), [5])
    [2, 2]
    """
    if isinstance(lie_type, (list, tuple)):
        letter, n = str(lie_type[0]).upper(), int(lie_type[1])
    else:
        letter = str(lie_type).upper()
        if rank is None:
            raise ValueError("rank must be specified when lie_type is a string")
        n = int(rank)

    eigs = _partition_eigenvalues(partition)

    if letter == "A":
        N = n + 1
        return [eigs[i] - eigs[i + 1] for i in range(N - 1)]

    # For B, C, D: take the top n eigenvalues (h_1 >= ... >= h_n >= 0)
    h = eigs[:n]
    d = [h[i] - h[i + 1] for i in range(n - 1)]

    if letter == "B":
        # Simple roots: e_1 - e_2, ..., e_{n-1} - e_n, e_n
        d.append(h[n - 1])
    elif letter == "C":
        # Simple roots: e_1 - e_2, ..., e_{n-1} - e_n, 2*e_n
        d.append(2 * h[n - 1])
    elif letter == "D":
        # Simple roots: e_1 - e_2, ..., e_{n-1} - e_n, e_{n-1} + e_n
        d.append(h[n - 2] + h[n - 1])
    else:
        raise ValueError(f"Unsupported Lie algebra type: {letter}")

    return d


# ---------------------------------------------------------------------------
# Root Space Grading
# ---------------------------------------------------------------------------


@dataclass
class RootSpaceGrading:
    r"""The root space grading induced by a semisimple element `h`.

    Attributes
    ----------
    lie_type : tuple
        Cartan type, e.g. ``('A', 3)``.
    wdd : list of int
        Weighted Dynkin diagram labels `(d_1, \dots, d_n)`.
    grading : dict mapping int → list
        ``grading[j]`` is the list of roots `\alpha` with
        `\alpha(h) = j`, i.e. `[h, E^\alpha] = j\, E^\alpha`.
    """

    lie_type: Tuple[str, int]
    wdd: List[int]
    grading: Dict[int, list] = field(default_factory=dict)

    @property
    def grades(self) -> List[int]:
        """Sorted list of eigenvalues `j` that appear."""
        return sorted(self.grading.keys())

    def __getitem__(self, j: int) -> list:
        r"""Return roots in `\Delta_j`."""
        return self.grading.get(j, [])

    def dimension(self, j: int) -> int:
        r"""Dimension of `\mathfrak{g}_j` (number of roots with eigenvalue `j`)."""
        return len(self.grading.get(j, []))

    def __repr__(self) -> str:
        parts = []
        for j in self.grades:
            parts.append(f"Δ_{j}: {len(self.grading[j])} roots")
        return (
            f"RootSpaceGrading({self.lie_type[0]}{self.lie_type[1]}, "
            f"WDD={self.wdd}, {', '.join(parts)})"
        )


def root_space_grading(
    lie_type: Union[str, Tuple[str, int]],
    wdd: List[int],
    rank: Optional[int] = None,
) -> RootSpaceGrading:
    r"""Compute the root space grading `\Delta = \bigcup_j \Delta_j`.

    For the semisimple element `h` with weighted Dynkin diagram
    `(d_1, \dots, d_n)`, each root `\alpha = \sum m_i \alpha_i`
    has eigenvalue

    $$j = \alpha(h) = \sum_i m_i\, d_i.$$

    Parameters
    ----------
    lie_type : str or tuple
        Cartan type letter or ``(letter, rank)`` tuple.
    wdd : list of int
        Weighted Dynkin diagram labels.
    rank : int, optional
        Rank; ignored when *lie_type* is a tuple.

    Returns
    -------
    RootSpaceGrading
        Object containing `grading[j]` for each eigenvalue `j`.
    """
    if isinstance(lie_type, (list, tuple)):
        letter, n = str(lie_type[0]).upper(), int(lie_type[1])
    else:
        letter = str(lie_type).upper()
        if rank is None:
            raise ValueError("rank must be specified when lie_type is a string")
        n = int(rank)

    R = RootSystem([letter, n])
    rl = R.root_lattice()
    pos_roots = list(rl.positive_roots())

    grading: Dict[int, list] = defaultdict(list)

    for r in pos_roots:
        coeffs = r.monomial_coefficients()
        j = sum(coeffs.get(i, 0) * wdd[i - 1] for i in range(1, n + 1))
        grading[j].append(r)
        grading[-j].append(-r)

    # The zero eigenvalue also includes the Cartan subalgebra,
    # but we only record the roots (not the Cartan generators).
    grading_dict = dict(grading)

    return RootSpaceGrading(
        lie_type=(letter, n),
        wdd=list(wdd),
        grading=grading_dict,
    )


# ---------------------------------------------------------------------------
# SL2 Triple
# ---------------------------------------------------------------------------


@dataclass
class SL2Triple:
    r"""An `\mathfrak{sl}_2`-triple `(h, e, f)` in a Lie algebra.

    Satisfies `[h,e] = 2e`, `[h,f] = -2f`, `[e,f] = h`.

    Equivalently, with `x = h/2`:
    `[x,e] = e`, `[x,f] = -f`, `[e,f] = 2x`.

    Attributes
    ----------
    lie_type : tuple
        Cartan type, e.g. ``('A', 3)``.
    partition : list of int
        The partition labelling the nilpotent orbit.
    wdd : list of int
        Weighted Dynkin diagram ``(d_1, ..., d_n)``.
    h : LieAlgebra element
        The semisimple element in the Cartan subalgebra.
    e : LieAlgebra element
        The nilpotent raising operator (in `\mathfrak{g}_2`).
    f : LieAlgebra element
        The nilpotent lowering operator (in `\mathfrak{g}_{-2}`).
    h_coroot_coeffs : list
        Coefficients of `h` in the simple coroot basis:
        `h = \sum_i c_i \alpha_i^\vee`.
    """

    lie_type: Tuple[str, int]
    partition: List[int]
    wdd: List[int]
    h: Any  # SageMath LieAlgebra element
    e: Any
    f: Any
    h_coroot_coeffs: List = field(default_factory=list)

    def verify(self) -> bool:
        r"""Verify the `\mathfrak{sl}_2`-relations hold."""
        if self.h == 0 and self.e == 0 and self.f == 0:
            return True
        L = self.h.parent()
        return (
            L.bracket(self.h, self.e) == 2 * self.e
            and L.bracket(self.h, self.f) == -2 * self.f
            and L.bracket(self.e, self.f) == self.h
        )

    @property
    def x(self):
        """The semisimple element `x = h/2` with `[x,e]=e, [x,f]=-f`."""
        return self.h * QQ((1, 2))

    def root_grading(self) -> RootSpaceGrading:
        """Compute the root space grading induced by `h`."""
        return root_space_grading(self.lie_type, self.wdd)

    def h_f(self) -> List:
        r"""Compute the subalgebra `\mathfrak{h}^f = \{h \in \mathfrak{h} \mid [h, f] = 0\}`.

        This is the subspace of the Cartan subalgebra that commutes with the
        nilpotent lowering operator `f`.

        Returns
        -------
        list
            Basis vectors of `\mathfrak{h}^f`, each as a coroot lattice element
            `\sum_i c_i \alpha_i^\vee`.

        Examples
        --------
        >>> triple = compute_sl2_triple(('A', 3), [2, 1, 1])
        >>> triple.h_f()  # 2-dimensional for the minimal orbit
        [alphacheck[1] - alphacheck[3], alphacheck[2]]
        """
        letter, n = self.lie_type
        R = RootSystem([letter, n])
        rl = R.root_lattice()
        alpha_check = rl.simple_coroots()

        if self.f == 0:
            # Zero orbit: h^f = entire Cartan subalgebra
            return [alpha_check[i] for i in range(1, n + 1)]

        # Extract positive roots appearing in f
        f_mc = self.f.monomial_coefficients()
        f_pos_roots = [-r for r in f_mc.keys()]

        # Build constraint: for each beta in f, beta(h) = 0
        # beta(h) = sum_i c_i <beta, alpha_i^vee> = 0
        rows = []
        for beta in f_pos_roots:
            row = [beta.scalar(alpha_check[i]) for i in range(1, n + 1)]
            rows.append(row)

        M = Matrix(ZZ, rows)
        K = M.right_kernel()
        return [sum(ZZ(v[i]) * alpha_check[i + 1] for i in range(n)) for v in K.basis()]

    def delta_l(self) -> List:
        r"""Compute `\Delta_\mathfrak{l} = \{\alpha \in \Delta \mid \alpha|_{\mathfrak{h}^f} = 0\}`.

        These are the roots that vanish identically on `\mathfrak{h}^f`.

        Returns
        -------
        list
            Roots (SageMath root lattice elements) in `\Delta_\mathfrak{l}`.

        Examples
        --------
        >>> triple = compute_sl2_triple(('A', 3), [2, 1, 1])
        >>> len(triple.delta_l())  # minimal orbit of A3
        2
        """
        letter, n = self.lie_type
        hf_basis = self.h_f()

        R = RootSystem([letter, n])
        rl = R.root_lattice()
        pos_roots = list(rl.positive_roots())
        all_roots = pos_roots + [-r for r in pos_roots]

        if not hf_basis:
            # h^f = {0}, so every root "vanishes on h^f" trivially
            return list(all_roots)

        result = []
        for r in all_roots:
            if all(r.scalar(v) == 0 for v in hf_basis):
                result.append(r)
        return result

    def __repr__(self) -> str:
        return (
            f"SL2Triple({self.lie_type[0]}{self.lie_type[1]}, "
            f"partition={self.partition}, WDD={self.wdd})"
        )


@dataclass
class StandardLeviSL2Triple:
    r"""An `\mathfrak{sl}_2`-triple with `f'` regular in a standard Levi.

    Attributes
    ----------
    lie_type : tuple
        Ambient Cartan type.
    partition : list of int
        Partition labelling the ambient nilpotent orbit.
    standard_levi_indices : list of int
        Indices of the ambient simple roots spanning the standard Levi.
    hprime, eprime, fprime : LieAlgebra element
        The conjugate-style representative triple in the chosen standard Levi.
    standard_levi_roots : list
        Full ambient root subsystem of the standard Levi.
    """

    lie_type: Tuple[str, int]
    partition: List[int]
    standard_levi_indices: List[int]
    hprime: Any
    eprime: Any
    fprime: Any
    standard_levi_roots: List[Any] = field(default_factory=list)

    @property
    def xprime(self):
        """The semisimple element `x' = h'/2`."""
        return self.hprime * QQ((1, 2))

    def verify(self) -> bool:
        r"""Verify `[h',e']=2e'`, `[h',f']=-2f'`, `[e',f']=h'`."""
        if self.hprime == 0 and self.eprime == 0 and self.fprime == 0:
            return True
        L = self.hprime.parent()
        return (
            L.bracket(self.hprime, self.eprime) == 2 * self.eprime
            and L.bracket(self.hprime, self.fprime) == -2 * self.fprime
            and L.bracket(self.eprime, self.fprime) == self.hprime
        )


def _generic_hf_element(hf_basis: List[Any], all_roots: List[Any]) -> Any:
    r"""Choose a generic element of `\mathfrak{h}^f` defining the same Levi.

    We search for a small integer combination whose vanishing roots are exactly
    the roots vanishing on all of `\mathfrak{h}^f`.
    """
    if not hf_basis:
        return None

    target_roots = {r for r in all_roots if all(r.scalar(v) == 0 for v in hf_basis)}
    m = len(hf_basis)

    candidate_lists = [
        tuple(2**i for i in range(m)),
        tuple(i + 1 for i in range(m)),
        tuple(2 * i + 1 for i in range(m)),
    ]
    candidate_lists.extend(product(range(1, 5), repeat=m))

    for coeffs in candidate_lists:
        z = sum(ZZ(coeffs[i]) * hf_basis[i] for i in range(m))
        roots_vanishing_on_z = {r for r in all_roots if r.scalar(z) == 0}
        if roots_vanishing_on_z == target_roots:
            return z

    raise ValueError("Could not find a generic element of h^f defining the Levi")


def _dominantize_coroot(coweight: Any, lie_type: Tuple[str, int]) -> Any:
    r"""Move a coroot-lattice element to the closed dominant chamber."""
    letter, n = lie_type
    simple_roots = RootSystem([letter, n]).root_lattice().simple_roots()

    dominant = coweight
    while True:
        negative_index = None
        for i in range(1, n + 1):
            if simple_roots[i].scalar(dominant) < 0:
                negative_index = i
                break
        if negative_index is None:
            return dominant
        dominant = dominant.simple_reflection(negative_index)


def _principal_standard_levi_triple(
    lie_type: Tuple[str, int],
    partition: List[int],
    standard_levi_indices: List[int],
    standard_levi_roots: List[Any],
) -> StandardLeviSL2Triple:
    r"""Construct the principal triple in a standard Levi subalgebra."""
    letter, n = lie_type
    L = LieAlgebra(QQ, cartan_type=[letter, n])
    B_basis = L.basis()
    rl = RootSystem([letter, n]).root_lattice()
    alpha = rl.simple_roots()
    alpha_check = rl.simple_coroots()
    positive_levi_roots = [
        r for r in standard_levi_roots if getattr(r, "is_positive_root", lambda: False)()
    ]

    if not standard_levi_indices:
        zero = L.zero()
        return StandardLeviSL2Triple(
            lie_type=lie_type,
            partition=list(partition),
            standard_levi_indices=[],
            hprime=zero,
            eprime=zero,
            fprime=zero,
            standard_levi_roots=list(standard_levi_roots),
        )

    A_mat = Matrix(QQ, CartanType([letter, n]).cartan_matrix())
    levi_positions = [i - 1 for i in standard_levi_indices]
    A_levi = Matrix(
        QQ,
        [[A_mat[r, c] for c in levi_positions] for r in levi_positions],
    )
    d_space = QQ ** len(standard_levi_indices)
    d_vec = d_space([2] * len(standard_levi_indices))
    h_coeffs_levi = list((A_levi.transpose()).inverse() * d_vec)
    hprime = sum(
        (h_coeffs_levi[j] * B_basis[alpha_check[i]] for j, i in enumerate(standard_levi_indices)),
        L.zero(),
    )

    h_coeffs = [QQ(0)] * n
    for j, i in enumerate(standard_levi_indices):
        h_coeffs[i - 1] = h_coeffs_levi[j]

    def _root_eigenvalue(root):
        return sum(h_coeffs[i - 1] * root.scalar(alpha_check[i]) for i in range(1, n + 1))

    g2_roots = [r for r in positive_levi_roots if _root_eigenvalue(r) == 2]
    if not g2_roots:
        raise ValueError(f"Could not locate g_2 roots in the standard Levi for {letter}{n}")

    dim_g2 = len(g2_roots)
    eprime = sum((B_basis[r] for r in g2_roots), L.zero())
    fprime = _solve_for_f(L, hprime, eprime, g2_roots, h_coeffs, alpha_check, n)
    if fprime is None or not (
        L.bracket(hprime, eprime) == 2 * eprime
        and L.bracket(hprime, fprime) == -2 * fprime
        and L.bracket(eprime, fprime) == hprime
    ):
        for size in range(dim_g2 - 1, 0, -1):
            for subset in combinations(range(dim_g2), size):
                e_cand = sum((B_basis[g2_roots[i]] for i in subset), L.zero())
                f_cand = _solve_for_f(L, hprime, e_cand, g2_roots, h_coeffs, alpha_check, n)
                if f_cand is not None and (
                    L.bracket(hprime, e_cand) == 2 * e_cand
                    and L.bracket(hprime, f_cand) == -2 * f_cand
                    and L.bracket(e_cand, f_cand) == hprime
                ):
                    eprime = e_cand
                    fprime = f_cand
                    break
            else:
                continue
            break

    if fprime is None:
        raise ValueError(
            f"Could not construct principal triple in the standard Levi for {letter}{n}"
        )

    triple = StandardLeviSL2Triple(
        lie_type=lie_type,
        partition=list(partition),
        standard_levi_indices=list(standard_levi_indices),
        hprime=hprime,
        eprime=eprime,
        fprime=fprime,
        standard_levi_roots=list(standard_levi_roots),
    )
    if not triple.verify():
        raise ValueError(
            f"Constructed standard Levi triple does not satisfy sl2 relations for {letter}{n}"
        )
    return triple


def compute_standard_levi_regular_sl2_triple(
    lie_type: Union[str, Tuple[str, int]],
    partition: List[int],
    rank: Optional[int] = None,
) -> StandardLeviSL2Triple:
    r"""Construct a triple whose `f'` is regular in a standard Levi.

    Starting from the orbit's Jacobson-Morozov triple, we compute the attached
    Levi `\Delta_\mathfrak{l} = \{\alpha \mid \alpha|_{\mathfrak{h}^f}=0\}`,
    move a generic element of `\mathfrak{h}^f` to the dominant chamber, and use
    the resulting standard Levi to build its principal `\mathfrak{sl}_2`-triple.
    The resulting `f'` is regular in that standard Levi and represents the same
    Bala-Carter Levi type as the original orbit representative.
    """
    if isinstance(lie_type, (list, tuple)):
        letter, n = str(lie_type[0]).upper(), int(lie_type[1])
    else:
        letter = str(lie_type).upper()
        if rank is None:
            raise ValueError("rank must be specified when lie_type is a string")
        n = int(rank)

    triple = compute_sl2_triple((letter, n), partition)
    R = RootSystem([letter, n])
    rl = R.root_lattice()
    pos_roots = list(rl.positive_roots())
    all_roots = pos_roots + [-r for r in pos_roots]
    simple_roots = rl.simple_roots()

    hf_basis = triple.h_f()
    if not hf_basis:
        standard_levi_roots = list(all_roots)
        standard_levi_indices = list(range(1, n + 1))
        return _principal_standard_levi_triple(
            (letter, n), partition, standard_levi_indices, standard_levi_roots
        )

    z = _generic_hf_element(hf_basis, all_roots)
    dominant_z = _dominantize_coroot(z, (letter, n))
    standard_levi_roots = [r for r in all_roots if r.scalar(dominant_z) == 0]
    standard_levi_indices = [i for i in range(1, n + 1) if simple_roots[i].scalar(dominant_z) == 0]
    return _principal_standard_levi_triple(
        (letter, n), partition, standard_levi_indices, standard_levi_roots
    )


def _solve_for_f(
    L: Any,
    h_elem: Any,
    e_elem: Any,
    g2_roots: List,
    h_coeffs: Any,
    alpha_check: Dict,
    n: int,
) -> Optional[Any]:
    r"""Solve for `f` given `h` and `e` such that `[e,f] = h`.

    Sets up the linear system: for `f = \sum_j b_j E_{-\beta_j}`,
    the equation `[e, f] = h` becomes a linear system in the `b_j`.
    """
    B_basis = L.basis()
    dim_g2 = len(g2_roots)

    # Collect all basis keys from the brackets [e, E_{-beta_j}]
    bracket_mcs: List[dict] = []
    all_keys: set = set()
    for j in range(dim_g2):
        br = L.bracket(e_elem, B_basis[-g2_roots[j]])
        mc = br.monomial_coefficients()
        bracket_mcs.append(mc)
        all_keys.update(mc.keys())

    h_mc = h_elem.monomial_coefficients()
    all_keys.update(h_mc.keys())
    all_keys_list = sorted(all_keys, key=str)

    # Build matrix M and target vector v such that M * b = v
    rows = []
    rhs = []
    for k in all_keys_list:
        row = [mc.get(k, 0) for mc in bracket_mcs]
        rows.append(row)
        rhs.append(h_mc.get(k, 0))

    M = Matrix(QQ, rows)
    v_target = QQ ** len(rhs)
    v = v_target(rhs)

    try:
        b = M.solve_right(v)
    except ValueError:
        return None

    f_elem = sum(b[j] * B_basis[-g2_roots[j]] for j in range(dim_g2))
    return f_elem


def compute_sl2_triple(
    lie_type: Union[str, Tuple[str, int]],
    partition: List[int],
    rank: Optional[int] = None,
) -> SL2Triple:
    r"""Construct the standard `\mathfrak{sl}_2`-triple for a nilpotent orbit.

    Parameters
    ----------
    lie_type : str or tuple
        Cartan type letter or ``(letter, rank)`` tuple.
    partition : list of int
        The partition labelling the nilpotent orbit.
    rank : int, optional
        Rank; ignored when *lie_type* is a tuple.

    Returns
    -------
    SL2Triple
        The triple `(h, e, f)` satisfying the `\mathfrak{sl}_2` relations.

    Raises
    ------
    ValueError
        If the sl2 triple cannot be constructed.

    Examples
    --------
    >>> triple = compute_sl2_triple('A', [3, 1], rank=3)
    >>> triple.verify()
    True
    >>> triple.wdd
    [2, 0, 2]
    """
    if isinstance(lie_type, (list, tuple)):
        letter, n = str(lie_type[0]).upper(), int(lie_type[1])
    else:
        letter = str(lie_type).upper()
        if rank is None:
            raise ValueError("rank must be specified when lie_type is a string")
        n = int(rank)

    wdd = weighted_dynkin_diagram((letter, n), partition)

    L = LieAlgebra(QQ, cartan_type=[letter, n])
    B_basis = L.basis()
    R = RootSystem([letter, n])
    rl = R.root_lattice()
    alpha = rl.simple_roots()
    alpha_check = rl.simple_coroots()
    pos_roots = list(rl.positive_roots())

    # ------------------------------------------------------------------
    # Step 1: Compute h from WDD
    # ------------------------------------------------------------------
    # The SageMath Cartan matrix satisfies A_{ij} = <alpha_j, alpha_i^vee>.
    # For h = sum_j c_j alpha_j^vee, we have:
    #   alpha_i(h) = sum_j c_j <alpha_i, alpha_j^vee> = (A^T c)_i = d_i
    # So c = (A^T)^{-1} d.
    A_mat = Matrix(QQ, CartanType([letter, n]).cartan_matrix())
    d = QQ**n
    d_vec = d(wdd)
    h_coeffs_vec = (A_mat.transpose()).inverse() * d_vec
    h_coeffs = list(h_coeffs_vec)

    h_elem = sum(h_coeffs[i] * B_basis[alpha_check[i + 1]] for i in range(n))

    # ------------------------------------------------------------------
    # Step 2: Find the eigenspace g_2
    # ------------------------------------------------------------------
    def _root_eigenvalue(root, wdd_):
        c = root.monomial_coefficients()
        return sum(c.get(i, 0) * wdd_[i - 1] for i in range(1, n + 1))

    g2_roots = [r for r in pos_roots if _root_eigenvalue(r, wdd) == 2]

    # Zero orbit
    if not g2_roots:
        return SL2Triple(
            lie_type=(letter, n),
            partition=list(partition),
            wdd=wdd,
            h=L.zero(),
            e=L.zero(),
            f=L.zero(),
            h_coroot_coeffs=h_coeffs,
        )

    # ------------------------------------------------------------------
    # Step 3: Find e and f
    # ------------------------------------------------------------------
    # Strategy: try different choices of e in g_2, then solve for f.
    #
    # (a) Try e = sum of all g_2 root vectors.
    # (b) If that fails, try subsets of g_2 roots.
    # (c) If that fails, try single root vectors.

    dim_g2 = len(g2_roots)

    # (a) Try e = sum of all g_2 root vectors
    e_elem = sum(B_basis[r] for r in g2_roots)
    f_elem = _solve_for_f(L, h_elem, e_elem, g2_roots, h_coeffs, alpha_check, n)
    if f_elem is not None:
        ok = (
            L.bracket(h_elem, e_elem) == 2 * e_elem
            and L.bracket(h_elem, f_elem) == -2 * f_elem
            and L.bracket(e_elem, f_elem) == h_elem
        )
        if ok:
            return SL2Triple(
                lie_type=(letter, n),
                partition=list(partition),
                wdd=wdd,
                h=h_elem,
                e=e_elem,
                f=f_elem,
                h_coroot_coeffs=h_coeffs,
            )

    # (b) Try subsets of g_2 roots (from largest to smallest)
    for size in range(dim_g2 - 1, 0, -1):
        for subset in combinations(range(dim_g2), size):
            e_cand = sum(B_basis[g2_roots[i]] for i in subset)
            f_cand = _solve_for_f(L, h_elem, e_cand, g2_roots, h_coeffs, alpha_check, n)
            if f_cand is not None:
                ok = (
                    L.bracket(h_elem, e_cand) == 2 * e_cand
                    and L.bracket(h_elem, f_cand) == -2 * f_cand
                    and L.bracket(e_cand, f_cand) == h_elem
                )
                if ok:
                    return SL2Triple(
                        lie_type=(letter, n),
                        partition=list(partition),
                        wdd=wdd,
                        h=h_elem,
                        e=e_cand,
                        f=f_cand,
                        h_coroot_coeffs=h_coeffs,
                    )

    raise ValueError(
        f"Could not construct sl2 triple for {letter}{n}, partition {partition}, WDD {wdd}"
    )
