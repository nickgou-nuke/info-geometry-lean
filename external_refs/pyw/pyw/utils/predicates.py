"""Predicate helpers for roots/weights.

This project wraps SageMath root/weight objects and also defines the Di Francesco
`pyw.core.affine_weight.AffineWeight` triple (finite_part; level; grade).

These helpers intentionally rely on duck-typing so they work across Sage element
types (root space vs root lattice vs weight space) without importing Sage
internals.
"""

from __future__ import annotations

from typing import Any, Iterable, Optional


def _is_zero(x: Any) -> bool:
    if x == 0:
        return True
    if hasattr(x, "is_zero"):
        try:
            return bool(x.is_zero())
        except Exception:
            return False
    return False


def _parent_type_name(x: Any) -> str:
    try:
        parent = x.parent()
    except Exception:
        return ""
    return type(parent).__name__.lower()


def _values(obj: Any) -> Iterable[Any]:
    if obj is None:
        return []
    if isinstance(obj, dict):
        return obj.values()
    if hasattr(obj, "values"):
        try:
            return obj.values()
        except Exception:
            pass
    if isinstance(obj, (list, tuple, set)):
        return obj
    try:
        return list(obj)
    except Exception:
        return []


def _contains(container: Any, item: Any) -> bool:
    """Best-effort membership check that avoids requiring hashability."""

    try:
        return item in container
    except Exception:
        pass

    try:
        for x in _values(container):
            try:
                if item == x:
                    return True
            except Exception:
                continue
    except Exception:
        return False

    return False


def _neg(x: Any) -> Any:
    try:
        return -x
    except Exception:
        return None


def _monomial_coeffs(x: Any) -> dict:
    if hasattr(x, "monomial_coefficients"):
        try:
            return dict(x.monomial_coefficients())
        except Exception:
            return {}
    return {}


def _finite_root_system_from_algebra(algebra: Any):
    if algebra is None:
        return None
    # AffineLieAlgebra keeps the finite root system cached for affine types.
    rs = getattr(algebra, "_finite_root_system", None)
    if rs is not None:
        return rs
    return getattr(algebra, "_root_system", None)


def _roots_from_parent(x: Any) -> Optional[Iterable[Any]]:
    """Best-effort: get the full (finite) root set from x.parent()."""

    try:
        parent = x.parent()
    except Exception:
        return None

    # Many Sage root parents (root space/lattice) expose roots().
    if hasattr(parent, "roots"):
        try:
            return parent.roots()
        except Exception:
            pass

    # Some parents expose root_system() to reach the lattice.
    if hasattr(parent, "root_system"):
        try:
            rs = parent.root_system()
            Q = rs.root_lattice()
            if hasattr(Q, "roots"):
                return Q.roots()
        except Exception:
            pass

    return None


def _positive_roots_from_parent(x: Any) -> Optional[Iterable[Any]]:
    """Best-effort: get the positive (finite) root set from x.parent()."""

    try:
        parent = x.parent()
    except Exception:
        return None

    if hasattr(parent, "positive_roots"):
        try:
            return parent.positive_roots()
        except Exception:
            pass

    if hasattr(parent, "root_system"):
        try:
            rs = parent.root_system()
            Q = rs.root_lattice()
            if hasattr(Q, "positive_roots"):
                return Q.positive_roots()
        except Exception:
            pass

    return None


def _finite_roots_from_algebra(algebra: Any) -> Optional[Iterable[Any]]:
    rs = _finite_root_system_from_algebra(algebra)
    if rs is None:
        return None

    # Prefer root lattice roots() if available.
    try:
        Q = rs.root_lattice()
        if hasattr(Q, "roots"):
            return Q.roots()
    except Exception:
        pass

    # Fallback: root space roots().
    try:
        R = rs.root_space()
        if hasattr(R, "roots"):
            return R.roots()
    except Exception:
        pass

    # Fallback: ambient space roots().
    try:
        A = rs.ambient_space()
        if hasattr(A, "roots"):
            return A.roots()
    except Exception:
        pass

    return None


def _finite_positive_roots_from_algebra(algebra: Any) -> Optional[Iterable[Any]]:
    rs = _finite_root_system_from_algebra(algebra)
    if rs is None:
        return None

    try:
        Q = rs.root_lattice()
        if hasattr(Q, "positive_roots"):
            return Q.positive_roots()
    except Exception:
        pass

    try:
        R = rs.root_space()
        if hasattr(R, "positive_roots"):
            return R.positive_roots()
    except Exception:
        pass

    return None


def is_affine_root(x: Any) -> bool:
    """Return True iff x is an affine root (alpha; 0; n) in Di Francesco notation."""

    from pyw.core.affine_weight import AffineWeight

    return isinstance(x, AffineWeight) and x.level == 0


def _is_finite_root_impl(x: Any, algebra: Any) -> bool:
    """Internal: is finite root, using algebra context when available."""

    from pyw.core.affine_weight import AffineWeight

    if isinstance(x, AffineWeight):
        if not is_affine_root(x) or x.grade != 0:
            return False
        if _is_zero(x.finite_part):
            return False
        # Prefer the embedded algebra on the AffineWeight.
        return _is_finite_root_impl(x.finite_part, algebra=x.algebra)

    # 1) If caller provided an algebra, use it.
    if algebra is not None:
        roots = _finite_roots_from_algebra(algebra)
        if roots is None:
            return False
        if _contains(roots, x):
            return True

        # Some Sage containers expose only positive roots; in that case accept
        # negatives by checking membership in positive_roots().
        pos = _finite_positive_roots_from_algebra(algebra)
        if pos is not None:
            if _contains(pos, x):
                return True
            nx = _neg(x)
            if nx is not None and _contains(pos, nx):
                return True
        return False

    # 2) Otherwise infer from the element's parent, if possible.
    roots = _roots_from_parent(x)
    if roots is not None and _contains(roots, x):
        return True

    pos = _positive_roots_from_parent(x)
    if pos is not None:
        if _contains(pos, x):
            return True
        nx = _neg(x)
        if nx is not None and _contains(pos, nx):
            return True

    return False


def is_finite_root(x: Any, algebra: Any = None) -> bool:
    """Return True iff x is a finite root.

    This requires algebra context unless x is an `AffineWeight` (then it uses
    `x.algebra`).
    """

    from pyw.core.affine_weight import AffineWeight

    if isinstance(x, AffineWeight):
        return _is_finite_root_impl(x, algebra=x.algebra)
    return _is_finite_root_impl(x, algebra=algebra)


def is_positive_finite_root(x: Any, algebra: Any = None) -> bool:
    """Return True iff x is a positive finite root (alpha>0)."""

    from pyw.core.affine_weight import AffineWeight

    if isinstance(x, AffineWeight):
        return is_finite_root(x) and is_positive_finite_root(x.finite_part, algebra=x.algebra)

    if not is_finite_root(x, algebra=algebra):
        return False

    # Prefer explicit positive-root membership if available.
    if algebra is not None:
        pos = _finite_positive_roots_from_algebra(algebra)
        if pos is not None:
            if _contains(pos, x):
                return True

    pos = _positive_roots_from_parent(x)
    if pos is not None:
        if _contains(pos, x):
            return True

    mc = _monomial_coeffs(x)
    if not mc:
        return False
    coeffs = list(mc.values())
    return all(c >= 0 for c in coeffs) and any(c > 0 for c in coeffs)


def is_finite_weight(x: Any) -> bool:
    """Return True iff x is a finite weight (Sage weight space/lattice element)."""

    from pyw.core.affine_weight import AffineWeight

    if isinstance(x, AffineWeight):
        return False
    p = _parent_type_name(x)
    return "weight" in p and "coweight" not in p


def is_zero_weight(x: Any) -> bool:
    """Return True iff x is the zero weight.

    Accepts both finite Sage weights and `AffineWeight`.
    """

    from pyw.core.affine_weight import AffineWeight

    if isinstance(x, AffineWeight):
        return _is_zero(x.finite_part) and x.level == 0 and x.grade == 0
    return _is_zero(x)


def is_simple_root(x: Any) -> bool:
    """Return True iff x is a simple root.

    - For `AffineWeight`: checks against `x.algebra.affine_simple_roots()`.
    - For Sage root elements: checks against `x.parent().simple_roots()` when
      available (note: this verifies *simplicity*, not being a root).
    """

    from pyw.core.affine_weight import AffineWeight

    if isinstance(x, AffineWeight):
        if not is_affine_root(x):
            return False
        try:
            return x in _values(x.algebra.affine_simple_roots())
        except Exception:
            return False

    try:
        parent = x.parent()
    except Exception:
        return False

    if not hasattr(parent, "simple_roots"):
        return False

    try:
        sr = parent.simple_roots()
    except Exception:
        return False

    return x in set(_values(sr))


def is_positive_affine_root(x: Any) -> bool:
    """Return True iff x is a positive affine root.

    User convention:
    - (alpha>0, 0, n=0)
    - (alpha in Delta, 0, n>0)
    - (0, 0, n>0)

    i.e. n>0 OR (n==0 and alpha>0).
    """

    if not is_affine_root(x):
        return False

    if x.grade > 0:
        # (alpha in Delta, 0, n>0) and (0,0,n>0)
        return _is_zero(x.finite_part) or is_finite_root(x.finite_part, algebra=x.algebra)
    if x.grade != 0:
        return False
    return is_positive_finite_root(x.finite_part, algebra=x.algebra)


def is_real_affine_root(x: Any) -> bool:
    """Return True iff x is a real affine root.

    User convention: real roots are exactly (alpha != 0, 0, n).
    """

    return is_affine_root(x) and is_finite_root(x.finite_part, algebra=x.algebra)


def is_positive_real_affine_root(x: Any) -> bool:
    """Return True iff x is a positive real affine root."""

    return is_real_affine_root(x) and is_positive_affine_root(x)
