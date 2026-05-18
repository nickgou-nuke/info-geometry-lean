"""
Affine Root System Wrapper Module

This module provides a convenient wrapper around SageMath's RootSystem
for both finite and affine root systems.
"""

from typing import List, Tuple, Union, Any
from sage.all import RootSystem


class RootWithReflection:
    def __init__(self, root: Any) -> None:
        self.sage_root = root

    def associated_reflection(self) -> tuple[int, ...]:
        return tuple(int(i) for i in self.sage_root.associated_reflection())

    def __getattr__(self, name: str) -> Any:
        return getattr(self.sage_root, name)

    def __repr__(self) -> str:
        return repr(self.sage_root)

    def __str__(self) -> str:
        return str(self.sage_root)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, RootWithReflection):
            return self.sage_root == other.sage_root
        return self.sage_root == other

    def __hash__(self) -> int:
        return hash(self.sage_root)

    def __neg__(self) -> Any:
        return -self.sage_root

    def __add__(self, other: Any) -> Any:
        if isinstance(other, RootWithReflection):
            return self.sage_root + other.sage_root
        return self.sage_root + other

    def __radd__(self, other: Any) -> Any:
        return other + self.sage_root

    def __sub__(self, other: Any) -> Any:
        if isinstance(other, RootWithReflection):
            return self.sage_root - other.sage_root
        return self.sage_root - other

    def __rsub__(self, other: Any) -> Any:
        return other - self.sage_root

    def __mul__(self, other: Any) -> Any:
        return self.sage_root * other

    def __rmul__(self, other: Any) -> Any:
        return other * self.sage_root


class AffineRootSystem:
    """
    Wrapper class for SageMath RootSystem supporting finite and affine types.

    This class provides a convenient interface to access root system data
    including roots, coroots, Cartan matrix, and other invariants.
    Supports both finite types (e.g., ['A', 2]) and affine types (e.g., ['A', 2, 1]).

    Attributes:
        cartan_type: The Cartan type of the root system
        root_system: The underlying SageMath RootSystem object
        cartan_matrix: The Cartan matrix of the root system
        roots: List of roots (real and imaginary for affine systems)
        coroots: List of coroots
        simple_roots: List of simple roots
        simple_coroots: List of simple coroots
        dual_coxeter_number: Dual Coxeter number g^\vee

    Examples:
        >>> # Finite type A2
        >>> rs = AffineRootSystem(['A', 2])
        >>> print(rs.cartan_type)
        A2

        >>> # Affine type A2^(1)
        >>> rs_affine = AffineRootSystem(['A', 2, 1])
        >>> print(rs_affine.cartan_type)
        ['A', 2, 1]

    Notes:
        For affine root systems, the roots property returns all roots from the
        ambient space, which includes both real and imaginary roots.
        The dual Coxeter number g^\vee is computed as the scalar
        k = h^\vee for the dual root system.
    """

    def __init__(self, cartan_type: Union[Tuple[str, int], List[Union[str, int]]]) -> None:
        """
        Initialize the AffineRootSystem wrapper.

        Args:
            cartan_type: The Cartan type of the root system. Can be:
                - A tuple for finite types, e.g., ('A', 2) or ['A', 2]
                - A list for affine types, e.g., ['A', 2, 1]

        Raises:
            TypeError: If cartan_type is not a tuple or list
        """
        if isinstance(cartan_type, list):
            self.cartan_type: Union[Tuple[str, int], List[Union[str, int]]] = cartan_type
        elif isinstance(cartan_type, tuple):
            self.cartan_type = cartan_type
        else:
            raise TypeError(f"cartan_type must be tuple or list, got {type(cartan_type)}")

        self.sage_root_system = None
        self._cartan_matrix = None
        self.sage_roots = None
        self._coroots = None
        self._simple_roots = None
        self._simple_coroots = None
        self._dual_coxeter_number = None

    @property
    def root_system(self) -> RootSystem:
        """
        Get the underlying SageMath RootSystem object.

        Returns:
            SageMath RootSystem instance

        Notes:
            This provides direct access to all SageMath RootSystem methods
        """
        if self.sage_root_system is None:
            self.sage_root_system = RootSystem(self.cartan_type)
        return self.sage_root_system

    @property
    def cartan_matrix(self):
        """
        Get the Cartan matrix of the root system.

        Returns:
            SageMath matrix representing the Cartan matrix

        Notes:
            The Cartan matrix C_ij satisfies α_j(H_i) = C_ij
            where α are simple roots and H are simple coroots
        """
        if self._cartan_matrix is None:
            self._cartan_matrix = self.root_system.cartan_matrix()
        return self._cartan_matrix

    @property
    def roots(self) -> List[Any]:
        """
        Get all roots of the root system.

        Returns:
            List of root vectors from the ambient space

        Notes:
            For finite types: returns all roots (positive and negative)
            For affine types: returns roots from the ambient space,
            which includes both real and imaginary roots
        """
        if self.sage_roots is None:
            ambient_space = self.root_system.ambient_space()
            self.sage_roots = list(ambient_space.roots())
        return self.sage_roots

    @property
    def coroots(self) -> List[Any]:
        """
        Get all coroots of the root system.

        Returns:
            List of coroot vectors

        Notes:
            Coroots live in the dual space and satisfy the pairing
            α_j(H_i) = C_ij where C_ij is the Cartan matrix
        """
        if self._coroots is None:
            self._coroots = list(self.root_system.coroot_lattice().basis())
        return self._coroots

    @property
    def simple_roots(self) -> List[Any]:
        """
        Get the simple roots of the root system.

        Returns:
            List of simple root vectors

        Notes:
            Simple roots form a basis of the root lattice and
            generate all roots under simple reflections
        """
        if self._simple_roots is None:
            self._simple_roots = list(self.root_system.root_lattice().simple_roots())
        return self._simple_roots

    @property
    def simple_coroots(self) -> List[Any]:
        """
        Get the simple coroots of the root system.

        Returns:
            List of simple coroot vectors

        Notes:
            Simple coroots form a basis of the coroot lattice
            and are dual to simple roots via the Cartan matrix
        """
        if self._simple_coroots is None:
            self._simple_coroots = list(self.root_system.coroot_lattice().simple_roots())
        return self._simple_coroots

    @property
    def rank(self) -> int:
        """
        Get the rank of the root system.

        Returns:
            The rank (number of simple roots) as an integer

        Notes:
            For finite types, rank = n (e.g., A_n has rank n)
            For affine types, rank = n+1 (e.g., A_n^(1) has rank n+1)
        """
        return self.root_system.cartan_type().rank()

    @property
    def dual_coxeter_number(self) -> Union[int, None]:
        """
        Get the dual Coxeter number g^\vee (also denoted h^\vee).

        Returns:
            The dual Coxeter number as an integer, or None if not defined

        Notes:
            The dual Coxeter number g^\vee is defined as:
            - For finite types: g^\vee = h^\vee (dual Coxeter number)
            - For affine types: g^\vee = sum of dual comarks a_i^\vee
              where theta^\vee = sum a_i^\vee alpha_i^\vee

        References:
            Kac, V. G. "Infinite Dimensional Lie Algebras" (3rd ed.), Table Aff 1-3
        """
        if self._dual_coxeter_number is None:
            try:
                cartan_type = self.root_system.cartan_type()

                # Try to get dual_coxeter_number directly from cartan_type
                if hasattr(cartan_type, "dual_coxeter_number"):
                    self._dual_coxeter_number = int(cartan_type.dual_coxeter_number())
                # For affine types: sum of dual comarks acheck()
                elif hasattr(cartan_type, "acheck"):
                    acheck = cartan_type.acheck()
                    self._dual_coxeter_number = int(sum(acheck[i] for i in acheck.keys()))
                # Fallback: Try coxeter_number for finite types
                elif hasattr(cartan_type, "coxeter_number"):
                    self._dual_coxeter_number = int(cartan_type.coxeter_number())
                else:
                    self._dual_coxeter_number = None
            except Exception:
                self._dual_coxeter_number = None

        return self._dual_coxeter_number

    def __repr__(self) -> str:
        """
        Return a string representation of the AffineRootSystem.

        Returns:
            String representation showing the Cartan type
        """
        return f"AffineRootSystem({self.cartan_type})"

    def wrap_root(self, root: Any) -> RootWithReflection:
        return RootWithReflection(root)
