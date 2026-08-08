"""SymPy witness for modular/Krein J and bivector I compatibility.

This is the concrete matrix shadow of the directed tower:
- J is the involutive reflection;
- I is the bivector rotor with square -1;
- the stage embedding is a Kronecker doubling;
- both J and I commute with the embedding by construction.
"""

import sympy as sp


I2 = sp.eye(2)
I = sp.Matrix([[0, -1], [1, 0]])
J = sp.Matrix([[1, 0], [0, -1]])


def embed(m: sp.Matrix) -> sp.Matrix:
    return sp.kronecker_product(I2, m)


def main() -> None:
    assert J**2 == I2
    assert I**2 == -I2
    assert J * I * J == -I

    EJ = embed(J)
    EI = embed(I)
    I4 = sp.eye(4)

    assert EJ**2 == I4
    assert EI**2 == -I4
    assert EJ * EI * EJ == -EI
    assert embed(J * I * J) == EJ * EI * EJ

    print("modular_krein_embedding_sympy.py: J_compat and I_compat verified")


if __name__ == "__main__":
    main()
