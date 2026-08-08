#!/usr/bin/env python3
"""
GAlgebra implementation of Conformal Cyclic Cosmology (CCC) Infinity-to-Zero transition.
"""

from galgebra.ga import Ga
from galgebra.printer import Format
import sympy as sp

def main():
    Format()
    # Define Cl(5,5) using GAlgebra
    # Base space: 4 positive, 4 negative. Conformal additions: 1 positive (ep), 1 negative (em)
    g = [1, 1, 1, 1, 1, -1, -1, -1, -1, -1]
    built = Ga.build('e_1 e_2 e_3 e_4 e_p e_5 e_6 e_7 e_8 e_m', g=g)
    cga = built[0]
    basis = built[1:]
    
    ep = basis[4]
    em = basis[9]
    
    # Construct conformal null vectors o (Zero) and inf (Infinity)
    # Standard CGA definition
    o = (em - ep) / 2
    inf = em + ep
    
    # Verify o . inf = -1
    dot_product = (o | inf)
    print("Zero and Infinity inner product (o . inf):", dot_product)
    
    # Conformal Inversion multivector
    # Inversion in CGA is represented by a reflection across the unit hypersphere (ep)
    inversion_operator = ep
    
    # Apply inversion: x' = - I x I^-1 (since ep^-1 = ep)
    # Note: galgebra allows standard multiplication
    o_inverted = -inversion_operator * o * inversion_operator
    inf_inverted = -inversion_operator * inf * inversion_operator
    
    print("\nOriginal o:", o)
    print("Inverted o:", o_inverted)
    print("Expected inverted o (inf / 2):", inf / 2)
    
    print("\nOriginal inf:", inf)
    print("Inverted inf:", inf_inverted)
    print("Expected inverted inf (2 * o):", 2 * o)

if __name__ == '__main__':
    main()
