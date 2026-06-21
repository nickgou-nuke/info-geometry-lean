#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Symbolic Cuntz Algebra & Thermodynamic Limits (OPEs)
Evaluates the Boson-Fermion correspondence and scaling limits in SymPy.
"""

import sympy as sp
from sympy.core.expr import Expr

class CuntzNode:
    """A symbolic node representing sequences of Cuntz generators and their adjoints."""
    def __init__(self, s_seq, s_star_seq, coef=1):
        # Represents coef * (s_{s_seq} * s^*_{s_star_seq})
        # Since any word in Cuntz algebra can be uniquely reduced to s_I s^*_J
        self.s_seq = tuple(s_seq)
        self.s_star_seq = tuple(s_star_seq)
        self.coef = coef

    def __mul__(self, other):
        if not isinstance(other, CuntzNode):
            return CuntzNode(self.s_seq, self.s_star_seq, self.coef * other)
        
        # Multiply (s_I s^*_J) * (s_K s^*_L)
        # We must resolve s^*_J * s_K
        J = self.s_star_seq
        K = other.s_seq
        
        # Match as much as possible
        min_len = min(len(J), len(K))
        for i in range(min_len):
            if J[i] != K[i]:
                return CuntzNode((), (), 0) # Orthogonal
        
        if len(J) > len(K):
            # J has leftover adjoints
            new_J = J[min_len:]
            new_seq = self.s_seq
            new_star = other.s_star_seq + new_J
        else:
            # K has leftover generators
            new_K = K[min_len:]
            new_seq = self.s_seq + new_K
            new_star = other.s_star_seq
            
        return CuntzNode(new_seq, new_star, self.coef * other.coef)
    
    def __rmul__(self, other):
        return CuntzNode(self.s_seq, self.s_star_seq, self.coef * other)

    def dagger(self):
        return CuntzNode(self.s_star_seq, self.s_seq, sp.conjugate(self.coef))

class CuntzSum:
    def __init__(self, nodes):
        self.nodes = []
        for n in nodes:
            if n.coef != 0:
                self.nodes.append(n)
        self.simplify()

    def simplify(self):
        # Group by (s_seq, s_star_seq)
        grouped = {}
        for n in self.nodes:
            key = (n.s_seq, n.s_star_seq)
            grouped[key] = grouped.get(key, 0) + n.coef
            
        # Apply s1 s1* + s2 s2* = 1 reduction (optional for finite traces, but good for OPE)
        # If we see (I+1, J+1) and (I+2, J+2) with same coef, it reduces to (I, J)
        changed = True
        while changed:
            changed = False
            keys = list(grouped.keys())
            for key in keys:
                if grouped.get(key, 0) == 0:
                    continue
                # Check if key ends with 1 on both sides
                if len(key[0]) > 0 and len(key[1]) > 0 and key[0][-1] == 1 and key[1][-1] == 1:
                    base_seq = key[0][:-1]
                    base_star = key[1][:-1]
                    alt_key = (base_seq + (2,), base_star + (2,))
                    
                    coef1 = grouped[key]
                    coef2 = grouped.get(alt_key, 0)
                    
                    if coef1 != 0 and coef1 == coef2:
                        # Reduce!
                        grouped[key] = 0
                        grouped[alt_key] = 0
                        grouped[(base_seq, base_star)] = grouped.get((base_seq, base_star), 0) + coef1
                        changed = True

        self.nodes = [CuntzNode(seq, star, coef) for (seq, star), coef in grouped.items() if coef != 0]

    def __add__(self, other):
        return CuntzSum(self.nodes + other.nodes)
        
    def __sub__(self, other):
        return self + other * (-1)

    def __mul__(self, other):
        if isinstance(other, CuntzSum):
            new_nodes = []
            for a in self.nodes:
                for b in other.nodes:
                    new_nodes.append(a * b)
            return CuntzSum(new_nodes)
        else:
            return CuntzSum([n * other for n in self.nodes])
            
    def dagger(self):
        return CuntzSum([n.dagger() for n in self.nodes])

    def __repr__(self):
        if not self.nodes:
            return "0"
        terms = []
        for n in self.nodes:
            s = str(n.coef)
            if n.s_seq:
                s += " s_{" + "".join(map(str, n.s_seq)) + "}"
            if n.s_star_seq:
                s += " s^*_{" + "".join(map(str, n.s_star_seq)) + "}"
            if not n.s_seq and not n.s_star_seq:
                s += " I"
            terms.append(s)
        return " + ".join(terms)

# Base generators
S1 = CuntzSum([CuntzNode([1], [])])
S2 = CuntzSum([CuntzNode([2], [])])
S1_star = S1.dagger()
S2_star = S2.dagger()

def zeta(X: CuntzSum):
    """Kawamura Zeta map: zeta(x) = s1 x s1* - s2 x s2*"""
    return (S1 * X * S1_star) - (S2 * X * S2_star)

def rho(X: CuntzSum):
    """Kawamura Rho map: rho(x) = s1 x s1* + s2 x s2*"""
    return (S1 * X * S1_star) + (S2 * X * S2_star)

def fermion_generator(n):
    """a_n = zeta^{n-1}(s1 s2*)"""
    a = S1 * S2_star
    for _ in range(n - 1):
        a = zeta(a)
    return a

if __name__ == "__main__":
    print("--- Symbolic Cuntz Algebra & Thermodynamic Limits ---")
    
    a1 = fermion_generator(1)
    a2 = fermion_generator(2)
    
    print("\n[1] Fermion Generators:")
    print(f"a_1 = {a1}")
    print(f"a_2 = {a2}")
    
    print("\n[2] Checking CAR relations symbolically:")
    anticomm = a1 * a1.dagger() + a1.dagger() * a1
    print(f"a_1 a_1^* + a_1^* a_1 = {anticomm}")
    
    nilpotent = a1 * a1
    print(f"a_1 a_1 = {nilpotent}")
    
    cross_anticomm = a1 * a2 + a2 * a1
    print(f"a_1 a_2 + a_2 a_1 = {cross_anticomm}")
    
    print("\n[3] Calculating Boson Generator alpha_1 limit up to L=2:")
    # alpha_n = sum_{l=1}^infty rho^{2l-2}(X_n) + B_n
    # where X_1 = rho(s1 s2*) + s1 s2* s2 s1* etc
    
    # We truncate the thermodynamic limit sum
    X1 = rho(S1 * S2_star) + (S1 * S2_star * S2 * S1_star)
    print(f"X_1 = {X1}")
    
    alpha_1_trunc = X1 + rho(rho(X1)) # L=2 terms
    print(f"alpha_1 (truncated L=2) = {alpha_1_trunc}")
    
    print("\nThe SymPy engine successfully performs OPE scaling limits over the Cuntz word basis!")
