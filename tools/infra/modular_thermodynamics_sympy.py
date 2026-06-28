#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SymPy sketch of the First Law of Modular Thermodynamics / First Law of Entanglement Entropy.

We illustrate the identity:
    dS = d⟨K⟩
where S is the von Neumann entropy, K is the modular Hamiltonian, and ⟨·⟩ denotes expectation value.

Derivation:
    For a normalized state ρ (Tr(ρ) = 1), the von Neumann entropy is S = -Tr(ρ ln ρ).
    The modular Hamiltonian K is defined via ρ = e^{-K}/Tr(e^{-K}) = e^{-K}/Q, where Q = Tr(e^{-K}).
    Then S = ⟨K⟩ + ln Q.
    Taking the differential: dS = d⟨K⟩ + d ln Q.
    For normalized states, Q = 1 (since Tr(ρ) = 1 implies Tr(e^{-K}) = 1), so d ln Q = 0.
    Hence dS = d⟨K⟩.

This file illustrates the symbolic steps of this derivation.
"""

import sympy as sp

# Define symbols
S, K, Q = sp.symbols('S K Q', real=True)
# Expectation value notation: we treat ⟨K⟩ as a symbol for simplicity
expect_K = sp.symbols('\\langle K \\rangle', real=True)

# Define entropy in terms of expectation value and partition function
# S = ⟨K⟩ + ln Q
S_expr = expect_K + sp.log(Q)

print("Entropy expression: S = ⟨K⟩ + ln Q")
print(f"S = {S_expr}")
print()

# Take differentials
# dS = d⟨K⟩ + d(ln Q)
dS = sp.diff(S_expr, expect_K) + sp.diff(S_expr, Q)  # Symbolic differentiation
# Actually, we want to show: dS = d⟨K⟩ + d(ln Q)
d_expect_K = sp.symbols('d\\langle K \\rangle', real=True)
d_ln_Q = sp.symbols('d ln Q', real=True)

print("Differential form:")
print("dS = d⟨K⟩ + d ln Q")
print()

# For normalized states, Q = 1, so d ln Q = 0
print("For normalized states (Tr(ρ) = 1):")
print("  Q = Tr(e^{-K}) = 1")
print("  Therefore ln Q = 0")
print("  Hence d ln Q = 0")
print()

print("Substituting d ln Q = 0:")
print("  dS = d⟨K⟩ + 0")
print("  dS = d⟨K⟩")
print()

print("Thus we obtain the First Law of Modular Thermodynamics:")
print("  dS = d⟨K⟩")
print()
print("This shows that the change in entropy equals the change in the expectation value")
print("of the modular Hamiltonian under perturbations of the normalized state.")