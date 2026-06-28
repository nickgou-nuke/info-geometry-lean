#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-
"""
SageMath sketch of the First Law of Modular Thermodynamics / First Law of Entanglement Entropy.

We illustrate the identity:
    dS = d⟨K⟩
where S is the von Neumann entropy, K is the modular Hamiltonian, and ⟨·⟩ denotes expectation value.

This mirrors the SymPy version but uses Sage's syntax.
"""

# Define symbols using Sage's symbolic ring
S, K, Q = var('S K Q')
# Expectation value notation
expect_K = var('\\langle K \\rangle')

# Define entropy in terms of expectation value and partition function
# S = ⟨K⟩ + ln Q
S_expr = expect_k + log(Q)

print("Entropy expression: S = ⟨K⟩ + ln Q")
print(f"S = {S_expr}")
print()

# Take differentials conceptually
# dS = d⟨K⟩ + d(ln Q)
d_expect_K = var('d\\langle K \\rangle')
d_ln_Q = var('d ln Q')

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