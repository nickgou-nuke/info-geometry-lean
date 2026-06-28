#!/usr/bin/env python3
"""
Symbolic modeling of the A=39 mirror system using SymPy.
"""

import sympy as sp
import sys

def main():
    # Define symbolic variables
    # Ex: excitation energy
    # R_0: ground state nuclear radius
    # k: rate of radius increase with excitation
    # a: related to proton charge overlap integral
    Ex, a, R_0, k = sp.symbols('Ex a R_0 k', positive=True, real=True)
    
    # Formulate R as an increasing function of Ex for negative parity (proton excitation) configurations: R(Ex) = R_0 + k*Ex
    R_Ex = R_0 + k * Ex
    
    # Formulate the CED symbolically: CED(R) = a/R
    CED = a / R_Ex
    
    # Differentiate CED with respect to Ex
    dCED_dEx = sp.diff(CED, Ex)
    
    print(f"CED(Ex) = {CED}")
    print(f"d(CED)/d(Ex) = {dCED_dEx}")
    
    # Formally prove the downsloping trend d(CED)/d(Ex) < 0
    # Since a, R_0, k, Ex are defined as positive real numbers, dCED_dEx should be negative.
    is_negative = dCED_dEx.is_negative
    
    if is_negative:
        print("Proof successful: d(CED)/d(Ex) is strictly negative under the given assumptions.")
        print("PASS")
        sys.exit(0)
    else:
        print("Proof failed: Could not determine if d(CED)/d(Ex) is strictly negative.")
        print("FAIL")
        sys.exit(1)

if __name__ == "__main__":
    main()
