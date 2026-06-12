#!/usr/bin/env python3
"""
SymPy witness for the KMS Modular Flow invariance of the Horizon.

Validates that the Event Horizon (the chiral crossing) and the 
Higgs Mass operator are macroscopic structures strictly invariant 
under time evolution.
"""

import sympy as sp
from primitive_cuntz_exactness_bridge import reduce_cuntz, SL, SR, SLs, SRs

def main():
    print("--- SymPy Twin: Modular Flow KMS Invariance ---")
    
    # 1. Define the Modular Flow parameters
    # The phase scales SL and SR by phase, and their adjoints by phase_star
    phase = sp.Symbol("phase", commutative=True)
    phase_star = sp.Symbol("phase_star", commutative=True)
    
    # We represent the modular flow action directly as a function
    def modular_flow(expr):
        # Substitute SL -> phase * SL
        # SR -> phase * SR
        # SLs -> SLs * phase_star
        # SRs -> SRs * phase_star
        # Because phase is commutative, order doesn't matter for the scalars
        return expr.subs({
            SL: phase * SL,
            SR: phase * SR,
            SLs: SLs * phase_star,
            SRs: SRs * phase_star
        })
        
    # The physical requirement of KMS state is that phase is a unitary unit:
    # phase * phase_star = 1
    
    # 2. Test Invariance of the Left-Right Horizon (S_L S_R*)
    horizon = SL * SRs
    flowed_horizon = modular_flow(horizon)
    
    # Substitute the unitary condition
    flowed_horizon_reduced = sp.expand(flowed_horizon).subs(phase * phase_star, 1)
    
    print(f"Original Horizon: {horizon}")
    print(f"Time-Evolved Horizon (reduced): {flowed_horizon_reduced}")
    assert flowed_horizon_reduced == horizon
    
    # 3. Test Invariance of the Modular Conjugation (Higgs Mass)
    higgs = SL * SRs + SR * SLs
    flowed_higgs = modular_flow(higgs)
    
    flowed_higgs_reduced = sp.expand(flowed_higgs).subs(phase * phase_star, 1)
    
    print(f"Original Higgs Mass: {higgs}")
    print(f"Time-Evolved Higgs Mass (reduced): {flowed_higgs_reduced}")
    assert flowed_higgs_reduced == higgs
    
    print("\n[SUCCESS] The Black Hole Event Horizon and the Higgs Mass are completely stationary under time evolution.")

if __name__ == "__main__":
    main()
