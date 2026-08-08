import sympy
from galgebra.ga import Ga
from galgebra.printer import Format

def main():
    Format()
    print("=== Geometric Algebra: Spacetime Orientability ===")
    
    # 1. Define Spacetime Algebra (STA) with signature (1, -1, -1, -1)
    # e0 is timelike, e1, e2, e3 are spacelike
    coords = sympy.symbols('t x y z')
    st = Ga('e', g=[1, -1, -1, -1], coords=coords)
    e0, e1, e2, e3 = st.mv()
    
    print("\n--- Spacetime Basis ---")
    print("Timelike basis vector (T-orientation):", e0)
    print("Spacelike basis vectors:", e1, e2, e3)
    
    # Space pseudoscalar (representing spatial orientation)
    I_space = e1 ^ e2 ^ e3
    print("Spatial pseudoscalar (P-orientation):", I_space)
    
    # Spacetime pseudoscalar
    I = e0 ^ e1 ^ e2 ^ e3
    print("Spacetime pseudoscalar:", I)
    
    print("\n--- Pseudo-orthogonal Transformations ---")
    
    def apply_reflection(v, n):
        # n is the normal vector to the reflection hyperplane
        # reflection formula: - n * v * n_inv
        n_inv = n / (n * n)
        return -n * v * n_inv
    
    print("1. Time Inversion (T) via reflection along e0:")
    Te0 = apply_reflection(e0, e0)
    Te1 = apply_reflection(e1, e0)
    print("  T(e0) =", Te0)
    print("  T(e1) =", Te1)
    
    # Time inversion character sigma_-
    print("  => Time orientation character sigma_-(T) maps to -1 (since e0 flips).")
    
    # Space orientation character under T
    T_I_space = Te1 ^ apply_reflection(e2, e0) ^ apply_reflection(e3, e0)
    print("  T(I_space) =", T_I_space)
    print("  => Space orientation character sigma_+(T) maps to +1 (I_space is preserved).")
    
    print("\n2. Spatial Inversion (P) via product of reflections along e1, e2, e3:")
    def apply_P(v):
        v1 = apply_reflection(v, e1)
        v2 = apply_reflection(v1, e2)
        v3 = apply_reflection(v2, e3)
        return v3
        
    Pe0 = apply_P(e0)
    Pe1 = apply_P(e1)
    print("  P(e0) =", Pe0)
    print("  P(e1) =", Pe1)
    
    # Parity inversion characters
    print("  => Time orientation character sigma_-(P) maps to +1 (e0 is preserved).")
    P_I_space = apply_P(e1) ^ apply_P(e2) ^ apply_P(e3)
    print("  P(I_space) =", P_I_space)
    print("  => Space orientation character sigma_+(P) maps to -1 (I_space flips).")

if __name__ == "__main__":
    main()
