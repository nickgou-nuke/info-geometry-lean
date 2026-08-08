import clifford as cf
import numpy as np

def main():
    # Setup 2D Geometric Algebra
    layout, blades = cf.Cl(2)
    e1 = blades['e1']
    e2 = blades['e2']
    e12 = blades['e12']
    
    def is_convex(v1, v2, v3, global_ps_sign):
        # Edge vectors
        u = (v2[0]-v1[0])*e1 + (v2[1]-v1[1])*e2
        v = (v3[0]-v2[0])*e1 + (v3[1]-v2[1])*e2
        
        # Outer product (local area bivector)
        bivec = u ^ v
        
        # Extract scalar coefficient of e12
        # ~e12 is the reverse of e12, which is -e12.
        # bivec is c*e12. bivec * ~e12 = c
        local_ps_val = (bivec * ~e12).value[0]
        local_ps_sign = np.sign(local_ps_val)
        
        print(f"Vectors: {v1} -> {v2} -> {v3}")
        print(f"Local bivector: {bivec}")
        print(f"Local pseudoscalar sign: {local_ps_sign}")
        print(f"Is convex? {local_ps_sign == global_ps_sign}\n")
        return local_ps_sign == global_ps_sign

    # Assuming global CCW polygon (global_ps_sign = 1)
    print("--- CCW Polygon (Global PS Sign = 1) ---")
    
    # Convex vertex turn
    v1 = (0, 0)
    v2 = (1, 0)
    v3 = (1, 1)
    is_convex(v1, v2, v3, 1)
    
    # Concave vertex turn (indentation into the polygon)
    v1 = (1, 1)
    v2 = (0.5, 0.5)
    v3 = (0, 1)
    is_convex(v1, v2, v3, 1)

if __name__ == "__main__":
    main()
