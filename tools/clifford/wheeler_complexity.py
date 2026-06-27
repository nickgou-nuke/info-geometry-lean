import sympy
from galgebra.ga import Ga
import clifford as cf

def model_cosmological_complexity():
    print("=== Cosmological Complexity Expansion Model ===\n")
    
    # 1. Initialize a low-dimensional Geometric Algebra (Cl(1,3))
    print("--- 1. Initialization (Symbolic and Numeric) ---")
    
    # Symbolic initialization with galgebra
    coords = sympy.symbols('t x y z', real=True)
    ga = Ga('e', g=[1, -1, -1, -1], coords=coords)
    e_sym = ga.mv()
    print("Symbolic Base Vectors (galgebra):", e_sym)
    
    # Numeric initialization with clifford
    layout, blades = cf.Cl(1, 3)
    print(f"Numeric Algebra (clifford): Cl(1,3) with Signature {layout.sig}")
    
    # Extract basis vectors (clifford names them e1, e2, e3, e4 by default)
    e1, e2, e3, e4 = blades['e1'], blades['e2'], blades['e3'], blades['e4']
    vectors = [e1, e2, e3, e4]
    
    # 2. Show how higher-grade elements are generated
    print("\n--- 2. Generating Higher-Grade Elements (Wedge Product) ---")
    
    # Grade 1
    print(f"Vectors (Grade 1): {len(vectors)} elements")
    
    # Grade 2 (Bivectors)
    bivectors = []
    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            bivectors.append(vectors[i] ^ vectors[j])
            
    print(f"Bivectors (Grade 2): {len(bivectors)} elements generated from v_i ^ v_j")
    
    # Grade 3 (Trivectors)
    trivectors = []
    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            for k in range(j + 1, len(vectors)):
                trivectors.append(vectors[i] ^ vectors[j] ^ vectors[k])
                
    print(f"Trivectors (Grade 3): {len(trivectors)} elements generated from v_i ^ v_j ^ v_k")
    
    # Grade 4 (Pseudoscalar)
    pseudoscalar = vectors[0] ^ vectors[1] ^ vectors[2] ^ vectors[3]
    print(f"Pseudoscalar (Grade 4): 1 element generated from v_1 ^ v_2 ^ v_3 ^ v_4")
    
    # 3. Compute geometric dimension (complexity) after products
    print("\n--- 3. Cosmological Complexity Computation ---")
    
    # The cosmological complexity here is modeled as the total dimension of the
    # generated geometric algebraic space.
    scalar_dim = 1
    vec_dim = len(vectors)
    bivec_dim = len(bivectors)
    trivec_dim = len(trivectors)
    pseudo_dim = 1
    
    total_complexity = scalar_dim + vec_dim + bivec_dim + trivec_dim + pseudo_dim
    print(f"Subspace Dimensions: 1 (Scalar) + {vec_dim} (Vector) + {bivec_dim} (Bivector) + {trivec_dim} (Trivector) + {pseudo_dim} (Pseudoscalar)")
    print(f"Total Geometric Dimension (Complexity): {total_complexity} = 2^{len(vectors)}")
    
    print("\n--- Geometric Product Interaction ---")
    print("Successive geometric products mix grades, modeling interacting cosmological fields.")
    v_a = e1 + 2.0*e2
    v_b = e1 - e3
    
    # Geometric product
    interaction = v_a * v_b
    print(f"Geometric Product of ({v_a}) and ({v_b}):\n  => {interaction}")
    print("Notice how the geometric product generates a multivector containing both scalar and bivector parts, reflecting complex coupled interactions.")

if __name__ == '__main__':
    model_cosmological_complexity()
