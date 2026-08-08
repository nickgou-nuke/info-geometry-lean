import sympy as sp

def penrose_inversion():
    x, y, z, t = sp.symbols('x y z t', real=True)
    # Projective coordinates
    X = sp.Matrix([x, y, z, t])
    
    # State |infty> and |0>
    infty = sp.Matrix([1, 0, 0, 0])
    zero = sp.Matrix([0, 0, 0, 1])
    
    # Inversion matrix (Weyl Involution / Conformal Inversion)
    I = sp.Matrix([
        [0, 0, 0, 1],
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [1, 0, 0, 0]
    ])
    
    print("State |infty>:", infty.T)
    print("State |0>:", zero.T)
    print("Inversion Matrix I:")
    sp.pprint(I)
    
    mapped = I * infty
    print("I * |infty> = ", mapped.T)
    
    if mapped == zero:
        print("Success: |infty> maps exactly to |0>")

if __name__ == '__main__':
    penrose_inversion()
