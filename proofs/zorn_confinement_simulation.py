import sympy as sp

def dot3(u, v):
    return u[0]*v[0] + u[1]*v[1] + u[2]*v[2]

def cross3(u, v):
    return [
        u[1]*v[2] - u[2]*v[1],
        u[2]*v[0] - u[0]*v[2],
        u[0]*v[1] - u[1]*v[0]
    ]

def vec_add(u, v):
    return [u[i] + v[i] for i in range(3)]

def vec_sub(u, v):
    return [u[i] - v[i] for i in range(3)]

def vec_scale(s, u):
    return [s * u[i] for i in range(3)]

class Zorn:
    def __init__(self, a, b, u, v):
        self.a = sp.simplify(a)
        self.b = sp.simplify(b)
        self.u = [sp.simplify(x) for x in u]
        self.v = [sp.simplify(x) for x in v]

    def __mul__(self, other):
        # Zorn multiplication:
        # a = X.a * Y.a + dot3(X.u, Y.v)
        # b = X.b * Y.b + dot3(X.v, Y.u)
        # u = X.a * Y.u + Y.b * X.u - cross3(X.v, Y.v)
        # v = Y.a * X.v + X.b * Y.v + cross3(X.u, Y.u)
        a_new = self.a * other.a + dot3(self.u, other.v)
        b_new = self.b * other.b + dot3(self.v, other.u)
        
        u1 = vec_scale(self.a, other.u)
        u2 = vec_scale(other.b, self.u)
        u3 = cross3(self.v, other.v)
        u_new = vec_sub(vec_add(u1, u2), u3)
        
        v1 = vec_scale(other.a, self.v)
        v2 = vec_scale(self.b, other.v)
        v3 = cross3(self.u, other.u)
        v_new = vec_add(vec_add(v1, v2), v3)
        
        return Zorn(a_new, b_new, u_new, v_new)

    def __add__(self, other):
        return Zorn(self.a + other.a, self.b + other.b, vec_add(self.u, other.u), vec_add(self.v, other.v))

    def __sub__(self, other):
        return Zorn(self.a - other.a, self.b - other.b, vec_sub(self.u, other.u), vec_sub(self.v, other.v))

    def display(self, name="Zorn Matrix"):
        print(f"\n=== {name} ===")
        print(f"a (Upper Diagonal, P+) : {self.a}")
        print(f"b (Lower Diagonal, P-) : {self.b}")
        print(f"u (Upper Vector, Color)     : {self.u}")
        print(f"v (Lower Vector, Anti-Color): {self.v}")

def main():
    print("Initializing SymPy Zorn Algebra Simulation for Color Confinement...")
    
    # Define three quark color vectors
    u1 = [sp.Symbol(f'u1_{i}') for i in ['R', 'G', 'B']]
    u2 = [sp.Symbol(f'u2_{i}') for i in ['R', 'G', 'B']]
    u3 = [sp.Symbol(f'u3_{i}') for i in ['R', 'G', 'B']]
    
    # Define three anti-quark color vectors
    v1 = [sp.Symbol(f'v1_{i}') for i in ['R', 'G', 'B']]
    v2 = [sp.Symbol(f'v2_{i}') for i in ['R', 'G', 'B']]
    v3 = [sp.Symbol(f'v3_{i}') for i in ['R', 'G', 'B']]
    
    # Construct Nilpotent Quarks
    Q1 = Zorn(0, 0, u1, [0,0,0])
    Q2 = Zorn(0, 0, u2, [0,0,0])
    Q3 = Zorn(0, 0, u3, [0,0,0])
    
    # Construct Nilpotent Anti-Quarks
    Qbar1 = Zorn(0, 0, [0,0,0], v1)
    Qbar2 = Zorn(0, 0, [0,0,0], v2)
    Qbar3 = Zorn(0, 0, [0,0,0], v3)
    
    print("\n--- 1. THE BARYON CONFINEMENT (3 Quarks) ---")
    left_bracket = (Q1 * Q2) * Q3
    right_bracket = Q1 * (Q2 * Q3)
    
    Baryon = left_bracket - right_bracket
    Baryon.display("Baryon Associator [Q1, Q2, Q3]")
    
    # The expected Color Determinant (Scalar Triple Product)
    T = sp.simplify(dot3(cross3(u1, u2), u3))
    print(f"\nExpected Scalar Triple Product T = u1 . (u2 x u3):")
    print(T)
    
    print("\nVerify Baryon == -T * P_+  +  T * P_-")
    print(f"Baryon.a matches -T: {sp.simplify(Baryon.a - (-T)) == 0}")
    print(f"Baryon.b matches  T: {sp.simplify(Baryon.b - T) == 0}")
    
    print("\n--- 2. THE ANTI-BARYON CONFINEMENT (3 Anti-Quarks) ---")
    left_bracket_bar = (Qbar1 * Qbar2) * Qbar3
    right_bracket_bar = Qbar1 * (Qbar2 * Qbar3)
    
    AntiBaryon = left_bracket_bar - right_bracket_bar
    AntiBaryon.display("Anti-Baryon Associator [Qbar1, Qbar2, Qbar3]")
    
    # Expected Anti-Color Determinant
    T_bar = sp.simplify(dot3(cross3(v1, v2), v3))
    print(f"\nExpected Anti-Color Determinant T_bar = v1 . (v2 x v3):")
    print(T_bar)
    print(f"AntiBaryon.a matches -T_bar: {sp.simplify(AntiBaryon.a - (-T_bar)) == 0}")
    print(f"AntiBaryon.b matches  T_bar: {sp.simplify(AntiBaryon.b - T_bar) == 0}")

    print("\n--- 3. THE MESON CONFINEMENT (Quark + Anti-Quark) ---")
    # Meson is the symmetric Jordan product (anticommutator)
    Meson = (Q1 * Qbar1) + (Qbar1 * Q1)
    Meson.display("Meson Anticommutator {Q1, Qbar1}")
    
    # Expected Dot Product
    S = sp.simplify(dot3(u1, v1))
    print(f"\nExpected Color-AntiColor Dot Product S = u1 . v1:")
    print(S)
    print(f"Meson.a matches S: {sp.simplify(Meson.a - S) == 0}")
    print(f"Meson.b matches S: {sp.simplify(Meson.b - S) == 0}")

if __name__ == "__main__":
    main()
