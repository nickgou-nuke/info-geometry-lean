import sympy as sp

def verify_brillouin_klein_bottle_model():
    print("=== Brillouin Klein Bottle from Artificial Gauge Fields ===")
    kx, ky = sp.symbols('kx ky', real=True)
    eps = sp.symbols('epsilon', real=True)
    t11x, t12x, t21x, t22x = sp.symbols('t11x t12x t21x t22x', real=True)
    t1y, t2y = sp.symbols('t1y t2y', real=True)
    lam = sp.symbols('lambda', real=True)
    
    # Hopping functions
    q1x = t11x + t12x * sp.exp(sp.I * kx)
    q2x = t21x + t22x * sp.exp(sp.I * kx)
    
    q_plus_y = t1y + t2y * sp.exp(sp.I * ky)
    q_minus_y = t1y - t2y * sp.exp(sp.I * ky)
    
    # H0(k) Eq. (10)
    H0 = sp.Matrix([
        [eps, sp.conjugate(q1x), sp.conjugate(q_plus_y), 0],
        [q1x, eps, 0, sp.conjugate(q_minus_y)],
        [q_plus_y, 0, -eps, sp.conjugate(q2x)],
        [0, q_minus_y, q2x, -eps]
    ])
    
    # Pauli matrices for tensor product
    tau_1 = sp.Matrix([[0, 1], [1, 0]])
    tau_2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    tau_3 = sp.Matrix([[1, 0], [0, -1]])
    tau_0 = sp.eye(2)
    
    sig_1 = sp.Matrix([[0, 1], [1, 0]])
    sig_2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    sig_3 = sp.Matrix([[1, 0], [0, -1]])
    sig_0 = sp.eye(2)
    
    # Tensor products
    def kron(A, B):
        import numpy as np
        return sp.Matrix(np.kron(np.array(A.tolist(), dtype=object), np.array(B.tolist(), dtype=object)))
    
    # H1(k) = lambda*cos(ky) * (tau_1 x sig_2) + lambda*sin(ky) * (tau_2 x sig_2)
    t1_s2 = kron(tau_1, sig_2)
    t2_s2 = kron(tau_2, sig_2)
    H1 = lam * sp.cos(ky) * t1_s2 + lam * sp.sin(ky) * t2_s2
    
    H = H0 + H1
    
    # Glide symmetry: Mx = tau_0 x sig_1
    U = kron(tau_0, sig_1)
    
    H_transformed = sp.simplify(U * H * U.inv())
    
    # Note: the paper says H(kx, ky) is mapped to H(-kx, ky + pi)
    H_target = sp.simplify(H.subs({kx: -kx, ky: ky + sp.pi}))
    
    # Check if H_transformed == H_target under the condition t11x = t21x, t12x = t22x ?
    # Let's substitute the parameter values from the paper to check explicitly.
    # "t11x = t22x = 1, t12x = t21x = 3.5" for Fig 3d,e
    # Wait, if we use symbolic, we might need specific relations. Let's try to check the symmetry directly with parameters.
    val_subs = {t11x: 1, t22x: 1, t12x: 3.5, t21x: 3.5, t1y: 2, t2y: 1.5, eps: 1, lam: 1}
    
    H_num = H.subs(val_subs)
    H_num_transformed = sp.simplify(U * H_num * U.inv())
    H_num_target = sp.simplify(H_num.subs({kx: -kx, ky: ky + sp.pi}))
    
    is_symmetric = H_num_transformed == H_num_target
    print(f"Momentum-space glide symmetry U*H(k)*U^-1 == H(-kx, ky+pi) with specific parameters: {is_symmetric}")
    if not is_symmetric:
        print("Diff:", sp.simplify(H_num_transformed - H_num_target))

if __name__ == "__main__":
    verify_brillouin_klein_bottle_model()
