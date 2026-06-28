import sympy as sp

def verify_logcft():
    print("=== SymPy c=0 LogCFT Jordan Block ===")
    h, t = sp.symbols('h t', real=True)
    
    # Jordan block for L_0
    L0 = sp.Matrix([[h, 1], [0, h]])
    
    # Decomposition
    I = sp.eye(2)
    N = sp.Matrix([[0, 1], [0, 0]])
    
    assert L0 == h*I + N, "L0 must be h*I + N"
    assert N**2 == sp.zeros(2), "N must be nilpotent"
    
    # Correlator generator (evolution operator)
    # exp(-t L0) = exp(-ht) * (I - tN)
    evol = sp.exp(-t * L0)
    expected_evol = sp.exp(-h*t) * (I - t*N)
    
    # We can simplify the difference
    diff = sp.simplify(evol - expected_evol)
    assert diff == sp.zeros(2), "Logarithmic evolution mismatch!"
    
    print("[OK] LogCFT Jordan Block and Logarithmic Evolution Verified.")
    print("SYMPY_LOGCFT_OK")

if __name__ == "__main__":
    verify_logcft()
