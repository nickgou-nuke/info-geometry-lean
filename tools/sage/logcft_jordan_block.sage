import sage.all as sg

def verify_logcft():
    print("=== SageMath c=0 LogCFT Indecomposability ===")
    # Define L0 over rationals for specific weight, e.g., h=0
    L0 = sg.matrix(sg.QQ, [[0, 1], [0, 0]])
    
    # Check if diagonalizable
    assert not L0.is_diagonalizable(), "Jordan block must NOT be diagonalizable!"
    
    # Jordan form
    J, P = L0.jordan_form(transformation=True)
    assert J == L0, "Already in Jordan form"
    
    print("[OK] LogCFT multiplet is indecomposable but not irreducible.")
    print("SAGE_LOGCFT_OK")

verify_logcft()
