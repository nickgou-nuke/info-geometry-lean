import sympy as sp

def thermodynamic_bvn_nmf():
    """
    Symbolically evaluate thermodynamic regression to the Birkhoff polytope edges.
    """
    n = 2
    # Define variables for a 2x2 doubly stochastic matrix
    x11, x12, x21, x22 = sp.symbols('x11 x12 x21 x22', positive=True)
    
    # Constraints: Row sums and Col sums = 1
    # x11 + x12 = 1 => x12 = 1 - x11
    # x11 + x21 = 1 => x21 = 1 - x11
    # x21 + x22 = 1 => x22 = 1 - x21 = x11
    
    # So the matrix is:
    # [x11, 1 - x11]
    # [1 - x11, x11]
    
    # Temperature parameter T for thermodynamic regression (softmax/entropy regularization)
    T = sp.symbols('T', positive=True)
    
    # Vertices (permutation matrices)
    P1 = sp.Matrix([[1, 0], [0, 1]]) # x11 = 1
    P2 = sp.Matrix([[0, 1], [1, 0]]) # x11 = 0
    
    # Let theta be the coordinate x11. 0 <= theta <= 1
    theta = sp.symbols('theta', real=True)
    
    # Entropy of the matrix entries
    # H(X) = -sum(x * log(x))
    def entropy(p):
        return -p * sp.log(p) - (1-p) * sp.log(1-p)
    
    H = entropy(theta) * 2  # Since x11=x22=theta and x12=x21=1-theta
    
    # Target matrix A
    A11, A12, A21, A22 = sp.symbols('A11 A12 A21 A22', positive=True)
    
    # Minimizing Frobenius distance to target A, minus T * Entropy
    # D(X, A) = (theta - A11)**2 + (1-theta - A12)**2 + (1-theta - A21)**2 + (theta - A22)**2
    D = (theta - A11)**2 + (1-theta - A12)**2 + (1-theta - A21)**2 + (theta - A22)**2
    
    # Free energy F = D - T * H
    F = D - T * H
    
    # Gradient dF/dtheta = 0
    dF_dtheta = sp.diff(F, theta)
    
    print("Thermodynamic Free Energy:", F)
    print("Gradient wrt theta:", dF_dtheta)
    
    # Low temperature limit T -> 0: Regression to vertices (edges of the polytope)
    # The gradient is dominated by dD/dtheta
    grad_D = sp.diff(D, theta)
    print("Low Temperature Gradient (T->0):", grad_D)
    
    # High temperature limit T -> infinity: Dominated by Entropy
    # Maximize entropy => theta = 0.5
    print("Max Entropy State (T->inf): theta = 1/2")

if __name__ == "__main__":
    thermodynamic_bvn_nmf()
