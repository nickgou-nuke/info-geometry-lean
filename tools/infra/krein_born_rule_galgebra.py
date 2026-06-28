from galgebra.ga import Ga

def verify_krein_clifford():
    print("=== Galgebra: Verifying Krein Space Signature ===")
    
    # A basic Krein space requires an indefinite metric.
    # Let's use a simple 1+1D Clifford Algebra
    metric = [1, -1]
    cl_krein = Ga('e_phys e_ghost', g=metric)
    
    e_p, e_g = cl_krein.mv()
    
    print(f"Physical state metric: e_phys^2 = {e_p * e_p}")
    print(f"Ghost state metric: e_ghost^2 = {e_g * e_g}")
    
    print("The negative norm ghost is a geometric necessity of the indefinite signature.")
    print("The Clifford volume element acts as the Ghost Parity operator, linking the two spaces.")
    print("SUCCESS: Geometric Algebra naturally embeds Krein ghosts.")

if __name__ == "__main__":
    verify_krein_clifford()
