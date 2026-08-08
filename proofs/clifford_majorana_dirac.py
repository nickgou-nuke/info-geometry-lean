"""
Clifford (clifford_majorana_dirac.py)
Uses Cl(5,5) to define D using null vectors (Majorana parafermions).
Computes D + D^dagger and proves it collapses algebraically to 1.
"""
import clifford as cf

def main():
    print("--- Clifford Algebra Cl(5,5) Majorana Dirac ---")
    # Initialize Cl(5,5)
    layout, blades = cf.Cl(5, 5)
    
    # Extract basis vectors e1 to e10
    e = [blades[f'e{i}'] for i in range(1, 11)]
    
    # Define 5 null vectors (Majorana parafermions) and their duals
    # In Cl(5,5), e1..e5 square to +1 and e6..e10 square to -1.
    a = [0.5 * (e[i] + e[i+5]) for i in range(5)]
    a_dag = [0.5 * (e[i] - e[i+5]) for i in range(5)]
    
    print("Defined Null Vectors (Majorana Parafermions):")
    for i in range(5):
        print(f"a_{i+1} = {a[i]}")
        print(f"a_{i+1}^dag = {a_dag[i]}")
        # Verify null property
        assert abs(a[i]*a[i]) < 1e-12, f"a_{i+1} is not null"
        assert abs(a_dag[i]*a_dag[i]) < 1e-12, f"a_{i+1}^dag is not null"
        
    # Define D and D^dagger
    # The geometric projection operator that perfectly balances the space
    D = sum([a[i] * a_dag[i] for i in range(5)]) / 5.0
    D_dag = sum([a_dag[i] * a[i] for i in range(5)]) / 5.0
    
    print(f"\nD = {D}")
    print(f"D^dagger = {D_dag}")
    
    # Compute D + D^dagger
    result = D + D_dag
    print(f"\nD + D^dagger = {result}")
    
    # Verify it collapses to identity
    assert result == 1.0, "D + D^dagger does not equal 1"
    print("Proof successful: Maximal isotropy enforces D + D^dagger = I geometrically.")

if __name__ == "__main__":
    main()
