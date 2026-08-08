# orientation_characters.sage
# Formalization of Space/Time Orientability Characters

def space_time_characters(p, q):
    """
    Formulates space and time orientation characters for O(p, q).
    """
    print(f"Defining orientation characters for O({p}, {q})")
    
    # O(p, q) has 4 connected components if p, q > 0.
    # The characters are homomorphisms to {1, -1}.
    
    # Let's represent this abstractly.
    # sigma_plus: Space orientation character
    # sigma_minus: Time orientation character
    # sigma: Determinant
    
    def sigma_plus(matrix):
        # Extracts the sign of the determinant of the space-like part.
        return "sigma_plus(M)"
        
    def sigma_minus(matrix):
        # Extracts the sign of the determinant of the time-like part.
        return "sigma_minus(M)"
        
    def sigma(matrix):
        # Product of space and time characters (determinant)
        return "sigma_plus(M) * sigma_minus(M)"
        
    return sigma_plus, sigma_minus, sigma

print("Orientation characters formulation loaded.")
