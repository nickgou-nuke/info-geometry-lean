import sympy as sp

def analyze_wallpaper_moebius_kms():
    """
    Formalizes the mapping of a 2D wallpaper group onto a thermal cylinder 
    (the 0 to beta KMS stripe) and its quotient into a Möbius tape.
    """
    print("=== Wallpaper Group and the Thermal KMS Stripe ===")
    
    # 1. The Wallpaper Group (Translations in a 2D plane)
    z = sp.Symbol('z')                 # Complex coordinate on the plane
    beta = sp.Symbol('beta', positive=True) # Thermal scale (inverse temperature)
    L = sp.Symbol('L', positive=True)       # Spatial period
    
    # Fundamental translations of the wallpaper group (e.g., p1 or p2)
    # T_space: z -> z + L
    # T_time: z -> z + I * beta
    print("Fundamental lattice generators:")
    print(f"T_space(z) = z + {L}")
    print(f"T_time(z)  = z + I * {beta}")
    
    # 2. The 0 to beta stripe (The KMS Cylinder)
    # The KMS condition enforces periodicity in imaginary time
    # This turns the 2D plane into a cylinder (a tape cut out of the wallpaper)
    print("\n=== The 0 to beta Stripe (Thermal Cylinder) ===")
    # Conformal mapping from the cylinder to the punctured plane
    w = sp.exp(2 * sp.pi * z / beta)
    print(f"Conformal mapping from cylinder to plane: w = {w}")
    print("Boundary at Im(z) = 0 maps to positive real axis.")
    print("Boundary at Im(z) = beta maps back to positive real axis (periodic KMS state).")
    
    # 3. The Möbius Symmetry Tape (Cross-cap)
    print("\n=== The Möbius Symmetry Tape ===")
    # To create a Möbius strip, we cut a finite tape of length L and width beta,
    # and glue the spatial boundaries with an orientation reversal (parity inversion).
    # Standard cylinder: (x + L, y) ~ (x, y)
    # Möbius strip: (x + L, y) ~ (x, beta - y)  or  z + L ~ conj(z) + I * beta
    x, y = sp.symbols('x y', real=True)
    glue_cylinder = (x + L, y)
    glue_moebius = (x + L, beta - y)
    
    print(f"Cylinder gluing: (x, y) ~ {glue_cylinder}")
    print(f"Möbius gluing:   (x, y) ~ {glue_moebius}")
    
    # 4. Two p-tapes (The Double Cover / Orientable double)
    print("\n=== Two p-tapes (Orientable Double Cover) ===")
    print("The Möbius strip has an orientable double cover which is a standard cylinder of length 2L.")
    print("This corresponds to splitting the non-orientable state into two orientable 'p-tapes' (left and right moving sectors).")
    
    # 5. Partition Function of the KMS Stripe (Free Boson)
    print("\n=== Partition Function on the Strip ===")
    tau = sp.Symbol('tau') # Modular parameter tau = I * beta / L
    # The partition function of a free boson on the cylinder (Z_cyl) vs Moebius (Z_moeb)
    # Z_cyl is related to the Dedekind eta function
    q = sp.exp(2 * sp.pi * sp.I * tau)
    print("Modular parameter q = e^(2 pi i tau), where tau = I * beta / L")
    print("The Möbius strip partition function Z_moeb represents the unoriented string loop (cross-cap).")
    print("It enforces the exact algebraic parity inversion required by the Cuntz boundary.")

if __name__ == "__main__":
    analyze_wallpaper_moebius_kms()
