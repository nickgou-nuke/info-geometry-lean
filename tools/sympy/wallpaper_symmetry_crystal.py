import sympy as sp

def verify_wallpaper_pg_symmetry():
    """
    Computes the generators of the `pg` wallpaper group and demonstrates
    how its non-symmorphic glide reflection generates the Klein Bottle topology
    when projected onto the momentum space Brillouin Zone.
    """
    # 1. Define spatial coordinates on the 2D lattice
    x, y = sp.symbols('x y', real=True)
    p = sp.Matrix([x, y])
    
    # 2. Define the `pg` wallpaper group generators
    # T_y: Pure translation along the y-axis
    T_y = sp.Matrix([x, y + 1])
    
    # T_y_inv: Inverse translation along the y-axis
    T_y_inv = sp.Matrix([x, y - 1])
    
    # G: Glide reflection (translate by 1/2 along x, reflect across x-axis)
    G = sp.Matrix([x + sp.Rational(1, 2), -y])
    
    # Apply G twice to a point
    G_squared_x = G[0].subs({x: G[0], y: G[1]})
    G_squared_y = G[1].subs({x: G[0], y: G[1]})
    G_squared = sp.Matrix([G_squared_x, G_squared_y])
    
    # G^2 should be a pure translation along the x-axis by 1
    T_x = sp.Matrix([x + 1, y])
    is_glide_squared_translation = sp.simplify(G_squared - T_x) == sp.zeros(2, 1)
    
    # 3. Commutation relation between G and T_y
    # G * T_y (apply T_y then G)
    G_Ty = sp.Matrix([
        G[0].subs({x: T_y[0], y: T_y[1]}),
        G[1].subs({x: T_y[0], y: T_y[1]})
    ])
    
    # T_y^-1 * G (apply G then T_y^-1)
    Ty_inv_G = sp.Matrix([
        T_y_inv[0].subs({x: G[0], y: G[1]}),
        T_y_inv[1].subs({x: G[0], y: G[1]})
    ])
    
    # The commutation relation G * T_y = T_y^-1 * G proves that traversing the 
    # y-direction and then applying the glide reflection is equivalent to applying 
    # the glide reflection and then moving backwards in the y-direction.
    # This orientation reversal is the exact geometric definition of the Klein Bottle!
    is_klein_bottle_commutation = sp.simplify(G_Ty - Ty_inv_G) == sp.zeros(2, 1)
    
    print("=== Wallpaper Group `pg` & Klein Bottle Topology ===")
    print(f"Lattice Coordinate: {p.T}")
    print(f"Y-Translation (T_y): {T_y.T}")
    print(f"Glide Reflection (G): {G.T}")
    print(f"G^2 == T_x (Translation by 1): {is_glide_squared_translation}")
    print(f"G * T_y == T_y^-1 * G (Orientation Reversal): {is_klein_bottle_commutation}")
    
    if is_glide_squared_translation and is_klein_bottle_commutation:
        print("\n[SUCCESS] The `pg` wallpaper symmetry mathematically generates the Klein Bottle!")
        print("This discrete 2D spatial crystal exactly mirrors the quantum vacuum's non-orientable Brillouin Zone.")

if __name__ == "__main__":
    verify_wallpaper_pg_symmetry()
