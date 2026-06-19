import sympy as sp

def classify_wallpaper_groups():
    """
    Classifies the 17 2D Wallpaper Groups and their Point Groups (Holonomy).
    This establishes the basis for their irreducible representations.
    """
    print("=== THE 17 WALLPAPER GROUPS AND THEIR POINT GROUPS ===")
    
    # The 17 Wallpaper Groups are classified by their Point Group (which must be a subgroup of O(2) 
    # compatible with a 2D lattice, specifically crystallographic restriction implies order 1, 2, 3, 4, 6)
    
    wallpaper_groups = [
        {"IT": 1, "Symbol": "p1", "PointGroup": "C1 (Z/1Z)", "Lattice": "Oblique"},
        {"IT": 2, "Symbol": "p2", "PointGroup": "C2 (Z/2Z)", "Lattice": "Oblique"},
        {"IT": 3, "Symbol": "pm", "PointGroup": "D1 (Z/2Z)", "Lattice": "Rectangular"},
        {"IT": 4, "Symbol": "pg", "PointGroup": "D1 (Z/2Z)", "Lattice": "Rectangular"},
        {"IT": 5, "Symbol": "cm", "PointGroup": "D1 (Z/2Z)", "Lattice": "Rhombic"},
        {"IT": 6, "Symbol": "pmm", "PointGroup": "D2 (V4 / Z/2Z x Z/2Z)", "Lattice": "Rectangular"},
        {"IT": 7, "Symbol": "pmg", "PointGroup": "D2 (V4)", "Lattice": "Rectangular"},
        {"IT": 8, "Symbol": "pgg", "PointGroup": "D2 (V4)", "Lattice": "Rectangular"},
        {"IT": 9, "Symbol": "cmm", "PointGroup": "D2 (V4)", "Lattice": "Rhombic"},
        {"IT": 10, "Symbol": "p4", "PointGroup": "C4 (Z/4Z)", "Lattice": "Square"},
        {"IT": 11, "Symbol": "p4m", "PointGroup": "D4 (Dihedral 8)", "Lattice": "Square"},
        {"IT": 12, "Symbol": "p4g", "PointGroup": "D4 (Dihedral 8)", "Lattice": "Square"},
        {"IT": 13, "Symbol": "p3", "PointGroup": "C3 (Z/3Z)", "Lattice": "Hexagonal"},
        {"IT": 14, "Symbol": "p3m1", "PointGroup": "D3 (Dihedral 6 / S3)", "Lattice": "Hexagonal"},
        {"IT": 15, "Symbol": "p31m", "PointGroup": "D3 (Dihedral 6 / S3)", "Lattice": "Hexagonal"},
        {"IT": 16, "Symbol": "p6", "PointGroup": "C6 (Z/6Z)", "Lattice": "Hexagonal"},
        {"IT": 17, "Symbol": "p6m", "PointGroup": "D6 (Dihedral 12)", "Lattice": "Hexagonal"},
    ]
    
    print(f"{'IT#':<4} | {'H-M Symbol':<10} | {'Lattice':<12} | {'Point Group (Holonomy)':<25}")
    print("-" * 60)
    for g in wallpaper_groups:
        print(f"{g['IT']:<4} | {g['Symbol']:<10} | {g['Lattice']:<12} | {g['PointGroup']:<25}")
        
    print("\n=== REPRESENTATION THEORY (Irreducible Representations) ===")
    print("The irreducible representations of the wallpaper group G are induced from the representations of its Point Group P via the little group method (Mackey theory).")
    print("For a given momentum vector k in the Brillouin zone:")
    print("1. If k is generic, the little group is trivial, and the representation is 1D.")
    print("2. If k is at a high-symmetry point (e.g. Gamma point k=0), the little group is the full point group P.")
    print("   Therefore, at k=0, the representations of the wallpaper group are exactly the representations of P.")
    print("   Example: For p4m (Point Group D4), the representations at k=0 are the 4 1D reps and 1 2D rep of D4.")

if __name__ == "__main__":
    classify_wallpaper_groups()
