# tools/sage/wallpaper_groups_reps.sage
import sys
from sage.all import *

def classify_wallpaper_reps():
    print("=== SAGE/GAP: FULL CLASSIFICATION OF WALLPAPER GROUP REPRESENTATIONS ===")
    
    # In GAP, 2D space groups (wallpaper groups) are accessed via SpaceGroup(2, i) where i = 1..17
    # Note: SpaceGroup is in the 'cryst' or 'crystcat' package.
    # We will use GAP through Sage.
    
    gap.eval('LoadPackage("cryst");')
    
    for i in range(1, 18):
        print(f"\n--- Wallpaper Group IT number {i} ---")
        
        # Get the group
        G_gap = gap.eval(f'G := SpaceGroup(2, {i});')
        
        # Get the point group to analyze finite quotients (since the full space group is infinite)
        P_gap = gap.eval('P := PointGroup(G);')
        
        # Space groups are infinite, so their full character table isn't finite. 
        # But we can get the character table of the Point Group (the holonomy group).
        # We can also compute the abelianization to get 1D representations of the space group.
        
        hm_symbol = gap.eval('SpaceGroupName(G);')
        print(f"Hermann-Mauguin Symbol: {hm_symbol}")
        print(f"Point Group Size: {gap.eval('Size(P);')}")
        
        # Character Table of the Point Group
        char_table = gap.eval('Display(CharacterTable(P));')
        print("Point Group Character Table (Irreducible Representations):")
        print(char_table)
        
        # Finite abelianization (1D representations of the full infinite group)
        abelian_invariants = gap.eval('AbelianInvariants(G);')
        print(f"Abelian Invariants of full Space Group (1D Reps classification): {abelian_invariants}")

if __name__ == "__main__":
    classify_wallpaper_reps()
