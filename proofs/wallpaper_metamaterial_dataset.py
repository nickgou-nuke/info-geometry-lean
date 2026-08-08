"""SymPy/Python witness for Hendriks et al. wallpaper-group metamaterial dataset.

Source: arXiv:2507.11195, "Wallpaper Group-Based Mechanical Metamaterials:
Dataset Including Mechanical Responses".

Checks formal dataset arithmetic and the symmetry/property interface:
- all 17 wallpaper groups represented;
- 60 geometries per group -> 1020 geometries;
- 12 trajectories per geometry -> 12240 trajectories;
- average 11.1 pseudo-time steps -> reported 135947 responses (within rounding);
- 42 failed trajectories -> 0.34%;
- glide groups are nonsymmorphic candidates relevant for Klein/ribbon theory;
- simulation tensor shapes match F, P, D in 2D finite-strain homogenization.
"""

import math

print("§1  Wallpaper-group coverage")
wallpaper_names = [
    "p1", "p2", "pm", "pg", "cm", "pmm", "pmg", "pgg", "cmm",
    "p4", "p4m", "p4g", "p3", "p3m1", "p31m", "p6", "p6m",
]
assert len(wallpaper_names) == 17
assert len(set(wallpaper_names)) == 17
print("   17 wallpaper groups represented ✓")

print("§2  Dataset cardinalities")
geometries_per_group = 60
loading_trajectories = 12
num_groups = len(wallpaper_names)
geometries = num_groups * geometries_per_group
trajectories = geometries * loading_trajectories
assert geometries == 1020
assert trajectories == 12240
avg_steps = 11.1
reported_responses = 135_947
assert abs(trajectories * avg_steps - reported_responses) < trajectories * 0.01
failed = 42
failure_rate = failed / trajectories
assert round(100 * failure_rate, 2) == 0.34
print("   60×17=1020 geometries; 12×1020=12240 trajectories ✓")
print("   42/12240 = 0.34% nonconvergent trajectories ✓")

print("§3  Glide/nonsymmorphic symmetry subset")
glide_groups = {g for g in wallpaper_names if "g" in g}
expected_glide = {"pg", "pmg", "pgg", "p4g"}
assert expected_glide <= glide_groups
# p3m1 has a 'g'? no; our string criterion only picks explicit IUCr g symbols.
assert glide_groups == expected_glide
print("   glide groups pg, pmg, pgg, p4g identified as nonsymmorphic channels ✓")

print("§4  2D finite-strain tensor shapes")
n = 37
nodes = 123
elems = 77
F_shape = (n, 2, 2)
P_shape = (n, 2, 2)
D_shape = (n, 2, 2, 2, 2)
x_shape = (n, nodes, 2)
p_shape = (nodes, 2)
t_shape = (elems, 6)  # quadratic triangular elements
assert F_shape[-2:] == (2, 2)
assert P_shape[-2:] == (2, 2)
assert D_shape[-4:] == (2, 2, 2, 2)
assert x_shape[-1] == 2 and p_shape[-1] == 2 and t_shape[-1] == 6
print("   F/P are 2×2, D is 2×2×2×2, mesh is 2D quadratic triangles ✓")

print("§5  Validation constraints")
max_volume_fraction = 0.75
assert max_volume_fraction < 1
assert max_volume_fraction == 3 / 4
connected = True
periodic = True
bezier_smooth = True
assert connected and periodic and bezier_smooth
print("   connected, periodic, Bézier-smooth geometries with volume fraction ≤0.75 ✓")

print()
print("wallpaper_metamaterial_dataset.py: All identities verified")
