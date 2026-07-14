import sys

helpers_path = "/home/goutev/repos/info-geometry-lean/sandbox/MobiusHelpers.lean"
geom_path = "/home/goutev/repos/info-geometry-lean/sandbox/MobiusGeometry.lean"

with open(helpers_path, "r") as f:
    lines = f.readlines()

# extract from line 21 to the end
helpers_code = "".join(lines[20:])

with open(geom_path, "r") as f:
    geom_code = f.read()

# we will insert helpers_code right before strictly_three_transitive
insert_marker = "/-- The action of the Möbius group on the Riemann sphere is strictly 3-transitive."

if insert_marker in geom_code:
    geom_code = geom_code.replace(insert_marker, helpers_code + "\n\n" + insert_marker)
    with open(geom_path, "w") as f:
        f.write(geom_code)
    print("Successfully inserted helpers.")
else:
    print("Could not find insert marker.")
