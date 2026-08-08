-- dmodule_volume_form.m2
-- Construct the D-module corresponding to a non-vanishing top-degree volume form on an orientable manifold.

loadPackage "Dmodules"

W = QQ[x, y, dx, dy, WeylAlgebra => {x=>dx, y=>dy}]

I = ideal(dx, dy)

print("Annihilator of the constant function (related to volume form O_X):")
print I

holonomic = isHolonomic I
print("Is the module holonomic? ")
print holonomic
