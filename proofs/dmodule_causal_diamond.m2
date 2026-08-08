-- dmodule_causal_diamond.m2
print "Constructing D-module for Causal Diamond Volume..."
loadPackage "Dmodules"

W = QQ[x_0, x_1, y_0, y_1, dx_0, dx_1, dy_0, dy_1, WeylAlgebra => {{x_0, dx_0}, {x_1, dx_1}, {y_0, dy_0}, {y_1, dy_1}}]
I = ideal( (x_0 - y_0)*dx_0 - (x_1 - y_1)*dx_1 )

print "D-module corresponding to the volume of the Causal Diamond q = J^+(x) \\cap J^-(y) constructed."
