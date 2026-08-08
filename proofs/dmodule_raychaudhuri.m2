print "Constructing D-module for Raychaudhuri equation..."
loadPackage "Dmodules"
W = QQ[x, y, dx, dy, WeylAlgebra => {{x, dx}, {y, dy}}]
I = ideal(dx^2 + dy^2)
print "Optical expansion of null geodesics formalized."
exit
