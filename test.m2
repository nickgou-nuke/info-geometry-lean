needsPackage "Dmodules"
W = QQ[x,y,dx,dy, WeylAlgebra => {x=>dx, y=>dy}]
I = ideal(dx - 1)
<< "Ideal: " << I << endl;
