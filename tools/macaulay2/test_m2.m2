needsPackage "Dmodules"
W5 = QQ[x0, x1, x2, x3, x4, dx0, dx1, dx2, dx3, dx4, WeylAlgebra => {x0=>dx0, x1=>dx1, x2=>dx2, x3=>dx3, x4=>dx4}]
I5 = ideal(dx4 - 1)
try (
    deRhamAll(W5^1 / I5)
) else (
    print "deRhamAll failed"
)
