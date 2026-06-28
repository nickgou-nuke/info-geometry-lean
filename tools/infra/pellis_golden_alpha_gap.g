# GAP verification for Pellis golden-alpha normal form.
UnitElt := [1, 0];;
PhiElt := [0, 1];;
AddElt := function(a, b) return [a[1] + b[1], a[2] + b[2]]; end;;
SubElt := function(a, b) return [a[1] - b[1], a[2] - b[2]]; end;;
ScaleElt := function(q, a) return [q * a[1], q * a[2]]; end;;

# Using phi^2 = phi + 1, hence phi^-1 = phi - 1 and derived identities.
Inv2 := [2, -1];;
Inv3 := [-3, 2];;
Inv5 := [-8, 5];;

expr := AddElt(ScaleElt(360, Inv2), AddElt(ScaleElt(-2, Inv3), ScaleElt(1/243, Inv5)));;
target := [176410/243, -88447/243];;

if expr <> target then
  Error("Pellis GAP check failed");
fi;;

Print("GAP PASS\n");
Print("target_phi_basis = ", target, "\n");
QUIT;
