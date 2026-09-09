# Coefficient-level diagnostic for the (-1,-1,zeroScale) Lean lane.
# This mirrors only the four relevant basis elements and is not a Lean proof.

Print("FREUDENTHAL_SCALE_JACOBI_DIAGNOSTIC\n");
F := Rationals;;

# Coordinates are [E-, x-, y-, H].  The bracket is encoded bilinearly.
lb := function(x,y)
  return [
    2*(x[2]*y[3]-x[3]*y[2])
      -2*(x[4]*y[1]-x[1]*y[4]),
    -(x[4]*y[2]-x[2]*y[4]),
    -(x[4]*y[3]-x[3]*y[4]),
    0
  ];
end;;

add := function(x,y) return List([1..4],i -> x[i]+y[i]); end;;
J := function(x,y,z)
  return add(add(lb(x,lb(y,z)),lb(y,lb(z,x))),lb(z,lb(x,y)));
end;;

e := [1,0,0,0];; x := [0,1,0,0];; y := [0,0,1,0];; h := [0,0,0,1];;
res := J(x,y,h);;
Print("basis_order=Eminus,xminus,yminus,H\n");
Print("jacobi(xminus,yminus,H)=",res,"\n");
Print("STATUS=",res=[0,0,0,0],"\n");
QUIT;
