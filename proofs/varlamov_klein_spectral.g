su5AdjointDim := 5^2 - 1;;
spinorDim := 2^5;;
varlamovEven := Binomial(5,0) + Binomial(5,2) + Binomial(5,4);;
varlamovOdd := Binomial(5,1) + Binomial(5,3) + Binomial(5,5);;
wittenMoebiusIndex := varlamovEven - varlamovOdd;;
weylA4 := SymmetricGroup(5);;
mobiusZ2 := Group((1,2));;
Mobius := k -> -k;;
Trip := d -> d^3 - d;;

if su5AdjointDim <> 24 then Error("su5 adjoint"); fi;
if spinorDim <> 32 then Error("spinor dim"); fi;
if varlamovEven <> 16 or varlamovOdd <> 16 then Error("varlamov split"); fi;
if varlamovEven + varlamovOdd <> spinorDim then Error("spinor total"); fi;
if wittenMoebiusIndex <> 0 then Error("witten index"); fi;
if Size(weylA4) <> 120 then Error("weyl A4 order"); fi;
if Size(mobiusZ2) <> 2 then Error("mobius order"); fi;
if Mobius(Mobius(7)) <> 7 then Error("mobius involution"); fi;
if List([-1,0,1], Trip) <> [0,0,0] then Error("tripotent roots"); fi;

Print(rec(
  su5AdjointDim := su5AdjointDim,
  spinorDim := spinorDim,
  varlamovEven := varlamovEven,
  varlamovOdd := varlamovOdd,
  wittenMoebiusIndex := wittenMoebiusIndex,
  weylA4Order := Size(weylA4),
  mobiusGroupOrder := Size(mobiusZ2),
  tripotentRoots := [-1,0,1],
  edges := 6
), "\n");
QUIT;
