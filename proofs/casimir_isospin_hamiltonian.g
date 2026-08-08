MassCasimir := m2 -> -m2;;
SpinCasimir := J -> J*(J+1);;
IsospinCasimir := T -> T*(T+1);;
SeniorityCasimir := v -> v*(v+1);;
Stiffness := C -> -C;;
Imme := function(a,b,c,Tz) return a + b*Tz + c*Tz*Tz; end;;
PairHamiltonian := function(k0,k1) return k0+k1; end;;
CasimirHamiltonian := function(alpha,beta,gamma,delta,m2,J,T,v)
  return alpha*MassCasimir(m2) + beta*SpinCasimir(J) + gamma*IsospinCasimir(T) + delta*SeniorityCasimir(v);
end;;
Generalized := function(alpha,beta,gamma,delta,a,b,c,k0,k1,spring,m2,J,T,v,Tz)
  return CasimirHamiltonian(alpha,beta,gamma,delta,m2,J,T,v) + Imme(a,b,c,Tz) + PairHamiltonian(k0,k1) + spring;
end;;

if IsospinCasimir(1) <> 2 then Error("T1 casimir"); fi;
if IsospinCasimir(1/2) <> 3/4 then Error("half casimir"); fi;
if Stiffness(MassCasimir(94)) <> 94 then Error("stiffness"); fi;
if Imme(11,3,5,7) - Imme(11,3,5,-7) <> 2*3*7 then Error("imme diff"); fi;
if Imme(11,3,5,7) + Imme(11,3,5,-7) <> 2*11 + 2*5*7*7 then Error("imme sum"); fi;
if Generalized(1,2,3,4,11,3,5,13,17,19,94,8,1,2,7) -
   Generalized(1,2,3,4,11,3,5,13,17,19,94,8,1,2,-7) <> 2*3*7 then Error("generalized diff"); fi;

Print(rec(
  C_T_T1 := 2,
  C_T_half := 3/4,
  massStiffness94 := 94,
  mirrorDifference := "2*b*t",
  pairChannels := 2,
  edges := 5
), "\n");
QUIT;
