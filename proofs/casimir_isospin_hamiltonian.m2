R = QQ[m2,J,T,v,Tz,alpha,beta,gamma,delta,a,b,c,k0,k1,spring,t]

massCasimir = x -> -x
spinCasimir = x -> x*(x+1)
isospinCasimir = x -> x*(x+1)
seniorityCasimir = x -> x*(x+1)
stiffness = C -> -C
imme = (a0,b0,c0,tz) -> a0 + b0*tz + c0*tz^2
pairHamiltonian = (k0v,k1v) -> k0v + k1v
casimirHamiltonian = (alpha0,beta0,gamma0,delta0,m20,J0,T0,v0) ->
  alpha0*massCasimir(m20) + beta0*spinCasimir(J0) + gamma0*isospinCasimir(T0) + delta0*seniorityCasimir(v0)
generalized = (alpha0,beta0,gamma0,delta0,a0,b0,c0,k0v,k1v,spring0,m20,J0,T0,v0,tz) ->
  casimirHamiltonian(alpha0,beta0,gamma0,delta0,m20,J0,T0,v0) + imme(a0,b0,c0,tz) + pairHamiltonian(k0v,k1v) + spring0

assert(isospinCasimir(1) == 2)
assert(isospinCasimir(1/2) == 3/4)
assert(stiffness(massCasimir(m2)) == m2)
assert(imme(a,b,c,t) - imme(a,b,c,-t) == 2*b*t)
assert(imme(a,b,c,t) + imme(a,b,c,-t) == 2*a + 2*c*t^2)
assert(generalized(alpha,beta,gamma,delta,a,b,c,k0,k1,spring,m2,J,T,v,t) -
  generalized(alpha,beta,gamma,delta,a,b,c,k0,k1,spring,m2,J,T,v,-t) == 2*b*t)

D = QQ[q,dq, WeylAlgebra => {q=>dq}]
casimirDmodule = ideal(q*dq - dq*q - 1)
assert(numgens casimirDmodule == 1)

print {
  "C_T_T1", 2,
  "C_T_half", 3/4,
  "massStiffness94", 94,
  "mirrorDifference", "2*b*t",
  "pairChannels", 2,
  "dmoduleGenerators", numgens casimirDmodule,
  "edges", 5
}
