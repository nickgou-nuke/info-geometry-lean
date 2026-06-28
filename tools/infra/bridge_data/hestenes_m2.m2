-- Macaulay2: Hestenes Spacetime Algebra
-- Verifies Clifford algebra structure

R = QQ[i]/(i^2+1)

-- Spacetime metric (signature +---)
g = matrix{{1,0,0,0},{0,-1,0,0},{0,0,-1,0},{0,0,0,-1}}

-- Gamma matrices (simplified representation)
gamma0 = matrix{{1,0,0,0},{0,1,0,0},{0,0,-1,0},{0,0,0,-1}}
gamma1 = matrix{{0,0,0,1},{0,0,1,0},{0,-1,0,0},{-1,0,0,0}}
gamma2 = matrix{{0,0,0,-i},{0,0,i,0},{0,i,0,0},{-i,0,0,0}}
gamma3 = matrix{{0,0,1,0},{0,0,0,-1},{-1,0,0,0},{0,1,0,0}}

-- Verify anticommutation
print "=== Anticommutation Relations ==="
for mu from 0 to 3 do (
  for nu from 0 to 3 do (
    gMus := if mu==0 then gamma0 else if mu==1 then gamma1 else if mu==2 then gamma2 else gamma3;
    gNus := if nu==0 then gamma0 else if nu==1 then gamma1 else if nu==2 then gamma2 else gamma3;
    anticomm = gMus * gNus + gNus * gMus;
    expected = 2 * g_(mu,nu) * identity(4_R);
    if anticomm == expected then
      print("✓ g_"|mu|" g_"|nu|" + g_"|nu|" g_"|mu|" = 2g_"|mu|nu|"|)
    else
      print("FAIL: mu="|mu|", nu="|nu|"|)
  )
)

-- Verify squares
print "\n=== Gamma Squares ==="
print("gamma0^2 = " | toString(gamma0*gamma0))
print("gamma1^2 = " | toString(gamma1*gamma1))
print("gamma2^2 = " | toString(gamma2*gamma2))
print("gamma3^2 = " | toString(gamma3*gamma3))

-- Pseudoscalar
print "\n=== Pseudoscalar ==="
I_sta = gamma0 * gamma1 * gamma2 * gamma3
I_sq = I_sta * I_sta
print("I = g0g1g2g3")
print("I^2 = " | toString(I_sq))
print("I^2 == -1? " | toString(I_sq == -identity(4_R)))

-- Spin bivector
print "\n=== Spin Bivector ==="
sigma3 = gamma3 * gamma0
sigma3_sq = sigma3 * sigma3
print("sigma3 = g3g0")
print("sigma3^2 = " | toString(sigma3_sq))

-- Bivector basis
print "\n=== Bivector Basis ==="
bivectors = {}
for mu from 0 to 3 do (
  for nu from mu+1 to 3 do (
    gMus := if mu==0 then gamma0 else if mu==1 then gamma1 else if mu==2 then gamma2 else gamma3;
    gNus := if nu==0 then gamma0 else if nu==1 then gamma1 else if nu==2 then gamma2 else gamma3;
    biv = (gMus * gNus - gNus * gMus) / 2;
    bivectors = append(bivectors, biv);
    print("g_"|mu|"^g_"|nu|" trace=" | toString(trace(biv)))
  )
)

print("\nTotal bivectors: " | toString(#bivectors))
print "\n✓ Macaulay2 verification complete"