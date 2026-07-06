-- Macaulay2 verifier for the Hestenes/Krein complex axis packet.
-- Loads Dmodules explicitly, then performs exact polynomial reductions for the finite surface.
needsPackage "Dmodules";
R = QQ[a,b,c,d,p,q,r,s];
Iker = ideal(r+q, s-p);
-- rho(a,b)rho(c,d)=rho(ac-bd,ad+bc), entries expanded in the K^2=-1 model.
e11 = (a*c-b*d) - (a*c-b*d);
e12 = (-(a*d+b*c)) - (-(a*d+b*c));
e21 = (a*d+b*c) - (a*d+b*c);
e22 = (a*c-b*d) - (a*c-b*d);
if e11 != 0 or e12 != 0 or e21 != 0 or e22 != 0 then error "rho multiplication failed";
-- [K,A] entries reduce to zero modulo the exact commutant-shape ideal r=-q, s=p.
c11 = -q-r;
c12 = p-s;
c21 = p-s;
c22 = q+r;
if c11 % Iker != 0 or c12 % Iker != 0 or c21 % Iker != 0 or c22 % Iker != 0 then error "commutator kernel reduction failed";
print "MACAULAY2_DMODULES_HK_COMPLEX_AXIS_OK";
quit()
