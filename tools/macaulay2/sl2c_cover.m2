R = QQ[a,b,c,d,L];
I_SL2 = ideal(a*d - b*c - 1);
I_map = ideal(a - L, b, c, d - L);
I_ker = I_SL2 + I_map;
J = eliminate({a,b,c,d}, I_ker);

expected = ideal(L^2 - 1);
if J == expected then print "SUCCESS: Kernel ideal is L^2 - 1" else (print "FAILED"; exit 1);
exit 0;
