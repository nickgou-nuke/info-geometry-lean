-- Macaulay2 exact polynomial certificate for a generic O(5,5) reflection.

R = QQ[t,a_1..a_10,v_1..v_10];
aa = {a_1,a_2,a_3,a_4,a_5,a_6,a_7,a_8,a_9,a_10};
vv = {v_1,v_2,v_3,v_4,v_5,v_6,v_7,v_8,v_9,v_10};
sgn = {1,1,1,1,1,-1,-1,-1,-1,-1};

Qa = sum(10, i -> sgn#i * (aa#i)^2);
Qv = sum(10, i -> sgn#i * (vv#i)^2);
Bav = sum(10, i -> sgn#i * aa#i * vv#i);
polav = 2*Bav;
rr = apply(10, i -> vv#i - t*polav*aa#i);
Qr = sum(10, i -> sgn#i * (rr#i)^2);
Iunit = ideal(t*Qa - 1);

certificate = (Qr-Qv) % Iunit;
if certificate != 0 then error "generic reflection failed to preserve Q(5,5)";

print "pin55_reflection.m2: PASS";
print "generic reflection preserves the split quadratic form modulo t*Q(a)-1";
exit 0;
