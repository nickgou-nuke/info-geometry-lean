-- Define the Mellin transform evaluation equations as a system of algebraic ideals and compute their syzygies
R = QQ[x,y,z,w];
I = ideal(x*y - z, x^2 + y^2 - w^2, x*y*z - w);
C = res I;
print "Syzygies and Free Resolution of the Mellin transform evaluation ideal:"
print C
exit
