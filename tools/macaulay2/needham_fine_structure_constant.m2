R = QQ[pi,e,lp,p];
S = R/ideal(p^2 - p - 1);
phi = substitute(p, S);
expr = 10*pi*e*phi - lp;
print "MACAULAY2 NEEDHAM PACKET";
print concatenate("phi_quadratic_remainder = ", toString(phi^2 - phi - 1));
print concatenate("formal_expression = ", toString(expr));
