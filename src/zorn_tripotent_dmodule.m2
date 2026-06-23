-- Finite tripotent packet with Dmodules loaded.
loadPackage "Dmodules";

R = QQ[t];
T = matrix {{1_R, 0_R, 0_R}, {0_R, -1_R, 0_R}, {0_R, 0_R, 0_R}};
tripResidual = T*T*T - T;
tripResidualZero = (tripResidual == 0);
charPoly = det((t * id_(R^3)) - T);

print "ZORN_TRIPOTENT_DMODULE_PACKET";
print ("tripotentResidualZero=" | toString(tripResidualZero));
print ("characteristicPolynomial=" | toString(charPoly));
print ("scope=finite tripotent matrix only; Dmodules loaded, no global classification claim");
exit 0;
