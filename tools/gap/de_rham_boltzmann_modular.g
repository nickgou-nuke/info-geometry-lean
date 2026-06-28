# GAP finite shadow for the bridge at concrete parameters.
# We verify the scalar model Q(beta) = 2 cosh(beta r) and d/dβ log Q = r tanh(beta r)
# at a rationally specified floating point sample.

a := 1.0;;
b := 2.0;;
beta := 0.5;;
r := Sqrt(a^2 + b^2);;
Q := 2.0 * (Exp(beta * r) + Exp(-beta * r)) / 2.0;;
dlogQ := r * (Exp(beta * r) - Exp(-beta * r)) / (Exp(beta * r) + Exp(-beta * r));;
minusKexpect := dlogQ;;
Print("GAP bridge finite shadow\n");
Print("r = ", r, "\n");
Print("Q = ", Q, "\n");
Print("dlogQ = ", dlogQ, "\n");
Print("-<K> = ", minusKexpect, "\n");
if dlogQ - minusKexpect < 1.0e-10 and minusKexpect - dlogQ < 1.0e-10 then
  Print("PASS: d/dβ log Q = -<K> in the concrete GAP shadow\n");
else
  Error("bridge check failed");
fi;
QUIT_GAP(0);
