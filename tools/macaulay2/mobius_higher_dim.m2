R = QQ[xa, aa, r]
F = frac R

xF = matrix {{1_F}, {0_F}}
aF = matrix {{0_F}, {1_F}}

dotA = v -> v_(0,0)*xa + v_(1,0)*aa
Dval = v -> dotA(v) - r
Nval = aa

Rop = v -> v - 2 * (Dval(v) / Nval) * aF

Rx = Rop(xF)
print "--- Reflection of x ---"
print Rx

Dx = Dval(xF)
DRx = Dval(Rx)

print "--- D values ---"
<< "D(x) = " << Dx << endl
<< "D(R(x)) = " << DRx << endl
<< "DRx == -Dx is " << (DRx == -Dx) << endl
assert(DRx == -Dx)

RRx = Rop(Rx)

print "--- Double Reflection ---"
<< "R(R(x)) = " << RRx << endl
<< "R(R(x)) == x is " << (RRx == xF) << endl
assert(RRx == xF)
