-- tools/macaulay2/inverse_limit_resolution.m2

R = QQ[x, y]
I = ideal(x, y)

n = 3
Rn = R/(I^n)
Mn = coker vars Rn
Fn = res(Mn, LengthLimit=>4)

nMinus1 = n - 1
RnMinus1 = R/(I^nMinus1)

MnMinus1 = coker vars RnMinus1
FnMinus1 = res(MnMinus1, LengthLimit=>4)

phi = map(RnMinus1, Rn)
FnMapped = phi Fn

chMap = extend(FnMinus1, FnMapped, matrix{{1_RnMinus1}})

print "======================================================"
print "Resolution over R/I^n (Fn):"
print Fn
print "------------------------------------------------------"
print "Resolution over R/I^{n-1} (FnMinus1):"
print FnMinus1
print "------------------------------------------------------"
print "Mapped resolution (phi Fn):"
print FnMapped
print "------------------------------------------------------"
print "Chain map components (FnMapped -> FnMinus1):"
for i from 0 to 4 do (
    if FnMapped_i != 0 and FnMinus1_i != 0 then (
        print(concatenate("Degree ", toString(i), " map:"));
        print(chMap_i);
    )
)
print "======================================================"
