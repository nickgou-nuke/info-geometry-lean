R = QQ[L, invL]
I = ideal(L * invL - 1)

sigma = (L + invL)^2
sigma2 = (L^2 + invL^2)^2

eqDiff = sigma2 - (sigma - 2)^2

rem = eqDiff % I

print("Expression eqDiff: " | toString(eqDiff))
print("Remainder modulo I: " | toString(rem))

if rem == 0 then (
    print("Success: sigma_2 - (sigma - 2)^2 evaluates rigorously to 0 over the ideal L*invL - 1");
    exit(0);
) else (
    print("Failure: result is not 0");
    exit(1);
)
