R = QQ[L, invL];
I = ideal(L*invL - 1);
sigma = (L + invL)^2;
expr = sigma - 4 - (L - invL)^2;
rem = expr % I;
print(rem);
print(rem == 0);
exit 0;
