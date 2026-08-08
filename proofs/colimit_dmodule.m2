-- Macaulay2: Filtered colimits and pushout varieties

-- Base ring
Z = ZZ
-- Localization to Q
Q = QQ

-- Pushout to C
-- R[x]/(x^2 + 1)
R = QQ[x]
I = ideal(x^2 + 1)
C = R/I

print("Base Ring: ", Z)
print("Localized Ring: ", Q)
print("Complex Pushout: ", C)
