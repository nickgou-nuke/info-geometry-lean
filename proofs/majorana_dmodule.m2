-- Construct the coordinate ring for the isotropic boundary modes
R = QQ[v_1..v_10]
Q = v_1^2 + v_2^2 + v_3^2 + v_4^2 + v_5^2 - v_6^2 - v_7^2 - v_8^2 - v_9^2 - v_10^2
QuotientRing = R / ideal(Q)

-- Define differential operators evaluating to zero on the null cone
loadPackage "Dmodules"
W = QQ[v_1..v_10, d_1..d_10, WeylAlgebra => {v_1=>d_1, v_2=>d_2, v_3=>d_3, v_4=>d_4, v_5=>d_5, v_6=>d_6, v_7=>d_7, v_8=>d_8, v_9=>d_9, v_10=>d_10}]

-- Laplacian for the split metric
Lap = d_1^2 + d_2^2 + d_3^2 + d_4^2 + d_5^2 - d_6^2 - d_7^2 - d_8^2 - d_9^2 - d_10^2
print(Lap)
