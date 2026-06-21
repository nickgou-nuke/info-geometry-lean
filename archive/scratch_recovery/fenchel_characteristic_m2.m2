W_gr = QQ[x, y, X, Y]
I_char = ideal(x*X - y*Y, x*y - 1, X*Y)
dim_char = dim(W_gr / I_char)
print(dim_char)
exit(0)