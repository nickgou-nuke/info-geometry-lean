-- Macaulay2 verification of Zorn projectors and sandwich formulas
OP1 = matrix(QQ, {{1, 0}, {0, 0}})
OP2 = matrix(QQ, {{0, 0}, {0, 1}})
I = id_(QQ^2)

assert(OP1 * OP1 == OP1)
assert(OP2 * OP2 == OP2)
assert(OP1 * OP2 == 0)

T = OP1 - OP2
assert(T^3 == T)

-- Reconstruct
assert((T^2 + T)/2 == OP1)
assert((T^2 - T)/2 == OP2)
assert(I - T^2 == 0)

-- Sandwich
R = QQ[a, b, x, y]
X = matrix {{a, x}, {y, b}}
OP1R = substitute(OP1, R)
OP2R = substitute(OP2, R)
S12 = OP1R * X * OP2R
S21 = OP2R * X * OP1R

-- Element-by-element check
assert(S12_(0,0) == 0)
assert(S12_(0,1) == x)
assert(S12_(1,0) == 0)
assert(S12_(1,1) == 0)

assert(S21_(0,0) == 0)
assert(S21_(0,1) == 0)
assert(S21_(1,0) == y)
assert(S21_(1,1) == 0)

print "Macaulay2: Zorn projector and sandwich verification successful."
exit 0
