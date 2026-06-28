#!/usr/bin/env python3
"""
Debug Zorn matrix multiplication for Furey operators
"""
import sympy as sp
from dataclasses import dataclass
from typing import Tuple

@dataclass(frozen=True)
class ZornMatrix:
    a: sp.Expr
    b: sp.Expr
    x: Tuple[sp.Expr, sp.Expr, sp.Expr]
    y: Tuple[sp.Expr, sp.Expr, sp.Expr]

    def __add__(self, other):
        return ZornMatrix(
            self.a + other.a, self.b + other.b,
            tuple(self.x[i] + other.x[i] for i in range(3)),
            tuple(self.y[i] + other.y[i] for i in range(3)),
        )

    def __sub__(self, other):
        return ZornMatrix(
            self.a - other.a, self.b - other.b,
            tuple(self.x[i] - other.x[i] for i in range(3)),
            tuple(self.y[i] - other.y[i] for i in range(3)),
        )

    def scalar_mul(self, s):
        return ZornMatrix(
            s * self.a, s * self.b,
            tuple(s * self.x[i] for i in range(3)),
            tuple(s * self.y[i] for i in range(3)),
        )

    def half(self):
        return self.scalar_mul(sp.Rational(1, 2))

    @staticmethod
    def dot(v, w):
        return v[0]*w[0] + v[1]*w[1] + v[2]*w[2]

    @staticmethod
    def cross(v, w):
        return (
            v[1]*w[2] - v[2]*w[1],
            v[2]*w[0] - v[0]*w[2],
            v[0]*w[1] - v[1]*w[0],
        )

    def __mul__(self, other):
        a = self.a * other.a + ZornMatrix.dot(self.x, other.y)
        b = self.b * other.b + ZornMatrix.dot(self.y, other.x)
        x = tuple(
            self.a * other.x[i] + other.b * self.x[i]
            - ZornMatrix.cross(self.y, other.y)[i]
            for i in range(3)
        )
        y = tuple(
            self.b * other.y[i] + other.a * self.y[i]
            + ZornMatrix.cross(self.x, other.x)[i]
            for i in range(3)
        )
        return ZornMatrix(a, b, x, y)

    def __eq__(self, other):
        if not isinstance(other, ZornMatrix):
            return False
        return (sp.simplify(self.a - other.a) == 0 and
                sp.simplify(self.b - other.b) == 0 and
                all(sp.simplify(self.x[i] - other.x[i]) == 0 for i in range(3)) and
                all(sp.simplify(self.y[i] - other.y[i]) == 0 for i in range(3)))

    def __repr__(self):
        return f"[{self.a} {self.x}; {self.y} {self.b}]"


oneZ = ZornMatrix(1, 1, (0,0,0), (0,0,0))
zeroZ = ZornMatrix(0, 0, (0,0,0), (0,0,0))
ePlus = ZornMatrix(1, 0, (0,0,0), (0,0,0))
eMinus = ZornMatrix(0, 1, (0,0,0), (0,0,0))

up0 = ZornMatrix(0, 0, (1,0,0), (0,0,0))
down0 = ZornMatrix(0, 0, (0,0,0), (1,0,0))
J = ZornMatrix(0, 0, (1,0,0), (-1,0,0))

print("J =", J)
print("J*J =", J*J)
print("up0*up0 =", up0*up0)
print("down0*down0 =", down0*down0)
print("up0*down0 =", up0*down0)
print("down0*up0 =", down0*up0)
print("J*up0 =", J*up0)
print("up0*J =", up0*J)

# Try x = J
x = J
alpha = (x + J*x).half()
alpha_dag = (x - J*x).half()
print("\nWith x = J:")
print("alpha =", alpha)
print("alpha_dag =", alpha_dag)
print("alpha^2 =", alpha*alpha)
print("alpha_dag^2 =", alpha_dag*alpha_dag)
print("{alpha, alpha_dag} =", alpha*alpha_dag + alpha_dag*alpha)

# Try x = up0
x = up0
alpha = (x + J*x).half()
alpha_dag = (x - J*x).half()
print("\nWith x = up0:")
print("alpha =", alpha)
print("alpha_dag =", alpha_dag)
print("alpha^2 =", alpha*alpha)
print("alpha_dag^2 =", alpha_dag*alpha_dag)
print("{alpha, alpha_dag} =", alpha*alpha_dag + alpha_dag*alpha)

# Try x = down0
x = down0
alpha = (x + J*x).half()
alpha_dag = (x - J*x).half()
print("\nWith x = down0:")
print("alpha =", alpha)
print("alpha_dag =", alpha_dag)
print("alpha^2 =", alpha*alpha)
print("alpha_dag^2 =", alpha_dag*alpha_dag)
print("{alpha, alpha_dag} =", alpha*alpha_dag + alpha_dag*alpha)

# Try x = up0 + down0
x = up0 + down0
alpha = (x + J*x).half()
alpha_dag = (x - J*x).half()
print("\nWith x = up0 + down0:")
print("alpha =", alpha)
print("alpha_dag =", alpha_dag)
print("alpha^2 =", alpha*alpha)
print("alpha_dag^2 =", alpha_dag*alpha_dag)
print("{alpha, alpha_dag} =", alpha*alpha_dag + alpha_dag*alpha)

# What if J is different?
# J = up0 + down0?
J2 = up0 + down0
print("\nJ2 = up0 + down0 =", J2)
print("J2^2 =", J2*J2)

# J = ePlus - eMinus?
J3 = ePlus - eMinus
print("\nJ3 = ePlus - eMinus =", J3)
print("J3^2 =", J3*J3)

# What about the Hestenes bivector? e12 = [0 -1; 1 0]
# In Zorn matrices, this might be something else...
# Let's check what element has J^2 = -1 and J*x gives nice results for x=up0

# We want J*up0 = something nice
# J = {a,b,x,y}, up0 = {0,0,[1,0,0],0}
# J*up0: a = a*0 + dot(x,0) = 0
#        b = b*0 + dot(y,[1,0,0]) = y[0]
#        x = a*[1,0,0] + 0*x - cross(y,0) = [a,0,0]
#        y = b*0 + 0*y + cross(x,[1,0,0]) = cross(x,[1,0,0])
# We want J*up0 = ePlus = {1,0,0,0}
# So: 0=1? Impossible.
# What if we want J*up0 = eMinus = {0,1,0,0}?
# So: 0=0, y[0]=1, [a,0,0]=0 => a=0, cross(x,[1,0,0])=0
# cross(x,[1,0,0]) = [0, x[2], -x[1]] = 0 => x[1]=0, x[2]=0
# So x = [x0, 0, 0], y = [1, y1, y2]
# Also J^2 = -1

# Let's try to find J such that J^2 = -1 and J*up0 = eMinus
# J = {0, 0, [x0,0,0], [1, y1, y2]}
# J^2: a = 0 + dot([x0,0,0], [1,y1,y2]) = x0
#      b = 0 + dot([1,y1,y2], [x0,0,0]) = x0
#      x = 0 - cross([1,y1,y2], [1,y1,y2]) = 0
#      y = 0 + cross([x0,0,0], [x0,0,0]) = 0
# So J^2 = {x0, x0, 0, 0}
# Want J^2 = -1 = {-1, -1, 0, 0} => x0 = -1
# So J = {0, 0, [-1,0,0], [1, y1, y2]}

# Try J = {0, 0, [-1,0,0], [1,0,0]} = -up0 + down0
J4 = ZornMatrix(0, 0, (-1,0,0), (1,0,0))
print("\nJ4 = -up0 + down0 =", J4)
print("J4^2 =", J4*J4)
print("J4*up0 =", J4*up0)
print("up0*J4 =", up0*J4)

x = up0
alpha = (x + J4*x).half()
alpha_dag = (x - J4*x).half()
print("\nWith J=J4, x=up0:")
print("alpha =", alpha)
print("alpha_dag =", alpha_dag)
print("alpha^2 =", alpha*alpha)
print("alpha_dag^2 =", alpha_dag*alpha_dag)
print("{alpha, alpha_dag} =", alpha*alpha_dag + alpha_dag*alpha)
