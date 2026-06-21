import sympy as sp

def cross_product(u, v):
    return [
        u[1]*v[2] - u[2]*v[1],
        u[2]*v[0] - u[0]*v[2],
        u[0]*v[1] - u[1]*v[0]
    ]

def dot_product(u, v):
    return sum(x*y for x, y in zip(u, v))

def add_vec(u, v):
    return [x + y for x, y in zip(u, v)]

def sub_vec(u, v):
    return [x - y for x, y in zip(u, v)]

def scale_vec(c, u):
    return [c * x for x in u]

class ZornMatrix:
    def __init__(self, a, b, u, v):
        self.a = sp.sympify(a)
        self.b = sp.sympify(b)
        self.u = [sp.sympify(x) for x in u]
        self.v = [sp.sympify(x) for x in v]

    def norm(self):
        return sp.simplify(self.a * self.b - dot_product(self.u, self.v))

    def __mul__(self, other):
        # A = [[a, u], [v, b]]
        # B = [[c, w], [x, d]]
        # A * B = [[a*c + u.x, a*w + d*u - v x x],
        #          [c*v + b*x + u x w, b*d + v.w]]
        
        ac = self.a * other.a
        ux = dot_product(self.u, other.v) # other.v is 'x'
        new_a = sp.simplify(ac + ux)
        
        bd = self.b * other.b
        vw = dot_product(self.v, other.u) # other.u is 'w'
        new_b = sp.simplify(bd + vw)
        
        aw = scale_vec(self.a, other.u)
        du = scale_vec(other.b, self.u)
        v_cross_x = cross_product(self.v, other.v)
        new_u = sub_vec(add_vec(aw, du), v_cross_x)
        new_u = [sp.simplify(k) for k in new_u]
        
        cv = scale_vec(other.a, self.v)
        bx = scale_vec(self.b, other.v)
        u_cross_w = cross_product(self.u, other.u)
        new_v = add_vec(add_vec(cv, bx), u_cross_w)
        new_v = [sp.simplify(k) for k in new_v]
        
        return ZornMatrix(new_a, new_b, new_u, new_v)

    def is_zero(self):
        return (self.a == 0 and self.b == 0 and 
                all(x == 0 for x in self.u) and 
                all(x == 0 for x in self.v))
                
    def __str__(self):
        return f"[ {self.a}, {self.u} ]\n[ {self.v}, {self.b} ]"

print("==================================================")
print("SPLIT OCTONION ZORN MATRIX ALGEBRA")
print("==================================================")

# Let's find two non-zero Zorn matrices A and B such that A * B = 0
# Let A have a=1, b=0, u=[1,0,0], v=[0,0,0]
# Then N(A) = 1*0 - 0 = 0
A = ZornMatrix(1, 0, [1, 0, 0], [0, 0, 0])

# We want A * B = 0.
# Let B have c=0, d=1, w=[-1,0,0], x=[0,0,0]
# N(B) = 0
B = ZornMatrix(0, 1, [-1, 0, 0], [0, 0, 0])

C = A * B

print("Matrix A:")
print(A)
print(f"Norm(A) = {A.norm()}\n")

print("Matrix B:")
print(B)
print(f"Norm(B) = {B.norm()}\n")

print("Product C = A * B:")
print(C)
print(f"Is C zero? {C.is_zero()}")
print("==================================================")
