#!/usr/bin/env sage
import sys
import itertools
from sage.all import *

print("=" * 80)
print("Gogberashvili Split-Octonion Basis Verification")
print("=" * 80)

# Define Zorn matrix class
class ZornMatrix:
    def __init__(self, a, b, x, y):
        self.a = QQ(a)
        self.b = QQ(b)
        self.x = vector(QQ, x)
        self.y = vector(QQ, y)
        
    def __add__(self, other):
        return ZornMatrix(self.a + other.a, self.b + other.b, self.x + other.x, self.y + other.y)
        
    def __sub__(self, other):
        return ZornMatrix(self.a - other.a, self.b - other.b, self.x - other.x, self.y - other.y)
        
    def __neg__(self):
        return ZornMatrix(-self.a, -self.b, -self.x, -self.y)
        
    def smul(self, c):
        return ZornMatrix(self.a * c, self.b * c, self.x * c, self.y * c)
        
    def __mul__(self, other):
        # dot product helper
        def dot(u, v):
            return u[0]*v[0] + u[1]*v[1] + u[2]*v[2]
        # cross product helper
        def cross(u, v):
            return vector(QQ, [
                u[1]*v[2] - u[2]*v[1],
                u[2]*v[0] - u[0]*v[2],
                u[0]*v[1] - u[1]*v[0]
            ])
        return ZornMatrix(
            self.a * other.a + dot(self.x, other.y),
            self.b * other.b + dot(self.y, other.x),
            self.a * other.x + other.b * self.x - cross(self.y, other.y),
            self.b * other.y + other.a * self.y + cross(self.x, other.x)
        )
        
    def to_vector(self):
        return vector(QQ, [self.a, self.b, self.x[0], self.x[1], self.x[2], self.y[0], self.y[1], self.y[2]])
        
    @staticmethod
    def from_vector(v):
        return ZornMatrix(v[0], v[1], [v[2], v[3], v[4]], [v[5], v[6], v[7]])
        
    def __eq__(self, other):
        return (self.a == other.a and 
                self.b == other.b and 
                self.x == other.x and 
                self.y == other.y)
                
    def __str__(self):
        return f"Zorn(a={self.a}, b={self.b}, x={list(self.x)}, y={list(self.y)})"

# Define basis elements
oneZ = ZornMatrix(1, 1, [0,0,0], [0,0,0])
I = ZornMatrix(1, -1, [0,0,0], [0,0,0])
J = [
    ZornMatrix(0, 0, [1,0,0], [1,0,0]),
    ZornMatrix(0, 0, [0,1,0], [0,1,0]),
    ZornMatrix(0, 0, [0,0,1], [0,0,1])
]
j = [
    ZornMatrix(0, 0, [1,0,0], [-1,0,0]),
    ZornMatrix(0, 0, [0,1,0], [0,-1,0]),
    ZornMatrix(0, 0, [0,0,1], [0,0,-1])
]

basis_elements = [oneZ, J[0], J[1], J[2], j[0], j[1], j[2], I]
basis_names = ["1", "J0", "J1", "J2", "j0", "j1", "j2", "I"]

print("\n1. Verifying Gogberashvili multiplication table using Zorn matrices:")

# Levi-Civita
def eps3(i, k, r):
    val_tuple = (i, k, r)
    if val_tuple in [(0,1,2), (1,2,0), (2,0,1)]:
        return 1
    elif val_tuple in [(1,0,2), (0,2,1), (2,1,0)]:
        return -1
    return 0

# Check relations
all_ok = True

for n in range(3):
    # J_n^2 = 1
    if J[n] * J[n] != oneZ:
        print(f"FAIL: J{n}^2")
        all_ok = False
    # j_n^2 = -1
    if j[n] * j[n] != -oneZ:
        print(f"FAIL: j{n}^2")
        all_ok = False
        
# I^2 = 1
if I * I != oneZ:
    print("FAIL: I^2")
    all_ok = False

# Cross relations
for n in range(3):
    for m in range(3):
        if n != m:
            # J_n * J_m = -eps3(n,m,k) j_k
            sum_jk = ZornMatrix(0, 0, [0,0,0], [0,0,0])
            for k in range(3):
                sum_jk = sum_jk + j[k].smul(eps3(n, m, k))
            if J[n] * J[m] != -sum_jk:
                print(f"FAIL: J{n} * J{m}")
                all_ok = False
                
            # j_n * j_m = -eps3(n,m,k) j_k
            if j[n] * j[m] != -sum_jk:
                print(f"FAIL: j{n} * j{m}")
                all_ok = False
                
            # j_m * J_n = -eps3(n,m,k) J_k
            sum_Jk = ZornMatrix(0, 0, [0,0,0], [0,0,0])
            for k in range(3):
                sum_Jk = sum_Jk + J[k].smul(eps3(n, m, k))
            if j[m] * J[n] != -sum_Jk:
                print(f"FAIL: j{m} * J{n}")
                all_ok = False

# Mixed relations with I
for n in range(3):
    if J[n] * I != -j[n]:
        print(f"FAIL: J{n} * I")
        all_ok = False
    if I * J[n] != j[n]:
        print(f"FAIL: I * J{n}")
        all_ok = False
    if j[n] * I != -J[n]:
        print(f"FAIL: j{n} * I")
        all_ok = False
    if I * j[n] != J[n]:
        print(f"FAIL: I * j{n}")
        all_ok = False

if all_ok:
    print("✓ All Gogberashvili multiplication table equations hold exactly in the Zorn representation!")
else:
    print("FAIL: Some relations did not hold.")
    sys.exit(1)

print("\n2. Finding the algebra isomorphism to abstract split-octonions:")

# Standard split octonions algebra in Sage
O = OctonionAlgebra(QQ, -1, -1, 1)
O_basis = list(O.basis())

# We want to find a linear map M: O -> Zorn such that M(x * y) = M(x) * M(y)
zorn_basis_vectors = [e.to_vector() for e in basis_elements]
zorn_to_vec = Matrix(QQ, zorn_basis_vectors).transpose()

# Find the structure constants of Gogberashvili basis
table = []
for i in range(8):
    row_table = []
    for j_idx in range(8):
        prod = basis_elements[i] * basis_elements[j_idx]
        coords = zorn_to_vec.solve_right(prod.to_vector())
        row_table.append(coords)
    table.append(row_table)

imaginary_basis = basis_elements[1:]
imaginary_names = basis_names[1:]

found_iso = False
# Use Python ints for itertools
for p, q, r in itertools.permutations(range(int(7)), int(3)):
    u1 = imaginary_basis[p]
    u2 = imaginary_basis[q]
    u4 = imaginary_basis[r]
    
    if u1*u1 != -oneZ or u2*u2 != -oneZ or u4*u4 != oneZ:
        continue
        
    for s1, s2, s3 in itertools.product([-1, 1], repeat=3):
        img_e1 = u1.smul(s1)
        img_e2 = u2.smul(s2)
        img_e4 = u4.smul(s3)
        
        # Now compute all other images according to Sage's convention:
        img_e3 = -(img_e1 * img_e2)
        img_e5 = -(img_e1 * img_e4)
        img_e6 = -(img_e2 * img_e4)
        img_e7 = -(img_e3 * img_e4)
        
        # Check if the images are mutually independent
        img_basis = [oneZ, img_e1, img_e2, img_e3, img_e4, img_e5, img_e6, img_e7]
        img_vectors = [e.to_vector() for e in img_basis]
        if Matrix(QQ, img_vectors).rank() == 8:
            # Verify all products
            is_hom = True
            for i in range(8):
                for k in range(8):
                    # Abstract product
                    o_prod = O_basis[i] * O_basis[k]
                    # Map of product
                    img_o_prod = ZornMatrix(0, 0, [0,0,0], [0,0,0])
                    for idx in range(8):
                        img_o_prod = img_o_prod + img_basis[idx].smul(o_prod.coefficient(idx))
                    # Product of images
                    prod_img = img_basis[i] * img_basis[k]
                    if img_o_prod != prod_img:
                        is_hom = False
                        break
                if not is_hom:
                    break
            if is_hom:
                print(f"✓ Found exact algebra isomorphism from standard Sage Cayley-Dickson basis to Zorn basis:")
                for idx in range(8):
                    g_name = "unknown"
                    for g_idx, g_elem in enumerate(basis_elements):
                        if img_basis[idx] == g_elem:
                            g_name = basis_names[g_idx]
                            break
                        elif img_basis[idx] == -g_elem:
                            g_name = f"-{basis_names[g_idx]}"
                            break
                    print(f"  e{idx}  |--->  {g_name}")
                found_iso = True
                break
    if found_iso:
        break

if not found_iso:
    print("Could not find direct permutation isomorphism.")
    
print("=" * 80)
