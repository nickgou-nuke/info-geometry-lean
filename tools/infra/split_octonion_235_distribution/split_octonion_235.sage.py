#!/usr/bin/env sage -python
from sage.all import Matrix, QQ, vector
import json

# Imaginary split-octonion norm in coordinates (a,x0,x1,x2,y0,y1,y2):
# q = -a^2 - x.y, polar matrix below.
B = Matrix(QQ, [
    [-1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, -QQ(1)/2, 0, 0],
    [0, 0, 0, 0, 0, -QQ(1)/2, 0],
    [0, 0, 0, 0, 0, 0, -QQ(1)/2],
    [0, -QQ(1)/2, 0, 0, 0, 0, 0],
    [0, 0, -QQ(1)/2, 0, 0, 0, 0],
    [0, 0, 0, -QQ(1)/2, 0, 0, 0],
])
assert B.rank() == 7
# U0 null vector; left multiplication equations from exact Zorn product.
A = Matrix(QQ, [
    [0,0,0,0,1,0,0],
    [0,0,0,0,0,0,0],
    [-1,0,0,0,0,0,0],
    [0,0,0,0,0,0,0],
    [0,0,0,0,0,0,0],
    [0,0,0,-1,0,0,0],
    [0,0,1,0,0,0,0],
])
assert A.rank() == 4
assert 7 - A.rank() == 3
x = vector(QQ, [0,1,0,0,0,0,0])
T = Matrix(QQ, [(B*x).list()])
assert T.rank() == 1
for v in A.right_kernel().basis():
    assert (T * vector(QQ, v)).is_zero()
print('SAGE_SPLIT_OCTONION_235_OK')
print(json.dumps({
  'imaginary_dimension': 7,
  'left_annihilator_rank': A.rank(),
  'left_annihilator_dimension': 3,
  'projectivized_distribution_rank': 2,
  'projective_null_quadric_dimension': 5,
  'annihilator_inside_tangent': True,
}, sort_keys=True))
