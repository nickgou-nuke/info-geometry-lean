"""Derive exact Lean PC/Weyl matrices from the source coordinate formulas."""
import itertools
import sympy as sp

def xor(*xs):
    v = 0
    for x in xs: v ^= x
    return v
def mm(a, b): return (a*b).applyfunc(lambda x: int(x) % 2)

def pc(k, X):
    a,b,x0,x1,x2,y0,y1,y2 = X
    if k == 0: return (xor(a,x1),xor(b,x1),xor(x0,y2),x1,xor(x1,x2,y0),y0,xor(a,b,x1,y1,y2),y2)
    if k == 1: return (xor(a,y2),xor(b,y2),x0,xor(x0,x1),xor(a,b,x1,x2,y2),xor(x0,x1,y0,y1,y2),xor(x0,y1,y2),y2)
    if k == 2: return (xor(a,x0,y2),xor(b,x0,y2),x0,xor(x1,y2),xor(a,b,x1,x2,y1),xor(a,b,x0,x1,y0,y2),xor(x0,y1,y2),y2)
    if k == 3: return (a,b,x0,x1,xor(x1,x2),y0,xor(y1,y2),y2)
    if k == 4: return (xor(a,y2),xor(b,y2),x0,x1,xor(a,b,x1,x2,y2),xor(x1,y0),xor(x0,y1,y2),y2)
    return (a,b,x0,x1,xor(x0,x2),xor(y0,y2),y1,y2)

basis = [(1,0,0,0,0,0,0,0),(0,1,0,0,0,0,0,0),(0,0,1,0,0,0,0,0),(0,0,0,1,0,0,0,0),(0,0,0,0,1,0,0,0),(0,0,0,0,0,1,0,0),(0,0,0,0,0,0,1,0),(0,0,0,0,0,0,0,1)]
gens = [sp.Matrix([[pc(k,b)[i] for j,b in enumerate(basis)] for i in range(8)]) for k in range(6)]
s = sp.Matrix([[int(i == p) for p in [0,1,3,2,4,6,5,7]] for i in range(8)])
cycle = sp.Matrix([[int(i == p) for p in [0,1,3,4,2,6,7,5]] for i in range(8)])
cartan = sp.Matrix([[int(i == p) for p in [1,0,5,6,7,2,3,4]] for i in range(8)])
c = cycle * cartan
t = s * c
def perm(p, X): return tuple(X[i] for i in p)
direct_t = sp.Matrix([[int(i == j) for j in range(8)] for i in range(8)])
direct_perm = [1,0,5,6,7,2,3,4]
def apply_t(X): return tuple(perm([0,1,3,4,2,6,7,5], perm(direct_perm, perm([0,1,3,2,4,6,5,7], X))))
direct_t = sp.Matrix([[apply_t(b)[i] for b in basis] for i in range(8)])
print("T_MATRIX_MATCH_c_times_s", direct_t == t)
print("T_MATRIX_MATCH_s_times_c", direct_t == s*c)
print("T_MATRIX_MATCH_cT_times_sT", direct_t == c.T*s.T)
print("EXACT_LEAN_MATRIX_CAS=PASS")
for name,w in (("s",s),("t",t)):
  print(name)
  for k,g in enumerate(gens):
    target = mm(mm(w.inv(), g), w)
    hits=[]
    for bits in itertools.product((0,1), repeat=6):
      q=sp.eye(8)
      for i,bit in enumerate(bits):
        if bit: q=mm(gens[i], q)
      if q==target: hits.append(bits)
    print(k, hits)
print("s0_target", mm(mm(s,gens[0]),s))
print("word_001011", mm(mm(gens[5],gens[4]),gens[2]))
