import sympy as sp
Q=sp.Rational

y= -Q(12,125)
sy= Q(37,1000)
yr=-Q(51,500)
syr=Q(41,1000)
obs=Q(90); sobs=Q(35); weighted=Q(72); sweighted=Q(26); pred=Q(190)
b11=Q(4,5); b3k=Q(19,100); b3o=Q(1,100); b3=b3k+b3o
A11=-Q(2,3); A13=Q(1,3)
weighted_A=b11*A11+b3*A13

def interval(c,s): return (c-s,c+s)
def significance(a,s): return abs(a)/s

def rel(o,p): return o/p
def deficit(o,p): return 1-o/p

assert y == -Q(12,125) and sy == Q(37,1000)
assert yr == -Q(51,500) and syr == Q(41,1000)
assert significance(y,sy) == Q(96,37)
assert significance(yr,syr) == Q(102,41)
assert interval(obs,sobs) == (55,125)
assert interval(weighted,sweighted) == (46,98)
assert rel(obs,pred) == Q(9,19)
assert rel(weighted,pred) == Q(36,95)
assert deficit(obs,pred) == Q(10,19)
assert deficit(weighted,pred) == Q(59,95)
assert b11+b3k+b3o == 1
assert b3 == Q(1,5)
assert weighted_A == -Q(7,15)
assert abs(weighted_A - (-Q(467,1000))) == Q(1,3000)
edges=['decays_to','measures','implies','compares_with','motivates']
print({'y_weighted': y, 'sigma_y': sy, 'y_recoil': yr, 'sigma_recoil': syr, 'coulomb_observed_interval_keV': interval(obs,sobs), 'coulomb_weighted_interval_keV': interval(weighted,sweighted), 'observed_to_predicted': rel(obs,pred), 'weighted_to_predicted': rel(weighted,pred), 'weighted_GT_asymmetry': weighted_A, 'edges': len(edges)})
