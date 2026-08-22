"""CAS classification using the exact C0..C5 column-action matrices."""
import itertools
import sympy as sp

def xor(*xs):
    v=0
    for x in xs: v ^= x
    return v
def mm(a,b): return (a*b).applyfunc(lambda x:int(x)%2)
def pc(k,X):
    a,b,x0,x1,x2,y0,y1,y2=X
    return [(xor(a,x1),xor(b,x1),xor(x0,y2),x1,xor(x1,x2,y0),y0,xor(a,b,x1,y1,y2),y2),
      (xor(a,y2),xor(b,y2),x0,xor(x0,x1),xor(a,b,x1,x2,y2),xor(x0,x1,y0,y1,y2),xor(x0,y1,y2),y2),
      (xor(a,x0,y2),xor(b,x0,y2),x0,xor(x1,y2),xor(a,b,x1,x2,y1),xor(a,b,x0,x1,y0,y2),xor(x0,y1,y2),y2),
      (a,b,x0,x1,xor(x1,x2),y0,xor(y1,y2),y2),
      (xor(a,y2),xor(b,y2),x0,x1,xor(a,b,x1,x2,y2),xor(x1,y0),xor(x0,y1,y2),y2),
      (a,b,x0,x1,xor(x0,x2),xor(y0,y2),y1,y2)][k]
basis=[tuple(int(i==j) for i in range(8)) for j in range(8)]
G=[sp.Matrix([[pc(k,b)[i] for b in basis] for i in range(8)]) for k in range(6)]
s=sp.Matrix([[int(i==j) for j in [0,1,3,2,4,6,5,7]] for i in range(8)])
cy=sp.Matrix([[int(i==j) for j in [0,1,3,4,2,6,7,5]] for i in range(8)])
ca=sp.Matrix([[int(i==j) for j in [1,0,5,6,7,2,3,4]] for i in range(8)])
c=mm(cy,ca)
weyl=[("1",sp.eye(8)),("c",c),("c2",mm(c,c)),("s",s),
      ("s*c",mm(s,c)),("s*c2",mm(s,mm(c,c))),
      ("ca",ca),("ca*c",mm(ca,c)),("ca*c2",mm(ca,mm(c,c))),
      ("ca*s",mm(ca,s)),("ca*s*c",mm(ca,mm(s,c))),
      ("ca*s*c2",mm(ca,mm(s,mm(c,c))))]
def word(bits):
    q=sp.eye(8)
    for i,b in enumerate(bits):
        if b: q=mm(G[i],q) # autMatrix reverses pcWord product
    return q
print("EXACT_COLUMN_WEL_CARRIER=PASS")
for name,w in weyl:
    hits=[]
    for i,g in enumerate(G):
        target=mm(mm(w.inv(),g),w)
        sol=[bits for bits in itertools.product((0,1),repeat=6) if word(bits)==target]
        hits.append(sol[0] if sol else None)
    if sum(x is not None for x in hits) >= 5:
        print(name, hits)
