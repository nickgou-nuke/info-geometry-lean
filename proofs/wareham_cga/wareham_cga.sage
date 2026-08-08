import sympy as sp
x1,x2,x3,y1,y2,y3,l=sp.symbols('x1 x2 x3 y1 y2 y3 l')
G=sp.Matrix([[1,0,0,0,0],[0,1,0,0,0],[0,0,1,0,0],[0,0,0,0,-2],[0,0,0,-2,0]])
def dot(u,v): return sp.expand((u.T*G*v)[0])
def F(x,y,z):
    q=x*x+y*y+z*z
    return sp.Matrix([x,y,z,sp.Rational(1,2)*q,sp.Rational(1,2)])
X=F(x1,x2,x3); Y=F(y1,y2,y3)
assert sp.simplify(dot(X,X))==0
assert sp.simplify(dot(X,Y)+sp.Rational(1,2)*((x1-y1)**2+(x2-y2)**2+(x3-y3)**2))==0
assert sp.simplify(dot(F(l*x1,l*x2,l*x3),F(l*x1,l*x2,l*x3)))==0
print('OK')
