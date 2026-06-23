# Sage witness for split Zorn null-boundary identities.
R = PolynomialRing(QQ, 'r,s,x1,x2,x3,y1,y2,y3,R,S,u1,u2,u3,v1,v2,v3')
r,s,x1,x2,x3,y1,y2,y3,Rr,S,u1,u2,u3,v1,v2,v3 = R.gens()

def detZ(Z):
    r,s,x1,x2,x3,y1,y2,y3 = Z
    return r*s - (x1*y1 + x2*y2 + x3*y3)

def mulZ(X,Y):
    r,s,x1,x2,x3,y1,y2,y3 = X
    Rr,S,u1,u2,u3,v1,v2,v3 = Y
    return (
        r*Rr + (x1*v1 + x2*v2 + x3*v3),
        (y1*u1 + y2*u2 + y3*u3) + s*S,
        r*u1 + S*x1 - (y2*v3 - y3*v2),
        r*u2 + S*x2 - (y3*v1 - y1*v3),
        r*u3 + S*x3 - (y1*v2 - y2*v1),
        Rr*y1 + s*v1 + (x2*u3 - x3*u2),
        Rr*y2 + s*v2 + (x3*u1 - x1*u3),
        Rr*y3 + s*v3 + (x1*u2 - x2*u1))

X=(r,s,x1,x2,x3,y1,y2,y3); Y=(Rr,S,u1,u2,u3,v1,v2,v3)
assert detZ(mulZ(X,Y)) - detZ(X)*detZ(Y) == 0
n=(0,0,1,0,0,0,0,0); z=(0,0,0,0,0,0,0,0)
assert detZ(n) == 0 and n != z and mulZ(n,n) == z
print('split_zorn_null_boundary.sage: checks passed')
