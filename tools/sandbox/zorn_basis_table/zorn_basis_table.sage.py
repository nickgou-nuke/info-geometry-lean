#!/usr/bin/env python3
BASIS = ["E11","E22","U1","U2","U3","V1","V2","V3"]
EXPECTED = [['E11', '0', 'U1', 'U2', 'U3', '0', '0', '0'], ['0', 'E22', '0', '0', '0', 'V1', 'V2', 'V3'], ['0', 'U1', '0', 'V3', '-V2', 'E11', '0', '0'], ['0', 'U2', '-V3', '0', 'V1', '0', 'E11', '0'], ['0', 'U3', 'V2', '-V1', '0', '0', '0', 'E11'], ['V1', '0', 'E22', '0', '0', '0', '-U3', 'U2'], ['V2', '0', '0', 'E22', '0', 'U3', '0', '-U1'], ['V3', '0', '0', '0', 'E22', '-U2', 'U1', '0']]
def cell(name):
    d = dict.fromkeys(['r','s','x1','x2','x3','y1','y2','y3'], 0)
    if name == 'E11': d['r'] = 1
    elif name == 'E22': d['s'] = 1
    elif name == 'U1': d['x1'] = 1
    elif name == 'U2': d['x2'] = 1
    elif name == 'U3': d['x3'] = 1
    elif name == 'V1': d['y1'] = 1
    elif name == 'V2': d['y2'] = 1
    elif name == 'V3': d['y3'] = 1
    return tuple(d[k] for k in ['r','s','x1','x2','x3','y1','y2','y3'])
def neg(c): return tuple(-x for x in c)
ZERO=(0,0,0,0,0,0,0,0)
CELLS={b:cell(b) for b in BASIS}
CELL_TO_EXPR={ZERO:'0'}
for b,c in CELLS.items(): CELL_TO_EXPR[c]=b; CELL_TO_EXPR[neg(c)]='-'+b
def mul(X,Y):
    r,s,x1,x2,x3,y1,y2,y3=X; R,S,u1,u2,u3,v1,v2,v3=Y
    return (r*R+x1*v1+x2*v2+x3*v3, y1*u1+y2*u2+y3*u3+s*S,
            r*u1+S*x1-(y2*v3-y3*v2), r*u2+S*x2-(y3*v1-y1*v3), r*u3+S*x3-(y1*v2-y2*v1),
            R*y1+s*v1+(x2*u3-x3*u2), R*y2+s*v2+(x3*u1-x1*u3), R*y3+s*v3+(x1*u2-x2*u1))
for i,a in enumerate(BASIS):
  for j,b in enumerate(BASIS):
    got=CELL_TO_EXPR[mul(CELLS[a],CELLS[b])]
    assert got == EXPECTED[i][j], (a,b,got,EXPECTED[i][j])
print('SAGE_ZORN_BASIS_TABLE_OK entries=64')
