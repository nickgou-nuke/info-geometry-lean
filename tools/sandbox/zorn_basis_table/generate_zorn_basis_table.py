#!/usr/bin/env python3
"""Generate full 8x8 Zorn basis multiplication checks for several engines."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASIS = ["E11","E22","U1","U2","U3","V1","V2","V3"]


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
    else: raise ValueError(name)
    return tuple(d[k] for k in ['r','s','x1','x2','x3','y1','y2','y3'])

def neg(c): return tuple(-x for x in c)
ZERO = (0,0,0,0,0,0,0,0)
CELLS = {b: cell(b) for b in BASIS}
CELL_TO_EXPR = {ZERO: '0'}
for b,c in CELLS.items():
    CELL_TO_EXPR[c] = b
    CELL_TO_EXPR[neg(c)] = '-' + b

def mul(X,Y):
    r,s,x1,x2,x3,y1,y2,y3 = X
    R,S,u1,u2,u3,v1,v2,v3 = Y
    return (
        r*R + x1*v1 + x2*v2 + x3*v3,
        y1*u1 + y2*u2 + y3*u3 + s*S,
        r*u1 + S*x1 - (y2*v3 - y3*v2),
        r*u2 + S*x2 - (y3*v1 - y1*v3),
        r*u3 + S*x3 - (y1*v2 - y2*v1),
        R*y1 + s*v1 + (x2*u3 - x3*u2),
        R*y2 + s*v2 + (x3*u1 - x1*u3),
        R*y3 + s*v3 + (x1*u2 - x2*u1),
    )

TABLE = [[CELL_TO_EXPR[mul(CELLS[a], CELLS[b])] for b in BASIS] for a in BASIS]

def emit_markdown():
    lines = ["# Zorn 8-basis multiplication table", "", "Rows multiply columns.", "", "| · | " + " | ".join(BASIS) + " |", "|---|" + "---|"*len(BASIS)]
    for b,row in zip(BASIS,TABLE):
        lines.append("| " + b + " | " + " | ".join(row) + " |")
    (ROOT/'ZORN_BASIS_TABLE.md').write_text("\n".join(lines)+"\n")

def emit_python():
    (ROOT/'zorn_basis_table_sympy.py').write_text(r'''#!/usr/bin/env python3
import sympy as sp
BASIS = ["E11","E22","U1","U2","U3","V1","V2","V3"]
EXPECTED = ''' + repr(TABLE) + r'''
def cell(name):
    d = dict.fromkeys(['r','s','x1','x2','x3','y1','y2','y3'], sp.Integer(0))
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
print('SYMPY_ZORN_BASIS_TABLE_OK entries=64')
''')

def emit_sage():
    (ROOT/'zorn_basis_table.sage.py').write_text((ROOT/'zorn_basis_table_sympy.py').read_text().replace('SYMPY_', 'SAGE_').replace('import sympy as sp\n','').replace('sp.Integer(0)','0'))

def emit_gap():
    rows = []
    for row in TABLE:
        rows.append('["'+'","'.join(row)+'"]')
    expected = '['+','.join(rows)+']'
    (ROOT/'zorn_basis_table.g').write_text(f'''BNames := ["E11","E22","U1","U2","U3","V1","V2","V3"];;
Expected := {expected};;
BCell := function(name)
  if name="E11" then return [1,0,0,0,0,0,0,0]; fi;
  if name="E22" then return [0,1,0,0,0,0,0,0]; fi;
  if name="U1" then return [0,0,1,0,0,0,0,0]; fi;
  if name="U2" then return [0,0,0,1,0,0,0,0]; fi;
  if name="U3" then return [0,0,0,0,1,0,0,0]; fi;
  if name="V1" then return [0,0,0,0,0,1,0,0]; fi;
  if name="V2" then return [0,0,0,0,0,0,1,0]; fi;
  if name="V3" then return [0,0,0,0,0,0,0,1]; fi;
end;;
BNeg := c -> List(c, x -> -x);;
BExpr := function(c)
  local i;
  if c=[0,0,0,0,0,0,0,0] then return "0"; fi;
  for i in [1..Length(BNames)] do
    if c=BCell(BNames[i]) then return BNames[i]; fi;
    if c=BNeg(BCell(BNames[i])) then return Concatenation("-",BNames[i]); fi;
  od;
  Error("unknown cell");
end;;
BMul := function(X,Y)
  local r,s,x1,x2,x3,y1,y2,y3,R,S,u1,u2,u3,v1,v2,v3;
  r:=X[1]; s:=X[2]; x1:=X[3]; x2:=X[4]; x3:=X[5]; y1:=X[6]; y2:=X[7]; y3:=X[8];
  R:=Y[1]; S:=Y[2]; u1:=Y[3]; u2:=Y[4]; u3:=Y[5]; v1:=Y[6]; v2:=Y[7]; v3:=Y[8];
  return [r*R+x1*v1+x2*v2+x3*v3, y1*u1+y2*u2+y3*u3+s*S,
    r*u1+S*x1-(y2*v3-y3*v2), r*u2+S*x2-(y3*v1-y1*v3), r*u3+S*x3-(y1*v2-y2*v1),
    R*y1+s*v1+(x2*u3-x3*u2), R*y2+s*v2+(x3*u1-x1*u3), R*y3+s*v3+(x1*u2-x2*u1)];
end;;
for i in [1..8] do for j in [1..8] do
  if BExpr(BMul(BCell(BNames[i]),BCell(BNames[j]))) <> Expected[i][j] then Error("table mismatch"); fi;
od; od;
Print("GAP_ZORN_BASIS_TABLE_OK entries=64\\n");
QUIT;
''')

def emit_singular():
    def tuple_for_expr(expr):
        if expr == '0':
            return ZERO
        if expr.startswith('-'):
            return neg(CELLS[expr[1:]])
        return CELLS[expr]
    checks=[]
    for i,a in enumerate(BASIS):
        for j,b in enumerate(BASIS):
            exp = ','.join(str(x) for x in tuple_for_expr(TABLE[i][j]))
            checks.append(f'if (eqv(mul(cell("{a}"),cell("{b}")), intvec({exp})) == 0) {{ ERROR("mismatch {a} {b}"); }}')
    singular_prelude = """proc cell(string name) {
  if (name==\"E11\") { return(intvec(1,0,0,0,0,0,0,0)); }
  if (name==\"E22\") { return(intvec(0,1,0,0,0,0,0,0)); }
  if (name==\"U1\") { return(intvec(0,0,1,0,0,0,0,0)); }
  if (name==\"U2\") { return(intvec(0,0,0,1,0,0,0,0)); }
  if (name==\"U3\") { return(intvec(0,0,0,0,1,0,0,0)); }
  if (name==\"V1\") { return(intvec(0,0,0,0,0,1,0,0)); }
  if (name==\"V2\") { return(intvec(0,0,0,0,0,0,1,0)); }
  if (name==\"V3\") { return(intvec(0,0,0,0,0,0,0,1)); }
}
proc eqv(intvec X, intvec Y) { int k; for (k=1;k<=8;k++) { if (X[k]!=Y[k]) { return(0); } } return(1); }
proc mul(intvec X, intvec Y) {
  int r=X[1]; int s=X[2]; int x1=X[3]; int x2=X[4]; int x3=X[5]; int y1=X[6]; int y2=X[7]; int y3=X[8];
  int R=Y[1]; int S=Y[2]; int u1=Y[3]; int u2=Y[4]; int u3=Y[5]; int v1=Y[6]; int v2=Y[7]; int v3=Y[8];
  return(intvec(r*R+x1*v1+x2*v2+x3*v3, y1*u1+y2*u2+y3*u3+s*S,
    r*u1+S*x1-(y2*v3-y3*v2), r*u2+S*x2-(y3*v1-y1*v3), r*u3+S*x3-(y1*v2-y2*v1),
    R*y1+s*v1+(x2*u3-x3*u2), R*y2+s*v2+(x3*u1-x1*u3), R*y3+s*v3+(x1*u2-x2*u1)));
}
"""
    (ROOT/'zorn_basis_table.sing').write_text(
        singular_prelude + '\n'.join(checks) + '\n"SINGULAR_ZORN_BASIS_TABLE_OK entries=64";\n')
def emit_m2():
    rows = '{' + ','.join('{' + ','.join('"'+x+'"' for x in row) + '}' for row in TABLE) + '}'
    (ROOT/'zorn_basis_table.m2').write_text(f'''bnames={{"E11","E22","U1","U2","U3","V1","V2","V3"}};
expected={rows};
cell=name -> if name=="E11" then {{1,0,0,0,0,0,0,0}} else if name=="E22" then {{0,1,0,0,0,0,0,0}} else if name=="U1" then {{0,0,1,0,0,0,0,0}} else if name=="U2" then {{0,0,0,1,0,0,0,0}} else if name=="U3" then {{0,0,0,0,1,0,0,0}} else if name=="V1" then {{0,0,0,0,0,1,0,0}} else if name=="V2" then {{0,0,0,0,0,0,1,0}} else {{0,0,0,0,0,0,0,1}};
neg=X -> apply(X, x -> -x);
expr=X -> (if X=={{0,0,0,0,0,0,0,0}} then "0" else (for b in bnames do (if X==cell b then return b; if X==neg cell b then return concatenate("-",b)); error "unknown cell"));
mul=(X,Y) -> (r:=X#0; s:=X#1; x1:=X#2; x2:=X#3; x3:=X#4; y1:=X#5; y2:=X#6; y3:=X#7; R:=Y#0; S:=Y#1; u1:=Y#2; u2:=Y#3; u3:=Y#4; v1:=Y#5; v2:=Y#6; v3:=Y#7; {{r*R+x1*v1+x2*v2+x3*v3, y1*u1+y2*u2+y3*u3+s*S, r*u1+S*x1-(y2*v3-y3*v2), r*u2+S*x2-(y3*v1-y1*v3), r*u3+S*x3-(y1*v2-y2*v1), R*y1+s*v1+(x2*u3-x3*u2), R*y2+s*v2+(x3*u1-x1*u3), R*y3+s*v3+(x1*u2-x2*u1)}});
for i from 0 to 7 do for j from 0 to 7 do if expr(mul(cell(bnames#i),cell(bnames#j))) != (expected#i)#j then error "table mismatch";
print "MACAULAY2_ZORN_BASIS_TABLE_OK entries=64";
''')

def emit_coq():
    lemmas=[]
    for i,a in enumerate(BASIS):
        for j,b in enumerate(BASIS):
            name=f'T_{a}_{b}'.replace('-','neg')
            rhs=TABLE[i][j]
            if rhs=='0': r='Z0'
            elif rhs.startswith('-'): r=f'negZ {rhs[1:]}'
            else: r=rhs
            lemmas.append(f'Lemma {name} : mulZ {a} {b} = {r}. Proof. zc. Qed.')
    (ROOT/'coq').mkdir(exist_ok=True)
    (ROOT/'coq'/'ZornBasisTable.v').write_text(r'''From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.
Module ZornBasisTableMod.
Record Cell := mk { r:Z; s:Z; x1:Z; x2:Z; x3:Z; y1:Z; y2:Z; y3:Z }.
Definition mulZ X Y := mk
 (r X*r Y + x1 X*y1 Y + x2 X*y2 Y + x3 X*y3 Y)
 (y1 X*x1 Y + y2 X*x2 Y + y3 X*x3 Y + s X*s Y)
 (r X*x1 Y + s Y*x1 X - (y2 X*y3 Y - y3 X*y2 Y))
 (r X*x2 Y + s Y*x2 X - (y3 X*y1 Y - y1 X*y3 Y))
 (r X*x3 Y + s Y*x3 X - (y1 X*y2 Y - y2 X*y1 Y))
 (r Y*y1 X + s X*y1 Y + (x2 X*x3 Y - x3 X*x2 Y))
 (r Y*y2 X + s X*y2 Y + (x3 X*x1 Y - x1 X*x3 Y))
 (r Y*y3 X + s X*y3 Y + (x1 X*x2 Y - x2 X*x1 Y)).
Definition negZ X := mk (-r X) (-s X) (-x1 X) (-x2 X) (-x3 X) (-y1 X) (-y2 X) (-y3 X).
Definition Z0:=mk 0 0 0 0 0 0 0 0. Definition E11:=mk 1 0 0 0 0 0 0 0. Definition E22:=mk 0 1 0 0 0 0 0 0.
Definition U1:=mk 0 0 1 0 0 0 0 0. Definition U2:=mk 0 0 0 1 0 0 0 0. Definition U3:=mk 0 0 0 0 1 0 0 0.
Definition V1:=mk 0 0 0 0 0 1 0 0. Definition V2:=mk 0 0 0 0 0 0 1 0. Definition V3:=mk 0 0 0 0 0 0 0 1.
Ltac zc := vm_compute; reflexivity.
''' + '\n'.join(lemmas) + '\nEnd ZornBasisTableMod.\n')

def emit_isabelle():
    lemmas=[]
    defs='mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def'
    for i,a in enumerate(BASIS):
        for j,b in enumerate(BASIS):
            rhs=TABLE[i][j]
            if rhs=='0': r='Z0'
            elif rhs.startswith('-'): r=f'negZ {rhs[1:]}'
            else: r=rhs
            lemmas.append(f'lemma T_{a}_{b}: "mulZ {a} {b} = {r}" by (simp add: {defs})')
    (ROOT/'isabelle').mkdir(exist_ok=True)
    (ROOT/'isabelle'/'ZornBasisTable.thy').write_text(r'''theory ZornBasisTable imports Main begin
record cell = r :: int s :: int x1 :: int x2 :: int x3 :: int y1 :: int y2 :: int y3 :: int
definition mulZ :: "cell => cell => cell" where
"mulZ X Y = (|
  r = r X*r Y + x1 X*y1 Y + x2 X*y2 Y + x3 X*y3 Y,
  s = y1 X*x1 Y + y2 X*x2 Y + y3 X*x3 Y + s X*s Y,
  x1 = r X*x1 Y + s Y*x1 X - (y2 X*y3 Y - y3 X*y2 Y),
  x2 = r X*x2 Y + s Y*x2 X - (y3 X*y1 Y - y1 X*y3 Y),
  x3 = r X*x3 Y + s Y*x3 X - (y1 X*y2 Y - y2 X*y1 Y),
  y1 = r Y*y1 X + s X*y1 Y + (x2 X*x3 Y - x3 X*x2 Y),
  y2 = r Y*y2 X + s X*y2 Y + (x3 X*x1 Y - x1 X*x3 Y),
  y3 = r Y*y3 X + s X*y3 Y + (x1 X*x2 Y - x2 X*x1 Y) |)"
definition negZ :: "cell => cell" where "negZ X = (|r=-r X,s=-s X,x1=-x1 X,x2=-x2 X,x3=-x3 X,y1=-y1 X,y2=-y2 X,y3=-y3 X|)"
definition Z0 :: cell where "Z0=(|r=0,s=0,x1=0,x2=0,x3=0,y1=0,y2=0,y3=0|)"
definition E11 :: cell where "E11=(|r=1,s=0,x1=0,x2=0,x3=0,y1=0,y2=0,y3=0|)"
definition E22 :: cell where "E22=(|r=0,s=1,x1=0,x2=0,x3=0,y1=0,y2=0,y3=0|)"
definition U1 :: cell where "U1=(|r=0,s=0,x1=1,x2=0,x3=0,y1=0,y2=0,y3=0|)"
definition U2 :: cell where "U2=(|r=0,s=0,x1=0,x2=1,x3=0,y1=0,y2=0,y3=0|)"
definition U3 :: cell where "U3=(|r=0,s=0,x1=0,x2=0,x3=1,y1=0,y2=0,y3=0|)"
definition V1 :: cell where "V1=(|r=0,s=0,x1=0,x2=0,x3=0,y1=1,y2=0,y3=0|)"
definition V2 :: cell where "V2=(|r=0,s=0,x1=0,x2=0,x3=0,y1=0,y2=1,y3=0|)"
definition V3 :: cell where "V3=(|r=0,s=0,x1=0,x2=0,x3=0,y1=0,y2=0,y3=1|)"
''' + '\n'.join(lemmas) + '\nend\n')
    (ROOT/'isabelle'/'ROOT').write_text('session ZornBasisTable = HOL +\n  theories ZornBasisTable\n')

def emit_runner():
    (ROOT/'verify_zorn_basis_table.sh').write_text(r'''#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 generate_zorn_basis_table.py >/dev/null
(cd ../../.. && lake env lean lean_sandbox/ZornBasisTableSandbox.lean)
python3 zorn_basis_table_sympy.py
/home/goutev/miniforge3/envs/sage/bin/sage zorn_basis_table.sage.py
/home/goutev/miniforge3/envs/sage/bin/gap -q zorn_basis_table.g
/home/goutev/miniforge3/envs/sage/bin/Singular -q zorn_basis_table.sing
M2 --script zorn_basis_table.m2
/home/goutev/.opam/rocq-9.2/bin/coqc coq/ZornBasisTable.v
/usr/local/bin/isabelle build -D isabelle
printf 'ZORN_BASIS_TABLE_MULTIENGINE_OK entries=64 engines=lean,sympy,sage,gap,singular,macaulay2,coq,isabelle\n'
''')
    (ROOT/'verify_zorn_basis_table.sh').chmod(0o755)

if __name__ == '__main__':
    emit_markdown(); emit_python(); emit_sage(); emit_gap(); emit_singular(); emit_m2(); emit_coq(); emit_isabelle(); emit_runner()
    print('GENERATED_ZORN_BASIS_TABLE entries=64')
