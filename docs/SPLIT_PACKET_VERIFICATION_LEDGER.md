# Split packet verification ledger

## Scope

This ledger concerns the new definitions in:

```text
lean/InfoGeometry/Algebra/Zorn/SplitCayleyZeroDivisors.lean
```

The direct model is the repository's eight-coordinate Zorn product over exact
rationals/reals:

```text
(r,s,x1,x2,x3,y1,y2,y3)
```

with

```text
J1 = U1 + V1
j1 = U1 - V1
I  = E22 - E11
```

and therefore

```text
D+ = (1+J1)/2 = (1/2,1/2,1/2,0,0,1/2,0,0)
D- = (1-J1)/2 = (1/2,1/2,-1/2,0,0,-1/2,0,0)
d+ = (1+I)/2   = (0,1,0,0,0,0,0,0)
d- = (1-I)/2   = (1,0,0,0,0,0,0,0)
G+ = U1
G- = V1
```

## Packet-specific direct checks

The script `/tmp/split_packet_sympy.py` constructs the Zorn product directly
and checks exact identities with `sympy.Rational` coefficients.

```text
SymPy packet audit: PASS
Sage packet audit:  PASS
```

Checked:

```text
D+² = D+
D-² = D-
d+² = d+
d-² = d-
D+D- = 0
d+d- = 0
G+² = 0
G-² = 0
N(D+) = N(D-) = N(d+) = N(d-) = N(G+) = N(G-) = 0
J1² = 1
j1² = -1
I² = 1
```

## Broader, not packet-specific, checks

The maintained real-split-G₂ wrapper passes its existing checks in Lean, SymPy,
Sage, GAP, Singular, Macaulay2, Macaulay2 Dmodules, Coq, and Isabelle. Those
checks concern the derivation ledger, norm signature, Killing form, Weyl data,
and root/D-module evidence. They do not import or execute the new packet file.

The generic Clifford multi-engine suite is a separate test surface and is not
an audit of these Zorn-cell identities.

Therefore the honest status is:

```text
new packet direct symbolic verification: SymPy + Sage PASS
new packet GAP/Singular/Macaulay2/Dmodule/Coq/Isabelle execution: not yet run
new packet Lean kernel verification: PASS
broader real-split-G₂ evidence: all maintained engines PASS
```
