import InfoGeometry.Physics.ZornMatrixSU3.Vector3
import InfoGeometry.Physics.ZornMatrixSU3.ZornMatrixCore
import InfoGeometry.Physics.ZornMatrixSU3.ZornSU3Properties
import InfoGeometry.Physics.ZornMatrixSU3.Stabilizer

/-!
# InfoGeometry.Physics.ZornMatrixSU3

**Zorn Matrices, Split Octonions, and SU(3) Color Symmetry**

This file formalizes the Günaydin-Gürsey construction connecting:
1. Zorn's vector-matrix representation of octonions
2. Split octonions O_s with signature (4,4)
3. SU(3) as the stabilizer subgroup of G₂
4. Color triplet/antitriplet representations from off-diagonal vectors

## Mathematical Structure

A Zorn matrix has the form:
```
    [a   x⃗ ]
M = [       ]    where a,b ∈ ℝ, x⃗,y⃗ ∈ ℝ³
    [y⃗   b ]
```

Multiplication rule:
```
[a   x⃗ ] [a'  x⃗']   [aa' + x⃗·y⃗'    ax⃗' + a'x⃗ - y⃗×y⃗']
[y⃗   b ] [y⃗'  b'] = [ya' + b'y⃗ - x⃗×x⃗'    bb' + y⃗·x⃗'  ]
```

The split octonion norm is:
```
N(M) = ab - x⃗·y⃗
```

## Connection to Cl(1,1) and SU(3)

The diagonal projectors:
```
OP₁ = [1  0]    OP₂ = [0  0]
      [0  0]          [0  1]
```

Sandwiching isolates color modes:
```
OP₁ · M · OP₂ = [0  x⃗]    (color triplet 3)
                [0  0 ]

OP₂ · M · OP₁ = [0  0 ]    (color antitriplet 3̄)
                [y⃗ 0 ]
```

The G₂ automorphism group preserves this structure, with SU(3) ⊂ G₂
being the subgroup that fixes OP₁ and OP₂.

## Tripotent Eigenvalues and Anyonic Braiding

The grading operator χ from Cl(1,1) extends to the octonionic structure:
- Eigenvalue +1: quarks (fundamental 3)
- Eigenvalue -1: antiquarks (antifundamental 3̄)
- Eigenvalue 0: gluons/neutral operators\n-/
