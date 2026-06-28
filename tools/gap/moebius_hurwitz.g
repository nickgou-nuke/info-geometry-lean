# GAP Formalization: Möbius Transformations with Hurwitz Quaternions
# Eigenvalue Analysis and Group Actions

# =============================================================================
# 1. Hurwitz Quaternion Algebra in GAP
# =============================================================================

HurwitzQuaternion := function(a, b, c, d)
    return [a, b, c, d];
end;

# Quaternion addition
AddQuat := function(q1, q2)
    return [q1[1]+q2[1], q1[2]+q2[2], q1[3]+q2[3], q1[4]+q2[4]];
end;

# Quaternion multiplication
MulQuat := function(q1, q2)
    local a1, b1, c1, d1, a2, b2, c2, d2;
    a1 := q1[1]; b1 := q1[2]; c1 := q1[3]; d1 := q1[4];
    a2 := q2[1]; b2 := q2[2]; c2 := q2[3]; d2 := q2[4];
    return [
        a1*a2 - b1*b2 - c1*c2 - d1*d2,
        a1*b2 + b1*a2 + c1*d2 - d1*c2,
        a1*c2 - b1*d2 + c1*a2 + d1*b2,
        a1*d2 + b1*c2 - c1*b2 + d1*a2
    ];
end;

# Quaternion conjugate
ConjQuat := function(q)
    return [q[1], -q[2], -q[3], -q[4]];
end;

# Quaternion norm
NormQuat := function(q)
    return q[1]^2 + q[2]^2 + q[3]^2 + q[4]^2;
end;

# Quaternion inverse
InvQuat := function(q)
    local n, c;
    n := NormQuat(q);
    if n = 0 then
        Error("Zero quaternion has no inverse");
    fi;
    c := ConjQuat(q);
    return [c[1]/n, c[2]/n, c[3]/n, c[4]/n];
end;

# Check if Hurwitz (all components in Z or all in Z+1/2)
IsHurwitz := function(q)
    local v, ip;
    v := [q[1], q[2], q[3], q[4]];
    ip := List(v, x -> x - Int(x));
    return (ForAll(ip, x -> x = 0)) or (ForAll(ip, x -> x = 1/2));
end;

# =============================================================================
# 2. Möbius Transformation with Hurwitz Coefficients
# =============================================================================

MobiusTransform := function(a, b, c, d)
    local M;
    M := rec(
        a := a,
        b := b,
        c := c,
        d := d,
        trace := a[1]+d[1],
        det := MulQuat(a, d) - MulQuat(b, c)
    );
    return M;
end;

# Apply Möbius transformation to quaternion
ApplyMobius := function(M, z)
    local num, den, den_inv;
    num := AddQuat(MulQuat(M.a, z), M.b);
    den := AddQuat(MulQuat(M.c, z), M.d);
    if NormQuat(den) = 0 then
        return "infinity";
    fi;
    den_inv := InvQuat(den);
    return MulQuat(num, den_inv);
end;

# =============================================================================
# 3. Matrix Representation and Eigenvalue Analysis
# =============================================================================

# Embed quaternion into 4x4 real matrix
QuatToMatrix := function(q)
    return [
        [q[1], -q[2], -q[3], -q[4]],
        [q[2],  q[1], -q[4],  q[3]],
        [q[3],  q[4],  q[1], -q[2]],
        [q[4], -q[3],  q[2],  q[1]]
    ];
end;

# Möbius transformation as 8x8 real matrix
MobiusToMatrix := function(M)
    local A, B, C, D;
    A := QuatToMatrix(M.a);
    B := QuatToMatrix(M.b);
    C := QuatToMatrix(M.c);
    D := QuatToMatrix(M.d);
    return BlockMatrix([
        [1, 1, A], [1, 2, B],
        [2, 1, C], [2, 2, D]
    ]);
end;

# Eigenvalue analysis of Möbius transformation
MobiusEigenvalues := function(M)
    local mat, eig;
    mat := MobiusToMatrix(M);
    eig := Eigenvalues(mat);
    return eig;
end;

# Classification of Möbius transformation
ClassifyMobius := function(M)
    local tr, tr_sq, disc, real_disc;
    tr := M.trace;
    tr_sq := tr * tr;
    disc := tr_sq - 4;
    
    real_disc := disc[1];
    
    if real_disc < 0 then
        return "elliptic";
    elif real_disc = 0 then
        return "parabolic";
    elif real_disc > 0 then
        return "hyperbolic";
    else
        return "loxodromic";
    fi;
end;

# =============================================================================
# 4. Dual Möbius Transformation
# =============================================================================

DualMobius := function(M)
    return MobiusTransform(
        ConjQuat(M.d),
        [-M.b[1], -M.b[2], -M.b[3], -M.b[4]],
        [-M.c[1], -M.c[2], -M.c[3], -M.c[4]],
        ConjQuat(M.a)
    );
end;

# Verify duality relation
VerifyDuality := function(M)
    local M_dual, comp;
    M_dual := DualMobius(M);
    comp := MulQuat(M.a, M_dual.a) + MulQuat(M.b, M_dual.c);
    Print("Duality check (should be identity): ", comp, "\n");
end;

# =============================================================================
# 5. Fixed Points and Stable Directions
# =============================================================================

FixedPointsMobius := function(M)
    local c, a_minus_d, b, coeffs, eigs;
    c := M.c;
    a_minus_d := [M.a[1]-M.d[1], M.a[2]-M.d[2], M.a[3]-M.d[3], M.a[4]-M.d[4]];
    b := M.b;
    
    # Fixed points satisfy c z^2 + (d-a)z - b = 0
    # Use companion matrix method
    # For z in HP^1, we solve c z^2 + (d-a)z - b = 0
    # Embed into 8x8 real matrix for eigenvalue analysis
    
    return "Implementation needed: solve c z^2 + (d-a)z - b = 0";
end;

# =============================================================================
# 6. Stable Geometric Objects (Fixed Points, Invariant Circles)
# =============================================================================

InvariantCircles := function(M)
    # Find circles in HP^1 preserved by M
    # These correspond to eigenspaces of the 8x8 matrix representation
    return "Implementation needed";
end;

# =============================================================================
# 7. Hurwitz Integer Lattice
# =============================================================================

HurwitzLattice := function()
    local basis;
    basis := [
        [1, 0, 0, 0],   # 1
        [0, 1, 0, 0],   # i
        [0, 0, 1, 0],   # j
        [0, 0, 0, 1],   # k
        [1/2, 1/2, 1/2, 1/2]  # (1+i+j+k)/2
    ];
    return basis;
end;

# =============================================================================
# 5. Binary Tetrahedral Group
# =============================================================================

BinaryTetrahedralGroup := function()
    local elements;
    elements := [
        [1, 0, 0, 0], [-1, 0, 0, 0],
        [0, 1, 0, 0], [0, -1, 0, 0],
        [0, 0, 1, 0], [0, 0, -1, 0],
        [0, 0, 0, 1], [0, 0, 0, -1],
        [1/2, 1/2, 1/2, 1/2], [1/2, 1/2, 1/2, -1/2],
        [1/2, 1/2, -1/2, 1/2], [1/2, 1/2, -1/2, -1/2],
        [1/2, -1/2, 1/2, 1/2], [1/2, -1/2, 1/2, -1/2],
        [1/2, -1/2, -1/2, 1/2], [1/2, -1/2, -1/2, -1/2],
        [-1/2, 1/2, 1/2, 1/2], [-1/2, 1/2, 1/2, -1/2],
        [-1/2, 1/2, -1/2, 1/2], [-1/2, 1/2, -1/2, -1/2],
        [-1/2, -1/2, 1/2, 1/2], [-1/2, -1/2, 1/2, -1/2],
        [-1/2, -1/2, -1/2, 1/2], [-1/2, -1/2, -1/2, -1/2]
    ];
    return elements;
end;

# =============================================================================
# 10. Binary Octahedral and Icosahedral Groups
# =============================================================================

BinaryOctahedralGroup := function()
    local elements, tetra;
    tetra := BinaryTetrahedralGroup();
    elements := Concatenation(tetra, List(tetra, q -> MulQuat(q, [1/2, 1/2, 1/2, 1/2])));
    return elements;
end;

BinaryIcosahedralGroup := function()
    # 120 elements related to E8 root system
    return [];
end;

# =============================================================================
# Test Suite
# =============================================================================

# Test basic quaternion operations
q1 := [1, 1, 1, 1];
q2 := [1, -1, 0, 0];
Print("q1 = ", q1, "\n");
Print("q2 = ", q2, "\n");
Print("q1 * q2 = ", MulQuat(q1, q2), "\n");
Print("norm(q1) = ", NormQuat(q1), "\n");

# Test Möbius transformation
a := [1, 0, 0, 0];
b := [1, 0, 0, 0];
c := [0, 0, 0, 0];
d := [1, 0, 0, 0];

M := MobiusTransform(a, b, c, d);
z := [0, 1, 0, 0];
Print("M(z) = ", ApplyMobius(M, z), "\n");
Print("M trace = ", M.trace, "\n");

Print("GAP formalization loaded successfully!\n");