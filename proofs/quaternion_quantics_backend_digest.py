#!/usr/bin/env python3
"""External finite-shape audit for QuaternionQuanticsBackendDigest.lean.

This does not validate QuatIca or trainsum numerics.  It checks the finite
bookkeeping deferred_interface into Lean: quaternion real storage, complex doubling,
quantics dimensions, and a simple uniform tensor-train storage formula.
"""


def quaternion_matrix_real_storage(m: int, n: int) -> int:
    return 4 * m * n


def complex_adjoint_entries(m: int, n: int) -> int:
    return (2 * m) * (2 * n)


def quantics_full_dimension(base: int, digits: int) -> int:
    return base**digits


def uniform_tt_storage(cores: int, phys: int, rank: int) -> int:
    if cores == 0:
        return 0
    if cores == 1:
        return phys
    return 2 * phys * rank + (cores - 2) * phys * rank * rank

quat_features = [
    "quaternionHermitianAdjoint",
    "quaternionMatrixMultiply",
    "realOrComplexExpansion",
    "svdPseudoinverse",
    "newtonSchulzPseudoinverse",
    "qgmres",
    "quaternionTensorUnfoldFold",
    "qslstImageRestoration",
    "quaternionSDPBarrier",
]

trainsum_features = [
    "tensorTrain",
    "quanticsDimension",
    "einsum",
    "qft",
    "wavelet",
    "svdQrTruncation",
    "linearSolver",
    "eigenSolver",
    "crossInterpolation",
    "backendNumpyTorchCupy",
]

for m, n in [(1, 1), (2, 3), (5, 7)]:
    lhs = complex_adjoint_entries(m, n)
    rhs = quaternion_matrix_real_storage(m, n)
    print(f"complex adjoint entries ({m},{n}) = {lhs}; real storage = {rhs}")
    assert lhs == rhs

print("QuatIca feature count =", len(quat_features))
print("trainsum feature count =", len(trainsum_features))
print("binary quantics dimension, 10 digits =", quantics_full_dimension(2, 10))
print("uniform TT storage, 4 cores, phys=2, rank=2 =", uniform_tt_storage(4, 2, 2))
print("full binary tensor storage, 4 cores =", quantics_full_dimension(2, 4))

assert len(quat_features) == 9
assert len(trainsum_features) == 10
assert quantics_full_dimension(2, 10) == 1024
assert uniform_tt_storage(4, 2, 2) == 24
assert quantics_full_dimension(2, 4) == 16
print("Quaternion/quantics backend digest audit passed")
