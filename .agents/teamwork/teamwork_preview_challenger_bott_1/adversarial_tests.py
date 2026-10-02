
import numpy as np

def test_uniqueness_and_adversarial_scales():
    print("\n=== Additional Adversarial Stress Tests ===")
    
    # 1. Uniqueness of decomposition: Kernel of M
    M = np.array([
        [1, 0,  0,  1],
        [0, 1,  1,  0],
        [0, 1, -1,  0],
        [1, 0,  0, -1]
    ], dtype=np.float64)
    u, s, vh = np.linalg.svd(M)
    print("Singular values of change-of-basis matrix:", s)
    assert np.all(s > 1.0), "Singular values must be bounded away from 0"
    cond = s[0] / s[-1]
    print(f"Condition number of basis matrix: {cond:.4f}")
    assert abs(cond - 1.0) < 1e-12, f"Condition number expected 1.0 (orthogonal up to scale), got {cond}"
    print("[PASS] Basis matrix is a scaled orthogonal matrix (cond = 1.0). Representation is strictly unique!")

    # 2. Extreme dynamic ranges (1e-150 to 1e150)
    for exp in [-150, -100, -50, 0, 50, 100, 150]:
        scale = 10.0 ** exp
        A = np.array([[1.5, -2.5], [3.5, 4.5]]) * scale
        a = (A[0, 0] + A[1, 1]) / 2.0
        b = (A[0, 1] + A[1, 0]) / 2.0
        c = (A[0, 1] - A[1, 0]) / 2.0
        d = (A[0, 0] - A[1, 1]) / 2.0

        I2 = np.array([[1.0, 0.0], [0.0, 1.0]])
        s1 = np.array([[0.0, 1.0], [1.0, 0.0]])
        eps = np.array([[0.0, 1.0], [-1.0, 0.0]])
        s3 = np.array([[1.0, 0.0], [0.0, -1.0]])

        A_rec = a * I2 + b * s1 + c * eps + d * s3
        rel_diff = np.max(np.abs(A - A_rec)) / scale
        assert rel_diff < 1e-15, f"Failed at exp {exp}: rel_diff = {rel_diff}"
    print("[PASS] Scale invariance verified from 1e-150 to 1e150 with rel_diff < 1e-15.")

test_uniqueness_and_adversarial_scales()
