import numpy as np
import scipy.linalg
from clifford.g3 import *

def main():
    print("Simulating negative log of zeta-regularized determinant...")
    # Simulate simple Jacobian transformations for phase space
    J1 = np.array([[2.0, 0.5], [0.1, 3.0]])
    J2 = np.array([[4.0, 0.2], [0.3, 5.0]])
    
    det_J1 = np.linalg.det(J1)
    det_J2 = np.linalg.det(J2)
    
    # Direct product phase space -> block diagonal Jacobian
    J_block = scipy.linalg.block_diag(J1, J2)
    det_J_block = np.linalg.det(J_block)
    
    neg_log_det_J1 = -np.log(det_J1)
    neg_log_det_J2 = -np.log(det_J2)
    neg_log_det_J_block = -np.log(det_J_block)
    
    print(f"-log det(J1) = {neg_log_det_J1}")
    print(f"-log det(J2) = {neg_log_det_J2}")
    print(f"-log det(J1 oplus J2) = {neg_log_det_J_block}")
    
    additivity_sum = neg_log_det_J1 + neg_log_det_J2
    print(f"Sum of parts = {additivity_sum}")
    print(f"Is additive? {np.isclose(neg_log_det_J_block, additivity_sum)}")

if __name__ == "__main__":
    main()
