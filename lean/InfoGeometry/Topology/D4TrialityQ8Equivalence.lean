import Mathlib
import InfoGeometry.Topology.Q8ModularFlowBridge
import InfoGeometry.Topology.Q8V4SchurBridge

/-!
# D4 Triality and Q8 Generator Permutation Equivalence

This module formalizes the discrete analogue of the Spin(8) (D4) triality.
In continuous supergravity, the D4 triality is an S3 outer automorphism 
permuting the vector, spinor, and conjugate spinor representations 
(8_v, 8_s, 8_c).

On our non-orientable Brillouin Klein boundary, this continuous triality 
collapses into the exact discrete S3 outer automorphism of the Q8 centralizer, 
which acts by symmetrically permuting the three quaternion basis generators 
(M_a, M_b, M_c). We formally construct the explicit generating automorphisms
ω (order 3) and σ (order 2) proving that they satisfy the exact braiding relation
σ ω σ = ω⁻¹ within the quaternion algebra.
-/

namespace InfoGeometry.Topology.D4Triality

open QuaternionGroup

/-- 
  The explicit cyclic triality automorphism ω on Q8.
  It cycles the three imaginary axes: I → J → K → I.
  In QuaternionGroup 2:
  I = xa 0
  J = a 1
  K = xa 1
-/
def triality_omega : QuaternionGroup 2 ≃* QuaternionGroup 2 where
  toFun
    | a 0 => a 0
    | a 1 => xa 1
    | a 2 => a 2
    | a 3 => xa 3
    | xa 0 => a 1
    | xa 1 => xa 0
    | xa 2 => a 3
    | xa 3 => xa 2
  invFun
    | a 0 => a 0
    | xa 1 => a 1
    | a 2 => a 2
    | xa 3 => a 3
    | a 1 => xa 0
    | xa 0 => xa 1
    | a 3 => xa 2
    | xa 2 => xa 3
  left_inv x := by fin_cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl
  map_mul' x y := by fin_cases x <;> fin_cases y <;> decide

/-- 
  The exact order-3 property of the continuous triality, 
  projected onto the discrete Q8 boundary.
-/
theorem triality_omega_order_three (x : QuaternionGroup 2) : 
    triality_omega (triality_omega (triality_omega x)) = x := by
  fin_cases x <;> rfl

/-- 
  The explicit reflection automorphism σ on Q8.
  It acts as: I → -J, J → -I, K → -K.
  This exact mapping ensures that σ ω σ = ω⁻¹ in the automorphism group,
  generating a pristine S3 subgroup of Aut(Q8) which intersects trivially with Inn(Q8).
-/
def triality_sigma : QuaternionGroup 2 ≃* QuaternionGroup 2 where
  toFun
    | a 0 => a 0
    | a 1 => xa 2  -- J → -I
    | a 2 => a 2
    | a 3 => xa 0  -- -J → I
    | xa 0 => a 3  -- I → -J
    | xa 1 => xa 3 -- K → -K
    | xa 2 => a 1  -- -I → J
    | xa 3 => xa 1 -- -K → K
  invFun
    | a 0 => a 0
    | xa 2 => a 1
    | a 2 => a 2
    | xa 0 => a 3
    | a 3 => xa 0
    | xa 3 => xa 1
    | a 1 => xa 2
    | xa 1 => xa 3
  left_inv x := by fin_cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl
  map_mul' x y := by fin_cases x <;> fin_cases y <;> decide

/-- 
  The exact order-2 property of the reflection triality.
-/
theorem triality_sigma_order_two (x : QuaternionGroup 2) : 
    triality_sigma (triality_sigma x) = x := by
  fin_cases x <;> rfl

/-- 
  The S3 braiding relation of the triality generators: σ ω σ = ω⁻¹
-/
theorem triality_braiding_relation (x : QuaternionGroup 2) : 
    triality_sigma (triality_omega (triality_sigma x)) = 
    triality_omega (triality_omega x) := by
  fin_cases x <;> rfl

end InfoGeometry.Topology.D4Triality
