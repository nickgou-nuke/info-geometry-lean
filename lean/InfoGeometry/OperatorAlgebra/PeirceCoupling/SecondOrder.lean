/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceCoupling.Algebra

/-!
# Second-order idempotent coefficients

The coefficient of degree two in the idempotent equation for `p + t E + t² z`
is `p*z + z*p - z = -E²`. For opposite Peirce corners its full solution space
is the translate of the native odd range by the negative Lie product.
There is exactly one even solution. No analytic curve or derivative is assumed.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling

open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading

variable {A : Type*} [Ring A] {p : A} (hp : IsIdempotentElem p) (a b : A)

local notation "U" => component10 p a
local notation "V" => component01 p b
local notation "K" => ⁅U, V⁆

include hp

/-- All second-order coefficients differ from `-K` by a tangent direction. -/
theorem second_order_iff (z : A) :
    p * z + z * p - z = -((U + V) ^ 2) ↔
      z + K ∈ LinearMap.range (odd p) := by
  have hshift : p * (z + K) + (z + K) * p - (z + K) =
      (p * z + z * p - z) + (U * V + V * U) := by
    calc
      _ = (p * z + z * p - z) + (p * K + K * p - K) := by noncomm_ring
      _ = _ := by rw [lie_second_order_boundary hp a b]
  rw [opposite_sum_sq hp a b, mem_odd_iff hp,
    ← sub_eq_zero (a := p * (z + K) + (z + K) * p) (b := z + K), hshift]
  exact eq_neg_iff_add_eq_zero

/-- The negative Lie product is the unique even second-order coefficient. -/
theorem even_second_order_iff (z : A) :
    (p * z + z * p - z = -((U + V) ^ 2) ∧
      z ∈ LinearMap.range (even p)) ↔ z = -K := by
  constructor
  · rintro ⟨hz, he⟩
    have ho := (second_order_iff hp a b z).mp hz
    have hx : z + K ∈ LinearMap.range (even p) ⊓ LinearMap.range (odd p) :=
      ⟨(LinearMap.range (even p)).add_mem he (lie_mem_even hp a b), ho⟩
    have hzero : z + K = 0 := by
      simpa only [(isCompl hp).inf_eq_bot, Submodule.mem_bot] using hx
    exact eq_neg_of_add_eq_zero_left hzero
  · intro hz
    subst z
    refine ⟨(second_order_iff hp a b (-K)).mpr ?_, ?_⟩
    · simp
    · exact (LinearMap.range (even p)).neg_mem (lie_mem_even hp a b)

omit hp in
/-- The opposite-corner generator has the signed quadratic second variation. -/
theorem generator_lie_sum : ⁅V - U, U + V⁆ = -(2 • K) := by
  simp only [Ring.lie_def, two_nsmul]
  noncomm_ring

end InfoGeometry.OperatorAlgebra.PeirceCoupling
