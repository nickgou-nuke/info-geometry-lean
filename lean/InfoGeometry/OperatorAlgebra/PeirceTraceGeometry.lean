/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.IdempotentCartan
import InfoGeometry.Core.PeirceTangent
import InfoGeometry.OperatorAlgebra.MatrixTraceGeometry
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Hilbert--Schmidt geometry of the existing Peirce projections

`evenPart` and `oddPart` retain their ring-level owners. Here they are
complex-linear operators on the full matrix algebra. For a star projection,
their images are orthogonal in the trace pairing, and the exact positive
Kadison defect detects precisely the part that does not commute with it.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceTraceGeometry

open Matrix InfoGeometry.Core.IdempotentCartan InfoGeometry.Core.PeirceDecomposition
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The existing even Peirce operation as a native complex-linear map. -/
def evenLinearMap (p : Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := evenPart p
  map_add' := evenPart_add p
  map_smul' c A := by
    simp [evenPart, component11, component00, mul_smul_comm, smul_mul_assoc,
      smul_add]

/-- The existing odd Peirce operation as a native complex-linear map. -/
def oddLinearMap (p : Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := oddPart p
  map_add' := oddPart_add p
  map_smul' c A := by
    simp [oddPart, component10, component01, mul_smul_comm, smul_mul_assoc,
      smul_add]

/-- Complementarity holds as equality of native linear maps. -/
theorem evenLinearMap_add_oddLinearMap (p : Matrix n n ℂ) :
    evenLinearMap p + oddLinearMap p = LinearMap.id := by
  ext A i j
  exact congrFun (congrFun (even_add_odd p A) i) j

/-- The even operator is a projection on the full matrix space. -/
theorem evenLinearMap_idempotent {p : Matrix n n ℂ} (hp : IsIdempotentElem p) :
    (evenLinearMap p).comp (evenLinearMap p) = evenLinearMap p := by
  ext A i j
  exact congrFun (congrFun ((projection_laws hp A).1) i) j

/-- The odd operator is a projection on the full matrix space. -/
theorem oddLinearMap_idempotent {p : Matrix n n ℂ} (hp : IsIdempotentElem p) :
    (oddLinearMap p).comp (oddLinearMap p) = oddLinearMap p := by
  ext A i j
  exact congrFun (congrFun ((projection_laws hp A).2.2.2) i) j

/-- The native Lie adjoint squared is exactly the existing odd Peirce map. -/
theorem oddLinearMap_eq_ad_comp {p : Matrix n n ℂ} (hp : IsIdempotentElem p) :
    oddLinearMap p = (LieAlgebra.ad ℂ (Matrix n n ℂ) p).comp
      (LieAlgebra.ad ℂ (Matrix n n ℂ) p) := by
  ext A i j
  exact congrFun (congrFun (odd_eq_double_commutator hp A) i) j

/-- The fixed vectors of the odd projector satisfy exactly the first-order
idempotent equation. This does not assert construction of a manifold. -/
theorem oddPart_eq_self_iff_tangent {p : Matrix n n ℂ}
    (hp : IsIdempotentElem p) (A : Matrix n n ℂ) :
    oddPart p A = A ↔ p * A + A * p = A := by
  have hcomm : oddPart p A = (A * p - p * A) * p - p * (A * p - p * A) := by
    rw [odd_eq_double_commutator hp]
    noncomm_ring
  constructor
  · intro h
    have ht := InfoGeometry.Core.PeirceTangent.commutator_tangent hp (A * p - p * A)
    rw [← hcomm, h] at ht
    exact ht
  · intro h
    rw [hcomm]
    exact InfoGeometry.Core.PeirceTangent.tangent_eq_double_commutator hp h

/-- Cyclic trace transfers a two-sided sandwich to the other argument. -/
theorem trace_sandwich_mul (p A B : Matrix n n ℂ) :
    trace (p * A * p * B) = trace (A * (p * B * p)) := by
  calc
    _ = trace (p * (A * (p * B))) := by simp only [mul_assoc]
    _ = trace ((A * (p * B)) * p) := trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

/-- Algebraic symmetry for the bilinear trace pairing requires no adjoint
or idempotence hypothesis. -/
theorem trace_evenPart_mul (p A B : Matrix n n ℂ) :
    trace (evenPart p A * B) = trace (A * evenPart p B) := by
  simp only [evenPart, component11, component00, add_mul, mul_add, trace_add]
  rw [trace_sandwich_mul, trace_sandwich_mul]

/-- An idempotent pinching preserves trace, without requiring self-adjointness. -/
theorem trace_evenPart {p : Matrix n n ℂ} (hp : IsIdempotentElem p)
    (A : Matrix n n ℂ) : trace (evenPart p A) = trace A := by
  have hone : evenPart p (1 : Matrix n n ℂ) = 1 :=
    even_eq_self_of_commute hp (by simp)
  simpa only [mul_one, hone] using trace_evenPart_mul p A 1

/-- Peirce even projection commutes with the adjoint for self-adjoint `p`. -/
theorem star_evenPart {p : Matrix n n ℂ} (hp : IsSelfAdjoint p)
    (A : Matrix n n ℂ) : star (evenPart p A) = evenPart p (star A) := by
  simp only [evenPart, component11, component00, complementIdempotent,
    star_add, star_mul, star_sub, star_one, hp.star_eq, mul_assoc]

/-- Peirce odd projection commutes with the adjoint for self-adjoint `p`. -/
theorem star_oddPart {p : Matrix n n ℂ} (hp : IsSelfAdjoint p)
    (A : Matrix n n ℂ) : star (oddPart p A) = oddPart p (star A) := by
  simp only [oddPart, component10, component01, complementIdempotent,
    star_add, star_mul, star_sub, star_one, hp.star_eq, mul_assoc]
  exact add_comm _ _

/-- Self-adjointness of the even projection for the Hilbert--Schmidt pairing. -/
theorem trace_star_evenPart {p : Matrix n n ℂ} (hp : IsSelfAdjoint p)
    (A B : Matrix n n ℂ) :
    trace (star (evenPart p A) * B) = trace (star A * evenPart p B) := by
  rw [star_evenPart hp, trace_evenPart_mul]

/-- Self-adjointness of the odd projection for the Hilbert--Schmidt pairing. -/
theorem trace_star_oddPart {p : Matrix n n ℂ} (hp : IsSelfAdjoint p)
    (A B : Matrix n n ℂ) :
    trace (star (oddPart p A) * B) = trace (star A * oddPart p B) := by
  have heA : oddPart p A = A - evenPart p A := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm, even_add_odd]
  have heB : oddPart p B = B - evenPart p B := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm, even_add_odd]
  rw [heA, heB, star_sub, sub_mul, mul_sub, trace_sub, trace_sub,
    trace_star_evenPart hp]

/-- Orthogonality is an actual trace identity between arbitrary even and odd
operators, without assuming that the original inputs commute. -/
theorem trace_even_odd_zero {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (A B : Matrix n n ℂ) :
    trace (star (evenPart p A) * oddPart p B) = 0 := by
  rw [trace_star_evenPart hp.isSelfAdjoint,
    (projection_laws hp.isIdempotentElem B).2.1, mul_zero, trace_zero]

theorem trace_odd_even_zero {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (A B : Matrix n n ℂ) :
    trace (star (oddPart p A) * evenPart p B) = 0 := by
  rw [trace_star_oddPart hp.isSelfAdjoint,
    (projection_laws hp.isIdempotentElem B).2.2.1, mul_zero, trace_zero]

/-- Exact Pythagoras identity for the squared Hilbert--Schmidt size. -/
theorem trace_peirce_pythagoras {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (A : Matrix n n ℂ) :
    trace (star A * A) = trace (star (evenPart p A) * evenPart p A) +
      trace (star (oddPart p A) * oddPart p A) := by
  calc
    _ = trace (star (evenPart p A + oddPart p A) *
        (evenPart p A + oddPart p A)) := by rw [even_add_odd]
    _ = _ := by
      simp only [star_add, add_mul, mul_add, trace_add,
        trace_even_odd_zero hp, trace_odd_even_zero hp, add_zero, zero_add]

/-- The complete operator-valued defect, stronger than a scalar inequality. -/
theorem kadison_defect {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (A : Matrix n n ℂ) :
    evenPart p (star A * A) - star (evenPart p A) * evenPart p A =
      star (oddPart p A) * oddPart p A := by
  rw [(multiplication_rules hp.isIdempotentElem (star A) A).1,
    ← star_evenPart hp.isSelfAdjoint, ← star_oddPart hp.isSelfAdjoint]
  abel

/-- The Kadison defect lies in Mathlib's positive-semidefinite matrix cone. -/
theorem kadison_defect_posSemidef {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (A : Matrix n n ℂ) :
    (evenPart p (star A * A) - star (evenPart p A) * evenPart p A).PosSemidef := by
  rw [kadison_defect hp]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Equality in the pinching Schwarz inequality detects exactly the commutant.
There is no premise that `A` commutes with `p`: commutation is the conclusion. -/
theorem kadison_equality_iff_commute {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (A : Matrix n n ℂ) :
    evenPart p (star A * A) = star (evenPart p A) * evenPart p A ↔ Commute p A := by
  rw [← sub_eq_zero, kadison_defect hp]
  constructor
  · intro h
    have ht : trace (star (oddPart p A) * oddPart p A) = 0 := by rw [h, trace_zero]
    have hz : oddPart p A = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht
    exact (odd_zero_iff_commute hp.isIdempotentElem A).mp hz
  · intro h
    rw [(odd_zero_iff_commute hp.isIdempotentElem A).mpr h, star_zero, zero_mul]

end InfoGeometry.OperatorAlgebra.PeirceTraceGeometry
