import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordFiveBladeBridge

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

open ExteriorAlgebra

/-- The square of a decomposable exterior 5-vector vanishes by alternation
    and repeated generators.  The arbitrary module `V` here carries no
    specified Clifford form; this theorem therefore asserts neither a
    `Gr(5,n)` Plücker relation nor a `Cl(5,5)` kinematic result. -/
theorem native_plucker_five_blade_nilpotent (v1 v2 v3 v4 v5 : V) :
    (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5) * (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5) = 0 := by
  have h_anti : ∀ a b : V, (ι R a : ExteriorAlgebra R V) * ι R b = - (ι R b * ι R a) := by
    intro a b
    have h_sq := ExteriorAlgebra.ι_sq_zero (R := R) (a + b)
    have h_a := ExteriorAlgebra.ι_sq_zero (R := R) a
    have h_b := ExteriorAlgebra.ι_sq_zero (R := R) b
    have h_exp : (ι R (a + b) : ExteriorAlgebra R V) = ι R a + ι R b := map_add (ι R) a b
    rw [h_exp] at h_sq
    calc (ι R a : ExteriorAlgebra R V) * ι R b
      _ = (ι R a + ι R b) * (ι R a + ι R b) - ι R a * ι R a - ι R b * ι R b - ι R b * ι R a := by noncomm_ring
      _ = 0 - 0 - 0 - ι R b * ι R a := by rw [h_sq, h_a, h_b]
      _ = - (ι R b * ι R a) := by noncomm_ring

  have h_v1_sq : (ι R v1 : ExteriorAlgebra R V) * ι R v1 = 0 := ExteriorAlgebra.ι_sq_zero (R := R) v1

  calc
    (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5) * (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5)
      = ι R v1 * ι R v2 * ι R v3 * ι R v4 * (ι R v5 * ι R v1) * ι R v2 * ι R v3 * ι R v4 * ι R v5 := by noncomm_ring
    _ = ι R v1 * ι R v2 * ι R v3 * ι R v4 * (- (ι R v1 * ι R v5)) * ι R v2 * ι R v3 * ι R v4 * ι R v5 := by rw [h_anti v5 v1]
    _ = - (ι R v1 * ι R v2 * ι R v3 * (ι R v4 * ι R v1) * ι R v5 * ι R v2 * ι R v3 * ι R v4 * ι R v5) := by noncomm_ring
    _ = - (ι R v1 * ι R v2 * ι R v3 * (- (ι R v1 * ι R v4)) * ι R v5 * ι R v2 * ι R v3 * ι R v4 * ι R v5) := by rw [h_anti v4 v1]
    _ = ι R v1 * ι R v2 * (ι R v3 * ι R v1) * ι R v4 * ι R v5 * ι R v2 * ι R v3 * ι R v4 * ι R v5 := by noncomm_ring
    _ = ι R v1 * ι R v2 * (- (ι R v1 * ι R v3)) * ι R v4 * ι R v5 * ι R v2 * ι R v3 * ι R v4 * ι R v5 := by rw [h_anti v3 v1]
    _ = - (ι R v1 * (ι R v2 * ι R v1) * ι R v3 * ι R v4 * ι R v5 * ι R v2 * ι R v3 * ι R v4 * ι R v5) := by noncomm_ring
    _ = - (ι R v1 * (- (ι R v1 * ι R v2)) * ι R v3 * ι R v4 * ι R v5 * ι R v2 * ι R v3 * ι R v4 * ι R v5) := by rw [h_anti v2 v1]
    _ = (ι R v1 * ι R v1) * ι R v2 * ι R v3 * ι R v4 * ι R v5 * ι R v2 * ι R v3 * ι R v4 * ι R v5 := by noncomm_ring
    _ = 0 * ι R v2 * ι R v3 * ι R v4 * ι R v5 * ι R v2 * ι R v3 * ι R v4 * ι R v5 := by rw [h_v1_sq]
    _ = 0 := by noncomm_ring

/-- **Theorem**: Native Mathlib 5-Blade Pushforward Conservation under Linear Maps f : V → W. -/
theorem native_plucker_five_blade_linear_map_conservation (f : V →ₗ[R] W) (v1 v2 v3 v4 v5 : V) :
    (map f (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5)) * (map f (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5)) = 0 := by
  rw [← _root_.map_mul, native_plucker_five_blade_nilpotent, _root_.map_zero]

/-- Collects the exterior square-zero identity for a decomposable 5-vector and
    its transport under the exterior-algebra map induced by `f`.  No Clifford
    signature, orthogonal group, twistor extension, or Plücker classification
    is part of this statement. -/
theorem master_split_clifford_five_blade_synthesis
    (f : V →ₗ[R] W) (v1 v2 v3 v4 v5 : V) :
    ((ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5) * (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5) = 0) ∧
    ((map f (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5)) * (map f (ι R v1 * ι R v2 * ι R v3 * ι R v4 * ι R v5)) = 0) := ⟨
  native_plucker_five_blade_nilpotent v1 v2 v3 v4 v5,
  native_plucker_five_blade_linear_map_conservation f v1 v2 v3 v4 v5
⟩

end InfoGeometry.Canonical.SplitCliffordFiveBladeBridge
