/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic

/-!
# Coordinate-free Lorentz action from Clifford bivectors

The carrier is an abstract quadratic module, and Clifford vectors are supplied by the
universal map `CliffordAlgebra.ι`. No Dirac matrices or coordinate expansion are used.
The commutator formula below derives preservation of the vector submodule directly from
the Clifford relations. For a four-dimensional quadratic module, its vector carrier is
the four-dimensional translation module.
-/

noncomputable section

namespace InfoGeometry.Canonical.TetractysCliffordLorentzAction

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (Q : QuadraticForm R V)

/-- The vector-valued infinitesimal action of the simple bivector `a ∧ b`.
The convention is fixed by the Clifford commutator identity proved below. -/
def bivectorAction (a b v : V) : V :=
  QuadraticMap.polar Q b v • a - QuadraticMap.polar Q a v • b

/-- A Clifford bivector acts on every Clifford vector by another Clifford vector.
This is the coordinate-free Lorentz-stability theorem for the translation module. -/
theorem bivector_commutator_preserves_vectors (a b v : V) :
    CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q v -
        CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b =
      CliffordAlgebra.ι Q (bivectorAction Q a b v) := by
  have hbv := CliffordAlgebra.ι_mul_ι_comm (Q := Q) b v
  have hav := CliffordAlgebra.ι_mul_ι_comm (Q := Q) a v
  calc
    CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q v -
        CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b =
      algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q b v) * CliffordAlgebra.ι Q a -
        algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q a v) * CliffordAlgebra.ι Q b := by
          rw [mul_assoc, hbv]
          rw [Algebra.commutes]
          rw [mul_sub, ← mul_assoc, hav]
          noncomm_ring
    _ = CliffordAlgebra.ι Q
        (QuadraticMap.polar Q b v • a - QuadraticMap.polar Q a v • b) := by
          simp only [← Algebra.smul_def, map_sub, map_smul]

/-- The commutator with a simple bivector preserves the canonical vector submodule. -/
theorem simple_bivector_preserves_range (a b : V) :
    ∀ v : V,
      CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q v -
          CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b ∈
        LinearMap.range (CliffordAlgebra.ι Q) := by
  intro v
  rw [bivector_commutator_preserves_vectors]
  exact ⟨bivectorAction Q a b v, rfl⟩

/-- The action is linear in the translation vector. -/
def simpleBivectorAction (a b : V) : V →ₗ[R] V where
  toFun := bivectorAction Q a b
  map_add' v w := by
    simp only [bivectorAction, QuadraticMap.polar_add_right]
    module
  map_smul' r v := by
    simp [bivectorAction, QuadraticMap.polar_smul_right, smul_sub,
      smul_smul, mul_comm]

end InfoGeometry.Canonical.TetractysCliffordLorentzAction

end
