/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic

/-!
# Coordinate-free Clifford–Peirce Lorentz action

The carrier is an abstract quadratic module, and Clifford vectors are supplied by the
universal map `CliffordAlgebra.ι`. No Dirac matrices or coordinate expansion are used.
The commutator formula below derives preservation of the vector submodule directly from
the Clifford relations. When the tetraktys construction supplies a four-dimensional
quadratic module, this result acts on that four-dimensional translation carrier.
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
      smul_smul]

/-! ## The Peirce corner on a coordinate-free spinor carrier -/

/-- Two copies of the regular Clifford module, expressed as a direct sum. -/
abbrev CliffordPair := CliffordAlgebra Q × CliffordAlgebra Q

/-- The left Peirce sheet. -/
def leftSheet : CliffordPair Q →ₗ[R] CliffordPair Q where
  toFun z := (z.1, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- The right Peirce sheet. -/
def rightSheet : CliffordPair Q →ₗ[R] CliffordPair Q where
  toFun z := (0, z.2)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- The Peirce upper-corner translation operator associated to a Clifford vector. -/
def cornerTranslation (v : V) : CliffordPair Q →ₗ[R] CliffordPair Q where
  toFun z := (CliffordAlgebra.ι Q v * z.2, 0)
  map_add' z w := by simp [mul_add]
  map_smul' r z := by
    apply Prod.ext
    · exact (LinearMap.mulLeft R (CliffordAlgebra.ι Q v)).map_smul r z.2
    · simp

/-- Diagonal left multiplication is the Lorentz operator on the doubled regular module. -/
def diagonalBivector (a b : V) : CliffordPair Q →ₗ[R] CliffordPair Q where
  toFun z := (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * z.1,
    CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * z.2)
  map_add' z w := by simp [mul_add]
  map_smul' r z := by
    apply Prod.ext
    · exact (LinearMap.mulLeft R
        (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)).map_smul r z.1
    · exact (LinearMap.mulLeft R
        (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)).map_smul r z.2

/-- The translation operators lie in the Peirce upper corner `left · right`. -/
theorem cornerTranslation_is_peirce (v : V) :
    (leftSheet Q).comp (cornerTranslation Q v) = cornerTranslation Q v ∧
    (cornerTranslation Q v).comp (rightSheet Q) = cornerTranslation Q v := by
  constructor
  · apply LinearMap.ext
    intro z
    simp [leftSheet, cornerTranslation]
  · apply LinearMap.ext
    intro z
    simp [rightSheet, cornerTranslation]

/-- Bivector commutator action preserves the translation carrier inside the Peirce
corner. When its input quadratic module has dimension four, that carrier is four
dimensional. No covariance law is assumed: it follows from the Clifford relation. -/
theorem lorentz_action_preserves_corner_translation (a b v : V) :
    (diagonalBivector Q a b).comp (cornerTranslation Q v) -
        (cornerTranslation Q v).comp (diagonalBivector Q a b) =
      cornerTranslation Q (bivectorAction Q a b v) := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, diagonalBivector, cornerTranslation]
  apply Prod.ext
  · change CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b *
        (CliffordAlgebra.ι Q v * z.2) -
      CliffordAlgebra.ι Q v *
        (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * z.2) =
      CliffordAlgebra.ι Q (bivectorAction Q a b v) * z.2
    calc
      CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b *
          (CliffordAlgebra.ι Q v * z.2) -
        CliffordAlgebra.ι Q v *
          (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * z.2) =
        (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q v -
          CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) * z.2 := by
            noncomm_ring
      _ = CliffordAlgebra.ι Q (bivectorAction Q a b v) * z.2 := by
            rw [bivector_commutator_preserves_vectors]
  · simp

end InfoGeometry.Canonical.TetractysCliffordLorentzAction

end
