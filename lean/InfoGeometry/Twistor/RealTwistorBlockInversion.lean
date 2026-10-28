/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorSoldering
import InfoGeometry.Projective.KleinQuadricPlucker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The native real block rotation and its Plucker action

The actual real map `(ω,π) ↦ (π,-ω)` squares to minus the identity. Its
six-minor action squares to the identity and carries the graph chart to
`-X⁻¹`, with homogeneous factor `det X`. The opposite six-dimensional sign
belongs to a different linear map; it is not silently absorbed here.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealTwistorBlockInversion

open RealTwistorIncidence RealTwistorSoldering
open InfoGeometry.Projective.KleinQuadricPlucker
open scoped Matrix

abbrev TwistorSpace := Carrier Spinor Spinor

/-- A genuine real spinor-pair automorphism. -/
def blockRotation : TwistorSpace ≃ₗ[ℝ] TwistorSpace where
  toFun z := (z.2, -z.1)
  invFun z := (-z.2, z.1)
  left_inv z := by simp
  right_inv z := by simp
  map_add' z w := by simp [add_comm]
  map_smul' a z := by simp

@[simp] theorem blockRotation_apply (z : TwistorSpace) :
    blockRotation z = (z.2, -z.1) := rfl

theorem blockRotation_sq (z : TwistorSpace) :
    blockRotation (blockRotation z) = -z := by
  apply Prod.ext <;> simp

/-- The inverse chart is derived for the actual incidence parametrization. -/
theorem blockRotation_incidenceMap (X : Spinor ≃ₗ[ℝ] Spinor) (π : Spinor) :
    blockRotation (incidenceMap X.toLinearMap π) =
      incidenceMap (-X.symm.toLinearMap) (-X π) := by
  apply Prod.ext <;> simp [incidenceMap_apply]

/-- Equality of the native incidence submodules under the real rotation. -/
theorem blockRotation_incidenceSpace (X : Spinor ≃ₗ[ℝ] Spinor) :
    (incidenceSpace X.toLinearMap).map blockRotation.toLinearMap =
      incidenceSpace (-X.symm.toLinearMap) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' := (mem_incidenceSpace X.toLinearMap w).mp hw
    apply (mem_incidenceSpace _ _).mpr
    simp [hw']
  · intro hz
    have hz' := (mem_incidenceSpace (-X.symm.toLinearMap) z).mp hz
    refine ⟨blockRotation.symm z, ?_, blockRotation.apply_symm_apply z⟩
    apply (mem_incidenceSpace _ _).mpr
    change -z.2 = X z.1
    rw [hz']
    simp

def twistorCoordinates (z : TwistorSpace) : Vec4 ℝ :=
  ⟨z.1 0, z.1 1, z.2 0, z.2 1⟩

/-- These are the existing six minors of the actual two real twistors. -/
def twistorPlucker (z w : TwistorSpace) : Plucker6 ℝ :=
  Plucker6.pluckerLine (twistorCoordinates z) (twistorCoordinates w)

def pluckerRotation (P : Plucker6 ℝ) : Plucker6 ℝ :=
  ⟨P.p23, P.p02, P.p12, P.p03, P.p13, P.p01⟩

@[simp] theorem pluckerRotation_involutive (P : Plucker6 ℝ) :
    pluckerRotation (pluckerRotation P) = P := by
  cases P
  rfl

theorem pluckerRotation_add (P Q : Plucker6 ℝ) :
    pluckerRotation (Plucker6.add P Q) =
      Plucker6.add (pluckerRotation P) (pluckerRotation Q) := rfl

theorem pluckerRotation_scale (a : ℝ) (P : Plucker6 ℝ) :
    pluckerRotation (Plucker6.scale a P) =
      Plucker6.scale a (pluckerRotation P) := rfl

theorem pluckerRotation_preserves_kleinQ (P : Plucker6 ℝ) :
    Plucker6.kleinQ (pluckerRotation P) = Plucker6.kleinQ P := by
  simp only [Plucker6.kleinQ, pluckerRotation]
  ring

theorem pluckerRotation_preserves_polar (P Q : Plucker6 ℝ) :
    Plucker6.kleinPolar (pluckerRotation P) (pluckerRotation Q) =
      Plucker6.kleinPolar P Q := by
  simp only [Plucker6.kleinPolar, pluckerRotation]
  ring

/-- Exact signed intertwining on the six minors, before projectivization. -/
theorem twistorPlucker_blockRotation (z w : TwistorSpace) :
    twistorPlucker (blockRotation z) (blockRotation w) =
      pluckerRotation (twistorPlucker z w) := by
  apply Plucker6.ext <;>
    simp [twistorPlucker, twistorCoordinates, pluckerRotation,
      Plucker6.pluckerLine] <;> ring

/-- Ordered standard frame of the actual incidence graph. -/
def graphFrame (X : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) : TwistorSpace :=
  incidenceMap (Matrix.toLin' X) (Pi.single j 1)

def graphPlucker (X : Matrix (Fin 2) (Fin 2) ℝ) : Plucker6 ℝ :=
  twistorPlucker (graphFrame X 0) (graphFrame X 1)

theorem graphPlucker_coordinates (X : Matrix (Fin 2) (Fin 2) ℝ) :
    graphPlucker X =
      ⟨X.det, -X 0 1, X 0 0, -X 1 1, X 1 0, 1⟩ := by
  apply Plucker6.ext <;>
    simp [graphPlucker, graphFrame, twistorPlucker, twistorCoordinates,
      Plucker6.pluckerLine, Matrix.toLin'_apply, Matrix.det_fin_two, mul_comm]

theorem graphPlucker_kleinQ (X : Matrix (Fin 2) (Fin 2) ℝ) :
    Plucker6.kleinQ (graphPlucker X) = 0 :=
  Plucker6.kleinQ_pluckerLine _ _

/-- The nonzero determinant is precisely the domain of the inverse chart. -/
theorem pluckerRotation_graph_inverse (X : Matrix (Fin 2) (Fin 2) ℝ)
    (hX : X.det ≠ 0) :
    pluckerRotation (graphPlucker X) =
      Plucker6.scale X.det (graphPlucker (-X⁻¹)) := by
  rw [graphPlucker_coordinates, graphPlucker_coordinates]
  have hinvdet : (-X⁻¹).det = X.det⁻¹ := by
    rw [Matrix.det_neg, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    norm_num
  apply Plucker6.ext <;>
    simp only [pluckerRotation, Plucker6.scale, hinvdet]
  all_goals
    try simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two,
      Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
  all_goals field_simp [hX]

end InfoGeometry.Twistor.RealTwistorBlockInversion
