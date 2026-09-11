import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LieFenchelQuadratic

/-!
# InfoGeometry.Canonical.SO3RotationFenchelWitness

Concrete `SO(3)`-style witness (z-axis rotations) on `Fin 3 → ℝ`.

This module proves:
* explicit rotation action formulas,
* invariance of Euclidean norm-squared,
* invariance of quadratic potential and Bregman divergence (explicit 3D formulas).

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.SO3RotationFenchelWitness

open Matrix

noncomputable section

abbrev V3 := InfoGeometry.Algebra.FiniteSpin.Vec3R
abbrev M3 := InfoGeometry.Algebra.FiniteSpin.Mat3R

/-- Rotation around the z-axis by angle `θ`. -/
noncomputable def Rz (θ : ℝ) : M3 :=
  !![Real.cos θ, -Real.sin θ, 0;
     Real.sin θ,  Real.cos θ, 0;
     0,           0,          1]

/-- Action of `Rz θ` on vectors. -/
noncomputable def rotZ (θ : ℝ) (v : V3) : V3 := (Rz θ).mulVec v

/-- Euclidean norm-squared on `V3`. -/
def normSq3 (v : V3) : ℝ := v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2

/-- Euclidean dot product on `V3`. -/
def dot3 (u v : V3) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Squared radial coordinate in the `xy`-plane. -/
def rhoSq3 (v : V3) : ℝ := v 0 ^ 2 + v 1 ^ 2

/-- Symmetry-adapted invariants for the z-rotation action. -/
def symmetryCoords (v : V3) : ℝ × ℝ := (rhoSq3 v, v 2)

/-- Quadratic potential on `V3`. -/
def psi3 (v : V3) : ℝ := (1 / 2 : ℝ) * normSq3 v

/-- Quadratic Bregman divergence on `V3`. -/
def bregman3 (x y : V3) : ℝ := psi3 x - psi3 y - dot3 y (x - y)

theorem rotZ_apply0 (θ : ℝ) (v : V3) :
    rotZ θ v 0 = Real.cos θ * v 0 - Real.sin θ * v 1 := by
  unfold rotZ Rz
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem rotZ_apply1 (θ : ℝ) (v : V3) :
    rotZ θ v 1 = Real.sin θ * v 0 + Real.cos θ * v 1 := by
  unfold rotZ Rz
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem rotZ_apply2 (θ : ℝ) (v : V3) :
    rotZ θ v 2 = v 2 := by
  unfold rotZ Rz
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem rotZ_add (θ : ℝ) (u v : V3) :
    rotZ θ (u + v) = rotZ θ u + rotZ θ v := by
  unfold rotZ
  simpa using Matrix.mulVec_add (Rz θ) u v

/-- Norm-squared invariance under z-rotation. -/
theorem normSq3_rotZ (θ : ℝ) (v : V3) :
    normSq3 (rotZ θ v) = normSq3 v := by
  unfold normSq3
  rw [rotZ_apply0, rotZ_apply1, rotZ_apply2]
  ring_nf
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-- `xy` radial coordinate is invariant under z-rotation. -/
theorem rhoSq3_rotZ (θ : ℝ) (v : V3) :
    rhoSq3 (rotZ θ v) = rhoSq3 v := by
  unfold rhoSq3
  rw [rotZ_apply0, rotZ_apply1]
  ring_nf
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-- Symmetry-adapted coordinates are invariant under z-rotation. -/
theorem symmetryCoords_rotZ (θ : ℝ) (v : V3) :
    symmetryCoords (rotZ θ v) = symmetryCoords v := by
  unfold symmetryCoords
  simp [rhoSq3_rotZ, rotZ_apply2]

/-- Orbit chart at fixed radius `ρ` and height `z`. -/
def orbitChart (ρ z φ : ℝ) : V3 :=
  fun i =>
    if i = 0 then ρ * Real.cos φ
    else if i = 1 then ρ * Real.sin φ
    else z

/-- z-rotation acts by phase translation in the orbit chart. -/
theorem rotZ_orbitChart (θ ρ z φ : ℝ) :
    rotZ θ (orbitChart ρ z φ) = orbitChart ρ z (θ + φ) := by
  ext i
  fin_cases i
  · unfold rotZ orbitChart Rz
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Real.cos_add, Real.sin_add]
    ring
  · unfold rotZ orbitChart Rz
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Real.cos_add, Real.sin_add]
    ring
  · unfold rotZ orbitChart Rz
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Dot-product invariance under z-rotation. -/
theorem dot3_rotZ (θ : ℝ) (u v : V3) :
    dot3 (rotZ θ u) (rotZ θ v) = dot3 u v := by
  unfold dot3
  rw [rotZ_apply0, rotZ_apply1, rotZ_apply2, rotZ_apply0, rotZ_apply1, rotZ_apply2]
  ring_nf
  have hsplit :
      Real.cos θ ^ 2 * u 0 * v 0 + Real.cos θ ^ 2 * u 1 * v 1 + u 0 * Real.sin θ ^ 2 * v 0 +
          Real.sin θ ^ 2 * u 1 * v 1 + u 2 * v 2
        = (Real.cos θ ^ 2 + Real.sin θ ^ 2) * (u 0 * v 0) +
            (Real.cos θ ^ 2 + Real.sin θ ^ 2) * (u 1 * v 1) + u 2 * v 2 := by
    ring
  rw [hsplit]
  rw [Real.cos_sq_add_sin_sq θ]
  ring

/-- Quadratic potential invariance under z-rotation. -/
theorem psi3_rotZ (θ : ℝ) (v : V3) :
    psi3 (rotZ θ v) = psi3 v := by
  unfold psi3
  rw [normSq3_rotZ]

/-- Bregman invariance under z-rotation. -/
theorem bregman3_rotZ (θ : ℝ) (x y : V3) :
    bregman3 (rotZ θ x) (rotZ θ y) = bregman3 x y := by
  unfold bregman3
  have hsub : rotZ θ (x - y) = rotZ θ x - rotZ θ y := by
    unfold rotZ
    ext i
    simp [sub_eq_add_neg, Matrix.mulVec_add, Matrix.mulVec_neg]
  rw [psi3_rotZ, psi3_rotZ]
  rw [← hsub]
  have hdot : dot3 (rotZ θ y) (rotZ θ (x - y)) = dot3 y (x - y) := dot3_rotZ θ y (x - y)
  linarith [hdot]

/-- Symmetry coordinates of the orbit chart are explicit. -/
theorem symmetryCoords_orbitChart (ρ z φ : ℝ) :
    symmetryCoords (orbitChart ρ z φ) = (ρ ^ 2, z) := by
  unfold symmetryCoords rhoSq3 orbitChart
  ext <;> simp
  nlinarith [Real.cos_sq_add_sin_sq φ]

/-- Phase-translation orbit statement in symmetry-adapted chart form. -/
theorem orbitChart_mem_rotOrbit (ρ z φ θ : ℝ) :
    orbitChart ρ z (θ + φ) ∈ Set.range (fun t : ℝ => rotZ t (orbitChart ρ z φ)) := by
  refine ⟨θ, ?_⟩
  simpa using rotZ_orbitChart θ ρ z φ

/--
Quadratic potential is constant along the z-rotation orbit of `x`.
-/
theorem psi3_constant_on_zOrbit (x z : V3)
    (hz : z ∈ Set.range (fun θ : ℝ => rotZ θ x)) :
    psi3 z = psi3 x := by
  rcases hz with ⟨θ, rfl⟩
  exact psi3_rotZ θ x

/--
The third coordinate is fixed along the z-rotation orbit.
-/
theorem zCoord_constant_on_zOrbit (x z : V3)
    (hz : z ∈ Set.range (fun θ : ℝ => rotZ θ x)) :
    z 2 = x 2 := by
  rcases hz with ⟨θ, rfl⟩
  exact rotZ_apply2 θ x

end

end InfoGeometry.Canonical.SO3RotationFenchelWitness
