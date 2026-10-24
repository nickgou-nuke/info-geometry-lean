/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevDiracBoundaryProjector
import InfoGeometry.CliffordWeyl.DiracPeircePairing

/-! The actual sweet-spot BdG matrix is skew-adjoint for particleHole4.
Its kernel ket–bras are annihilated on both sides. Existing Dirac Peirce
transport applies to the actual boundary projector on this same carrier.
-/
noncomputable section
namespace InfoGeometry.Canonical.ConcreteKitaevBdGMatrix
open Matrix InfoGeometry.CliffordWeyl.SpinorBilinearSoldering
open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Physics

theorem sweetSpot_eq_BdG (t : ℝ) : kitaevSweetSpot4 t = kitaevBdG4 0 t t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kitaevSweetSpot4, kitaevBdG4]

theorem sweetSpot_metric_adjoint (t : ℝ) :
    particleHole4 * (kitaevSweetSpot4 t).conjTranspose * particleHole4 =
      -kitaevSweetSpot4 t := by
  rw [sweetSpot_eq_BdG]
  exact kitaevBdG4_particle_hole_symmetry 0 t t

theorem kernel_solder_left_annihilated (t : ℝ) (l r : Vec4C)
    (hl : kitaevSweetSpot4 t *ᵥ l = 0) :
    kitaevSweetSpot4 t * solder particleHole4 l r = 0 := by
  rw [← solder_left_operator_action, hl]
  simp [solder]

theorem kernel_solder_right_annihilated (t : ℝ) (l r : Vec4C)
    (hr : kitaevSweetSpot4 t *ᵥ r = 0) :
    solder particleHole4 l r * kitaevSweetSpot4 t = 0 := by
  have h := solder_right_operator_action particleHole4 particleHole4
    (kitaevSweetSpot4 t) particleHole4_square l r
  have hz : -(solder particleHole4 l r * kitaevSweetSpot4 t) = 0 := by
    calc
      _ = solder particleHole4 l r * (-kitaevSweetSpot4 t) := (mul_neg _ _).symm
      _ = solder particleHole4 l (kitaevSweetSpot4 t *ᵥ r) := by
        rw [← sweetSpot_metric_adjoint]
        exact h.symm
      _ = 0 := by rw [hr]; simp [solder, diracRow]
  exact neg_eq_zero.mp hz

/-- Adapter for Dirac adjunction. The auxiliary `gamma = 1` makes no claim
about a physical grading or oddness of the Hamiltonian. -/
def boundaryKreinData : KasparovKreinData Mat4C :=
  ⟨{ eta := particleHole4, gamma := 1 }, by
    refine ⟨particleHole4_square, ?_, by simp, by simp⟩
    change particleHole4.conjTranspose = particleHole4
    ext i j
    fin_cases i <;> fin_cases j <;> simp [particleHole4, conjTranspose_apply]⟩

theorem boundaryProjector_diracAdjoint :
    boundaryKreinData.diracAdjoint boundaryDiracProjector = boundaryDiracProjector :=
  boundaryDiracProjector_metric_adjoint

theorem boundary_component10_diracAdjoint (X : Mat4C) :
    boundaryKreinData.diracAdjoint (component10 boundaryDiracProjector X) =
      component01 boundaryDiracProjector (boundaryKreinData.diracAdjoint X) := by
  rw [KasparovKreinData.diracAdjoint_component10, boundaryProjector_diracAdjoint]

end InfoGeometry.Canonical.ConcreteKitaevBdGMatrix
