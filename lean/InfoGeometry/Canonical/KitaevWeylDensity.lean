/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevNativeCARDensity

/-! Native boundary Weyl conjugation exchanges the two CAR density weights.
The resulting trace transport uses actual ambient units, with no positivity premise. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevWeylDensity
open InfoGeometry.Quantum.KitaevChain InfoGeometry.NCG
open KitaevBoundaryDiracPair KitaevNativeCARDensity
open InfoGeometry.OperatorAlgebra.TracialCARDensity
open ReflexiveNilpotentFlows
variable {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}
variable (hN : 0 < N) (ops : MajoranaCliffordOperators N A)

theorem boundaryWeylUnit_conjugates_density (a b : ℂ) :
    (boundaryWeylUnit hN ops : A) * density (boundaryCARPair hN ops) a b *
        (↑((boundaryWeylUnit hN ops)⁻¹) : A) =
      density (boundaryCARPair hN ops) b a := by
  obtain ⟨hp, hm⟩ := weyl_swap_supports (boundaryAnnihilation_sq hN ops)
    (boundaryCreation_sq hN ops) (boundary_reflexive hN ops).1
    (boundary_reflexive hN ops).2
  change weyl _ _ * (a • (_ * _) + b • (_ * _)) * weylInv _ _ =
    b • (_ * _) + a • (_ * _)
  simp only [boundaryCARPair, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hp, hm]
  abel

theorem boundaryWeyl_density_pullback (τ : TracialFunctional ℂ A)
    (a b : ℂ) (x : A) :
    weighted τ (density (boundaryCARPair hN ops) b a) x =
      weighted τ (density (boundaryCARPair hN ops) a b)
        ((↑((boundaryWeylUnit hN ops)⁻¹) : A) * x * (boundaryWeylUnit hN ops : A)) := by
  rw [← boundaryWeylUnit_conjugates_density hN ops a b]
  exact inverse_pullback τ _ _ _

theorem boundaryWeyl_density_joint_covariance (τ : TracialFunctional ℂ A)
    (a b : ℂ) (x : A) :
    weighted τ (density (boundaryCARPair hN ops) b a)
        ((boundaryWeylUnit hN ops : A) * x * (↑((boundaryWeylUnit hN ops)⁻¹) : A)) =
      weighted τ (density (boundaryCARPair hN ops) a b) x := by
  rw [← boundaryWeylUnit_conjugates_density hN ops a b]
  exact joint_covariance τ _ _ _

end InfoGeometry.Canonical.KitaevWeylDensity
