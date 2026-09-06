/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
import InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge

/-!
# Calibration of the concrete and coordinate-root conventions

The long sector uses the opposite cyclic orientation.  The calibration fixes
the short sector and reverses the long-sector coordinate around `1 / 2`.
-/

namespace InfoGeometry.Exceptional.G2ConcreteCoordinateCalibration

open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
open InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge

noncomputable section

def concreteRootToCyclotomic : G2Root → Root
  | (RootLength.Short, k) => (false, k)
  | (RootLength.Long, k) => (true, 1 - k)

def cyclotomicToConcreteRoot : Root → G2Root
  | (false, k) => (RootLength.Short, k)
  | (true, k) => (RootLength.Long, 1 - k)

noncomputable def concreteRootCyclotomicEquiv : G2Root ≃ Root where
  toFun := concreteRootToCyclotomic
  invFun := cyclotomicToConcreteRoot
  left_inv := by
    intro r
    rcases r with ⟨l, k⟩
    cases l <;> simp [concreteRootToCyclotomic, cyclotomicToConcreteRoot]
  right_inv := by
    intro r
    rcases r with ⟨b, k⟩
    cases b <;> simp [concreteRootToCyclotomic, cyclotomicToConcreteRoot]

theorem concreteRootCyclotomicEquiv_sAction (r : G2Root) :
    concreteRootCyclotomicEquiv (sAction r) =
      cyclotomicS1Perm (concreteRootCyclotomicEquiv r) := by
  rcases r with ⟨l, k⟩
  cases l <;>
    simp [concreteRootCyclotomicEquiv, concreteRootToCyclotomic,
      sAction, cyclotomicS1Perm, cyclotomicS1Fun]
  all_goals ring

theorem concreteRootCyclotomicEquiv_sAction_cAction (r : G2Root) :
    concreteRootCyclotomicEquiv (sAction (cAction r)) =
      cyclotomicS2Perm (concreteRootCyclotomicEquiv r) := by
  rcases r with ⟨l, k⟩
  cases l <;>
    simp [concreteRootCyclotomicEquiv, concreteRootToCyclotomic,
      sAction, cAction, cyclotomicS2Perm, cyclotomicS2Fun] <;>
      ring

noncomputable def concreteRootCoordinateEquiv : G2Root ≃ G2CoordinateRoot :=
  concreteRootCyclotomicEquiv.trans signedRootCyclotomicEquiv.symm

theorem concreteRootCoordinateEquiv_sAction (r : G2Root) :
    concreteRootCoordinateEquiv (sAction r) =
      s1Root (concreteRootCoordinateEquiv r) := by
  apply signedRootCyclotomicEquiv.injective
  simp only [concreteRootCoordinateEquiv, Equiv.trans_apply]
  rw [concreteRootCyclotomicEquiv_sAction]
  rw [Equiv.apply_symm_apply]
  symm
  simpa using
    (signedRootCyclotomicEquiv_s1
      (signedRootCyclotomicEquiv.symm (concreteRootCyclotomicEquiv r)))

theorem concreteRootCoordinateEquiv_sAction_cAction (r : G2Root) :
    concreteRootCoordinateEquiv (sAction (cAction r)) =
      s2Root (concreteRootCoordinateEquiv r) := by
  apply signedRootCyclotomicEquiv.injective
  simp only [concreteRootCoordinateEquiv, Equiv.trans_apply]
  rw [concreteRootCyclotomicEquiv_sAction_cAction]
  rw [Equiv.apply_symm_apply]
  symm
  simpa using
    (signedRootCyclotomicEquiv_s2
      (signedRootCyclotomicEquiv.symm (concreteRootCyclotomicEquiv r)))

end

end InfoGeometry.Exceptional.G2ConcreteCoordinateCalibration
