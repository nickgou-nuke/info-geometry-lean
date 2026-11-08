/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevBoundaryDiracPair
import InfoGeometry.Canonical.PeirceWeightedTrace

/-! The native Kitaev endpoints instantiate the existing CAR density API,
including its division-free weighted trace identity for arbitrary observables. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevNativeCARDensity
open InfoGeometry.Quantum.KitaevChain
open KitaevBoundaryDiracPair PeirceWeightedTrace
open InfoGeometry.OperatorAlgebra.TracialCARDensity
variable {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}

/-- The existing CAR carrier, filled by the actual boundary operators. -/
def boundaryCARPair (hN : 0 < N) (ops : MajoranaCliffordOperators N A) :
    SplitClifford.CARPair A where
  ann := boundaryAnnihilation hN ops
  cre := boundaryCreation hN ops
  ann_sq := boundaryAnnihilation_sq hN ops
  cre_sq := boundaryCreation_sq hN ops
  anti := boundary_CAR hN ops

theorem boundary_density_eq_supportWeight (hN : 0 < N)
    (ops : MajoranaCliffordOperators N A) (a b : ℂ) :
    density (boundaryCARPair hN ops) a b =
      supportWeight a b (boundaryAnnihilation hN ops) (boundaryCreation hN ops) := rfl

/-- The native density identity applies to all ambient observables. -/
theorem boundary_density_divisionFree (hN : 0 < N)
    (ops : MajoranaCliffordOperators N A) (τ : InfoGeometry.NCG.TracialFunctional ℂ A)
    (a b : ℂ) (x y : A) :
    (a * b) * weighted τ (density (boundaryCARPair hN ops) a b) (x * y) =
      weighted τ (density (boundaryCARPair hN ops) a b)
        (y * (density (boundaryCARPair hN ops) a b * x *
          densityAdjugate (boundaryCARPair hN ops) a b)) :=
  density_divisionFreeKMS τ (boundaryCARPair hN ops) a b x y

end InfoGeometry.Canonical.KitaevNativeCARDensity
