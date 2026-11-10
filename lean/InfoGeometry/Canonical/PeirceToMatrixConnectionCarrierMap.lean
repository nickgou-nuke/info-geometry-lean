/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixConnectionCurvatureTransport
import InfoGeometry.Canonical.MatrixTracedChernWeilBridge
import InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
import InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Peirce expressions under ring homomorphisms

Proves naturality of Peirce corner expressions under ring endomorphisms of the
same matrix ring `Mat`. This file does not construct a map from an arbitrary
Peirce carrier to a matrix carrier. Differential transport belongs to
`MatrixConnectionCurvatureTransport`, where compatibility assumptions are
stated explicitly.
-/

noncomputable section

namespace InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap

open ExteriorAlgebra
open InfoGeometry.Canonical.MatrixConnectionCurvatureTransport
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)

/-- `f` intertwines `conePlus`: `f (conePlus P A) = conePlus (f P) (f A)`. -/
theorem intertwines_conePlus (f : Mat →+* Mat) (P A : Mat) :
    f (conePlus P A) = conePlus (f P) (f A) := by
  calc
    f (conePlus P A) = f (P * A * (1 - P)) := rfl
    _ = f P * f A * f (1 - P) := by
      rw [map_mul, map_mul]
    _ = f P * f A * (1 - f P) := by
      have h : f (1 - P) = 1 - f P := by
        calc
          f (1 - P) = f 1 - f P := by rw [map_sub]
          _ = 1 - f P := by rw [map_one]
      rw [h]
    _ = conePlus (f P) (f A) := rfl

/-- `f` intertwines `coneMinus`: `f (coneMinus P C) = coneMinus (f P) (f C)`. -/
theorem intertwines_coneMinus (f : Mat →+* Mat) (P C : Mat) :
    f (coneMinus P C) = coneMinus (f P) (f C) := by
  calc
    f (coneMinus P C) = f ((1 - P) * C * P) := rfl
    _ = f (1 - P) * f C * f P := by
      rw [map_mul, map_mul]
    _ = (1 - f P) * f C * f P := by
      have h : f (1 - P) = 1 - f P := by
        calc
          f (1 - P) = f 1 - f P := by rw [map_sub]
          _ = 1 - f P := by rw [map_one]
      rw [h]
    _ = coneMinus (f P) (f C) := rfl

/-- `f` intertwines `genPhi`: `f (genPhi P A C) = genPhi (f P) (f A) (f C)`. -/
theorem intertwines_genPhi (f : Mat →+* Mat) (P A C : Mat) :
    f (genPhi P A C) = genPhi (f P) (f A) (f C) := by
  calc
    f (genPhi P A C) = f (conePlus P A + coneMinus P C) := rfl
    _ = f (conePlus P A) + f (coneMinus P C) := by rw [map_add]
    _ = conePlus (f P) (f A) + coneMinus (f P) (f C) := by
      rw [intertwines_conePlus f P A, intertwines_coneMinus f P C]
    _ = genPhi (f P) (f A) (f C) := rfl

/-- `f` intertwines `genV`: `f (genV P A C) = genV (f P) (f A) (f C)`. -/
theorem intertwines_genV (f : Mat →+* Mat) (P A C : Mat) :
    f (genV P A C) = genV (f P) (f A) (f C) := by
  calc
    f (genV P A C) = f (anticomm (conePlus P A) (coneMinus P C)) := rfl
    _ = f (conePlus P A * coneMinus P C + coneMinus P C * conePlus P A) := rfl
    _ = f (conePlus P A * coneMinus P C) + f (coneMinus P C * conePlus P A) := by
      rw [map_add]
    _ = f (conePlus P A) * f (coneMinus P C) + f (coneMinus P C) * f (conePlus P A) := by
      rw [map_mul, map_mul]
    _ = conePlus (f P) (f A) * coneMinus (f P) (f C) +
        coneMinus (f P) (f C) * conePlus (f P) (f A) := by
      rw [intertwines_conePlus f P A, intertwines_coneMinus f P C]
    _ = genV (f P) (f A) (f C) := by simp [genV, anticomm]

/-- `f` intertwines `peirceGradingDeriv`: `f (peirceGradingDeriv P X) = peirceGradingDeriv (f P) (f X)`. -/
theorem intertwines_peirceGradingDeriv (f : Mat →+* Mat) (P X : Mat) :
    f (peirceGradingDeriv P X) = peirceGradingDeriv (f P) (f X) := by
  calc
    f (peirceGradingDeriv P X) = f (comm P X) := rfl
    _ = f (P * X - X * P) := rfl
    _ = f P * f X - f X * f P := by
      rw [map_sub, map_mul, map_mul]
    _ = comm (f P) (f X) := rfl
    _ = peirceGradingDeriv (f P) (f X) := rfl

/-- `f` intertwines `peirceCovariantDeriv`:
`f (peirceCovariantDeriv P A C X) = peirceCovariantDeriv (f P) (f A) (f C) (f X)`. -/
theorem intertwines_peirceCovariantDeriv (f : Mat →+* Mat) (P A C X : Mat) :
    f (peirceCovariantDeriv P A C X) = peirceCovariantDeriv (f P) (f A) (f C) (f X) := by
  calc
    f (peirceCovariantDeriv P A C X) = f (peirceGradingDeriv P X + comm (genPhi P A C) X) := rfl
    _ = f (peirceGradingDeriv P X) + f (comm (genPhi P A C) X) := by rw [map_add]
    _ = peirceGradingDeriv (f P) (f X) + f (genPhi P A C * X - X * genPhi P A C) := by
      rw [intertwines_peirceGradingDeriv f P X]
      rfl
    _ = peirceGradingDeriv (f P) (f X) + (f (genPhi P A C) * f X - f X * f (genPhi P A C)) := by
      rw [map_sub, map_mul, map_mul]
    _ = peirceGradingDeriv (f P) (f X) + (genPhi (f P) (f A) (f C) * f X - f X * genPhi (f P) (f A) (f C)) := by
      rw [intertwines_genPhi f P A C]
    _ = peirceGradingDeriv (f P) (f X) + InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi (f P) (f A) (f C)) (f X) := by
      simp [InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    _ = peirceCovariantDeriv (f P) (f A) (f C) (f X) := rfl

/-- `f` intertwines `peirceMaurerCartanCurvature`:
`f (peirceMaurerCartanCurvature P A C) = peirceMaurerCartanCurvature (f P) (f A) (f C)`. -/
theorem intertwines_peirceMaurerCartanCurvature (f : Mat →+* Mat) (P A C : Mat) :
    f (peirceMaurerCartanCurvature P A C) = peirceMaurerCartanCurvature (f P) (f A) (f C) := by
  calc
    f (peirceMaurerCartanCurvature P A C) =
      f (peirceGradingDeriv P (genPhi P A C) + genPhi P A C * genPhi P A C) := rfl
    _ = f (peirceGradingDeriv P (genPhi P A C)) + f (genPhi P A C * genPhi P A C) := by
      rw [map_add]
    _ = peirceGradingDeriv (f P) (f (genPhi P A C)) + f (genPhi P A C) * f (genPhi P A C) := by
      rw [intertwines_peirceGradingDeriv f P (genPhi P A C)]
      rw [map_mul]
    _ = peirceGradingDeriv (f P) (genPhi (f P) (f A) (f C)) +
        genPhi (f P) (f A) (f C) * genPhi (f P) (f A) (f C) := by
      rw [intertwines_genPhi f P A C]
    _ = peirceMaurerCartanCurvature (f P) (f A) (f C) := rfl

end InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap

end noncomputable section
