/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace InfoGeometry.Canonical.SouriauKaehlerKleinBottle

structure SouriauTemperature where
  beta : ℝ
  time : ℝ

def complexTemperature (θ : SouriauTemperature) : ℂ := ⟨θ.beta, θ.time⟩

theorem complexTemperature_parts (θ : SouriauTemperature) :
    (complexTemperature θ).re = θ.beta ∧
      (complexTemperature θ).im = θ.time := by
  exact ⟨rfl, rfl⟩

abbrev Mat2 := InfoGeometry.Algebra.FiniteSpin.Mat2R

def complexStructure : Mat2 := !![0, -1; 1, 0]

theorem complexStructure_sq : complexStructure * complexStructure = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexStructure, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]

structure OrbitVector where
  x : ℝ
  y : ℝ

def metric (u v : OrbitVector) : ℝ := u.x * v.x + u.y * v.y

def symplectic (u v : OrbitVector) : ℝ := u.x * v.y - u.y * v.x

def actComplex (v : OrbitVector) : OrbitVector := ⟨-v.y, v.x⟩

theorem kahler_compatibility (u v : OrbitVector) :
    symplectic u (actComplex v) = metric u v := by
  dsimp [symplectic, actComplex, metric]
  ring

def modularTwist (θ : SouriauTemperature) : SouriauTemperature :=
  ⟨1 - θ.beta, -θ.time⟩

theorem modularTwist_involutive (θ : SouriauTemperature) :
    modularTwist (modularTwist θ) = θ := by
  cases θ
  simp [modularTwist]

theorem modularTwist_fixed_beta (t : ℝ) :
    (modularTwist ⟨1 / 2, t⟩).beta = 1 / 2 := by
  simp [modularTwist]
  ring

theorem modularTwist_reverses_time (t : ℝ) :
    (modularTwist ⟨1 / 2, t⟩).time = -t := by
  rfl

end InfoGeometry.Canonical.SouriauKaehlerKleinBottle
