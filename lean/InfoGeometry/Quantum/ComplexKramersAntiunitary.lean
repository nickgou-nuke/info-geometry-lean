/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.AntilinearSquare

/-! Canonical complex Kramers antiunitary on `ℂ²`.

This is the finite operator readout from the upstream Kramers lane.  It is
kept independent of Pin, Klein, and spacetime interpretations.
-/
noncomputable section
namespace InfoGeometry.Quantum.ComplexKramersAntiunitary

open scoped ComplexConjugate

abbrev H2 := InfoGeometry.Algebra.FiniteSpin.Vec2C

def standardInner (u v : H2) : ℂ :=
  star (u 0) * v 0 + star (u 1) * v 1

@[simp] theorem standardInner_zero_left (v : H2) : standardInner 0 v = 0 := by
  simp [standardInner]

@[simp] theorem standardInner_zero_right (u : H2) : standardInner u 0 = 0 := by
  simp [standardInner]

@[simp] theorem standardInner_add_left (u v w : H2) :
    standardInner (u + v) w = standardInner u w + standardInner v w := by
  simp [standardInner]
  ring

@[simp] theorem standardInner_add_right (u v w : H2) :
    standardInner u (v + w) = standardInner u v + standardInner u w := by
  simp [standardInner]
  ring

@[simp] theorem standardInner_smul_left (c : ℂ) (u v : H2) :
    standardInner (c • u) v = star c * standardInner u v := by
  simp [standardInner, Pi.smul_apply]
  ring

@[simp] theorem standardInner_smul_right (c : ℂ) (u v : H2) :
    standardInner u (c • v) = c * standardInner u v := by
  simp [standardInner, Pi.smul_apply]
  ring

@[simp] theorem standardInner_conj_symm (u v : H2) :
    star (standardInner u v) = standardInner v u := by
  simp [standardInner]
  ring

def timeReversal : H2 ≃ₗ⋆[ℂ] H2 where
  toFun v := ![-star (v 1), star (v 0)]
  invFun v := ![star (v 1), -star (v 0)]
  left_inv v := by
    ext i
    fin_cases i <;> simp
  right_inv v := by
    ext i
    fin_cases i <;> simp
  map_add' u v := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [Pi.smul_apply] <;> ring

@[simp] theorem timeReversal_apply_zero (v : H2) :
    timeReversal v 0 = -star (v 1) := rfl

@[simp] theorem timeReversal_apply_one (v : H2) :
    timeReversal v 1 = star (v 0) := rfl

@[simp] theorem timeReversal_add (u v : H2) :
    timeReversal (u + v) = timeReversal u + timeReversal v := by
  exact map_add timeReversal u v

@[simp] theorem timeReversal_smul (c : ℂ) (v : H2) :
    timeReversal (c • v) = star c • timeReversal v := by
  exact map_smulₛₗ timeReversal c v

@[simp] theorem timeReversal_sq (v : H2) :
    timeReversal (timeReversal v) = -v := by
  ext i
  fin_cases i <;> simp [timeReversal]

@[simp] theorem timeReversal_fourth (v : H2) :
    timeReversal (timeReversal (timeReversal (timeReversal v))) = v := by
  simp

theorem timeReversal_antiunitary (u v : H2) :
    standardInner (timeReversal u) (timeReversal v) = standardInner v u := by
  simp [standardInner, timeReversal]
  ring

/-- The existing Kramers operator has no nonzero eigenvector for any complex
eigenvalue. This specializes the general semilinear negative-square theorem. -/
theorem timeReversal_eigenvector_eq_zero {v : H2} {c : ℂ}
    (hv : timeReversal v = c • v) : v = 0 :=
  InfoGeometry.Algebra.AntilinearSquare.eq_zero_of_eigenvector
    timeReversal.toLinearMap timeReversal_sq hv

@[simp] theorem timeReversal_kramers_orthogonal (v : H2) :
    standardInner v (timeReversal v) = 0 := by
  simp [standardInner, timeReversal]
  ring

theorem timeReversal_ne_self_of_ne_zero {v : H2} (hv : v ≠ 0) :
    timeReversal v ≠ v := by
  intro hfixed
  exact hv (timeReversal_eigenvector_eq_zero (c := 1) (by simpa using hfixed))

theorem timeReversal_preserves_real_eigenvalue
    (A : Module.End ℂ H2)
    (hcomm : ∀ v, A (timeReversal v) = timeReversal (A v))
    (lam : ℝ) (v : H2)
    (hv : A v = (lam : ℂ) • v) :
    A (timeReversal v) = (lam : ℂ) • timeReversal v := by
  rw [hcomm, hv, timeReversal_smul]
  simp

theorem kramers_eigenpair_packet
    (A : Module.End ℂ H2)
    (hcomm : ∀ v, A (timeReversal v) = timeReversal (A v))
    (lam : ℝ) (v : H2) (hv0 : v ≠ 0)
    (hv : A v = (lam : ℂ) • v) :
    A (timeReversal v) = (lam : ℂ) • timeReversal v ∧
      standardInner v (timeReversal v) = 0 ∧
      timeReversal v ≠ v := by
  exact ⟨timeReversal_preserves_real_eigenvalue A hcomm lam v hv,
    timeReversal_kramers_orthogonal v,
    timeReversal_ne_self_of_ne_zero hv0⟩

end InfoGeometry.Quantum.ComplexKramersAntiunitary
end noncomputable section
