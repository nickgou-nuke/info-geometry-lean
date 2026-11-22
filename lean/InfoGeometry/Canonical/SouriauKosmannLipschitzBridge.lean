/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic

/-!
# Souriau–Kosmann–Lipschitz algebraic bridge

Pure algebraic core linking Souriau's Killing temperature vectors to one-parameter
Lipschitz/Clifford flows, stripped of manifold/analytic claims.

For a quadratic space `(M, Q)` and vectors `a b : M`, the Clifford bivector
`ι a * ι b` acts on a vector `v` by the commutator `½[ιaιb, ιv]`.  This module
proves natively:

* the commutator identity (the result is again a vector),
* the induced vector action `bivectorAction` satisfies Killing's polar equation
  `B_Q(D u, w) + B_Q(u, D w) = 0` (Souriau's equilibrium condition),
* the scalar-centre dilation `2σ·id` appended to it satisfies the conformal
  Killing equation with factor `4σ`.

The spin-group rotor witness already in the repo is not duplicated here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauKosmannLipschitzBridge

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

/-- The vector representative of the bivector commutator action
    `D_{a,b}(v) = ½ (polar(b,v) a - polar(a,v) b)`. -/
def bivectorAction (a b : M) : M →ₗ[ℝ] M where
  toFun v := (1 / 2 : ℝ) • (QuadraticMap.polar Q b v • a - QuadraticMap.polar Q a v • b)
  map_add' x y := by
    simp [QuadraticMap.polar_add_right]
    module
  map_smul' r x := by
    simp [QuadraticMap.polar_smul_right]
    module

/-- The Clifford commutator of a bivector with a vector is a scalar combination
    of vectors: `[ιaιb, ιv] = polar(b,v)ιa - polar(a,v)ιb`. -/
theorem bivector_commutator (a b v : M) :
    CliffordAlgebra.ι Q a * (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q v) -
        CliffordAlgebra.ι Q v * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) =
      algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q b v) * CliffordAlgebra.ι Q a -
        algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a v) * CliffordAlgebra.ι Q b := by
  have h_av := CliffordAlgebra.ι_mul_ι_comm (Q := Q) a v
  have h_bv := CliffordAlgebra.ι_mul_ι_comm (Q := Q) b v
  calc
    CliffordAlgebra.ι Q a * (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q v) -
        CliffordAlgebra.ι Q v * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)
        = CliffordAlgebra.ι Q a *
              (algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q b v) -
                CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q b) -
          CliffordAlgebra.ι Q v * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) := by
            rw [h_bv]
    _ = CliffordAlgebra.ι Q a * algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q b v) -
          (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q v) * CliffordAlgebra.ι Q b -
          CliffordAlgebra.ι Q v * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) := by
            noncomm_ring
    _ = algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q b v) * CliffordAlgebra.ι Q a -
          (algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a v) -
            CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q a) * CliffordAlgebra.ι Q b -
          CliffordAlgebra.ι Q v * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b) := by
            rw [Algebra.commutes, h_av]
    _ = algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q b v) * CliffordAlgebra.ι Q a -
          algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q a v) * CliffordAlgebra.ι Q b := by
            noncomm_ring

/-- `ι` of the vector action is the half-commutator with the Clifford bivector. -/
theorem ι_bivectorAction (a b v : M) :
    CliffordAlgebra.ι Q (bivectorAction Q a b v) =
      (1 / 2 : ℝ) •
        (CliffordAlgebra.ι Q a * (CliffordAlgebra.ι Q b * CliffordAlgebra.ι Q v) -
          CliffordAlgebra.ι Q v * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b)) := by
  rw [bivector_commutator]
  simp [bivectorAction, Algebra.smul_def]

/-- Souriau's Killing equation in polar form: the bivector action is an
    infinitesimal isometry, `B_Q(D u, w) + B_Q(u, D w) = 0`. -/
theorem bivectorAction_isKilling (a b u w : M) :
    QuadraticMap.polar Q (bivectorAction Q a b u) w +
        QuadraticMap.polar Q u (bivectorAction Q a b w) = 0 := by
  simp [bivectorAction, QuadraticMap.polar_smul_right, QuadraticMap.polar_comm]
  ring

/-- The scalar-centre dilation joined with the bivector action gives the
    conformal Killing equation with conformal factor `4σ`. -/
theorem conformalAction_isConformalKilling (σ : ℝ) (a b u w : M) :
    QuadraticMap.polar Q ((2 * σ) • u + bivectorAction Q a b u) w +
        QuadraticMap.polar Q u ((2 * σ) • w + bivectorAction Q a b w) =
      4 * σ * QuadraticMap.polar Q u w := by
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
  have hkill := bivectorAction_isKilling Q a b u w
  simp only [smul_eq_mul]
  nlinarith

end InfoGeometry.Canonical.SouriauKosmannLipschitzBridge
