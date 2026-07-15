import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Clifford.DiracPauliGamma
import InfoGeometry.Canonical.TorsionSpinorEinsteinFinite

/-!
# InfoGeometry.Canonical.TorsionSpinorGammaBridge

Finite bridge from the committed Dirac-Pauli gamma owner surface to the clean
finite torsion/spinor packet lane.

This file does not derive continuum Einstein-Cartan equations. It only proves
that the committed Lorentz-generator convention is antisymmetric in its tensor
indices, that the induced bivector bilinear is antisymmetric, and that a real
readout of that bilinear furnishes a valid lower-pair antisymmetric torsion
source packet for the finite owner lane.
-/

noncomputable section

namespace TorsionSpinorGammaBridge

open DiracPauliGamma
open TorsionSpinorEinsteinFinite

abbrev Idx : Type := Fin 4

/-- Real readout of a complex scalar, using the real part. -/
def realPartReadout (z : ℂ) : ℝ := z.re

theorem lorentzGenerator_swap (mu nu : Idx) :
    lorentzGenerator nu mu = -lorentzGenerator mu nu := by
  ext i j
  simp [lorentzGenerator, sub_eq_add_neg, Matrix.neg_apply]
  ring

theorem bivectorBilinear_antisymm (psi : DiracSpinor) (mu nu : Idx) :
    bivectorBilinear nu mu psi = -bivectorBilinear mu nu psi := by
  unfold bivectorBilinear spinorExpectation
  rw [lorentzGenerator_swap]
  have hleft :
      gamma0 * -lorentzGenerator mu nu = -(gamma0 * lorentzGenerator mu nu) := by
    simp
  rw [hleft]
  have hmulVec :
      Matrix.mulVec (-(gamma0 * lorentzGenerator mu nu)) psi
        = -Matrix.mulVec (gamma0 * lorentzGenerator mu nu) psi := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct]
  rw [hmulVec]
  simp_rw [Pi.neg_apply]
  simp_rw [mul_neg]
  rw [← Finset.sum_neg_distrib]

/-- Gamma-induced finite spinor source packet. -/
def gammaSpinorSource (psi : DiracSpinor) : SpinorSourcePacket where
  S := fun lam mu nu => realPartReadout (bivectorBilinear mu nu psi)
  antisymm := by
    intro lam mu nu
    unfold realPartReadout
    rw [bivectorBilinear_antisymm psi mu nu]
    simp

/-- The induced finite torsion source from the gamma bridge is antisymmetric in the lower pair. -/
theorem gammaSpinorTorsion_antisymm
    (κ β : ℝ) (psi : DiracSpinor) (lam mu nu : Idx) :
    spinorTorsion κ β (gammaSpinorSource psi).S lam mu nu
      = -spinorTorsion κ β (gammaSpinorSource psi).S lam nu mu := by
  exact spinorTorsion_antisymm κ β (gammaSpinorSource psi) lam mu nu

end TorsionSpinorGammaBridge
