import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InfoGeometry.Physics.SpectralFluctuationIdeal

/-!
# Derivative readback for the spectral surprisal fluctuation

This owner records the first-order cancellation of
`exp (-β λ) - 1 + β λ`.  It is deliberately separate from the factorisation
and functional-calculus owner.
-/

namespace InfoGeometry.Physics.SpectralFluctuation

theorem hasDerivAt_surprisalFluctuation_zero (beta : ℝ) :
    HasDerivAt (fun lambda : ℝ => surprisalFluctuation beta lambda) 0 0 := by
  have hlin : HasDerivAt (fun lambda : ℝ => -beta * lambda) (-beta) 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (-beta)).mul
      (hasDerivAt_id (x := (0 : ℝ))) using 1 <;> simp <;> ring
  have hexp : HasDerivAt (fun lambda : ℝ => Real.exp (-beta * lambda)) (-beta) 0 := by
    convert hlin.exp using 1 <;> simp
  have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 :=
    hasDerivAt_const (x := (0 : ℝ)) 1
  have hbeta : HasDerivAt (fun lambda : ℝ => beta * lambda) beta 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) beta).mul
      (hasDerivAt_id (x := (0 : ℝ))) using 1 <;> simp <;> ring
  convert hexp.sub (hone.sub hbeta) using 1
  · funext lambda
    simp [surprisalFluctuation]
    ring
  · simp

theorem surprisalFluctuation_zero_and_deriv_zero (beta : ℝ) :
    surprisalFluctuation beta 0 = 0 ∧
      deriv (fun lambda : ℝ => surprisalFluctuation beta lambda) 0 = 0 := by
  refine ⟨surprisalFluctuation_zero beta, ?_⟩
  exact (hasDerivAt_surprisalFluctuation_zero beta).deriv

theorem hasDerivAt_surprisalFluctuation_derivative_expression_zero
    (beta : ℝ) :
    HasDerivAt
      (fun lambda : ℝ => -beta * Real.exp (-beta * lambda) + beta)
      (beta ^ 2) 0 := by
  have hlin : HasDerivAt (fun lambda : ℝ => -beta * lambda) (-beta) 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (-beta)).mul
      (hasDerivAt_id (x := (0 : ℝ))) using 1 <;> simp <;> ring
  have hexp : HasDerivAt (fun lambda : ℝ => Real.exp (-beta * lambda)) (-beta) 0 := by
    convert hlin.exp using 1 <;> simp
  have hmul := (hasDerivAt_const (x := (0 : ℝ)) (-beta)).mul hexp
  have hconst : HasDerivAt (fun _ : ℝ => beta) 0 0 :=
    hasDerivAt_const (x := (0 : ℝ)) beta
  convert hmul.add hconst using 1 <;> simp <;> ring

end InfoGeometry.Physics.SpectralFluctuation
