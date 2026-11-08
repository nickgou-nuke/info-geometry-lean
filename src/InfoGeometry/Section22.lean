import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import InfoGeometry.Section5
import InfoGeometry.Section8

/-!
# Section 22: finite quaternion-condensate algebra

The source text proposes moving from spinor condensates to quaternion
condensates.  This file repairs that proposal into finite algebraic claims.

#### BUCKET 1: CLOSED FINITE THEOREMS
Quaternion conjugation/norm and Hamilton basis laws are reused from Section 8.
The real part of the finite quaternion bilinear
`conj Q * e_a * dQ_mu` vanishes for zero derivative.  The induced metric built
from quaternion bilinear coefficients is symmetric.  The companion SymPy script
checks the concrete gamma-bivector embedding `γ1γ2`, `γ2γ3`, and `γ3γ1`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.  These are direct finite algebraic statements.

#### BUCKET 3: OPEN CLOSURE DEBT
No quaternion field theory, vacuum expectation value, nonzero condensate
existence theorem, differentiable bilinear map, emergent vierbein
nondegeneracy, gauge interpretation, or gravitational bootstrap equation is
claimed here.
-/

noncomputable section

namespace Section22

open Matrix

set_option linter.unusedSimpArgs false

abbrev Quat := Section8.Quat
abbrev DiracMatrix := Section5.DiracMatrix

/-- Quaternion basis elements used as finite analogues of gamma matrices. -/
def quaternionBasis : Fin 4 → Quat
  | 0 => 1
  | 1 => Section8.Quat.qi
  | 2 => Section8.Quat.qj
  | 3 => Section8.Quat.qk

/-- Real-part quaternion bilinear `Re(conj Q * e_a * dQ_mu)`. -/
def quaternionBilinear (Q : Quat) (dQ : Fin 4 → Quat) (a mu : Fin 4) : ℝ :=
  (Section8.Quat.conj Q * quaternionBasis a * dQ mu).r

/-- Constant quaternion field gives zero bilinear derivative readout. -/
theorem quaternionBilinear_zero_derivative (Q : Quat) (a mu : Fin 4) :
    quaternionBilinear Q (fun _ => 0) a mu = 0 := by
  fin_cases a <;> simp [quaternionBilinear, quaternionBasis]

/-- Quaternion conjugation gives the norm-squared scalar. -/
theorem quaternion_conj_mul_self_scalar (Q : Quat) :
    Section8.Quat.conj Q * Q = Section8.Quat.scalar (Section8.Quat.normSq Q) :=
  Section8.Quat.conj_mul_self Q

/-- Finite quaternion-bilinear vielbein coefficient table. -/
def quaternionVielbein (Q : Quat) (dQ : Fin 4 → Quat) : Fin 4 → Fin 4 → ℝ :=
  fun a mu => quaternionBilinear Q dQ a mu

/-- Metric readout from a quaternionic vielbein with `(+---)` signature. -/
def quaternionInducedMetric (e : Fin 4 → Fin 4 → ℝ) (mu nu : Fin 4) : ℝ :=
  e 0 mu * e 0 nu - e 1 mu * e 1 nu - e 2 mu * e 2 nu - e 3 mu * e 3 nu

/-- The metric readout remains symmetric for quaternionic bilinear coefficients. -/
theorem quaternionInducedMetric_symmetric
    (e : Fin 4 → Fin 4 → ℝ) (mu nu : Fin 4) :
    quaternionInducedMetric e mu nu = quaternionInducedMetric e nu mu := by
  simp [quaternionInducedMetric]
  ring

/-- Section 8's quaternion units satisfy the Hamilton table. -/
theorem quaternionBasis_hamilton_table :
    Section8.Quat.qi * Section8.Quat.qi = -(1 : Quat)
      ∧ Section8.Quat.qj * Section8.Quat.qj = -(1 : Quat)
      ∧ Section8.Quat.qk * Section8.Quat.qk = -(1 : Quat)
      ∧ Section8.Quat.qi * Section8.Quat.qj = Section8.Quat.qk
      ∧ Section8.Quat.qj * Section8.Quat.qk = Section8.Quat.qi
      ∧ Section8.Quat.qk * Section8.Quat.qi = Section8.Quat.qj := by
  constructor
  · ext <;> norm_num [Section8.Quat.qi]
  constructor
  · ext <;> norm_num [Section8.Quat.qj]
  constructor
  · ext <;> norm_num [Section8.Quat.qk]
  constructor
  · ext <;> norm_num [Section8.Quat.qi, Section8.Quat.qj, Section8.Quat.qk]
  constructor
  · ext <;> norm_num [Section8.Quat.qi, Section8.Quat.qj, Section8.Quat.qk]
  · ext <;> norm_num [Section8.Quat.qi, Section8.Quat.qj, Section8.Quat.qk]

theorem section22_capstone :
    (∀ Q : Quat, Section8.Quat.conj Q * Q =
      Section8.Quat.scalar (Section8.Quat.normSq Q)) ∧
    (∀ Q : Quat, ∀ a mu : Fin 4,
      quaternionBilinear Q (fun _ => 0) a mu = 0) ∧
    (∀ e : Fin 4 → Fin 4 → ℝ, ∀ mu nu : Fin 4,
      quaternionInducedMetric e mu nu = quaternionInducedMetric e nu mu) ∧
    Section8.Quat.qi * Section8.Quat.qi = -(1 : Quat) ∧
    Section8.Quat.qj * Section8.Quat.qj = -(1 : Quat) ∧
    Section8.Quat.qk * Section8.Quat.qk = -(1 : Quat) ∧
    Section8.Quat.qi * Section8.Quat.qj = Section8.Quat.qk ∧
    Section8.Quat.qj * Section8.Quat.qk = Section8.Quat.qi ∧
    Section8.Quat.qk * Section8.Quat.qi = Section8.Quat.qj := by
  refine ⟨quaternion_conj_mul_self_scalar, quaternionBilinear_zero_derivative,
    quaternionInducedMetric_symmetric, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact quaternionBasis_hamilton_table.1
  · exact quaternionBasis_hamilton_table.2.1
  · exact quaternionBasis_hamilton_table.2.2.1
  · exact quaternionBasis_hamilton_table.2.2.2.1
  · exact quaternionBasis_hamilton_table.2.2.2.2.1
  · exact quaternionBasis_hamilton_table.2.2.2.2.2

end Section22
