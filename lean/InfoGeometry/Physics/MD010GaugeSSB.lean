import Mathlib.Tactic
import InfoGeometry.Canonical.QuaternionCondensate
import InfoGeometry.Physics.MD007QuantumEigenoperatorInterpretation
import InfoGeometry.Physics.Section34StrengthenedFormalism

/-!
# Repaired MD 010: finite gauge and SSB algebra

Source: `github-nick:nickgou-nuke/MD`, file `010.md`.

Chapter 10 reviews gauge theory, Standard Model interpretation, spontaneous
symmetry breaking, mass terms, hierarchy mechanisms, and anomaly cancellation.
This owner formalizes only the finite algebraic socket:

* adjoint covariant-derivative commutator covariance under finite conjugation;
* finite curvature/product transport under an explicit inverse gate;
* finite trace-level gauge invariance of the curvature-square integrand shadow;
* scalar potential square-completion and stationary-radius algebra;
* diagonal `E₁₁` vacuum/fluctuation trace identities in the matrix-unit basis;
* the already-owned finite quaternion `U(1)`-style phase/norm invariance;
* the already-owned finite density covariant-derivative zero-connection law.

No theorem here asserts Yang--Mills field theory, gauge-invariant actions as
integrals, Standard Model particle identification, Higgs mechanism, Goldstone
counting, hierarchy generation, Yukawa physics, or anomaly cancellation.
-/

noncomputable section

namespace InfoGeometry.Physics.MD010GaugeSSB

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open Matrix
open InfoGeometry.Physics.MD001MatrixQuantumGeometry
open InfoGeometry.Physics.MD006OperatorEigenoperators
open InfoGeometry.Physics.MD007QuantumEigenoperatorInterpretation


/-- Adjoint-representation finite covariant derivative algebraic part: `[A,Φ]`. -/
def adjointCovDeriv (A Φ : MatrixQuantumCarrier) : MatrixQuantumCarrier :=
  A * Φ - Φ * A

/-- Finite conjugation action with an explicitly supplied inverse-like matrix. -/
def gaugeConj (U V X : MatrixQuantumCarrier) : MatrixQuantumCarrier :=
  U * X * V

/-- Adjoint commutator covariance under finite conjugation when `V U = 1`. -/
theorem adjointCovDeriv_gauge_covariant
    (U V A Φ : MatrixQuantumCarrier) (hVU : V * U = 1) :
    adjointCovDeriv (gaugeConj U V A) (gaugeConj U V Φ) =
      gaugeConj U V (adjointCovDeriv A Φ) := by
  unfold adjointCovDeriv gaugeConj
  calc
    U * A * V * (U * Φ * V) - U * Φ * V * (U * A * V)
        = U * A * (V * U) * Φ * V - U * Φ * (V * U) * A * V := by
          simp [Matrix.mul_assoc]
    _ = U * A * Φ * V - U * Φ * A * V := by
          simp [hVU, Matrix.mul_assoc]
    _ = U * (A * Φ - Φ * A) * V := by
          rw [mul_sub, sub_mul]
          simp [Matrix.mul_assoc]

/-- Product of two adjoint-transformed finite curvatures. -/
theorem gaugeConj_product_transport
    (U V F G : MatrixQuantumCarrier) (hVU : V * U = 1) :
    gaugeConj U V F * gaugeConj U V G = gaugeConj U V (F * G) := by
  unfold gaugeConj
  calc
    U * F * V * (U * G * V) = U * F * (V * U) * G * V := by
      simp [Matrix.mul_assoc]
    _ = U * F * G * V := by simp [hVU, Matrix.mul_assoc]
    _ = U * (F * G) * V := by simp [Matrix.mul_assoc]

/-- Finite curvature shadow: the algebraic commutator part `[Aμ,Aν]`. -/
def finiteCurvature (A B : MatrixQuantumCarrier) : MatrixQuantumCarrier :=
  adjointCovDeriv A B

/-- Curvature commutator covariance under finite conjugation. -/
theorem finiteCurvature_gauge_covariant
    (U V A B : MatrixQuantumCarrier) (hVU : V * U = 1) :
    finiteCurvature (gaugeConj U V A) (gaugeConj U V B) =
      gaugeConj U V (finiteCurvature A B) := by
  exact adjointCovDeriv_gauge_covariant U V A B hVU

/-- Trace is invariant under finite conjugation with an explicit inverse gate. -/
theorem trace2_gaugeConj_invariant
    (U V X : MatrixQuantumCarrier) (hVU : V * U = 1) :
    trace2 (gaugeConj U V X) = trace2 X := by
  unfold gaugeConj trace2
  change Matrix.trace (U * X * V) = Matrix.trace X
  rw [show U * X * V = U * (X * V) by simp [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm]
  rw [Matrix.mul_assoc, hVU]
  simp

/-- Finite trace-product invariance for the transported curvature shadow. -/
theorem trace2_gaugeConj_product_invariant
    (U V F G : MatrixQuantumCarrier) (hVU : V * U = 1) :
    trace2 (gaugeConj U V F * gaugeConj U V G) = trace2 (F * G) := by
  rw [gaugeConj_product_transport U V F G hVU]
  exact trace2_gaugeConj_invariant U V (F * G) hVU

/-- Curvature-square trace invariance for the finite commutator curvature shadow. -/
theorem finiteCurvature_trace_square_gauge_invariant
    (U V A B : MatrixQuantumCarrier) (hVU : V * U = 1) :
    trace2 (finiteCurvature (gaugeConj U V A) (gaugeConj U V B) *
        finiteCurvature (gaugeConj U V A) (gaugeConj U V B)) =
      trace2 (finiteCurvature A B * finiteCurvature A B) := by
  rw [finiteCurvature_gauge_covariant U V A B hVU]
  exact trace2_gaugeConj_product_invariant U V (finiteCurvature A B) (finiteCurvature A B) hVU

/-- Scalar SSB potential depending only on the finite radial readout `s`. -/
def scalarPotential (mu lam s : ℝ) : ℝ :=
  - mu ^ 2 * s + lam * s ^ 2

/-- Square-completion identity for the quartic radial potential. -/
theorem scalarPotential_complete_square (mu lam s : ℝ) (hlam : lam ≠ 0) :
    scalarPotential mu lam s =
      lam * (s - mu ^ 2 / (2 * lam)) ^ 2 - mu ^ 4 / (4 * lam) := by
  unfold scalarPotential
  field_simp [hlam]
  ring

/-- The source's stationary radial value cancels the first derivative algebraically. -/
theorem scalarPotential_stationary_radius (mu lam : ℝ) (hlam : lam ≠ 0) :
    - mu ^ 2 + 2 * lam * (mu ^ 2 / (2 * lam)) = 0 := by
  field_simp [hlam]
  ring

/-- Diagonal `E₁₁` vacuum ansatz. -/
def diagVEV (v : ℂ) : MatrixQuantumCarrier :=
  v • E11

/-- Trace square of the diagonal `E₁₁` ansatz. -/
theorem diagVEV_trace_square (v : ℂ) :
    trace2 (diagVEV v * diagVEV v) = v * v := by
  simp [diagVEV, trace2, E11, Matrix.mul_apply, Fin.sum_univ_two]

/-- Diagonal fluctuation around an `E₁₁` vacuum remains in the `E₁₁` line. -/
def diagFluctuation (v h : ℂ) : MatrixQuantumCarrier :=
  (v + h) • E11

/-- Trace square of the diagonal fluctuation expands as `(v+h)^2`. -/
theorem diagFluctuation_trace_square (v h : ℂ) :
    trace2 (diagFluctuation v h * diagFluctuation v h) = (v + h) * (v + h) := by
  simp [diagFluctuation, trace2, E11, Matrix.mul_apply, Fin.sum_univ_two]

/-- Algebraic quadratic coefficient in the source's one-real-mode Higgs expansion. -/
theorem higgs_quadratic_coefficient_identity (lam v : ℝ) :
    2 * lam * v ^ 2 = 2 * (lam * v ^ 2) := by
  ring

/-- Reuse the finite quaternion owner: unit phase rotation preserves norm. -/
theorem quaternion_phase_metric_invariant
    {c s : ℝ} (hunit : c ^ 2 + s ^ 2 = 1)
    (q : InfoGeometry.Canonical.QuaternionCondensate.H4) :
    (InfoGeometry.Canonical.QuaternionCondensate.H4.phaseRotate c s q).normSq = q.normSq :=
  InfoGeometry.Canonical.QuaternionCondensate.H4.normSq_phaseRotate_of_unit hunit q

/-- Reuse the finite density-connection owner: zero connection gives the partial derivative. -/
theorem density_covariantDerivative_zero_connection
    (dRho rho : InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite.Mat2) :
    InfoGeometry.Physics.Section34StrengthenedFormalism.covariantDensityDerivative dRho 0 rho = dRho :=
  InfoGeometry.Physics.Section34StrengthenedFormalism.covariantDensityDerivative_zero_connection dRho rho

/-- Repaired theorem-safe Chapter 10 finite gauge/SSB packet. -/
theorem repaired_MD010_gauge_ssb_packet
    (U V A Φ F G : MatrixQuantumCarrier) (hVU : V * U = 1)
    (mu lam s : ℝ) (hlam : lam ≠ 0) (v h : ℂ)
    (cphase sphase : ℝ) (hunit : cphase ^ 2 + sphase ^ 2 = 1)
    (q : InfoGeometry.Canonical.QuaternionCondensate.H4)
    (dRho rho : InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite.Mat2) :
    adjointCovDeriv (gaugeConj U V A) (gaugeConj U V Φ) =
        gaugeConj U V (adjointCovDeriv A Φ) ∧
    gaugeConj U V F * gaugeConj U V G = gaugeConj U V (F * G) ∧
    trace2 (gaugeConj U V F * gaugeConj U V G) = trace2 (F * G) ∧
    trace2 (finiteCurvature (gaugeConj U V A) (gaugeConj U V Φ) *
        finiteCurvature (gaugeConj U V A) (gaugeConj U V Φ)) =
      trace2 (finiteCurvature A Φ * finiteCurvature A Φ) ∧
    scalarPotential mu lam s =
        lam * (s - mu ^ 2 / (2 * lam)) ^ 2 - mu ^ 4 / (4 * lam) ∧
    - mu ^ 2 + 2 * lam * (mu ^ 2 / (2 * lam)) = 0 ∧
    trace2 (diagVEV v * diagVEV v) = v * v ∧
    trace2 (diagFluctuation v h * diagFluctuation v h) = (v + h) * (v + h) ∧
    (InfoGeometry.Canonical.QuaternionCondensate.H4.phaseRotate cphase sphase q).normSq = q.normSq ∧
    InfoGeometry.Physics.Section34StrengthenedFormalism.covariantDensityDerivative dRho 0 rho = dRho := by
  exact ⟨adjointCovDeriv_gauge_covariant U V A Φ hVU,
    gaugeConj_product_transport U V F G hVU,
    trace2_gaugeConj_product_invariant U V F G hVU,
    finiteCurvature_trace_square_gauge_invariant U V A Φ hVU,
    scalarPotential_complete_square mu lam s hlam,
    scalarPotential_stationary_radius mu lam hlam,
    diagVEV_trace_square v,
    diagFluctuation_trace_square v h,
    quaternion_phase_metric_invariant hunit q,
    density_covariantDerivative_zero_connection dRho rho⟩

end InfoGeometry.Physics.MD010GaugeSSB

end noncomputable section
