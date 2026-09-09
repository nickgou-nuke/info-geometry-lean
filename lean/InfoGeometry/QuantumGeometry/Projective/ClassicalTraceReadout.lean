import InfoGeometry.QuantumGeometry.Projective.QGT
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
import InfoGeometry.Physics.Section38StressEnergyDomainSeparation
import InfoGeometry.Physics.SplitOctonionFibration
import InfoGeometry.Volume.DeterminantBundle
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Projective QGT to finite classical readout

This module closes the finite projective-to-classical edge without postulating a
new stress tensor or a new determinant theory.

On the native two-level Hilbert carrier `EuclideanSpace ℂ (Fin 2)`, the
horizontal QGT Gram pairing is the trace of the rank-one matrix

`|Y^⊥><X^⊥|`.

Therefore the exact `quantumTraceToClassical` map already owned by the finite
stress-energy domain-separation lane returns the QGT itself.  Its real part is
the Fubini--Study metric and `-2` times its imaginary part is the Berry
curvature.  The same classical scalar is then inserted into the existing Amari
base, determinant-line, and finite stress carriers, where their native duality,
Weyl scaling, and symmetry theorems apply.
-/

noncomputable section

namespace InfoGeometry.QuantumGeometry.Projective.ClassicalTraceReadout

open scoped InnerProductSpace
open Matrix
open InfoGeometry.QuantumGeometry.Projective
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
open InfoGeometry.Physics.Section38StressEnergyDomainSeparation
open InfoGeometry.Physics.SplitOctonionFibration
open InfoGeometry.Volume.DeterminantBundle

abbrev QubitH := FinKetSpace (Fin 2)
abbrev EndQ := QubitH →L[ℂ] QubitH

/--
Rank-one horizontal Gram matrix `|Y^⊥><X^⊥|` on the native two-level Hilbert
carrier.
-/
def horizontalGramMatrix
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec
    (fun i => (projOrth ψ Y) i)
    (fun i => star ((projOrth ψ X) i))

/--
The Section-38 quantum-to-classical trace of the horizontal rank-one operator
is exactly the projective quantum geometric tensor.
-/
theorem quantumTrace_horizontalGramMatrix_eq_QGT
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) :
    quantumTraceToClassical (horizontalGramMatrix ψ X Y) =
      QGT ψ X Y := by
  unfold quantumTraceToClassical horizontalGramMatrix
  rw [Matrix.trace_vecMulVec]
  rw [QGT_eq_inner_projOrth]
  exact (EuclideanSpace.inner_eq_star_dotProduct
    (projOrth ψ X) (projOrth ψ Y)).symm

/-- The real classical trace channel is precisely the Fubini--Study metric. -/
theorem quantumTrace_horizontalGramMatrix_re_eq_fubiniStudyMetric
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) :
    (quantumTraceToClassical (horizontalGramMatrix ψ X Y)).re =
      fubiniStudyMetric ψ X Y := by
  rw [quantumTrace_horizontalGramMatrix_eq_QGT]
  rfl

/-- The imaginary classical trace channel is precisely the Berry curvature readout. -/
theorem neg_two_quantumTrace_horizontalGramMatrix_im_eq_berryCurvature
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) :
    -2 * (quantumTraceToClassical (horizontalGramMatrix ψ X Y)).im =
      berryCurvature ψ X Y := by
  rw [quantumTrace_horizontalGramMatrix_eq_QGT]
  rfl

/--
A concrete one-parameter Amari base whose exponential connection is generated
by the Fubini--Study classical trace readout.
-/
def qgtAmariBase
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) : AmariBase where
  e_connection := fun t =>
    t * (quantumTraceToClassical (horizontalGramMatrix ψ X Y)).re
  m_connection := fun t =>
    -t * (quantumTraceToClassical (horizontalGramMatrix ψ X Y)).re
  duality := by
    intro t
    ring

@[simp]
theorem qgtAmariBase_e_connection_one
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) :
    (qgtAmariBase ψ X Y).e_connection 1 =
      fubiniStudyMetric ψ X Y := by
  simp [qgtAmariBase,
    quantumTrace_horizontalGramMatrix_re_eq_fubiniStudyMetric]

@[simp]
theorem qgtAmariBase_m_connection_one
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) :
    AmariBase.m_connection (qgtAmariBase ψ X Y) 1 =
      -fubiniStudyMetric ψ X Y := by
  simp [AmariBase.m_connection, qgtAmariBase,
    quantumTrace_horizontalGramMatrix_re_eq_fubiniStudyMetric]

/--
The QGT metric readout as a section of any finite-dimensional real determinant
line.
-/
def qgtDeterminantSection
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) : DeterminantLine V :=
  fubiniStudyMetric ψ X Y

/-- The QGT determinant-line readout has the native canonical conformal weight one. -/
theorem qgtDeterminantSection_hasConformalWeight_one
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) :
    HasConformalWeight (V := V) 1
      (qgtDeterminantSection (V := V) ψ X Y) := by
  exact hasConformalWeight_one
    (qgtDeterminantSection (V := V) ψ X Y)

/-- Exact Weyl/dilation law for the projective QGT determinant-line readout. -/
theorem weylAction_qgtDeterminantSection
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : V ≃ₗ[ℝ] V)
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) :
    weylAction f (qgtDeterminantSection (V := V) ψ X Y) =
      Dilation (volumeScale f) (qgtDeterminantSection (V := V) ψ X Y) := by
  exact weylAction_eq_dilation_volumeScale f
    (qgtDeterminantSection (V := V) ψ X Y)

/--
Finite stress-domain instantiation using the exact QGT trace as the scalar
potential channel and zero density derivative/connection variation.
-/
def qgtTraceStressDatum
    (metric : InfoGeometry.Physics.Section34StrengthenedFormalism.SpacetimeIndex →
      InfoGeometry.Physics.Section34StrengthenedFormalism.SpacetimeIndex → ClassicalScalar)
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) : DomainSeparatedStressDatum :=
  compactStressDatum metric (fun _ => 0)
    (quantumTraceToClassical (horizontalGramMatrix ψ X Y))

/-- The scalar potential carried by the finite stress datum is exactly the QGT. -/
theorem qgtTraceStressDatum_potential_eq_QGT
    (metric : InfoGeometry.Physics.Section34StrengthenedFormalism.SpacetimeIndex →
      InfoGeometry.Physics.Section34StrengthenedFormalism.SpacetimeIndex → ClassicalScalar)
    (ψ : NormalizedState QubitH)
    (X Y : EndQ) :
    (qgtTraceStressDatum metric ψ X Y).potential = QGT ψ X Y := by
  change quantumTraceToClassical (horizontalGramMatrix ψ X Y) = QGT ψ X Y
  exact quantumTrace_horizontalGramMatrix_eq_QGT ψ X Y

/--
The finite QGT stress readout is symmetric whenever the supplied classical
metric table is symmetric; no additional quantum symmetry hypothesis is
needed because the connection-variation channel is identically zero.
-/
theorem qgtTraceStressDatum_fullStress_symmetric
    (metric : InfoGeometry.Physics.Section34StrengthenedFormalism.SpacetimeIndex →
      InfoGeometry.Physics.Section34StrengthenedFormalism.SpacetimeIndex → ClassicalScalar)
    (hmetric : ∀ μ ν, metric μ ν = metric ν μ)
    (ψ : NormalizedState QubitH)
    (X Y : EndQ)
    (μ ν : InfoGeometry.Physics.Section34StrengthenedFormalism.SpacetimeIndex) :
    (qgtTraceStressDatum metric ψ X Y).fullStress μ ν =
      (qgtTraceStressDatum metric ψ X Y).fullStress ν μ := by
  apply DomainSeparatedStressDatum.fullStress_symmetric
  · exact hmetric
  · intro a b
    rfl

/--
Complete finite projective-QGT classical-readout packet.
-/
theorem projectiveQGT_classicalReadout_packet
    (metric : InfoGeometry.Physics.Section34StrengthenedFormalism.SpacetimeIndex →
      InfoGeometry.Physics.Section34StrengthenedFormalism.SpacetimeIndex → ClassicalScalar)
    (hmetric : ∀ μ ν, metric μ ν = metric ν μ)
    (ψ : NormalizedState QubitH)
    (X Y : EndQ)
    (μ ν : InfoGeometry.Physics.Section34StrengthenedFormalism.SpacetimeIndex) :
    quantumTraceToClassical (horizontalGramMatrix ψ X Y) = QGT ψ X Y ∧
    (qgtAmariBase ψ X Y).e_connection 1 = fubiniStudyMetric ψ X Y ∧
    AmariBase.m_connection (qgtAmariBase ψ X Y) 1 = -fubiniStudyMetric ψ X Y ∧
    (qgtTraceStressDatum metric ψ X Y).fullStress μ ν =
      (qgtTraceStressDatum metric ψ X Y).fullStress ν μ := by
  exact ⟨
    quantumTrace_horizontalGramMatrix_eq_QGT ψ X Y,
    qgtAmariBase_e_connection_one ψ X Y,
    qgtAmariBase_m_connection_one ψ X Y,
    qgtTraceStressDatum_fullStress_symmetric metric hmetric ψ X Y μ ν⟩

end InfoGeometry.QuantumGeometry.Projective.ClassicalTraceReadout

end noncomputable section
