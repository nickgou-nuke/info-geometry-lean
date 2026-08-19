/- Source API target:
   :contentReference[oaicite:0]{index=0}
-/

import InfoGeometry.QuantumGeometry.Projective.QGT
import InfoGeometry.QuantumGeometry.Projective.Basic

/-!
# QuantumGeometry namespace compatibility owner for the complex projective QGT

This module exposes the complex projective Hilbert-space quantum geometric
tensor under the namespace requested by the `QuantumGeometry` lane:

`InfoGeometry.QuantumGeometry.Projective`.

The mathematical owner is
`InfoGeometry.Quantum.ProjectiveGeometricTensor`. This file does not duplicate
its analytic proofs. Instead it gives definitionally transparent aliases and
theorem wrappers with complete proof terms, preserving the requested API while
keeping a single theorem owner.

The historical extra structure field `map_lie'` is not reintroduced: bracket
preservation already belongs to Mathlib's native `LieHom`. A theorem with the
same dot-notation surface is supplied and proved from the native bracket law
through the established projective-QGT owner.
-/

noncomputable section

open ContinuousLinearMap
open InnerProductSpace

namespace InfoGeometry.QuantumGeometry.Projective

namespace Base := InfoGeometry.QuantumGeometry.Projective

variable {H : Type*}
variable
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-- Compatibility alias for the native normalized-state owner. -/
abbrev NormalizedState
    (H : Type*)
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] :=
  Base.NormalizedState H

/-- Compatibility alias for the complex quantum geometric tensor. -/
abbrev QGT
    (ψ : NormalizedState H)
    (X Y : EndH) : ℂ :=
  Base.QGT ψ X Y

/-- Compatibility alias for the Fubini--Study metric component. -/
abbrev fubiniStudyMetric
    (ψ : NormalizedState H)
    (X Y : EndH) : ℝ :=
  Base.fubiniStudyMetric ψ X Y

/-- Compatibility alias for the Berry-curvature component. -/
abbrev berryCurvature
    (ψ : NormalizedState H)
    (X Y : EndH) : ℝ :=
  Base.berryCurvature ψ X Y

/-- Compatibility alias for horizontal projection. -/
abbrev projOrth
    (ψ : NormalizedState H)
    (X : EndH) : H :=
  Base.projOrth ψ X

/-- Compatibility alias for phase rotation of a normalized representative. -/
abbrev phaseRotate
    (ψ : NormalizedState H)
    (c : ℂ)
    (hc : starRingEnd ℂ c * c = 1) :
    NormalizedState H :=
  Base.phaseRotate ψ c hc

/-- Compatibility alias for the bounded-operator commutator. -/
abbrev opCommutator
    (X Y : EndH) : EndH :=
  Base.opCommutator X Y

/-- Compatibility alias for a skew-adjoint real Lie representation. -/
abbrev SkewAdjointLieRep
    (𝔤 : Type*)
    [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤] :=
  Base.SkewAdjointLieRep H 𝔤

namespace NormalizedState

/-- A normalized representative has norm one. -/
@[simp]
theorem norm_vec_eq_one
    (ψ : NormalizedState H) :
    ‖ψ.vec‖ = 1 := by
  exact
    Base.NormalizedState.norm_vec_eq_one ψ

end NormalizedState

/--
Horizontal projection is orthogonal to the state representative.
-/
@[simp]
theorem inner_state_projOrth
    (ψ : NormalizedState H)
    (X : EndH) :
    inner ψ.vec (projOrth ψ X) = 0 := by
  exact
    Base.inner_state_projOrth ψ X

/--
Scalar identity directions are vertical and have zero horizontal part.
-/
@[simp]
theorem projOrth_smul_id
    (ψ : NormalizedState H)
    (c : ℂ) :
    projOrth ψ
        (c • ContinuousLinearMap.id ℂ H)
      =
    0 := by
  exact
    Base.projOrth_smul_id ψ c

/--
The QGT is the Gram form of horizontal projections.
-/
theorem QGT_eq_inner_projOrth
    (ψ : NormalizedState H)
    (X Y : EndH) :
    QGT ψ X Y =
      inner
        (projOrth ψ X)
        (projOrth ψ Y) := by
  exact
    Base.QGT_eq_inner_projOrth ψ X Y

/--
QGT vanishes on a vertical direction in the first slot.
-/
@[simp]
theorem QGT_smul_id_left
    (ψ : NormalizedState H)
    (c : ℂ)
    (Y : EndH) :
    QGT ψ
        (c • ContinuousLinearMap.id ℂ H)
        Y
      =
    0 := by
  exact
    Base.QGT_smul_id_left ψ c Y

/--
QGT vanishes on a vertical direction in the second slot.
-/
@[simp]
theorem QGT_smul_id_right
    (ψ : NormalizedState H)
    (c : ℂ)
    (X : EndH) :
    QGT ψ
        X
        (c • ContinuousLinearMap.id ℂ H)
      =
    0 := by
  exact
    Base.QGT_smul_id_right ψ c X

/--
Hermitian symmetry of the complex QGT.
-/
theorem QGT_conj_symm
    (ψ : NormalizedState H)
    (X Y : EndH) :
    starRingEnd ℂ (QGT ψ X Y) =
      QGT ψ Y X := by
  exact
    Base.QGT_conj_symm ψ X Y

/--
Symmetry of the Fubini--Study metric.
-/
theorem fubiniStudyMetric_symm
    (ψ : NormalizedState H)
    (X Y : EndH) :
    fubiniStudyMetric ψ X Y =
      fubiniStudyMetric ψ Y X := by
  exact
    Base.fubiniStudyMetric_symm ψ X Y

/--
Skew-symmetry of Berry curvature.
-/
theorem berryCurvature_skew
    (ψ : NormalizedState H)
    (X Y : EndH) :
    berryCurvature ψ Y X =
      -berryCurvature ψ X Y := by
  exact
    Base.berryCurvature_skew ψ X Y

/--
Berry curvature vanishes on the diagonal.
-/
@[simp]
theorem berryCurvature_self
    (ψ : NormalizedState H)
    (X : EndH) :
    berryCurvature ψ X X = 0 := by
  exact
    Base.berryCurvature_self ψ X

/--
The diagonal metric equals the squared norm of the horizontal vector.
-/
theorem fubiniStudyMetric_self_eq_normSq
    (ψ : NormalizedState H)
    (X : EndH) :
    fubiniStudyMetric ψ X X =
      ‖projOrth ψ X‖ ^ 2 := by
  exact
    Base.fubiniStudyMetric_self_eq_normSq ψ X

/--
Positivity of the diagonal Fubini--Study metric.
-/
theorem fubiniStudyMetric_self_nonneg
    (ψ : NormalizedState H)
    (X : EndH) :
    0 ≤ fubiniStudyMetric ψ X X := by
  exact
    Base.fubiniStudyMetric_self_nonneg ψ X

/--
Horizontal projection is covariant under a unit-modulus phase rotation.
-/
theorem projOrth_phaseRotate
    (ψ : NormalizedState H)
    (X : EndH)
    (c : ℂ)
    (hc : starRingEnd ℂ c * c = 1) :
    projOrth
        (phaseRotate ψ c hc)
        X
      =
    c • projOrth ψ X := by
  exact
    Base.projOrth_phaseRotate
      ψ X c hc

/--
The QGT is invariant under phase rotation of the normalized representative.
-/
theorem QGT_phase_invariant
    (ψ : NormalizedState H)
    (X Y : EndH)
    (c : ℂ)
    (hc : starRingEnd ℂ c * c = 1) :
    QGT
        (phaseRotate ψ c hc)
        X
        Y
      =
    QGT ψ X Y := by
  exact
    Base.QGT_phase_invariant
      ψ X Y c hc

/--
The Fubini--Study metric is phase invariant.
-/
theorem fubiniStudyMetric_phase_invariant
    (ψ : NormalizedState H)
    (X Y : EndH)
    (c : ℂ)
    (hc : starRingEnd ℂ c * c = 1) :
    fubiniStudyMetric
        (phaseRotate ψ c hc)
        X
        Y
      =
    fubiniStudyMetric ψ X Y := by
  exact
    Base.fubiniStudyMetric_phase_invariant
      ψ X Y c hc

/--
Berry curvature is phase invariant.
-/
theorem berryCurvature_phase_invariant
    (ψ : NormalizedState H)
    (X Y : EndH)
    (c : ℂ)
    (hc : starRingEnd ℂ c * c = 1) :
    berryCurvature
        (phaseRotate ψ c hc)
        X
        Y
      =
    berryCurvature ψ X Y := by
  exact
    Base.berryCurvature_phase_invariant
      ψ X Y c hc

/--
Native Cauchy--Schwarz inequality for the QGT.
-/
theorem QGT_cauchy_schwarz
    (ψ : NormalizedState H)
    (X Y : EndH) :
    Complex.normSq (QGT ψ X Y) ≤
      fubiniStudyMetric ψ X X *
        fubiniStudyMetric ψ Y Y := by
  exact
    Base.QGT_cauchy_schwarz
      ψ X Y

/--
Pythagorean decomposition of the QGT norm.
-/
theorem QGT_normSq_decomposition
    (ψ : NormalizedState H)
    (X Y : EndH) :
    Complex.normSq (QGT ψ X Y) =
      fubiniStudyMetric ψ X Y ^ 2 +
        (1 / 4 : ℝ) *
          berryCurvature ψ X Y ^ 2 := by
  exact
    Base.QGT_normSq_decomposition
      ψ X Y

/--
Full geometric Robertson--Schroedinger inequality.
-/
theorem robertson_schrodinger_qgt_bound
    (ψ : NormalizedState H)
    (X Y : EndH) :
    fubiniStudyMetric ψ X X *
        fubiniStudyMetric ψ Y Y
      ≥
    fubiniStudyMetric ψ X Y ^ 2 +
      (1 / 4 : ℝ) *
        berryCurvature ψ X Y ^ 2 := by
  exact
    Base.robertson_schrodinger_qgt_bound
      ψ X Y

/--
Berry-curvature-only uncertainty bound.
-/
theorem berry_curvature_uncertainty_bound
    (psi : NormalizedState H)
    (X Y : EndH) :
    fubiniStudyMetric psi X X *
        fubiniStudyMetric psi Y Y
      ≥
    (1 / 4 : ℝ) *
      berryCurvature psi X Y ^ 2 := by
  exact
    Base.berry_curvature_uncertainty_bound
      psi X Y

/--
Pointwise formula for the operator commutator.
-/
@[simp]
theorem opCommutator_apply
    (X Y : EndH)
    (v : H) :
    opCommutator X Y v =
      X (Y v) - Y (X v) := by
  exact
    Base.opCommutator_apply
      X Y v

/--
The explicit commutator is Mathlib's associative-ring Lie bracket.
-/
theorem opCommutator_eq_lie
    (X Y : EndH) :
    opCommutator X Y =
      ⁅X, Y⁆ := by
  exact
    Base.opCommutator_eq_lie
      X Y

/--
Inner-product form of skew-adjointness.
-/
theorem inner_apply_eq_neg_inner_apply_of_adjoint_eq_neg
    (X : EndH)
    (hX :
      ContinuousLinearMap.adjoint X = -X)
    (u v : H) :
    inner (X u) v =
      -inner u (X v) := by
  exact
    Base.inner_apply_eq_neg_inner_apply_of_adjoint_eq_neg
      X hX u v

/--
Berry curvature equals the skew-adjoint commutator expectation.
-/
theorem berryCurvature_eq_commutator
    (ψ : NormalizedState H)
    (X Y : EndH)
    (hX :
      ContinuousLinearMap.adjoint X = -X)
    (hY :
      ContinuousLinearMap.adjoint Y = -Y) :
    (berryCurvature ψ X Y : ℂ) *
        Complex.I
      =
    inner ψ.vec
      (opCommutator X Y ψ.vec) := by
  exact
    Base.berryCurvature_eq_commutator
      ψ X Y hX hY

namespace SkewAdjointLieRep

/--
Compatibility theorem replacing the historical redundant `map_lie'`
structure field.

Bracket preservation is supplied by the native `LieHom`.
-/
theorem map_lie'
    {𝔤 : Type*}
    [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤]
    (ρ :
      SkewAdjointLieRep
        (H := H)
        𝔤)
    (X Y : 𝔤) :
    opCommutator
        (ρ.toLieHom X)
        (ρ.toLieHom Y)
      =
    ρ.toLieHom ⁅X, Y⁆ := by
  exact
    Base.SkewAdjointLieRep.opCommutator_map
      ρ X Y

end SkewAdjointLieRep

/--
Berry curvature reads the represented Lie bracket.
-/
theorem berryCurvature_eq_lie_bracket
    {𝔤 : Type*}
    [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤]
    (ρ :
      SkewAdjointLieRep
        (H := H)
        𝔤)
    (ψ : NormalizedState H)
    (X Y : 𝔤) :
    (berryCurvature
        ψ
        (ρ.toLieHom X)
        (ρ.toLieHom Y) : ℂ) *
        Complex.I
      =
    inner ψ.vec
      (ρ.toLieHom ⁅X, Y⁆ ψ.vec) := by
  exact
    Base.berryCurvature_eq_lie_bracket
      ρ ψ X Y

/--
Norm-square form of the Berry/Lie-bracket identity.
-/
theorem lie_bracket_normSq_eq_berry_sq
    {𝔤 : Type*}
    [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤]
    (ρ :
      SkewAdjointLieRep
        (H := H)
        𝔤)
    (ψ : NormalizedState H)
    (X Y : 𝔤) :
    Complex.normSq
        (inner ψ.vec
          (ρ.toLieHom ⁅X, Y⁆ ψ.vec))
      =
    berryCurvature
        ψ
        (ρ.toLieHom X)
        (ρ.toLieHom Y) ^ 2 := by
  exact
    Base.lie_bracket_normSq_eq_berry_sq
      ρ ψ X Y

/--
Full Robertson--Schroedinger bound in represented Lie-bracket form.
-/
theorem lie_rep_robertson_schrodinger_bound
    {𝔤 : Type*}
    [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤]
    (ρ :
      SkewAdjointLieRep
        (H := H)
        𝔤)
    (ψ : NormalizedState H)
    (X Y : 𝔤) :
    fubiniStudyMetric
          ψ
          (ρ.toLieHom X)
          (ρ.toLieHom X)
        *
      fubiniStudyMetric
          ψ
          (ρ.toLieHom Y)
          (ρ.toLieHom Y)
      ≥
    fubiniStudyMetric
          ψ
          (ρ.toLieHom X)
          (ρ.toLieHom Y) ^ 2
        +
      (1 / 4 : ℝ) *
        Complex.normSq
          (inner ψ.vec
            (ρ.toLieHom ⁅X, Y⁆ ψ.vec)) := by
  exact
    Base.lie_rep_robertson_schrodinger_bound
      ρ ψ X Y

/--
Lie-bracket uncertainty bound for a skew-adjoint representation.
-/
theorem lie_rep_uncertainty_bound
    {𝔤 : Type*}
    [LieRing 𝔤]
    [LieAlgebra ℝ 𝔤]
    (ρ :
      SkewAdjointLieRep
        (H := H)
        𝔤)
    (ψ : NormalizedState H)
    (X Y : 𝔤) :
    fubiniStudyMetric
          ψ
          (ρ.toLieHom X)
          (ρ.toLieHom X)
        *
      fubiniStudyMetric
          ψ
          (ρ.toLieHom Y)
          (ρ.toLieHom Y)
      ≥
    (1 / 4 : ℝ) *
      Complex.normSq
        (inner ψ.vec
          (ρ.toLieHom ⁅X, Y⁆ ψ.vec)) := by
  exact
    Base.lie_rep_uncertainty_bound
      ρ ψ X Y

/--
Consolidated theorem packet under the `QuantumGeometry` namespace.
-/
theorem projective_qgt_packet
    (ψ : NormalizedState H)
    (X Y : EndH) :
    QGT ψ X Y =
        inner
          (projOrth ψ X)
          (projOrth ψ Y)
      ∧
    fubiniStudyMetric ψ X Y =
        fubiniStudyMetric ψ Y X
      ∧
    berryCurvature ψ Y X =
        -berryCurvature ψ X Y
      ∧
    Complex.normSq
        (QGT ψ X Y)
      ≤
    fubiniStudyMetric ψ X X *
        fubiniStudyMetric ψ Y Y
      ∧
    fubiniStudyMetric ψ X X *
        fubiniStudyMetric ψ Y Y
      ≥
    fubiniStudyMetric ψ X Y ^ 2 +
      (1 / 4 : ℝ) *
        berryCurvature ψ X Y ^ 2 := by
  exact
    Base.projective_qgt_packet
      ψ X Y

end InfoGeometry.QuantumGeometry.Projective

end noncomputable section
