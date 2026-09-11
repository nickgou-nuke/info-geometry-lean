import InfoGeometry.Canonical.HestenesAnalyticity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Canonical.HestenesCohomology

/-!
# Hestenes cohomology/readout layer

This file records the real Hestenes replacement for complex-valued cochains.

Operator-valued cochains/readouts on the doubled carrier are phase-compatible
when they commute with the internal phase axis `K = clockAxis`.  This is the
existing `KLinear` owner predicate from `HestenesRealStructures`.

Scalar real readouts `H₂ →L[ℝ] ℝ` are kept separate: the codomain has no
internal `K`-axis, so they are not called `K`-linear unless an explicit
coefficient phase structure is supplied elsewhere.
-/

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.HestenesRealStructures

section OperatorCochains

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Operator-valued Hestenes cochains preserve the internal phase axis `K`. -/
@[rep_depth krein]
abbrev IsHestenesCochainOperator (A : EndH) : Prop :=
  KLinear (E := E) A

/-- Operator-valued Hestenes anticohains reverse the internal phase axis `K`. -/
@[rep_depth krein]
abbrev IsHestenesAnticohainOperator (A : EndH) : Prop :=
  KAntilinear (E := E) A

/-- Packaged K-linear operator-valued real cochain/readout. -/
@[rep_depth krein]
structure HestenesCochainOperator where
  op : EndH
  kLinear : IsHestenesCochainOperator (E := E) op

/-- Packaged K-antilinear operator-valued real cochain/readout. -/
@[rep_depth krein]
structure HestenesAnticohainOperator where
  op : EndH
  kAntilinear : IsHestenesAnticohainOperator (E := E) op

section OmitComplete

omit [CompleteSpace E]

/-- K-linear cochains are exactly Hestenes-analytic symmetry readouts. -/
@[rep_depth krein]
theorem isHestenesCochainOperator_iff_analyticSymmetry (A : EndH) :
    IsHestenesCochainOperator (E := E) A ↔
      IsHestenesAnalyticSymmetry (E := E) A := by
  rfl

/-- The zero operator is a K-linear cochain. -/
@[rep_depth krein]
theorem zero_isHestenesCochainOperator :
    IsHestenesCochainOperator (E := E) (0 : EndH) := by
  simp [IsHestenesCochainOperator, KLinear, IsPhaseLinear]

/-- The identity operator is a K-linear cochain. -/
@[rep_depth krein]
theorem id_isHestenesCochainOperator :
    IsHestenesCochainOperator (E := E) (ContinuousLinearMap.id ℝ H₂) := by
  simp [IsHestenesCochainOperator, KLinear, IsPhaseLinear]

/-- The internal phase axis itself is a K-linear cochain. -/
@[rep_depth krein]
theorem phaseAxis_isHestenesCochainOperator :
    IsHestenesCochainOperator (E := E) (InfoGeometry.Krein.clockAxis (E := E)) :=
  phaseAxisK_isKLinear (E := E)

/-- K-linear cochains are closed under addition. -/
@[rep_depth krein]
theorem add_isHestenesCochainOperator
    {A B : EndH}
    (hA : IsHestenesCochainOperator (E := E) A)
    (hB : IsHestenesCochainOperator (E := E) B) :
    IsHestenesCochainOperator (E := E) (A + B) := by
  unfold IsHestenesCochainOperator KLinear IsPhaseLinear at hA hB ⊢
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hA, hB]

/-- K-linear cochains are closed under real scalar multiplication. -/
@[rep_depth krein]
theorem smul_isHestenesCochainOperator
    (r : ℝ) {A : EndH}
    (hA : IsHestenesCochainOperator (E := E) A) :
    IsHestenesCochainOperator (E := E) (r • A) := by
  unfold IsHestenesCochainOperator KLinear IsPhaseLinear at hA ⊢
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hA]

/-- K-linear cochains are closed under subtraction. -/
@[rep_depth krein]
theorem sub_isHestenesCochainOperator
    {A B : EndH}
    (hA : IsHestenesCochainOperator (E := E) A)
    (hB : IsHestenesCochainOperator (E := E) B) :
    IsHestenesCochainOperator (E := E) (A - B) := by
  unfold IsHestenesCochainOperator KLinear IsPhaseLinear at hA hB ⊢
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, hA, hB]

/-- K-linear cochains are closed under composition. -/
@[rep_depth krein]
theorem comp_isHestenesCochainOperator
    {A B : EndH}
    (hA : IsHestenesCochainOperator (E := E) A)
    (hB : IsHestenesCochainOperator (E := E) B) :
    IsHestenesCochainOperator (E := E) (A.comp B) := by
  unfold IsHestenesCochainOperator KLinear IsPhaseLinear at hA hB ⊢
  calc
    (A.comp B).comp (InfoGeometry.Krein.clockAxis (E := E))
        = A.comp (B.comp (InfoGeometry.Krein.clockAxis (E := E))) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = A.comp ((InfoGeometry.Krein.clockAxis (E := E)).comp B) := by rw [hB]
    _ = (A.comp (InfoGeometry.Krein.clockAxis (E := E))).comp B := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = ((InfoGeometry.Krein.clockAxis (E := E)).comp A).comp B := by rw [hA]
    _ = (InfoGeometry.Krein.clockAxis (E := E)).comp (A.comp B) := by
            simp [ContinuousLinearMap.comp_assoc]

end OmitComplete

/-- K-linear cochains are closed under the Hestenes operator commutator. -/
@[rep_depth krein]
theorem commutator_isHestenesCochainOperator
    {A B : EndH}
    (hA : IsHestenesCochainOperator (E := E) A)
    (hB : IsHestenesCochainOperator (E := E) B) :
    IsHestenesCochainOperator (E := E)
      (hestenesSymmetryCommutator (E := E) A B) :=
  hestenesAnalyticSymmetry_commutator (E := E) hA hB

namespace HestenesCochainOperator

variable (Φ Ψ : HestenesCochainOperator (E := E))

/-- Sum of K-linear cochains. -/
@[rep_depth krein]
noncomputable def add : HestenesCochainOperator (E := E) where
  op := Φ.op + Ψ.op
  kLinear := add_isHestenesCochainOperator (E := E) Φ.kLinear Ψ.kLinear

/-- Real scalar multiple of a K-linear cochain. -/
@[rep_depth krein]
noncomputable def smul (r : ℝ) : HestenesCochainOperator (E := E) where
  op := r • Φ.op
  kLinear := smul_isHestenesCochainOperator (E := E) r Φ.kLinear

/-- Composition of K-linear cochains. -/
@[rep_depth krein]
noncomputable def comp : HestenesCochainOperator (E := E) where
  op := Φ.op.comp Ψ.op
  kLinear := comp_isHestenesCochainOperator (E := E) Φ.kLinear Ψ.kLinear

/-- Commutator of K-linear cochains. -/
@[rep_depth krein]
noncomputable def commutator : HestenesCochainOperator (E := E) where
  op := hestenesSymmetryCommutator (E := E) Φ.op Ψ.op
  kLinear := commutator_isHestenesCochainOperator (E := E) Φ.kLinear Ψ.kLinear

end HestenesCochainOperator

end OperatorCochains

section ScalarReadouts

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- Scalar real readouts on the doubled carrier.  The codomain has no phase axis. -/
@[rep_depth krein]
abbrev ScalarReadout := H₂ →L[ℝ] ℝ

section OmitComplete

omit [CompleteSpace E]

/--
A scalar readout that annihilates the internal phase-axis direction.

This is a real scalar-readout condition, not complex-linearity: the target is
`ℝ`, so there is no codomain `K` for an equation `φ K = K φ`.
-/
@[rep_depth krein]
def PhaseBlindScalarReadout (φ : ScalarReadout (E := E)) : Prop :=
  φ.comp (InfoGeometry.Krein.clockAxis (E := E)) = 0

/-- Pointwise readback of phase-blind scalar readouts. -/
@[rep_depth krein]
theorem phaseBlindScalarReadout_apply
    {φ : ScalarReadout (E := E)}
    (hφ : PhaseBlindScalarReadout (E := E) φ)
    (x : H₂) :
    φ ((InfoGeometry.Krein.clockAxis (E := E)) x) = 0 := by
  exact congrArg (fun F : H₂ →L[ℝ] ℝ => F x) hφ

end OmitComplete

end ScalarReadouts

end InfoGeometry.Canonical.HestenesCohomology
