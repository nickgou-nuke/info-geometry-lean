import InfoGeometry.Canonical.FilteredHestenesGlobalOperator

noncomputable section

namespace InfoGeometry.Canonical.FilteredHestenesGlobalPhase

open InfoGeometry.Krein
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredHestenesGlobalOperator

/-- The compatible finite-stage family formed by the Hestenes clock axes. -/
def clockAxisFamily (C : HestenesKreinCone) : LinearFamily C where
  op := fun n => clockAxis (E := C.Base n)
  op_hestenes := by
    intro n
    rfl
  op_bond := by
    intro n
    exact C.bond_hestenes n

namespace HestenesKreinCone

variable (C : HestenesKreinCone)

/-- Every finite-stage member of the clock-axis family is the canonical
Hestenes phase operator. -/
@[simp] theorem clockAxisFamily_op (n : ℕ) :
    (clockAxisFamily C).op n = clockAxis (E := C.Base n) :=
  rfl

/-- The global clock axis agrees with the finite clock axis on every canonical
cone image. -/
theorem globalClockAxis_isDescent :
    (clockAxisFamily C).IsGlobalDescent
      (clockAxis (E := C.LimitBase)) := by
  intro n x
  have h := congrArg
    (fun L : DoubledSpace (C.Base n) →L[ℝ] DoubledSpace C.LimitBase => L x)
    (C.ι_hestenes n)
  simpa [clockAxisFamily, ContinuousLinearMap.comp_apply] using h.symm

/-- Joint surjectivity characterizes the global clock axis uniquely among
continuous-linear descents of the finite phase family. -/
theorem globalClockAxis_unique
    (hsurj : JointlySurjective C)
    (T : DoubledSpace C.LimitBase →L[ℝ] DoubledSpace C.LimitBase)
    (hT : (clockAxisFamily C).IsGlobalDescent T) :
    T = clockAxis (E := C.LimitBase) :=
  (clockAxisFamily C).globalDescent_unique
    hsurj hT (globalClockAxis_isDescent C)

/-- The descended global Hestenes phase squares to minus the identity. -/
theorem globalClockAxis_sq_neg_id :
    (clockAxis (E := C.LimitBase)).comp
        (clockAxis (E := C.LimitBase)) =
      -(ContinuousLinearMap.id ℝ (DoubledSpace C.LimitBase)) := by
  exact (clockPhaseStructure C.LimitBase).K_square

/-- The global clock axis is Hestenes-holomorphic. -/
theorem globalClockAxis_hestenes :
    IsHestenesHolomorphicDifferential
      (E := C.LimitBase) (F := C.LimitBase)
      (clockAxis (E := C.LimitBase)) := by
  rfl

/-- The global filtered-colimit phase operator is Cauchy-analytic at every
point, with derivative equal to the clock axis itself. -/
def globalClockAxisCauchyAnalyticAt
    (y : DoubledSpace C.LimitBase) :
    CauchyAnalyticAt
      (clockPhaseStructure C.LimitBase)
      (clockPhaseStructure C.LimitBase)
      (fun z => clockAxis (E := C.LimitBase) z) y :=
  CauchyAnalyticAt.ofContinuousLinearMap
    (clockPhaseStructure C.LimitBase)
    (clockPhaseStructure C.LimitBase)
    (clockAxis (E := C.LimitBase))
    (globalClockAxis_hestenes C)
    y

@[simp] theorem globalClockAxisCauchyAnalyticAt_deriv
    (y : DoubledSpace C.LimitBase) :
    (globalClockAxisCauchyAnalyticAt C y).deriv =
      clockAxis (E := C.LimitBase) :=
  rfl

/-- The global phase derivative satisfies its Cauchy--Riemann law. -/
theorem globalClockAxis_cauchyRiemann
    (y v : DoubledSpace C.LimitBase) :
    (globalClockAxisCauchyAnalyticAt C y).deriv
        (clockAxis (E := C.LimitBase) v) =
      clockAxis (E := C.LimitBase)
        ((globalClockAxisCauchyAnalyticAt C y).deriv v) :=
  (globalClockAxisCauchyAnalyticAt C y).cauchyRiemann_apply v

end HestenesKreinCone

end InfoGeometry.Canonical.FilteredHestenesGlobalPhase
