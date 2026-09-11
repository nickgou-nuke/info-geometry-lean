import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.FilteredHestenesGlobalOperator

open InfoGeometry.Krein
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.FilteredHestenesKreinColimit

/-- Compatible continuous-linear operators on the finite stages of a
Hestenes--Krein filtered cone. -/
structure LinearFamily (C : HestenesKreinCone) where
  op : ∀ n, DoubledSpace (C.Base n) →L[ℝ] DoubledSpace (C.Base n)
  op_hestenes :
    ∀ n, IsHestenesHolomorphicDifferential
      (E := C.Base n) (F := C.Base n) (op n)
  op_bond :
    ∀ n, (C.bond n).comp (op n) = (op (n + 1)).comp (C.bond n)

/-- The cone maps cover the chosen filtered carrier.  This is the concrete
joint-epimorphism condition needed for uniqueness of descended maps. -/
def JointlySurjective (C : HestenesKreinCone) : Prop :=
  ∀ y : DoubledSpace C.LimitBase, ∃ n x, C.ι n x = y

namespace LinearFamily

variable {C : HestenesKreinCone} (F : LinearFamily C)

/-- A candidate global continuous-linear operator descends the finite family
when it agrees on every canonical stage image. -/
def IsGlobalDescent
    (T : DoubledSpace C.LimitBase →L[ℝ] DoubledSpace C.LimitBase) : Prop :=
  ∀ n x, T (C.ι n x) = C.ι n (F.op n x)

/-- A descended operator is unique when the cone maps are jointly
surjective. -/
theorem globalDescent_unique
    (hsurj : JointlySurjective C)
    {T U : DoubledSpace C.LimitBase →L[ℝ] DoubledSpace C.LimitBase}
    (hT : F.IsGlobalDescent T)
    (hU : F.IsGlobalDescent U) :
    T = U := by
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨n, x, rfl⟩ := hsurj y
  rw [hT n x, hU n x]

/-- Pointwise Hestenes law for each finite-stage operator. -/
theorem op_clockAxis (n : ℕ) (x : DoubledSpace (C.Base n)) :
    F.op n (clockAxis (E := C.Base n) x) =
      clockAxis (E := C.Base n) (F.op n x) := by
  have h := congrArg
    (fun L : DoubledSpace (C.Base n) →L[ℝ] DoubledSpace (C.Base n) => L x)
    (F.op_hestenes n)
  simpa [ContinuousLinearMap.comp_apply] using h

/-- Joint surjectivity and finite-stage Hestenes compatibility force every
global descent to commute with the global clock axis. -/
theorem globalDescent_hestenes
    (hsurj : JointlySurjective C)
    (T : DoubledSpace C.LimitBase →L[ℝ] DoubledSpace C.LimitBase)
    (hT : F.IsGlobalDescent T) :
    IsHestenesHolomorphicDifferential
      (E := C.LimitBase) (F := C.LimitBase) T := by
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨n, x, rfl⟩ := hsurj y
  change
    T (clockAxis (E := C.LimitBase) (C.ι n x)) =
      clockAxis (E := C.LimitBase) (T (C.ι n x))
  have hι_phase_apply :
      ∀ v : DoubledSpace (C.Base n),
        C.ι n (clockAxis (E := C.Base n) v) =
          clockAxis (E := C.LimitBase) (C.ι n v) := by
    intro v
    have h := congrArg
      (fun L : DoubledSpace (C.Base n) →L[ℝ] DoubledSpace C.LimitBase => L v)
      (C.ι_hestenes n)
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    T (clockAxis (E := C.LimitBase) (C.ι n x))
        = T (C.ι n (clockAxis (E := C.Base n) x)) := by
            rw [hι_phase_apply x]
    _ = C.ι n (F.op n (clockAxis (E := C.Base n) x)) := hT n _
    _ = C.ι n (clockAxis (E := C.Base n) (F.op n x)) := by
          rw [F.op_clockAxis n x]
    _ = clockAxis (E := C.LimitBase) (C.ι n (F.op n x)) :=
          hι_phase_apply (F.op n x)
    _ = clockAxis (E := C.LimitBase) (T (C.ι n x)) := by rw [hT n x]

/-- A descended global operator is Cauchy-analytic at every point of the
filtered carrier. -/
def globalDescentCauchyAnalyticAt
    (hsurj : JointlySurjective C)
    (T : DoubledSpace C.LimitBase →L[ℝ] DoubledSpace C.LimitBase)
    (hT : F.IsGlobalDescent T)
    (y : DoubledSpace C.LimitBase) :
    CauchyAnalyticAt
      (clockPhaseStructure C.LimitBase)
      (clockPhaseStructure C.LimitBase)
      (fun z => T z) y :=
  CauchyAnalyticAt.ofContinuousLinearMap
    (clockPhaseStructure C.LimitBase)
    (clockPhaseStructure C.LimitBase)
    T
    (F.globalDescent_hestenes hsurj T hT)
    y

@[simp] theorem globalDescentCauchyAnalyticAt_deriv
    (hsurj : JointlySurjective C)
    (T : DoubledSpace C.LimitBase →L[ℝ] DoubledSpace C.LimitBase)
    (hT : F.IsGlobalDescent T)
    (y : DoubledSpace C.LimitBase) :
    (F.globalDescentCauchyAnalyticAt hsurj T hT y).deriv = T :=
  rfl

end LinearFamily

end InfoGeometry.Canonical.FilteredHestenesGlobalOperator
