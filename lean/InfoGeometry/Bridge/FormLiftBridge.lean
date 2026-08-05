import Mathlib.Tactic
import Mathlib
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Topology.EckmannDiscreteHodge
import InfoGeometry.Canonical.DeRhamFenchelLegendre
import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.Geometry.FiniteDefectStokesModel

open Matrix
open Finsupp
open InfoGeometry.Topology.EckmannDiscreteHodge
open InfoGeometry.Canonical.DeRhamFenchelLegendre
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Geometry.FiniteDefectStokesModel

noncomputable section

namespace InfoGeometry.Bridge.FormLiftBridge

/-- A Finsupp-based 0-form: a finitely supported function from vertices to the base ring. -/
abbrev FinsuppZeroForm (V : Type*) [AddCommGroup V] (R : Type*) [CommRing R] :=
  V →₀ R

/-- A Finsupp-based 1-form: a finitely supported function from edges to the base ring. -/
abbrev FinsuppOneForm (V E : Type*) [AddCommGroup V] [AddCommGroup E] (R : Type*) [CommRing R] :=
  E →₀ R

/-- A Finsupp-based 2-form: a finitely supported function from faces to the base ring. -/
abbrev FinsuppTwoForm (V E F : Type*) [AddCommGroup V] [AddCommGroup E] [AddCommGroup F] (R : Type*) [CommRing R] :=
  F →₀ R

/-- The exterior derivative d₀ from 0-forms to 1-forms, lifted from the finite-matrix d0.
    d₀ ω (e : E) = ω (target e) - ω (source e) -/
def finsupp_d0 {V E : Type*} [AddCommGroup V] [AddCommGroup E] [Fintype V] [Fintype E]
    {R : Type*} [CommRing R]
    (d0_mat : Matrix E V R) (ω : FinsuppZeroForm V R) : FinsuppOneForm V E R :=
  Finsupp.onFinset Finset.univ (fun e => ∑ v, d0_mat e v * ω v) (by simp)

/-- The exterior derivative d₁ from 1-forms to 2-forms, lifted from the finite-matrix d1.
    d₁ ω (f : F) = ∑ e ∈ boundary f, ω e -/
def finsupp_d1 {V E F : Type*} [AddCommGroup V] [AddCommGroup E] [AddCommGroup F]
    [Fintype E] [Fintype F] {R : Type*} [CommRing R]
    (d1_mat : Matrix F E R) (ω : FinsuppOneForm V E R) : FinsuppTwoForm V E F R :=
  Finsupp.onFinset Finset.univ (fun f => ∑ e, d1_mat f e * ω e) (by simp)

/-- The De Rham complex structure using Finsupp forms, backed by finite matrices d0/d1. -/
class FinsuppDeRhamComplex (V E F : Type*) [AddCommGroup V] [AddCommGroup E] [AddCommGroup F]
    [Fintype V] [Fintype E] [Fintype F] (R : Type*) [CommRing R] where
  d0_mat : Matrix E V R
  d1_mat : Matrix F E R
  complex_condition : d1_mat * d0_mat = 0
  d0 : FinsuppZeroForm V R → FinsuppOneForm V E R
  d1 : FinsuppOneForm V E R → FinsuppTwoForm V E F R
  d0_spec : ∀ ω, d0 ω = finsupp_d0 d0_mat ω
  d1_spec : ∀ ω, d1 ω = finsupp_d1 d1_mat ω
  d_squared_zero : ∀ (f : FinsuppZeroForm V R) (x : F), d1 (d0 f) x = (0 : R)

/-- The Information Geometry Metric (Hessian) as a symmetric 2-form on Finsupp. -/
class FinsuppHessianMetric (V E F : Type*) [AddCommGroup V] [AddCommGroup E] [AddCommGroup F]
    [Fintype V] [Fintype E] [Fintype F] (R : Type*) [CommRing R]
    [FinsuppDeRhamComplex V E F R] (logQ : V → R) where
  metric : V → V → R
  metric_eq_symmetric_differential : ∀ x y, metric x y = metric y x

/-- The finite defect model provides concrete d0/d1 matrices for the 2×2 model. -/
def finiteDefectD0 : Matrix (Fin 1) (Fin 1) ℝ :=
  !![1]

def finiteDefectD1 : Matrix (Fin 1) (Fin 1) ℝ :=
  !![0]

/-- The finite defect De Rham complex instance for the 2×2 model. -/
instance : FinsuppDeRhamComplex Unit Unit Unit ℝ where
  d0_mat := (fun _ _ => (1 : ℝ))
  d1_mat := (fun _ _ => (0 : ℝ))
  complex_condition := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, finiteDefectD0, finiteDefectD1]
    <;> norm_num
  d0 := fun ω => finsupp_d0 (fun _ _ => (1 : ℝ)) ω
  d1 := fun ω => finsupp_d1 (fun _ _ => (0 : ℝ)) ω
  d0_spec := by intro ω; rfl
  d1_spec := by intro ω; rfl
  d_squared_zero := by
    intro f x
    simp [finsupp_d1, finsupp_d0, Fin.sum_univ_succ]
    <;> simp_all [Matrix.mul_apply, Fin.sum_univ_succ]
    <;> norm_num

/-- The Hestenes geometric derivative lifted to Finsupp forms. -/
def finsuppGeometricDerivative {V E F : Type*} [AddCommGroup V] [AddCommGroup E] [AddCommGroup F]
    [Fintype V] [Fintype E] [Fintype F]
    {R : Type*} [CommRing R] [FinsuppDeRhamComplex V E F R]
    (ω : FinsuppOneForm V E R) : FinsuppTwoForm V E F R :=
  (inferInstance : FinsuppDeRhamComplex V E F R).d1 ω

/-- A Finsupp-based geometric integral backend mirroring the BilingualAnalyticity structure. -/
structure FinsuppGeometricIntegralBackend
    (Region Point Tangent Value : Type*)
    [AddCommGroup Value] [Module ℝ Value] where
  boundaryIntegral :
    Region → (Point → Tangent → Value) → Value
  volumeIntegral :
    Region → (Point → Value) → Value
  geometricDerivative :
    (Point → Tangent → Value) → Point → Value
  stokes_eq :
    ∀ Ω ω,
      boundaryIntegral Ω ω =
        volumeIntegral Ω (geometricDerivative ω)
  volumeIntegral_zero_of_pointwise_zero :
    ∀ Ω f,
      (∀ p : Point, f p = 0) →
        volumeIntegral Ω f = 0

/-- Closed geometric form predicate for Finsupp backend. -/
def FinsuppIsClosedGeometricForm
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    (I : FinsuppGeometricIntegralBackend Region Point Tangent Value)
    (ω : Point → Tangent → Value) : Prop :=
  ∀ p : Point, I.geometricDerivative ω p = 0

/-- Boundary integral vanishes for closed forms in the Finsupp backend. -/
theorem finsupp_boundaryIntegral_eq_zero_of_closed
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    (I : FinsuppGeometricIntegralBackend Region Point Tangent Value)
    (Ω : Region)
    (ω : Point → Tangent → Value)
    (hclosed : FinsuppIsClosedGeometricForm I ω) :
  I.boundaryIntegral Ω ω = 0 := by
  rw [I.stokes_eq Ω ω]
  exact I.volumeIntegral_zero_of_pointwise_zero Ω
    (I.geometricDerivative ω)
    hclosed

/-- The concrete finite defect backend lifted to Finsupp forms. -/
def finiteDefectFinsuppBackend : FinsuppGeometricIntegralBackend Unit Unit Unit (Matrix (Fin 2) (Fin 2) ℝ) where
  boundaryIntegral := fun _ ω => ω () ()
  volumeIntegral := fun _ f => f ()
  geometricDerivative := fun ω _ => ω () ()
  stokes_eq := by
    intro Ω ω
    rfl
  volumeIntegral_zero_of_pointwise_zero := by
    intro Ω f hf
    simp [hf]

/-- The operator-valued 1-form (Cauchy form) lifted to Finsupp. -/
def finsuppOperatorOneForm
    {Point Tangent Value : Type*} (F : Point → Value)
    (leftAction : Value → Tangent → Value) :
    Point → Tangent → Value :=
  fun Z V => leftAction (F Z) V

/-- The Hestenes form calibration using Finsupp forms.

This declaration carries only a function, so the native function type is the
owner. The old `.formOf` projection is retained as a compatibility accessor.
-/
abbrev FinsuppHestenesFormCalibration (Point Tangent Value : Type*) :=
  (Point → Value) → (Point → Tangent → Value)

abbrev FinsuppHestenesFormCalibration.formOf
    {Point Tangent Value : Type*}
    (C : FinsuppHestenesFormCalibration Point Tangent Value) :
    (Point → Value) → (Point → Tangent → Value) := C

end InfoGeometry.Bridge.FormLiftBridge
