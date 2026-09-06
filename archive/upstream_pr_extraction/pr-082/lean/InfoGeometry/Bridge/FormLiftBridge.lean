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

theorem finsupp_d1_d0_eq_zero_of_matrix_condition
    {V E F : Type*} [AddCommGroup V] [AddCommGroup E] [AddCommGroup F]
    [Fintype V] [Fintype E] [Fintype F] {R : Type*} [CommRing R]
    (d0_mat : Matrix E V R) (d1_mat : Matrix F E R)
    (h : d1_mat * d0_mat = 0)
    (f : FinsuppZeroForm V R) (x : F) :
    finsupp_d1 d1_mat (finsupp_d0 d0_mat f) x = 0 := by
  classical
  simp [finsupp_d1, finsupp_d0]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y hy
  rw [← Finset.sum_mul]
  have hxy : ∑ e, d1_mat x e * d0_mat e y = 0 := by
    have hxy0 := congrFun (congrFun h x) y
    simpa [Matrix.mul_apply] using hxy0
  rw [hxy, zero_mul]

/-- The De Rham complex structure using Finsupp forms, backed by finite matrices d0/d1. -/
class FinsuppDeRhamComplex (V E F : Type*) [AddCommGroup V] [AddCommGroup E] [AddCommGroup F]
    [Fintype V] [Fintype E] [Fintype F] (R : Type*) [CommRing R] where
  d0_mat : Matrix E V R
  d1_mat : Matrix F E R

def FinsuppDeRhamComplex.d0
    {V E F : Type*} [AddCommGroup V] [AddCommGroup E] [AddCommGroup F]
    [Fintype V] [Fintype E] [Fintype F] {R : Type*} [CommRing R]
    [FinsuppDeRhamComplex V E F R] :
    FinsuppZeroForm V R → FinsuppOneForm V E R :=
  finsupp_d0 (FinsuppDeRhamComplex.d0_mat
    (V := V) (E := E) (F := F) (R := R))

def FinsuppDeRhamComplex.d1
    {V E F : Type*} [AddCommGroup V] [AddCommGroup E] [AddCommGroup F]
    [Fintype V] [Fintype E] [Fintype F] {R : Type*} [CommRing R]
    [FinsuppDeRhamComplex V E F R] :
    FinsuppOneForm V E R → FinsuppTwoForm V E F R :=
  finsupp_d1 (FinsuppDeRhamComplex.d1_mat
    (V := V) (E := E) (F := F) (R := R))

theorem FinsuppDeRhamComplex.d_squared_zero
    {V E F : Type*} [AddCommGroup V] [AddCommGroup E] [AddCommGroup F]
    [Fintype V] [Fintype E] [Fintype F] {R : Type*} [CommRing R]
    [FinsuppDeRhamComplex V E F R]
    (h : (FinsuppDeRhamComplex.d1_mat (V := V) (E := E) (F := F) (R := R)) *
        (FinsuppDeRhamComplex.d0_mat (V := V) (E := E) (F := F) (R := R)) = 0)
    (f : FinsuppZeroForm V R) (x : F) :
    (inferInstance : FinsuppDeRhamComplex V E F R).d1
        ((inferInstance : FinsuppDeRhamComplex V E F R).d0 f) x = 0 := by
  rw [FinsuppDeRhamComplex.d1, FinsuppDeRhamComplex.d0]
  exact finsupp_d1_d0_eq_zero_of_matrix_condition
    (FinsuppDeRhamComplex.d0_mat (V := V) (E := E) (F := F) (R := R))
    (FinsuppDeRhamComplex.d1_mat (V := V) (E := E) (F := F) (R := R))
    h f x

/-- The Hessian symmetry predicate for a finite Finsupp metric. -/
def FinsuppHessianMetric (V E F : Type*) [AddCommGroup V] [AddCommGroup E]
    [AddCommGroup F] [Fintype V] [Fintype E] [Fintype F] (R : Type*) [CommRing R]
    [FinsuppDeRhamComplex V E F R] (logQ : V → R) (metric : V → V → R) : Prop :=
  ∀ x y, metric x y = metric y x

theorem FinsuppHessianMetric.metric_eq_symmetric_differential
    {V E F : Type*} [AddCommGroup V] [AddCommGroup E] [AddCommGroup F]
    [Fintype V] [Fintype E] [Fintype F] {R : Type*} [CommRing R]
    [FinsuppDeRhamComplex V E F R] (logQ : V → R) (metric : V → V → R)
    (hmetric : FinsuppHessianMetric V E F R logQ metric) (x y : V) :
    metric x y = metric y x :=
  hmetric x y

/-- The finite defect model provides concrete d0/d1 matrices for the 2×2 model. -/
def finiteDefectD0 : Matrix (Fin 1) (Fin 1) ℝ :=
  !![1]

def finiteDefectD1 : Matrix (Fin 1) (Fin 1) ℝ :=
  !![0]

/-- The finite defect De Rham complex instance for the 2×2 model. -/
instance : FinsuppDeRhamComplex Unit Unit Unit ℝ where
  d0_mat := (fun _ _ => (1 : ℝ))
  d1_mat := (fun _ _ => (0 : ℝ))

theorem finiteDefect_d_squared_zero
    (f : FinsuppZeroForm Unit ℝ) (x : Unit) :
    (inferInstance : FinsuppDeRhamComplex Unit Unit Unit ℝ).d1
        ((inferInstance : FinsuppDeRhamComplex Unit Unit Unit ℝ).d0 f) x = 0 := by
  apply FinsuppDeRhamComplex.d_squared_zero
  ext i j
  change (∑ k : Unit, (0 : ℝ) * 1) = 0
  simp

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
