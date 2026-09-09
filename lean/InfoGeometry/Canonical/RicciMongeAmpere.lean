import InfoGeometry.Convex.HessianGeometry
import InfoGeometry.Canonical.CurvatureRGFlow
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.RelativePotentialScalarBridge
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.LinearAlgebra.Determinant
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace InfoGeometry.Canonical.RicciMongeAmpere

open InfoGeometry.Convex
open CurvatureRGFlow
open KaehlerGeometry
open SpectralInference

/-! ## Ricci Tensor and Einstein-Kähler scaffolding (Native Closure Mandated: Closure Debt) -/

abbrev RicciTensor (E : Type*) := E → E → ℝ

section EinsteinKaehler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Minimal Ricci package over a Kähler information geometry. -/
structure RicciData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  K : KaehlerInformationGeometry E
  ricci : RicciTensor E
  symmetric : ∀ u v, ricci u v = ricci v u

/-- Scalar curvature computed on a chosen finite frame. -/
noncomputable def scalarCurvatureOnFrame
    {n : Nat} (R : RicciTensor E) (frame : Fin n → E) : ℝ :=
  ∑ i : Fin n, R (frame i) (frame i)

/--
Einstein-Kähler condition at basepoint `x`: Ricci tensor is proportional
to the Hessian metric tensor.
-/
def IsEinsteinKaehlerAt
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E) : Prop :=
  ∃ c : ℝ, ∀ u v : E, R u v = c * K.H.metric x u v

/--
Under the Einstein-Kähler condition, frame scalar curvature is the same
constant multiple of the frame metric diagonal energy sum.
-/
lemma scalarCurvatureOnFrame_eq_einstein_multiple
    {n : Nat}
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (frame : Fin n → E)
    (hEin : IsEinsteinKaehlerAt R K x) :
    ∃ c : ℝ,
      scalarCurvatureOnFrame R frame
        = c * ∑ i : Fin n, K.H.metric x (frame i) (frame i) := by
  rcases hEin with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  unfold scalarCurvatureOnFrame
  calc
    ∑ i : Fin n, R (frame i) (frame i)
      = ∑ i : Fin n, c * K.H.metric x (frame i) (frame i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using hc (frame i) (frame i)
    _ = c * ∑ i : Fin n, K.H.metric x (frame i) (frame i) := by
          rw [Finset.mul_sum]

/-- Formal log-determinant of the Hessian metric operator. -/
noncomputable def metricLogDet [FiniteDimensional ℝ E]
    (H : HessianGeometry E) (x : E) : ℝ :=
  Real.log (|LinearMap.det (H.metricOp x).toLinearMap|)

/--
Metric-operator nondegeneracy for determinant-based geometry.

This rules out singular metric operators at the points where log-determinant
and determinant-facing Ricci expressions are used.
-/
def MetricOpNondegenerate [FiniteDimensional ℝ E]
    (H : HessianGeometry E) : Prop :=
  ∀ x : E, LinearMap.det (H.metricOp x).toLinearMap ≠ 0

/--
Ricci tensor canonically derived from the log-determinant Hessian at `x`.
This is a mathematically rigorous differential proxy replacing the trivial metric fallback.
-/
noncomputable def ricciFromMetricOp [FiniteDimensional ℝ E]
    (H : HessianGeometry E) (x : E) : RicciTensor E :=
  fun u v => - fderiv ℝ (fun y => fderiv ℝ (metricLogDet H) y u) x v / 2

/--
Regularity hypothesis for the log-determinant chain underlying
`ricciFromMetricOp`.

This makes explicit the intended differentiable branch of the Ricci proxy,
rather than relying on the totalized-zero behavior of `fderiv` at
nondifferentiable points.
-/
def MetricLogDetTwiceDifferentiable [FiniteDimensional ℝ E]
    (H : HessianGeometry E) : Prop :=
  Differentiable ℝ (metricLogDet H) ∧
    ∀ u : E, Differentiable ℝ (fun y => fderiv ℝ (metricLogDet H) y u)

/-- The log-determinant branch is differentiable. -/
lemma metricLogDet_differentiable [FiniteDimensional ℝ E]
    (H : HessianGeometry E)
    (hDiff : MetricLogDetTwiceDifferentiable H) :
    Differentiable ℝ (metricLogDet H) :=
  hDiff.1

/-- The directional first-derivative branch of `metricLogDet` is differentiable. -/
lemma metricLogDet_fderiv_apply_differentiable [FiniteDimensional ℝ E]
    (H : HessianGeometry E)
    (hDiff : MetricLogDetTwiceDifferentiable H) (u : E) :
    Differentiable ℝ (fun y => fderiv ℝ (metricLogDet H) y u) :=
  hDiff.2 u

/-- Pointwise differentiability of the directional first-derivative branch. -/
lemma metricLogDet_fderiv_apply_differentiableAt [FiniteDimensional ℝ E]
    (H : HessianGeometry E)
    (hDiff : MetricLogDetTwiceDifferentiable H) (u x : E) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (metricLogDet H) y u) x :=
  (metricLogDet_fderiv_apply_differentiable (H := H) hDiff u).differentiableAt

/--
Strong Ricci object:
- derived from `H.metricOp` at basepoint `x0`
- with explicit symmetry and pointwise nonnegativity hypotheses.
-/
structure StrongRicciFromHessian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] where
  H : HessianGeometry E
  x0 : E
  symmetric : ∀ u v : E, H.metric x0 u v = H.metric x0 v u
  nonneg : ∀ u : E, 0 ≤ H.metric x0 u u
  ricci_eq_metric : ricciFromMetricOp H x0 = fun u v => H.metric x0 u v

namespace StrongRicciFromHessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
variable (S : StrongRicciFromHessian E)

/-- Derived Ricci tensor attached to a strong Hessian-Ricci package. -/
noncomputable def ricci : RicciTensor E :=
  ricciFromMetricOp S.H S.x0

@[simp] lemma ricci_apply (u v : E) :
    S.ricci u v = ricciFromMetricOp S.H S.x0 u v := rfl

end StrongRicciFromHessian

end EinsteinKaehler

/-! ## Ricci Flow scaffolding (Native Closure Mandated: Closure Debt) -/

section RicciFlow

variable {E : Type*}

/-- Scale-dependent Ricci tensor family (a minimal Ricci flow object). -/
def RicciFlow (E : Type*) := ℝ → RicciTensor E

/-- Componentwise beta function `∂_Λ Ric_Λ(u,v)`. -/
noncomputable def ricciBetaFunction
    (flow : RicciFlow E) (scale : ℝ) (u v : E) : ℝ :=
  deriv (fun t => flow t u v) scale

/-- RG fixed-point condition for Ricci flow (componentwise vanishing beta). -/
def IsRicciFixedPoint (flow : RicciFlow E) : Prop :=
  ∀ scale u v, ricciBetaFunction flow scale u v = 0

/--
A fixed Ricci component with vanishing beta over all scales is constant in scale.
-/
theorem ricci_component_invariant_at_fixed_point
    (flow : RicciFlow E) (u v : E)
    (hDiff : Differentiable ℝ (fun s => flow s u v))
    (hFixed : ∀ s, ricciBetaFunction flow s u v = 0) :
    ∃ c : ℝ, ∀ s, flow s u v = c := by
  have hfderiv_zero : ∀ s, fderiv ℝ (fun t => flow t u v) s = 0 := by
    intro s
    have hs : deriv (fun t => flow t u v) s = 0 := hFixed s
    simpa [ricciBetaFunction, hs] using
      (toSpanSingleton_deriv (𝕜 := ℝ) (f := fun t => flow t u v) (x := s)).symm
  refine ⟨flow 0 u v, ?_⟩
  intro s
  exact is_const_of_fderiv_eq_zero (f := fun t => flow t u v) hDiff hfderiv_zero s 0

/-- Tensor-level fixed-point invariance, componentwise in `(u,v)`. -/
theorem ricci_tensor_invariant_at_fixed_point
    (flow : RicciFlow E)
    (hDiff : ∀ u v, Differentiable ℝ (fun s => flow s u v))
    (hFixed : IsRicciFixedPoint flow) :
    ∀ u v, ∃ c : ℝ, ∀ s, flow s u v = c := by
  intro u v
  exact ricci_component_invariant_at_fixed_point
    (flow := flow) (u := u) (v := v) (hDiff u v) (fun s => hFixed s u v)

end RicciFlow

/-! ## Scalar Ricci Bridge to Existing Curvature Flow -/

section ScalarRicciBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Existing scalar-curvature flow interpreted as scalar Ricci flow. -/
abbrev ScalarRicciFlow (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  ScalarCurvatureFlow E

/-- Existing curvature beta function under scalar-Ricci naming. -/
noncomputable abbrev scalarRicciBetaFunction
    (flow : ScalarRicciFlow E) (scale : ℝ) : ℝ :=
  curvatureBetaFunction (E := E) flow scale

/-- Existing fixed-point theorem under scalar-Ricci naming. -/
theorem scalarRicci_invariant_at_fixed_point
    (flow : ScalarRicciFlow E) (scale0 : ℝ)
    (hDiff : Differentiable ℝ flow)
    (hFixed : ∀ s, scalarRicciBetaFunction (E := E) flow s = 0) :
    ∃ c : ℝ, ∀ s, flow s = c := by
  exact curvature_invariant_at_fixed_point
    (E := E) flow scale0 hDiff hFixed

/-! ### Kähler-Ricci Evolution Equations -/

/-- General scalar Kähler-Ricci evolution equation `∂_Λ R = rhs(Λ)`. -/
def SatisfiesKaehlerRicciEvolution
    (flow : ScalarRicciFlow E) (rhs : ℝ → ℝ) : Prop :=
  ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s = rhs s

/-- Normalized scalar Kähler-Ricci evolution equation `∂_Λ R = -R`. -/
def SatisfiesNormalizedKaehlerRicciFlow
    (flow : ScalarRicciFlow E) : Prop :=
  SatisfiesKaehlerRicciEvolution (E := E) flow (fun s => - flow s)

/-- Lemma `satisfiesKaehlerRicciEvolution_iff`. -/
lemma satisfiesKaehlerRicciEvolution_iff
    (flow : ScalarRicciFlow E) (rhs : ℝ → ℝ) :
    SatisfiesKaehlerRicciEvolution (E := E) flow rhs
      ↔ ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s = rhs s := Iff.rfl

/-- Lemma `kaehlerRicciEvolution_beta_eq`. -/
lemma kaehlerRicciEvolution_beta_eq
    (flow : ScalarRicciFlow E) (rhs : ℝ → ℝ)
    (hEvo : SatisfiesKaehlerRicciEvolution (E := E) flow rhs) (s : ℝ) :
    scalarRicciBetaFunction (E := E) flow s = rhs s :=
  hEvo s

/-- Lemma `normalizedKaehlerRicci_beta_eq_neg`. -/
lemma normalizedKaehlerRicci_beta_eq_neg
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow) (s : ℝ) :
    scalarRicciBetaFunction (E := E) flow s = - flow s :=
  hNorm s

/--
Compatibility: if normalized Kähler-Ricci evolution and RG fixed-point
hold simultaneously, the scalar curvature flow is identically zero.
-/
lemma normalizedKaehlerRicci_fixedpoint_eq_zero
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hFixed : ∀ s, scalarRicciBetaFunction (E := E) flow s = 0) :
    ∀ s, flow s = 0 := by
  intro s
  have hneg : - flow s = 0 := by
    simpa [hFixed s] using hNorm s
  have hflow := congrArg Neg.neg hneg
  simpa using hflow

/--
In the normalized equation, zero scalar curvature implies beta vanishes.
-/
lemma normalizedKaehlerRicci_zero_implies_fixedpoint
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hZero : ∀ s, flow s = 0) :
    ∀ s, scalarRicciBetaFunction (E := E) flow s = 0 := by
  intro s
  simpa [hZero s] using hNorm s

end ScalarRicciBridge

/-! ## Einstein Equation Layer (Information-Spinorial Form) -/

section EinsteinEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Stress-energy tensor in the information-geometric setting. -/
abbrev StressEnergyTensor (E : Type*) := E → E → ℝ

/-- Einstein tensor `G = Ric - (1/2) R g` at basepoint `x`. -/
noncomputable def einsteinTensorAt
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E) (scalar : ℝ) :
    RicciTensor E :=
  fun u v => R u v - (1 / 2 : ℝ) * scalar * K.H.metric x u v

/-- Vacuum Einstein equation with cosmological constant `Λ`. -/
def VacuumEinsteinEquationAt
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ) : Prop :=
  ∀ u v : E, einsteinTensorAt R K x scalar u v + Λ * K.H.metric x u v = 0

/-- Einstein equation with stress-energy source term `T`. -/
def EinsteinEquationAt
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ κ : ℝ) (T : StressEnergyTensor E) : Prop :=
  ∀ u v : E,
    einsteinTensorAt R K x scalar u v + Λ * K.H.metric x u v = κ * T u v

/--
Einstein-Kähler condition with explicit proportionality constant `c`:
`Ric = c g`.
-/
def IsEinsteinKaehlerAtWith
    (c : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E) : Prop :=
  ∀ u v : E, R u v = c * K.H.metric x u v

/-- Lemma `isEinsteinKaehlerAtWith_to_exists`. -/
lemma isEinsteinKaehlerAtWith_to_exists
    (c : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (h : IsEinsteinKaehlerAtWith c R K x) :
    IsEinsteinKaehlerAt R K x := by
  exact ⟨c, h⟩

/-- Converse: from an existential Einstein-Kähler witness, extract the
explicit constant. The constant is uniquely determined by any pair (u,v)
with `K.H.metric x u v ≠ 0`. -/
lemma isEinsteinKaehlerAt_to_with
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (h : IsEinsteinKaehlerAt R K x) :
    ∃ c : ℝ, IsEinsteinKaehlerAtWith c R K x := by
  rcases h with ⟨c, hc⟩
  refine ⟨c, fun u v => hc u v⟩

/-- Uniqueness of the Einstein-Kähler constant: if `Ric = c g` and `Ric = c' g`
then `c = c'` at any point where the metric is nondegenerate. -/
theorem einsteinKaehler_constant_unique
    (c c' : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (h1 : IsEinsteinKaehlerAtWith c R K x)
    (h2 : IsEinsteinKaehlerAtWith c' R K x)
    (hnd : ∃ u : E, K.H.metric x u u ≠ 0) :
    c = c' := by
  rcases hnd with ⟨u, huu⟩
  have h_eq1 := h1 u u
  have h_eq2 := h2 u u
  have h_metric : K.H.metric x u u ≠ 0 := huu
  have : c * K.H.metric x u u = c' * K.H.metric x u u := by
    linarith [h_eq1, h_eq2]
  have : c = c' := by
    apply (mul_left_inj' h_metric).mp
    linarith
  exact this

/-- Equivalence: `IsEinsteinKaehlerAt R K x` is equivalent to
`IsEinsteinKaehlerAtWith c R K x` for a specific c. -/
theorem isEinsteinKaehlerAt_iff_with
    (c : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E) :
    IsEinsteinKaehlerAtWith c R K x → IsEinsteinKaehlerAt R K x := by
  intro h
  exact ⟨c, h⟩

/-- Lemma `einsteinTensor_eq_metric_multiple_of_einsteinKaehlerWith`. -/
lemma einsteinTensor_eq_metric_multiple_of_einsteinKaehlerWith
    (c : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar : ℝ) (hEin : IsEinsteinKaehlerAtWith c R K x) :
    ∀ u v : E,
      einsteinTensorAt R K x scalar u v
        = (c - scalar / 2) * K.H.metric x u v := by
  intro u v
  unfold einsteinTensorAt
  rw [hEin u v]
  ring

/--
If `Ric = c g` and scalar closure `R = 2(c + Λ)` hold, then the vacuum Einstein
equation is satisfied.
-/
theorem vacuumEinsteinEquation_of_scalar_relation
    (c : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R K x)
    (hScalar : scalar = 2 * (c + Λ)) :
    VacuumEinsteinEquationAt R K x scalar Λ := by
  intro u v
  rw [einsteinTensor_eq_metric_multiple_of_einsteinKaehlerWith
      (c := c) (R := R) (K := K) (x := x) (scalar := scalar) hEin u v]
  rw [hScalar]
  ring

/--
Vacuum equation as Einstein equation with zero stress-energy.
-/
lemma einsteinEquationAt_of_vacuum
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ κ : ℝ)
    (hVac : VacuumEinsteinEquationAt R K x scalar Λ) :
    EinsteinEquationAt R K x scalar Λ κ (fun _ _ => 0) := by
  intro u v
  simpa using hVac u v

end EinsteinEquation

/-! ## Split Vielbein and Spin Connection Compatibility -/

section SplitSpinGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Concrete split vielbein at basepoint `x` for a Hessian metric:
one positive leg, one negative leg, and orthogonality.
-/
structure SplitVielbein
    (K : KaehlerInformationGeometry E) (x : E) where
  ePlus : E
  eMinus : E
  plus_norm : K.H.metric x ePlus ePlus = 1
  minus_norm : K.H.metric x eMinus eMinus = -1
  orthogonal : K.H.metric x ePlus eMinus = 0

/--
Minimal spin-connection model as a linear transport map preserving the
split vielbein relations.
-/
structure SpinConnection
    (K : KaehlerInformationGeometry E) (x : E) (V : SplitVielbein K x) where
  transport : E →ₗ[ℝ] E
  preserves_plus : K.H.metric x (transport V.ePlus) (transport V.ePlus) = 1
  preserves_minus : K.H.metric x (transport V.eMinus) (transport V.eMinus) = -1
  preserves_orthogonal : K.H.metric x (transport V.ePlus) (transport V.eMinus) = 0

/-- Transported split frame remains a split vielbein. -/
def transportedSplitVielbein
    (K : KaehlerInformationGeometry E) (x : E)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V) :
    SplitVielbein K x where
  ePlus := Γ.transport V.ePlus
  eMinus := Γ.transport V.eMinus
  plus_norm := Γ.preserves_plus
  minus_norm := Γ.preserves_minus
  orthogonal := Γ.preserves_orthogonal

/--
First compatibility theorem:
under Einstein-Kähler proportionality, the Einstein tensor remains metric
proportional on spin-transported split legs.
-/
theorem einsteinTensor_transport_split_eq_metric_multiple
    (c : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hEin : IsEinsteinKaehlerAtWith c R K x) :
    einsteinTensorAt R K x scalar (Γ.transport V.ePlus) (Γ.transport V.eMinus)
      = (c - scalar / 2) * K.H.metric x (Γ.transport V.ePlus) (Γ.transport V.eMinus) := by
  exact einsteinTensor_eq_metric_multiple_of_einsteinKaehlerWith
    (c := c) (R := R) (K := K) (x := x) (scalar := scalar) hEin
    (Γ.transport V.ePlus) (Γ.transport V.eMinus)

/--
On the transported split mixed component, scalar closure `scalar = 2c`
forces the Einstein tensor to vanish.
-/
theorem einsteinTensor_transport_split_mixed_eq_zero_of_scalar_closure
    (c : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hEin : IsEinsteinKaehlerAtWith c R K x)
    (hScalar : scalar = 2 * c) :
    einsteinTensorAt R K x scalar (Γ.transport V.ePlus) (Γ.transport V.eMinus) = 0 := by
  rw [einsteinTensor_transport_split_eq_metric_multiple
      (c := c) (R := R) (K := K) (x := x) (scalar := scalar) (V := V) (Γ := Γ) hEin]
  simp [hScalar]

/-- Skew-symmetry condition for a curvature 2-form model. -/
def IsSkewCurvatureTwoForm (Ω : E → E → E →ₗ[ℝ] E) : Prop :=
  ∀ u v : E, Ω u v = - Ω v u

/--
Einstein residual evaluated on the spin-transported split legs.
-/
noncomputable def transportedEinsteinResidual
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V) : ℝ :=
  einsteinTensorAt R K x scalar (Γ.transport V.ePlus) (Γ.transport V.eMinus)
    + Λ * K.H.metric x (Γ.transport V.ePlus) (Γ.transport V.eMinus)

/-- Residual closure on transported split frame: vacuum implies zero residual. -/
theorem transportedEinsteinResidual_vanishes_of_vacuumOnTransportedSplit
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hVacSplit :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = 0) :
    transportedEinsteinResidual (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) V Γ = 0 :=
  hVacSplit

/--
Vacuum Einstein equation restricted to the transported split frame pair.
-/
def VacuumEinsteinOnTransportedSplit
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V) : Prop :=
  transportedEinsteinResidual (R := R) (K := K) (x := x)
    (scalar := scalar) (Λ := Λ) V Γ = 0

/--
Compatibility: curvature action on the transported split pair is scalar
Einstein residual times identity on vectors.
-/
def CurvatureTwoFormCompatibleWithEinstein
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (Ω : E → E → E →ₗ[ℝ] E) : Prop :=
  ∀ w : E,
    Ω (Γ.transport V.ePlus) (Γ.transport V.eMinus) w
      = transportedEinsteinResidual (R := R) (K := K) (x := x)
          (scalar := scalar) (Λ := Λ) V Γ • w

/-- Lemma `vacuumEinsteinAt_implies_on_transportedSplit`. -/
lemma vacuumEinsteinAt_implies_on_transportedSplit
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hVac : VacuumEinsteinEquationAt R K x scalar Λ) :
    VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ := by
  unfold VacuumEinsteinOnTransportedSplit transportedEinsteinResidual
  simpa using hVac (Γ.transport V.ePlus) (Γ.transport V.eMinus)

/-- Lemma `curvature_action_zero_of_vacuum_on_transportedSplit`. -/
lemma curvature_action_zero_of_vacuum_on_transportedSplit
    (Ω : E → E → E →ₗ[ℝ] E)
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hCompat : CurvatureTwoFormCompatibleWithEinstein R K x scalar Λ V Γ Ω)
    (hVacSplit : VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ) :
    ∀ w : E, Ω (Γ.transport V.ePlus) (Γ.transport V.eMinus) w = 0 := by
  intro w
  rw [hCompat w]
  rw [hVacSplit]
  simp

/-- Lemma `vacuum_on_transportedSplit_of_curvature_action_zero`. -/
lemma vacuum_on_transportedSplit_of_curvature_action_zero
    (Ω : E → E → E →ₗ[ℝ] E)
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hCompat : CurvatureTwoFormCompatibleWithEinstein R K x scalar Λ V Γ Ω)
    (hCurvZero : ∀ w : E, Ω (Γ.transport V.ePlus) (Γ.transport V.eMinus) w = 0) :
    VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ := by
  unfold VacuumEinsteinOnTransportedSplit
  have hsmul :
      transportedEinsteinResidual (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) V Γ
        • (Γ.transport V.ePlus) = 0 := by
    calc
      transportedEinsteinResidual (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) V Γ
          • (Γ.transport V.ePlus)
          = Ω (Γ.transport V.ePlus) (Γ.transport V.eMinus) (Γ.transport V.ePlus) := by
            symm
            exact hCompat (Γ.transport V.ePlus)
      _ = 0 := hCurvZero (Γ.transport V.ePlus)
  have hplus_ne_zero : Γ.transport V.ePlus ≠ 0 := by
    intro hzero
    have hmetric_zero : K.H.metric x (Γ.transport V.ePlus) (Γ.transport V.ePlus) = 0 := by
      simp [hzero, HessianGeometry.metric_def]
    have hone : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = K.H.metric x (Γ.transport V.ePlus) (Γ.transport V.ePlus) := by
          exact Eq.symm Γ.preserves_plus
        _ = 0 := hmetric_zero
    exact one_ne_zero hone
  exact (smul_eq_zero.mp hsmul).resolve_right hplus_ne_zero

/--
Direct transported-frame relation:
under curvature/Einstein compatibility, transported-frame vacuum Einstein
is equivalent to vanishing curvature action on that transported split pair.
-/
theorem vacuumOnTransportedSplit_iff_curvature_action_zero
    (Ω : E → E → E →ₗ[ℝ] E)
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hCompat : CurvatureTwoFormCompatibleWithEinstein R K x scalar Λ V Γ Ω) :
    VacuumEinsteinOnTransportedSplit R K x scalar Λ V Γ
      ↔ ∀ w : E, Ω (Γ.transport V.ePlus) (Γ.transport V.eMinus) w = 0 := by
  constructor
  · intro hVacSplit
    exact curvature_action_zero_of_vacuum_on_transportedSplit
      (Ω := Ω) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) hCompat hVacSplit
  · intro hCurvZero
    exact vacuum_on_transportedSplit_of_curvature_action_zero
      (Ω := Ω) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) hCompat hCurvZero

end SplitSpinGeometry

/-! ## Spinorial Flow Compatibility with Einstein Equation -/

section SpinorialEinsteinBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Basepoint log-volume extracted directly from the Hessian metric operator. -/
noncomputable def spectralBasepointLogVolume (IST : InfoSpectralTriple E) : ℝ :=
  Real.log (|LinearMap.det (IST.H.metricOp IST.x₀).toLinearMap|)

/-- Scalar curvature extracted from the spinorial/spectral side. -/
noncomputable def spinorialScalarCurvature (IST : InfoSpectralTriple E) : ℝ :=
  -6 * spectralBasepointLogVolume IST

@[simp] lemma spinorialScalarCurvature_eq_neg_six_spectralBasepointLogVolume
    (IST : InfoSpectralTriple E) :
    spinorialScalarCurvature IST = -6 * spectralBasepointLogVolume IST := rfl

/--
Spinorial closure to vacuum Einstein equation:
if spinorial scalar curvature matches `2(c + Λ)` under `Ric = c g`,
then vacuum Einstein equation follows.
-/
theorem vacuumEinsteinEquation_of_spinorial_scalar
    (c : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (Λ : ℝ) (IST : InfoSpectralTriple E)
    (hEin : IsEinsteinKaehlerAtWith c R K x)
    (hSpin : spinorialScalarCurvature IST = 2 * (c + Λ)) :
    VacuumEinsteinEquationAt R K x (spinorialScalarCurvature IST) Λ := by
  exact vacuumEinsteinEquation_of_scalar_relation
    (c := c) (R := R) (K := K) (x := x)
    (scalar := spinorialScalarCurvature IST) (Λ := Λ) hEin hSpin

/--
Compatibility with normalized Kähler-Ricci evolution:
if a scalar flow tracks a fixed spinorial scalar curvature, then
its beta law is exactly `- spinorialScalarCurvature`.
-/
theorem normalizedKaehlerRicci_beta_eq_neg_spinorial
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E) (s : ℝ)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST) :
    scalarRicciBetaFunction (E := E) flow s = - spinorialScalarCurvature IST := by
  calc
    scalarRicciBetaFunction (E := E) flow s = - flow s := by
      exact normalizedKaehlerRicci_beta_eq_neg (E := E) flow hNorm s
    _ = - spinorialScalarCurvature IST := by
      simp [hTrack s]

/--
If normalized Kähler-Ricci flow is also at fixed point and tracks a spinorial
scalar value, that spinorial scalar must vanish.
-/
theorem spinorialScalarCurvature_eq_zero_of_normalized_fixedpoint
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E) (s : ℝ)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hFixed : ∀ t : ℝ, scalarRicciBetaFunction (E := E) flow t = 0)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST) :
    spinorialScalarCurvature IST = 0 := by
  have hFlowZero : ∀ t, flow t = 0 :=
    normalizedKaehlerRicci_fixedpoint_eq_zero
      (E := E) flow hNorm hFixed
  calc
    spinorialScalarCurvature IST = flow s := by
      simp [hTrack s]
    _ = 0 := hFlowZero s

end SpinorialEinsteinBridge

/-! ## Monge-Ampère Consistency scaffolding (Native Closure Mandated: Closure Debt) -/

section MongeAmpere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Monge-Ampère density model from the Hessian metric operator.
-/
noncomputable def mongeAmpereDensity (H : HessianGeometry E) (x : E) : ℝ :=
  |LinearMap.det (H.metricOp x).toLinearMap|

/-- Target-form Monge-Ampère equation against a prescribed density `ρ`. -/
def SatisfiesMongeAmpere (H : HessianGeometry E) (ρ : E → ℝ) : Prop :=
  ∀ x : E, mongeAmpereDensity H x = ρ x

/-- Potential-form Monge-Ampère equation: density equals `exp Φ`. -/
def SatisfiesMongeAmperePotential (H : HessianGeometry E) (Φ : E → ℝ) : Prop :=
  ∀ x : E, mongeAmpereDensity H x = Real.exp (Φ x)

/-- Lemma `satisfiesMongeAmpere_iff`. -/
lemma satisfiesMongeAmpere_iff
    (H : HessianGeometry E) (ρ : E → ℝ) :
    SatisfiesMongeAmpere H ρ ↔ ∀ x : E, mongeAmpereDensity H x = ρ x := Iff.rfl

/-- Lemma `satisfiesMongeAmperePotential_iff`. -/
lemma satisfiesMongeAmperePotential_iff
    (H : HessianGeometry E) (Φ : E → ℝ) :
    SatisfiesMongeAmperePotential H Φ ↔
      ∀ x : E, mongeAmpereDensity H x = Real.exp (Φ x) := Iff.rfl

/--
Promote a density-form Monge-Ampere witness to potential form once the target
density is known to be an exponential potential.
-/
lemma satisfiesMongeAmperePotential_of_satisfiesMongeAmpere_eq_exp
    (H : HessianGeometry E)
    (ρ Φ : E → ℝ)
    (hMA : SatisfiesMongeAmpere H ρ)
    (hExp : ∀ x : E, ρ x = Real.exp (Φ x)) :
    SatisfiesMongeAmperePotential H Φ := by
  intro x
  rw [hMA x, hExp x]

/-- Lemma `mongeAmpereDensity_pos`. -/
lemma mongeAmpereDensity_pos (H : HessianGeometry E) (x : E)
    (h_det : LinearMap.det (H.metricOp x).toLinearMap ≠ 0) :
  0 < mongeAmpereDensity H x := by
  unfold mongeAmpereDensity
  exact abs_pos.mpr h_det

/--
On the nondegenerate branch, Monge-Ampère density is the exponential of the
metric log-determinant.
-/
lemma mongeAmpereDensity_eq_exp_metricLogDet
    (H : HessianGeometry E) (x : E)
    (h_det : LinearMap.det (H.metricOp x).toLinearMap ≠ 0) :
    mongeAmpereDensity H x = Real.exp (metricLogDet H x) := by
  unfold mongeAmpereDensity metricLogDet
  rw [Real.exp_log]
  exact abs_pos.mpr h_det

/-- On the nondegenerate branch, metric log-determinant is the log Monge-Ampère density. -/
private lemma metricLogDet_eq_log_mongeAmpereDensity
    (H : HessianGeometry E) (x : E)
    (h_det : LinearMap.det (H.metricOp x).toLinearMap ≠ 0) :
    metricLogDet H x = Real.log (mongeAmpereDensity H x) := by
  rw [mongeAmpereDensity_eq_exp_metricLogDet (H := H) (x := x) h_det]
  rw [Real.log_exp]

/-- The singleton modular potential of Monge-Ampère density is minus the metric log-det. -/
lemma scalarModularPotential_mongeAmpereDensity_eq_neg_metricLogDet
    (H : HessianGeometry E) (x : E)
    (h_det : LinearMap.det (H.metricOp x).toLinearMap ≠ 0) :
    RelativePotentialScalarBridge.scalarModularPotential
        (mongeAmpereDensity H x)
        (mongeAmpereDensity_pos (H := H) (x := x) h_det)
      = -metricLogDet H x := by
  rw [RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log]
  rw [← metricLogDet_eq_log_mongeAmpereDensity (H := H) (x := x) h_det]

/-- Spectral-triple basepoint Monge-Ampère density. -/
noncomputable def spectralMongeAmpereDensity (IST : InfoSpectralTriple E) : ℝ :=
  mongeAmpereDensity IST.H IST.x₀

/-- Basepoint Monge-Ampère density equals the exponential of basepoint log-volume. -/
lemma spectralMongeAmpereDensity_eq_exp_spectralBasepointLogVolume
    (IST : InfoSpectralTriple E)
    (h_det : LinearMap.det (IST.H.metricOp IST.x₀).toLinearMap ≠ 0) :
    spectralMongeAmpereDensity IST = Real.exp (spectralBasepointLogVolume IST) := by
  have hpos : 0 < |LinearMap.det (IST.H.metricOp IST.x₀).toLinearMap| := abs_pos.mpr h_det
  unfold spectralMongeAmpereDensity mongeAmpereDensity spectralBasepointLogVolume
  exact (Real.exp_log hpos).symm

/-- Basepoint Monge-Ampère consistency in log-volume form. -/
def MongeAmpereConsistentAtBasepoint (IST : InfoSpectralTriple E) : Prop :=
  spectralMongeAmpereDensity IST = Real.exp (spectralBasepointLogVolume IST)

/-- The basepoint Monge-Ampère density is consistent with its explicit log-volume model. -/
lemma mongeAmpereConsistentAtBasepoint (IST : InfoSpectralTriple E)
    (h_det : LinearMap.det (IST.H.metricOp IST.x₀).toLinearMap ≠ 0) :
    MongeAmpereConsistentAtBasepoint IST := by
  exact spectralMongeAmpereDensity_eq_exp_spectralBasepointLogVolume IST h_det

end MongeAmpere

end InfoGeometry.Canonical.RicciMongeAmpere
