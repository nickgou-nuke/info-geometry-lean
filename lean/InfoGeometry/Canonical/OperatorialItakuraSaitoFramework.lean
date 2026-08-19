import InfoGeometry.Canonical.OperatorMongeAmpereItakuraSaito
import InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence
import InfoGeometry.Canonical.ArakiItakuraSaitoCollapse
import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.OperatorAlgebra.UnnormalizedRelativeEntropy
import InfoGeometry.Optics.OperatorDerivationForms
import InfoGeometry.Geometry.ParaHessianMixedPotential
import InfoGeometry.Analysis.FiniteMatrixJacobiDerivative
import InfoGeometry.OperatorAlgebra.FiniteRelativeModularOperator
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelDerivative
import InfoGeometry.Volume.ConnesInfinitesimal

/-!
# Native operatorial Itakura--Saito framework

This file is an integration surface, not a new analytic model.  It combines
the existing finite Itakura--Saito channel, the bounded noncommutative Bregman
packet, the Frechet/transport Hessian, and the Onsager response form.

The operatorial channel is indexed by the Tomita--Takesaki relative modular
datum: its primary operator is `Delta_{phi,psi} = relativeModular phi psi`,
and its logarithmic datum is `log Delta_{phi,psi}` supplied by
`relativeLogBetween`.  The finite matrix channel below is only a separate
finite shadow and is not identified with the relative modular operator.

The direct- and inverse-colimit constructions remain owned by
`FilteredDirectInverseColimit`; this file does not duplicate their descent
obligations.  In particular, no identity between an arbitrary operator
`logDelta` and an operator logarithm is asserted here.
-/

noncomputable section

open scoped ComplexOrder

namespace InfoGeometry.Canonical.OperatorialItakuraSaitoFramework

open InfoGeometry.Canonical.ArakiItakuraSaitoCollapse
open InfoGeometry.Canonical.OperatorialHessianBridge
open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.OperatorMongeAmpereItakuraSaito
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence
open InfoGeometry.OperatorAlgebra.UnnormalizedRelativeEntropy
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Thermo.SusceptibilityOnsagerStress
open InfoGeometry.Geometry.ParaHessianMixedPotential
open InfoGeometry.Analysis.FiniteMatrixJacobiDerivative

/-! ## Unified finite and noncommutative value channels -/

abbrev FiniteOperatorModel (Op : Type*) [AddGroup Op] :=
  NoncommutativeItakuraSaitoModel Op

def finiteOperatorValue
    {Op : Type*} [AddGroup Op]
    (P : FiniteOperatorModel Op) (X Y : Op) : ℝ :=
  P.divergence X Y

@[simp]
theorem finiteOperatorValue_self
    {Op : Type*} [AddGroup Op]
    (P : FiniteOperatorModel Op)
    (hzero : ∀ X : Op, P.readout.readout (P.readout.product X 0) = 0)
    (X : Op) :
    finiteOperatorValue P X X = 0 := by
  exact P.divergence_self hzero X

/-! ## Tomita--Takesaki relative modular channel -/

section RelativeModular

variable {A Modular : Type*}
variable [Zero A] [Zero Modular] [Mul Modular]
variable [CStarAlgebra Modular] [PartialOrder Modular]

/-- The Tomita--Takesaki relative modular operator `Delta_{phi,psi}`. -/
def relativeDelta
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) : Modular :=
  D.relativeModular φ ψ

/-- The logarithmic relative modular operator `log Delta_{phi,psi}`. -/
def relativeLogDelta
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) : Modular :=
  D.relativeLogBetween φ ψ

/-- The genuine relative-modular Itakura--Saito operator. -/
def relativeOperatorItakuraSaito
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) : Modular :=
  operatorItakuraSaito (relativeDelta D φ ψ) (relativeLogDelta D φ ψ)

/-- The Tomita relative-modular complement `Delta - 1`. -/
def relativeDeltaComplement
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) : Modular :=
  relativeDelta D φ ψ - 1

theorem relativeOperatorItakuraSaito_eq_centered
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) :
    relativeOperatorItakuraSaito D φ ψ =
      (relativeDelta D φ ψ - 1) - relativeLogDelta D φ ψ := by
  exact InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence.operatorItakuraSaito_eq_centered
    _ _

/-- The operatorial IS deviance written through the native Tomita complement.
    This is only an additive rewrite; `relativeLogDelta` remains supplied
    logarithmic modular data rather than an inferred functional-calculus log. -/
theorem relativeOperatorItakuraSaito_eq_complement_sub_log
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) :
    relativeOperatorItakuraSaito D φ ψ =
      relativeDeltaComplement D φ ψ - relativeLogDelta D φ ψ := by
  change relativeOperatorItakuraSaito D φ ψ =
    (relativeDelta D φ ψ - 1) - relativeLogDelta D φ ψ
  exact relativeOperatorItakuraSaito_eq_centered D φ ψ

/-- Hamiltonian readout of the complement form under an explicit Tomita
    surprisal witness `log Δ = -K`. -/
theorem relativeOperatorItakuraSaito_eq_complement_add_hamiltonian
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) (K : Modular)
    (hK : relativeLogDelta D φ ψ = -K) :
    relativeOperatorItakuraSaito D φ ψ =
      relativeDeltaComplement D φ ψ + K := by
  rw [relativeOperatorItakuraSaito_eq_complement_sub_log, hK]
  rw [sub_neg_eq_add]

@[simp]
theorem relativeDeltaComplement_eq_sub_one
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) :
    relativeDeltaComplement D φ ψ = relativeDelta D φ ψ - 1 :=
  rfl

theorem relativeDeltaComplement_eq_perturbation
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) (X : Modular)
    (hDelta : relativeDelta D φ ψ = 1 + X) :
    relativeDeltaComplement D φ ψ = X := by
  exact InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence.relative_complement_eq_perturbation
    _ _ hDelta

theorem relativeOperatorItakuraSaito_eq_perturbation_sub_log
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) (X : Modular)
    (hDelta : relativeDelta D φ ψ = 1 + X) :
    relativeOperatorItakuraSaito D φ ψ = X - relativeLogDelta D φ ψ := by
  exact InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence.operatorItakuraSaito_eq_perturbation_sub_log
    _ _ _ hDelta

/-- Native `Delta - 1 + K` form of the relative-modular IS operator when the
    supplied logarithmic datum is explicitly witnessed as `-K`. -/
theorem relativeOperatorItakuraSaito_eq_delta_sub_one_add_hamiltonian
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) (K : Modular)
    (hK : relativeLogDelta D φ ψ = -K) :
    relativeOperatorItakuraSaito D φ ψ = relativeDelta D φ ψ - 1 + K := by
  exact InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence.operatorItakuraSaito_eq_delta_sub_one_add_hamiltonian
    (relativeDelta D φ ψ) (relativeLogDelta D φ ψ) K hK

@[simp]
theorem relativeDelta_eq_datum
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) :
    relativeDelta D φ ψ = D.relativeModular φ ψ :=
  rfl

@[simp]
theorem relativeLogDelta_eq_datum
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A) :
    relativeLogDelta D φ ψ = D.relativeLogBetween φ ψ :=
  rfl

theorem relativeDelta_chain
    (D : RelativeModularDatum A Modular)
    (φ ψ η : OperatorWeight A) :
    relativeDelta D φ ψ * relativeDelta D ψ η =
      relativeDelta D φ η :=
  D.relativeModular_mul φ ψ η

/-- The Tomita-channel readout is the Araki readout under the native
    normalization hypothesis.  The logarithmic datum remains the supplied
    `relativeLogBetween`; no functional-calculus identity is asserted. -/
theorem relativeOperatorItakuraSaito_expectation_eq_araki
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A)
    (ω : Modular →ₚ[ℂ] ℂ)
    (h_delta : ω (relativeDelta D φ ψ) = ω 1) :
    ω (relativeOperatorItakuraSaito D φ ψ) =
      InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence.arakiRelativeEntropy
        ω (relativeLogDelta D φ ψ) := by
  exact InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence.itakuraSaito_expectation_eq_araki
    (A := Modular) ω
    (relativeDelta D φ ψ) (relativeLogDelta D φ ψ) h_delta

theorem relativeDeltaComplement_expectation_eq_zero
    (D : RelativeModularDatum A Modular)
    (φ ψ : OperatorWeight A)
    (ω : Modular →ₚ[ℂ] ℂ)
    (h_delta : ω (relativeDelta D φ ψ) = ω 1) :
    ω (relativeDeltaComplement D φ ψ) = 0 := by
  exact InfoGeometry.Canonical.ArakiItakuraSaitoEquivalence.complement_expectation_eq_zero
    ω (relativeDelta D φ ψ) h_delta

end RelativeModular

/-! ## Finite Tomita relative-modular realization -/

section FiniteTomita

open InfoGeometry.OperatorAlgebra.FiniteRelativeModularOperator

variable {n : ℕ}

/-- The finite left-right relative modular operator is an actual linear
    equivalence, not an unconstrained operator parameter. -/
theorem finite_relativeDelta_is_linearEquiv
    (ρ σ : InvertibleMatrix n) :
    Function.Bijective (relativeModular ρ σ) := by
  exact (relativeModularEquiv ρ σ).bijective

/-- The finite relative modular operator sends the identity carrier to the
    left/right operator ratio. -/
theorem finite_relativeDelta_identity
    (ρ σ : InvertibleMatrix n) :
    relativeModular ρ σ (1 : MatrixCarrier n) = ρ.val * σ.inv := by
  rw [relativeModular_apply]
  simp

/-- Matrix-unit readout of the finite Tomita relative modular operator. -/
theorem finite_relativeDelta_matrixUnit
    (p pinv q qinv : Fin n → ℂ)
    (hp : ∀ i, p i * pinv i = 1)
    (hp' : ∀ i, pinv i * p i = 1)
    (hq : ∀ i, q i * qinv i = 1)
    (hq' : ∀ i, qinv i * q i = 1)
    (i j : Fin n) :
    relativeModular (diagonalInvertible p pinv hp hp')
        (diagonalInvertible q qinv hq hq') (matrixUnit i j) =
      (p i * qinv j) • matrixUnit i j := by
  exact diagonal_relativeModular_matrixUnit p pinv q qinv hp hp' hq hq' i j

/-- Native Duhamel/Frechet normalization at the zero relative generator. -/
theorem duhamel_relative_generator_zero
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] :
    InfoGeometry.OperatorAlgebra.duhamelDerivative (0 : A) =
      ContinuousLinearMap.id ℝ A := by
  exact InfoGeometry.OperatorAlgebra.duhamelDerivative_zero

end FiniteTomita

/-! ## Modular-Hamiltonian transport of the complement -/

section ModularHamiltonianComplement

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance : NormedRing
    (InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H) := inferInstance
noncomputable local instance : NormedAlgebra ℝ
    (InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H) := inferInstance
local instance : IsTopologicalRing
    (InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H) := inferInstance
local instance : CompleteSpace
    (InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H) := inferInstance

/-- Exponential-conjugation modular flow transports the relative complement
    `Delta - 1` as the complement of the transported `Delta`. -/
theorem modularHamiltonianAction_relativeDeltaComplement
    (K Delta : InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H) (t : ℝ) :
    InfoGeometry.Volume.ConnesInfinitesimal.modularHamiltonianAction
        (H := H) K (Delta - 1) t =
      InfoGeometry.Volume.ConnesInfinitesimal.modularHamiltonianAction
        (H := H) K Delta t - 1 := by
  rw [show Delta - 1 = Delta + (-1) by rw [sub_eq_add_neg]]
  rw [InfoGeometry.Volume.ConnesInfinitesimal.modularHamiltonianAction,
    InfoGeometry.Canonical.expTransport_add_seed]
  have hfixed : InfoGeometry.Canonical.expTransport K (-1) t =
      (-1 : InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H) := by
    apply InfoGeometry.Canonical.expTransport_eq_self_of_commute
    exact Commute.neg_left (Commute.one_left K)
  rw [hfixed]
  change InfoGeometry.Canonical.expTransport K Delta t + (-1) =
    InfoGeometry.Canonical.expTransport K Delta t - 1
  rw [sub_eq_add_neg]

/-- The IS complement follows the native modular Heisenberg flow.  The
    identity component is central, so its commutator drops out and the
    derivative is the transported commutator with `Delta` itself. -/
theorem modularHamiltonianAction_relativeDeltaComplement_hasDerivAt
    (K Delta : InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        InfoGeometry.Volume.ConnesInfinitesimal.modularHamiltonianAction
          (H := H) K (Delta - 1) s)
      (InfoGeometry.Volume.ConnesInfinitesimal.modularHamiltonianAction
        (H := H) K ⁅K, Delta⁆ t)
      t := by
  have hderiv :=
    InfoGeometry.Volume.ConnesInfinitesimal.modularHamiltonianAction_hasDerivAt
      (H := H) K (Delta - 1) t
  have hcomm : ⁅K, Delta - 1⁆ = ⁅K, Delta⁆ := by
    rw [Ring.lie_def, Ring.lie_def]
    noncomm_ring
  simpa [hcomm] using hderiv

end ModularHamiltonianComplement

/-! ## Native operatorial Hessian and Onsager sectors -/

section Operatorial

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

abbrev operatorialISHessian (X A : EndH) : EndH :=
  InfoGeometry.Canonical.OperatorialHessianBridge.operatorInformationHessian (E := E) X A

theorem operatorialISHessian_eq_double_transport
    (X A : EndH) :
    operatorialISHessian (E := E) X A =
      InfoGeometry.Canonical.BogoliubovTransport.transportCommutator X
        (InfoGeometry.Canonical.BogoliubovTransport.transportCommutator X A) := by
  exact OperatorialHessianBridge.operatorInformationHessian_eq_double_transportCommutator
    (E := E) X A

abbrev operatorialISOnsagerMetric
    (P : PotentialDatum (E := E)) (A : EndH) :
    LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  operatorMetricHessianForm (E := E) P A

theorem operatorialISOnsagerMetric_swap
    (P : PotentialDatum (E := E)) (A : EndH)
    (X Y : PerturbationChannel E) :
    operatorialISOnsagerMetric (E := E) P A X Y =
      operatorialISOnsagerMetric (E := E) P A Y X := by
  exact operatorMetricHessianForm_swap (E := E) P A X Y

theorem operatorialISOnsagerMetric_diag
    (P : PotentialDatum (E := E)) (A X : EndH) :
    operatorialISOnsagerMetric (E := E) P A X X =
      P.probe (operatorialISHessian (E := E) X A) := by
  exact operatorMetricHessianForm_diag (E := E) P A X

theorem operatorialISOnsagerMetric_eq_responseCoefficient
    (P : PotentialDatum (E := E)) (A X Y : EndH) :
    operatorialISOnsagerMetric (E := E) P A X Y =
      responseCoefficient (E := E) P X Y A := by
  rfl

theorem operatorialISOnsagerMetric_diag_eq_double_transport
    (P : PotentialDatum (E := E)) (A X : EndH) :
    operatorialISOnsagerMetric (E := E) P A X X =
      P.probe
        (InfoGeometry.Canonical.BogoliubovTransport.transportCommutator X
          (InfoGeometry.Canonical.BogoliubovTransport.transportCommutator X A)) := by
  rw [operatorialISOnsagerMetric_diag, operatorialISHessian_eq_double_transport]

theorem operatorialISOnsagerMetric_eq_half_probe_lie_hessian
    (P : PotentialDatum (E := E)) (A : EndH) (X Y : PerturbationChannel E) :
    operatorialISOnsagerMetric (E := E) P A X Y =
      (2 : ℝ)⁻¹ *
        (P.probe (observableLieHessian (E := E) X Y A) +
          P.probe (observableLieHessian (E := E) Y X A)) := by
  exact operatorMetricHessianForm_eq_half_probe_observableLieHessian_add_swap
    (E := E) P A X Y

end Operatorial

/-! ## Frechet, Hessian, and determinant derivative readouts -/

section NativeCalculus

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable [FiniteDimensional ℝ A]

/-- Canonical Frechet realization of a finite thermodynamic derivation. -/
abbrev finiteThermodynamicFrechetDerivation
    (D : ThermodynamicOperatorDerivation A) :
    FrechetOperatorDerivation ℝ A :=
  frechetOperatorDerivationOfThermodynamic D

theorem finiteThermodynamicFrechetDerivation_hasFDerivAt
    (D : ThermodynamicOperatorDerivation A) (a : A) :
    HasFDerivAt D
      (finiteThermodynamicFrechetDerivation D).toContinuousLinearMap a :=
  frechetOperatorDerivationOfThermodynamic_hasFDerivAt D a

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem paraHessian_gradient_frechet_readout
    (X U V : Doubled E) :
    productPairing
        (fderiv ℝ (InfoGeometry.Geometry.ParaHessianMixedPotential.gradient (E := E)) X U) V =
      metric U V :=
  fderiv_gradient_inner_eq_metric X U V

end NativeCalculus

section FiniteJacobi

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem finite_jacobi_derivative_readout
    {J : ℝ → Matrix n n ℝ} {Jdot : Matrix n n ℝ} {t : ℝ}
    (hJ : ∀ i j : n, HasDerivAt (fun u : ℝ => J u i j) (Jdot i j) t)
    (hinv : IsUnit (J t)) :
    HasDerivAt
      (fun u : ℝ => (J u).det)
      ((J t).det * Matrix.trace ((J t)⁻¹ * Jdot)) t :=
  hasDerivAt_det_of_hasDerivAt_matrix hJ hinv

/-! The logarithmic determinant is the scalar Jacobi readout. -/
theorem finite_logDet_derivative_readout
    {J : ℝ → Matrix n n ℝ} {Jdot : Matrix n n ℝ} {t : ℝ}
    (hJ : ∀ i j : n, HasDerivAt (fun u : ℝ => J u i j) (Jdot i j) t)
    (hinv : IsUnit (J t)) :
    HasDerivAt
      (fun u : ℝ => Real.log ((J u).det))
      (Matrix.trace ((J t)⁻¹ * Jdot)) t := by
  have hdet := hasDerivAt_det_of_hasDerivAt_matrix hJ hinv
  have hunitdet : IsUnit (J t).det :=
    (Matrix.isUnit_iff_isUnit_det (J t)).mp hinv
  have hdet_ne : (J t).det ≠ 0 := isUnit_iff_ne_zero.mp hunitdet
  have hlog := (Real.hasDerivAt_log hdet_ne).comp t hdet
  convert hlog using 1
  field_simp [hdet_ne]

theorem finite_logDet_deriv_readout
    {J : ℝ → Matrix n n ℝ} {Jdot : Matrix n n ℝ} {t : ℝ}
    (hJ : ∀ i j : n, HasDerivAt (fun u : ℝ => J u i j) (Jdot i j) t)
    (hinv : IsUnit (J t)) :
    deriv (fun u : ℝ => Real.log ((J u).det)) t =
      Matrix.trace ((J t)⁻¹ * Jdot) :=
  (finite_logDet_derivative_readout hJ hinv).deriv

end FiniteJacobi

/-! ## Finite diagonal Monge--Ampere channel -/

theorem finite_mongeAmpere_channel
    (κ a : ℝ) :
    -Real.log
        (InfoGeometry.Canonical.OperatorMongeAmpereItakuraSaito.det2
          (InfoGeometry.Canonical.OperatorMongeAmpereItakuraSaito.delta κ a)) =
      trace2 (InfoGeometry.Canonical.OperatorMongeAmpereItakuraSaito.surprisal κ a) :=
  monge_ampere_channel κ a

theorem finite_operator_defect_nonneg
    (κ a : ℝ) :
    0 ≤ InfoGeometry.Canonical.OperatorMongeAmpereItakuraSaito.trace2
      (InfoGeometry.Canonical.OperatorMongeAmpereItakuraSaito.operatorDefect κ a) :=
  defect_trace_nonneg κ a

end InfoGeometry.Canonical.OperatorialItakuraSaitoFramework
