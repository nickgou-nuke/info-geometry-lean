import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.CalabiYauBridge
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.SingularTransportSystem
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Grand Unification of the Physics of Information in Lean 4

Capstone synthesis layer connecting thermodynamic Sinkhorn/KMS closure,
geometric Ricci/Calabi-Yau closure, and algebraic Bott-Dirac closure.
-/

open scoped TensorProduct
open scoped Kronecker

namespace InfoGeometry.Canonical.GrandSynthesis

open InfoGeometry.Krein
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.CalabiYauBridge
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.SpectralInference

section Thermodynamic

variable (n : Nat)

/--
Thermodynamic equilibrium along a doubly-stochastic Sinkhorn trajectory:
each step has Lyapunov monotonicity and bounded routing chiral scale.
-/
def ThermodynamicEquilibrium
    (T : DoublyStochasticSinkhornTrajectory n) : Prop :=
  ∀ k : Nat, ∀ label : PermMode n → CliffordLabel,
    trajectoryLyapunovNext n T.traj k ≤ trajectoryLyapunov n T.traj k ∧
      trajectorySelectedRoutingEpsilon n T (k + 1) label ≤ 1

/--
Any doubly-stochastic Sinkhorn trajectory satisfies the thermodynamic equilibrium
control law from `sinkhorn_dynamics_step_control`.
-/
theorem thermodynamicEquilibrium_of_doublyStochastic
    (T : DoublyStochasticSinkhornTrajectory n) :
    ThermodynamicEquilibrium n T := by
  intro k label
  exact sinkhorn_dynamics_step_control (n := n) T k label

end Thermodynamic

section Geometric

variable {X : Type*}

/-- Geometric equilibrium is the Ricci RG fixed-point condition. -/
abbrev GeometricEquilibrium (flow : RicciFlow X) : Prop :=
  IsRicciFixedPoint flow

/--
At geometric equilibrium, every Ricci component is scale-invariant.
-/
theorem ricci_component_constant_of_geometricEquilibrium
    (flow : RicciFlow X) (u v : X)
    (hDiff : Differentiable ℝ (fun s => flow s u v))
    (hGeo : GeometricEquilibrium flow) :
    ∃ c : ℝ, ∀ s, flow s u v = c := by
  exact ricci_component_invariant_at_fixed_point
    (flow := flow) (u := u) (v := v) hDiff (fun s => hGeo s u v)

end Geometric


section DeterminantChainRule

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Classical log-absolute determinant functional on square real matrices. -/
noncomputable def logAbsDetMatrix (A : Matrix m m ℝ) : ℝ :=
  Real.log (|Matrix.det A|)

/--
Classical determinant chain rule:
`log |det(AB)| = log |det A| + log |det B|`.
-/
lemma logAbsDetMatrix_mul
    (A B : Matrix m m ℝ)
    (hA : Matrix.det A ≠ 0)
    (hB : Matrix.det B ≠ 0) :
    logAbsDetMatrix (A * B) = logAbsDetMatrix A + logAbsDetMatrix B := by
  have hAabs : |Matrix.det A| ≠ 0 := abs_ne_zero.mpr hA
  have hBabs : |Matrix.det B| ≠ 0 := abs_ne_zero.mpr hB
  unfold logAbsDetMatrix
  rw [Matrix.det_mul, abs_mul, Real.log_mul hAabs hBabs]

variable {k : Type*} [Fintype k] [DecidableEq k]

/--
Tensor-product determinant decomposition:
`det(A ⊗ B) = det(A)^dim(B) * det(B)^dim(A)`, after `log|·|` this becomes
an additive entropy-scaling law.
-/
lemma logAbsDetMatrix_kronecker
    (A : Matrix m m ℝ) (B : Matrix k k ℝ)
    (hA : Matrix.det A ≠ 0)
    (hB : Matrix.det B ≠ 0) :
    logAbsDetMatrix (A ⊗ₖ B)
      = (Fintype.card k) * logAbsDetMatrix A
          + (Fintype.card m) * logAbsDetMatrix B := by
  have hAabs : |Matrix.det A| ≠ 0 := abs_ne_zero.mpr hA
  have hBabs : |Matrix.det B| ≠ 0 := abs_ne_zero.mpr hB
  have hAabsPow : |Matrix.det A| ^ Fintype.card k ≠ 0 :=
    pow_ne_zero _ hAabs
  have hBabsPow : |Matrix.det B| ^ Fintype.card m ≠ 0 :=
    pow_ne_zero _ hBabs
  unfold logAbsDetMatrix
  rw [Matrix.det_kronecker, abs_mul, abs_pow, abs_pow, Real.log_mul hAabsPow hBabsPow]
  rw [Real.log_pow, Real.log_pow]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Quantum-side Jacobian determinant functional on continuous endomorphisms. -/
noncomputable def jacDetCLM (L : E →L[ℝ] E) : ℝ :=
  LinearMap.det L.toLinearMap

/-- Jacobian chain rule (quantum/operator side): multiplicativity under composition. -/
lemma jacDetCLM_comp (L₁ L₂ : E →L[ℝ] E) :
    jacDetCLM (L₁.comp L₂) = jacDetCLM L₁ * jacDetCLM L₂ := by
  have _ : FiniteDimensional ℝ E := inferInstance
  simp [jacDetCLM, LinearMap.det_comp]

/-- Log-absolute Jacobian on continuous endomorphisms. -/
noncomputable def logAbsJacDetCLM (L : E →L[ℝ] E) : ℝ :=
  Real.log (|jacDetCLM L|)

/--
Quantum-side log-Jacobian chain rule:
`log |det(L₁ ∘ L₂)| = log |det L₁| + log |det L₂|`.
-/
lemma logAbsJacDetCLM_comp
    (L₁ L₂ : E →L[ℝ] E)
    (h₁ : jacDetCLM L₁ ≠ 0)
    (h₂ : jacDetCLM L₂ ≠ 0) :
    logAbsJacDetCLM (L₁.comp L₂) = logAbsJacDetCLM L₁ + logAbsJacDetCLM L₂ := by
  have h₁abs : |jacDetCLM L₁| ≠ 0 := abs_ne_zero.mpr h₁
  have h₂abs : |jacDetCLM L₂| ≠ 0 := abs_ne_zero.mpr h₂
  unfold logAbsJacDetCLM
  rw [jacDetCLM_comp, abs_mul, Real.log_mul h₁abs h₂abs]

end DeterminantChainRule

section SpectralVolumeForm

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Log-volume identity for Monge-Ampere density:
on the nondegenerate branch, `log ρ = log |det(∇²ψ)|`.
-/
lemma log_mongeAmpereDensity_eq_logAbsDet_metricOp
    [FiniteDimensional ℝ E]
    (H : InfoGeometry.Convex.HessianGeometry E) (x : E)
    (hdet : LinearMap.det (H.metricOp x).toLinearMap ≠ 0) :
    Real.log (mongeAmpereDensity H x)
      = Real.log (|LinearMap.det (H.metricOp x).toLinearMap|) := by
  have hρ :
      mongeAmpereDensity H x = Real.exp (metricLogDet H x) :=
    mongeAmpereDensity_eq_exp_metricLogDet (H := H) (x := x) hdet
  rw [hρ, Real.log_exp]
  rfl

/-- Spectral specialization of the log-volume identity at the basepoint. -/
lemma log_spectralMongeAmpereDensity_eq_basepointLogVolume
    (IST : InfoSpectralTriple E)
    (h_det : LinearMap.det (IST.H.metricOp IST.x₀).toLinearMap ≠ 0) :
    Real.log (spectralMongeAmpereDensity IST)
      = spectralBasepointLogVolume IST := by
  rw [spectralMongeAmpereDensity_eq_exp_spectralBasepointLogVolume IST h_det]
  rw [Real.log_exp]

variable {m : Type*} [Fintype m] [DecidableEq m]

/--
Determinant-model bridge:
if a matrix determinant models the Monge-Ampere density, then its log-absolute
determinant equals the Hessian metric-op log-absolute determinant.
-/
lemma logAbsDet_metricModel_eq_logAbsDet_metricOp
    [FiniteDimensional ℝ E]
    (H : InfoGeometry.Convex.HessianGeometry E) (x : E) (A : Matrix m m ℝ)
    (h_det : LinearMap.det (H.metricOp x).toLinearMap ≠ 0)
    (hdet : Matrix.det A = mongeAmpereDensity H x) :
    logAbsDetMatrix A = Real.log (|LinearMap.det (H.metricOp x).toLinearMap|) := by
  unfold logAbsDetMatrix
  rw [hdet]
  rw [abs_of_pos (mongeAmpereDensity_pos (H := H) (x := x) h_det)]
  exact log_mongeAmpereDensity_eq_logAbsDet_metricOp (H := H) (x := x) h_det

/--
Spectral determinant-model bridge:
if a matrix determinant models the spectral Monge-Ampere density, then its
log-absolute determinant equals spectral volume.
-/
private lemma logAbsDet_spectralModel_eq_basepointLogVolume
    (IST : InfoSpectralTriple E) (A : Matrix m m ℝ)
    (h_det_m : LinearMap.det (IST.H.metricOp IST.x₀).toLinearMap ≠ 0)
    (hdet : Matrix.det A = spectralMongeAmpereDensity IST) :
    logAbsDetMatrix A = spectralBasepointLogVolume IST := by
  unfold logAbsDetMatrix
  rw [hdet]
  have hpos : 0 < spectralMongeAmpereDensity IST := by
    rw [spectralMongeAmpereDensity_eq_exp_spectralBasepointLogVolume IST h_det_m]
    exact Real.exp_pos _
  rw [abs_of_pos hpos]
  exact log_spectralMongeAmpereDensity_eq_basepointLogVolume (IST := IST) h_det_m

end SpectralVolumeForm

section EntropicCalabiBridge

variable (n : Nat)
variable {X : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [FiniteDimensional ℝ X]

/--
Entropy-sourced geometric gravity statement:
RN/Kahler-potential sourcing plus unit relative-volume closure and a metric RN
bridge implies the vacuum Einstein equation on the `c = 0` branch (`scalar = 2Λ`).
-/
private theorem vacuumEinsteinEquation_of_rnEntropySource
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  have hUnitState : UnitRelativeVolumeState Kgeo := by
    intro x'
    simpa [RNEntropySourcesMongeAmpere, hUnit] using hSource x'
  exact vacuumEinsteinEquation_of_unitRelativeVolume
    (R := R) (K := Kgeo) (x := x) (Λ := Λ) hUnitState hBridge

/--
Capstone entropy-to-gravity statement:
if RN/Kahler entropy sources Monge-Ampere density and unit relative-volume closure
is equipped with a metric RN bridge, then the induced information geometry is Ricci-flat and satisfies
the vacuum Einstein equation (`c = 0`, `scalar = 2Λ`).
-/
private theorem gravity_generated_by_rnEntropy
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  have hUnitState : UnitRelativeVolumeState Kgeo := by
    intro x'
    simpa [RNEntropySourcesMongeAmpere, hUnit] using hSource x'
  refine ⟨?_, ?_⟩
  · exact isRicciFlat_of_unitRelativeVolume
      (R := R) (K := Kgeo) (x := x) hUnitState hBridge
  · exact vacuumEinsteinEquation_of_rnEntropySource
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
      (M := M) hSource hUnit hBridge

end EntropicCalabiBridge

section EntropyFlow

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Entropy monotonicity along Sinkhorn flow (RN barrier form). -/
def SinkhornEntropyMonotoneRN (T : SinkhornTrajectory n) : Prop :=
  ∀ k : Nat, trajectoryRNBarrierNext n T k ≤ trajectoryRNBarrier n T k

/-- Every Sinkhorn trajectory satisfies RN-barrier entropy monotonicity. -/
theorem sinkhornEntropyMonotoneRN
    (T : SinkhornTrajectory n) :
    SinkhornEntropyMonotoneRN n T := by
  intro k
  exact trajectoryRNBarrier_monotone (n := n) T k

/--
Doubly-stochastic specialization of RN-barrier entropy monotonicity.
-/
theorem doublyStochastic_sinkhornEntropyMonotoneRN
    (T : DoublyStochasticSinkhornTrajectory n) :
    SinkhornEntropyMonotoneRN n T.traj := by
  exact sinkhornEntropyMonotoneRN (n := n) T.traj

end EntropyFlow

section Algebraic

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
Algebraic equilibrium: the Cl(1,1)-Bott Laplacian vanishes.
-/
def AlgebraicEquilibriumCl11 (Dn : Endomorphism F) : Prop :=
  cl11BottLaplacian (E := E) Dn = 0

/--
If the Cl(1,1)-Bott Laplacian is zero, then the squared Bott-Dirac operator is zero.
-/
private theorem cl11_bottDirac_sq_eq_zero_of_algebraicEquilibrium
    (Dn : Endomorphism F)
    (hAlg : AlgebraicEquilibriumCl11 (E := E) Dn) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn) = 0 := by
  exact (cl11_bottDirac_sq_eq_cl11BottLaplacian (E := E) (F := F) (Dn := Dn)).trans hAlg

/--
Pointwise harmonicity of a Bott state at algebraic equilibrium.
-/
private theorem cl11_bottDirac_sq_apply_eq_zero_of_algebraicEquilibrium
    (Dn : Endomorphism F)
    (hAlg : AlgebraicEquilibriumCl11 (E := E) Dn)
    (ψ : DoubledSpace E ⊗[ℝ] F) :
    ((bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn)) ψ = 0 := by
  have hSq :
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
        (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn) = 0 :=
    cl11_bottDirac_sq_eq_zero_of_algebraicEquilibrium (E := E) (Dn := Dn) hAlg
  simp [hSq]

end Algebraic

section LichnerowiczBridge

variable {A F : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
Lichnerowicz-style bridge in the current framework:
for `InfoSpectralTriple`, `D²` rewrites to the Hessian metric operator, and therefore
the split Bott-Dirac square rewrites to the corresponding metric-op Laplacian form.
-/
theorem cl11_bottDirac_sq_eq_metricOp_form
    (IST : InfoSpectralTriple F) :
    (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST)).comp
      (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST))
      =
    (TensorProduct.map
      ((cl11DiracSeed (E := A)).comp (cl11DiracSeed (E := A)))
      (LinearMap.id : Endomorphism F))
      +
    (TensorProduct.map
      (LinearMap.id : Endomorphism (DoubledSpace A))
      (IST.H.metricOp IST.x₀)) := by
  have hLich :
      (spectralDiracLinear IST).comp (spectralDiracLinear IST) = IST.H.metricOp IST.x₀ := by
    ext v
    have hv : (IST.D * IST.D) v = (IST.H.metricOp IST.x₀) v := by
      exact congrArg (fun T : F →L[ℝ] F => T v) IST.dirac_sq_eq_metric
    simpa [spectralDiracLinear, LinearMap.comp_apply] using hv
  calc
    (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST)).comp
        (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST))
      =
        (TensorProduct.map
          ((cl11DiracSeed (E := A)).comp (cl11DiracSeed (E := A)))
          (LinearMap.id : Endomorphism F))
          +
        (TensorProduct.map
          (LinearMap.id : Endomorphism (DoubledSpace A))
          ((spectralDiracLinear IST).comp (spectralDiracLinear IST))) := by
            simpa using
              (cl11_bottDirac_sq_eq_sum_laplacians
                (E := A) (F := F) (Dn := spectralDiracLinear IST))
    _ =
        (TensorProduct.map
          ((cl11DiracSeed (E := A)).comp (cl11DiracSeed (E := A)))
          (LinearMap.id : Endomorphism F))
          +
        (TensorProduct.map
          (LinearMap.id : Endomorphism (DoubledSpace A))
          (IST.H.metricOp IST.x₀)) := by
            simp [hLich]

/--
Metric-op closure condition for the split Bott Laplacian in the Lichnerowicz form.
-/
def LichnerowiczBalancedCl11 (IST : InfoSpectralTriple F) : Prop :=
  (TensorProduct.map
    ((cl11DiracSeed (E := A)).comp (cl11DiracSeed (E := A)))
    (LinearMap.id : Endomorphism F))
    +
  (TensorProduct.map
    (LinearMap.id : Endomorphism (DoubledSpace A))
    (IST.H.metricOp IST.x₀)) = 0

/--
If the Lichnerowicz-balanced metric-op closure holds, the split Bott-Dirac square vanishes.
-/
theorem cl11_bottDirac_sq_eq_zero_of_lichnerowiczBalanced
    (IST : InfoSpectralTriple F)
    (hBal : LichnerowiczBalancedCl11 (A := A) IST) :
    (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST)).comp
      (bottDirac (cl11DiracSeed (E := A)) (cl11Grading (E := A)) (spectralDiracLinear IST)) = 0 := by
  rw [cl11_bottDirac_sq_eq_metricOp_form (A := A) IST]
  exact hBal

end LichnerowiczBridge

section SingularBoundaryExtension

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Singular extension of the bulk transport law:
when the certified boundary obstruction vanishes, the logarithmic transport
observable closes on the non-anomalous sector contributions.
-/
private theorem logDivergence_eq_bulkSectors_of_boundaryScale_eq_zero
    (S : SingularTransportSystem E)
    (hBoundary : S.boundary.boundaryScale = 0) :
    S.logDivergence =
      S.radialTerm + S.projectiveTerm + S.nilpotentTerm + S.gradedTerm := by
  exact S.logDivergence_split_of_boundaryScale_eq_zero hBoundary

/--
Singular extension of bulk radial closure:
if the boundary obstruction vanishes, the radial term is determined by the
remaining non-anomalous sectors.
-/
private theorem radial_transport_closes_of_boundaryScale_eq_zero
    (S : SingularTransportSystem E)
    (hBoundary : S.boundary.boundaryScale = 0) :
    S.radialTerm =
      S.logDivergence - S.projectiveTerm - S.nilpotentTerm - S.gradedTerm := by
  exact S.regular_radial_transport_closes_of_boundaryScale_eq_zero hBoundary

/--
The scalar anomaly term is exactly the norm-shadow of the certified projector
commutator obstruction carried by the primitive boundary layer.
-/
private theorem anomalyTerm_eq_projectorObstruction_norm
    (S : SingularTransportSystem E) :
    S.anomalyTerm =
      ‖S.boundary.spectralProjector * S.boundary.leftProjector
          - S.boundary.leftProjector * S.boundary.spectralProjector‖₊ := by
  rw [S.anomalyTerm_eq_projector_commutator_norm,
    S.boundary.boundaryScale_eq_projectorObstruction_norm]

/--
Boundary-anomaly freeness is equivalent to commutation of the certified Drazin
and Moore-Penrose projectors in the primitive singular boundary layer.
-/
private theorem boundaryGenerator_eq_zero_iff_projectors_commute
    (S : SingularTransportSystem E) :
    S.boundary.boundaryGenerator = 0
      ↔ S.boundary.spectralProjector * S.boundary.leftProjector =
          S.boundary.leftProjector * S.boundary.spectralProjector := by
  exact S.boundaryGenerator_eq_zero_iff_projectors_commute

/--
Vanishing boundary generator forces the primitive singular boundary layer to
close to regular radial transport.
-/
theorem regularRadialTransportCloses_of_boundaryGenerator_eq_zero
    (S : SingularTransportSystem E)
    (hZero : S.boundary.boundaryGenerator = 0) :
    S.boundary.regularRadialTransportCloses := by
  have hScale : S.boundary.boundaryScale = 0 := by
    exact (S.boundary.boundaryScale_eq_zero_iff_boundaryGenerator_eq_zero).mpr hZero
  exact S.boundary.regular_radial_transport_closes_of_boundaryScale_eq_zero hScale

end SingularBoundaryExtension

section Capstone

variable (n : Nat)
variable {X E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
One-step grand synthesis control:
thermodynamic control from Sinkhorn, plus externally supplied geometric fixed-point
and algebraic Cl(1,1)-Bott equilibrium.
-/
private theorem grandSynthesis_step
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : RicciFlow X)
    (Dn : Endomorphism F)
    (hGeo : GeometricEquilibrium flow)
    (hAlg : AlgebraicEquilibriumCl11 (E := E) Dn)
    (k : Nat) (label : PermMode n → CliffordLabel) :
    trajectoryLyapunovNext n T.traj k ≤ trajectoryLyapunov n T.traj k ∧
      trajectorySelectedRoutingEpsilon n T (k + 1) label ≤ 1 ∧
      GeometricEquilibrium flow ∧
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
        (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn) = 0 := by
  refine ⟨?_, ?_, hGeo, ?_⟩
  · exact (sinkhorn_dynamics_step_control (n := n) T k label).1
  · exact (sinkhorn_dynamics_step_control (n := n) T k label).2
  · exact cl11_bottDirac_sq_eq_zero_of_algebraicEquilibrium
      (E := E) (Dn := Dn) hAlg

end Capstone

end InfoGeometry.Canonical.GrandSynthesis
