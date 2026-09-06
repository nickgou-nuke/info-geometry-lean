/-
InfoGeometry/Dynamics/OperatorialRicciFlow.lean

Operatorial Ricci flow and Drazin-Perelman surgery.

This module packages the dynamical synthesis:

  Perelman/Otto/JKO variational motion
      → horizon/rank boundary
      → Drazin regular-core surgery
      → optional arithmetic L-divisor readout.

It is intentionally witness-gated at the analytic level.  The file does not
prove Ricci-flow existence, Perelman surgery estimates, Otto calculus, or
holographic recovery.  It records the exact algebraic data needed by later
models and proves the immediate projector/horizon consequences.
-/

import Mathlib
import InfoGeometry.Canonical.OperatorJKOStep
import InfoGeometry.Singular.SchurDrazinMoorePenrose
import InfoGeometry.Arithmetic.LFunctionPotential

noncomputable section

namespace InfoGeometry.Dynamics.OperatorialRicciFlow

open InfoGeometry.Canonical.OperatorJKOStep
open InfoGeometry.Singular.SchurDrazinMoorePenrose
open InfoGeometry.Arithmetic.LFunction
open InfoGeometry.Exceptional.SplitJordan

/-! ## 1. Perelman/Otto operatorial flow socket -/

/--
Operatorial Ricci/Otto flow.

`State` is the nonlinear vacuum/charge-state carrier.
`Op` is the linearized operator algebra used to detect singular directions.

The smooth phase is constructive: away from the horizon, the installed time
derivative equals the installed vector field.  The identification with
Perelman/Otto/Ricci geometry remains a calibration certificate.
-/
structure OperatorialRicciFlow
    (State Op : Type*) [AddCommGroup State] [Module ℝ State]
    [Ring Op] [StarRing Op] where
  /-- Deterministic JKO/Otto potential controlling the energy landscape. -/
  jkoPotential :
    OperatorJKOPotential State

  /-- Time-parametrized state. -/
  trajectory :
    ℝ → State

  /-- Smooth vector field, morally `-∇_W Φ`. -/
  vectorField :
    State → State

  /-- Chosen time derivative backend for the trajectory. -/
  timeDerivative :
    (ℝ → State) → ℝ → State

  /-- Horizon/singularity locus where the smooth chart breaks. -/
  horizon :
    Set State

  /-- Linearized model operator attached to a state. -/
  modelOperator :
    State → Op

  /--
  Smooth flow law away from the horizon:

  `dX/dt = vectorField X`.
  -/
  smooth_flow_law :
    ∀ t : ℝ,
      trajectory t ∉ horizon →
        timeDerivative trajectory t = vectorField (trajectory t)

  /--
  Calibration saying this vector field is the intended Perelman/Otto/Ricci
  gradient flow of the installed information potential.
  -/
  perelman_otto_calibration : Prop

  /-- Proof/certificate of the Perelman/Otto calibration. -/
  perelman_otto_certificate :
    perelman_otto_calibration

namespace OperatorialRicciFlow

variable {State Op : Type*} [AddCommGroup State] [Module ℝ State]
variable [Ring Op] [StarRing Op]
variable (F : OperatorialRicciFlow State Op)

/-- The smooth flow equation is available away from the horizon. -/
theorem timeDerivative_eq_vectorField
    (t : ℝ)
    (h : F.trajectory t ∉ F.horizon) :
    F.timeDerivative F.trajectory t = F.vectorField (F.trajectory t) :=
  F.smooth_flow_law t h

/-- The stored Perelman/Otto calibration is available as a proof. -/
theorem perelman_otto_valid :
    F.perelman_otto_calibration :=
  F.perelman_otto_certificate

end OperatorialRicciFlow

/-! ## 2. Drazin-Perelman surgery -/

/--
Drazin-Perelman surgery data for an operatorial Ricci flow.

At a horizon time, the flow restarts from the Drazin regular-core projection
`A Aᴰ`.  The complementary projector `I - A Aᴰ` is the Drazin-null/horizon
component.
-/
structure DrazinPerelmanSurgery
    {State Op : Type*} [AddCommGroup State] [Module ℝ State]
    [Ring Op] [StarRing Op]
    (F : OperatorialRicciFlow State Op) where
  /-- Drazin/Moore--Penrose ledger attached to the model operator at time `t`. -/
  ledgerAt :
    ℝ → DrazinMoorePenroseLedger Op

  /-- The ledger's operator is the flow's linearized model operator. -/
  ledger_operator_eq :
    ∀ t : ℝ,
      (ledgerAt t).A = F.modelOperator (F.trajectory t)

  /-- Action of an algebraic projector on a state. -/
  applyProjector :
    Op → State → State

  /-- Post-surgery state selected at a critical time. -/
  postSurgeryState :
    ℝ → State

  /--
  Surgery law: at a horizon, restart from the Drazin regular-core projection.
  -/
  postSurgery_eq_regularCore :
    ∀ t : ℝ,
      F.trajectory t ∈ F.horizon →
        postSurgeryState t =
          applyProjector ((ledgerAt t).dynamicalRegularProjector)
            (F.trajectory t)

namespace DrazinPerelmanSurgery

variable {State Op : Type*} [AddCommGroup State] [Module ℝ State]
variable [Ring Op] [StarRing Op]
variable {F : OperatorialRicciFlow State Op}
variable (S : DrazinPerelmanSurgery F)

/-- Drazin regular-core projector at time `t`. -/
def regularCoreProjector
    (t : ℝ) : Op :=
  (S.ledgerAt t).dynamicalRegularProjector

/-- Drazin-null/horizon projector at time `t`. -/
def horizonNullProjector
    (t : ℝ) : Op :=
  (S.ledgerAt t).dynamicalNilpotentProjector

/-- The regular-core projector is idempotent. -/
theorem regularCoreProjector_idempotent
    (t : ℝ) :
    S.regularCoreProjector t * S.regularCoreProjector t =
      S.regularCoreProjector t :=
  (S.ledgerAt t).dynamicalRegularProjector_idempotent

/-- The Drazin-null/horizon projector is idempotent. -/
theorem horizonNullProjector_idempotent
    (t : ℝ) :
    S.horizonNullProjector t * S.horizonNullProjector t =
      S.horizonNullProjector t :=
  (S.ledgerAt t).dynamicalNilpotentProjector_idempotent

/-- At a horizon time, surgery restarts from the Drazin regular core. -/
theorem postSurgeryState_eq_regularCore
    (t : ℝ)
    (h : F.trajectory t ∈ F.horizon) :
    S.postSurgeryState t =
      S.applyProjector (S.regularCoreProjector t) (F.trajectory t) :=
  S.postSurgery_eq_regularCore t h

end DrazinPerelmanSurgery

/-! ## 3. JKO compatibility packet -/

/--
Discrete JKO compatibility for an operatorial Ricci flow.

The continuous flow and the discrete JKO path are linked by a model-specific
readout `sample`.  No convergence theorem is asserted here.
-/
structure OperatorialRicciJKOCompatibility
    {State Op : Type*} [AddCommGroup State] [Module ℝ State]
    [Ring Op] [StarRing Op]
    (F : OperatorialRicciFlow State Op) where
  /-- Stored deterministic JKO path. -/
  jkoPath :
    OperatorJKOPath F.jkoPotential

  /-- Sampling map from discrete index to continuous time. -/
  sampleTime :
    ℕ → ℝ

  /-- The JKO next state agrees with the sampled continuous trajectory. -/
  next_eq_sampled_trajectory :
    ∀ n : ℕ,
      (jkoPath.step n).next = F.trajectory (sampleTime n)

namespace OperatorialRicciJKOCompatibility

variable {State Op : Type*} [AddCommGroup State] [Module ℝ State]
variable [Ring Op] [StarRing Op]
variable {F : OperatorialRicciFlow State Op}
variable (C : OperatorialRicciJKOCompatibility F)

/-- Every stored JKO step decreases the installed energy. -/
theorem energy_antitone_step
    (n : ℕ) :
    F.jkoPotential.energy (C.jkoPath.step n).next ≤
      F.jkoPotential.energy (C.jkoPath.step n).previous :=
  C.jkoPath.energy_antitone_step n

/-- Sampled trajectory version of the JKO energy decrease. -/
theorem sampled_energy_le_previous
    (n : ℕ) :
    F.jkoPotential.energy (F.trajectory (C.sampleTime n)) ≤
      F.jkoPotential.energy (C.jkoPath.step n).previous := by
  rw [← C.next_eq_sampled_trajectory n]
  exact C.energy_antitone_step n

end OperatorialRicciJKOCompatibility

/-! ## 4. Unified horizon bridge -/

section UnifiedHorizon

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable {D : CubicJordanNormDatum J}
variable {L : ScatteringLFunction E}

/--
Bridge from an operatorial Ricci-flow horizon to the unified Jordan/arithmetic
horizon witness.
-/
structure OperatorialUnifiedHorizonBridge
    {State Op : Type*} [AddCommGroup State] [Module ℝ State]
    [Ring Op] [StarRing Op]
    (F : OperatorialRicciFlow State Op)
    (W : UnifiedHorizonWitness J D L) where
  /-- Extract the Jordan charge/state from the flow state. -/
  jordanState :
    State → J

  /-- The flow horizon is exactly the Jordan norm divisor. -/
  horizon_iff_jordan_divisor :
    ∀ t : ℝ,
      F.trajectory t ∈ F.horizon ↔
        D.norm (jordanState (F.trajectory t)) = 0

namespace OperatorialUnifiedHorizonBridge

variable {State Op : Type*} [AddCommGroup State] [Module ℝ State]
variable [Ring Op] [StarRing Op]
variable {F : OperatorialRicciFlow State Op}
variable {W : UnifiedHorizonWitness J D L}
variable (B : OperatorialUnifiedHorizonBridge F W)

/-- A flow horizon maps to an arithmetic L-divisor. -/
theorem flow_horizon_is_arithmetic_horizon
    (t : ℝ)
    (h : F.trajectory t ∈ F.horizon) :
    IsArithmeticHorizon L
      (W.spectralMap (B.jordanState (F.trajectory t))) := by
  exact
    W.geometric_horizon_is_arithmetic_horizon
      (B.jordanState (F.trajectory t))
      ((B.horizon_iff_jordan_divisor t).1 h)

/-- An arithmetic L-divisor pulls back to a flow horizon. -/
theorem arithmetic_horizon_is_flow_horizon
    (t : ℝ)
    (h :
      IsArithmeticHorizon L
        (W.spectralMap (B.jordanState (F.trajectory t)))) :
    F.trajectory t ∈ F.horizon := by
  exact
    (B.horizon_iff_jordan_divisor t).2
      (W.arithmetic_horizon_is_geometric_horizon
        (B.jordanState (F.trajectory t)) h)

/-- Exact equivalence between the flow horizon and the arithmetic horizon. -/
theorem flow_horizon_iff_arithmetic_horizon
    (t : ℝ) :
    F.trajectory t ∈ F.horizon ↔
      IsArithmeticHorizon L
        (W.spectralMap (B.jordanState (F.trajectory t))) := by
  constructor
  · exact B.flow_horizon_is_arithmetic_horizon t
  · exact B.arithmetic_horizon_is_flow_horizon t

end OperatorialUnifiedHorizonBridge

end UnifiedHorizon

/-! ## 5. Stratified Hessian-gradient normalization -/

section StratifiedHessianGradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
Abstract Drazin data for an endomorphism.

This is intentionally local and witness-gated.  It records the algebraic laws
needed for spectral surgery without assuming a ready-made matrix Drazin API.
-/
structure DrazinData
    (A : E →ₗ[ℝ] E) where
  /-- Drazin inverse of the linearized operator. -/
  inv :
    E →ₗ[ℝ] E

  /-- Drazin index. -/
  index :
    ℕ

  /-- The operator commutes with its Drazin inverse. -/
  commute :
    A.comp inv = inv.comp A

  /-- Reflexive Drazin law. -/
  reflexive :
    (inv.comp A).comp inv = inv

  /-- Index law. -/
  index_eq :
    Prop

  /-- Core projector idempotence. -/
  core_idem :
    (A.comp inv).comp (A.comp inv) = A.comp inv

  /-- Nilpotent-sector projector idempotence. -/
  nil_idem :
    ((LinearMap.id : E →ₗ[ℝ] E) - A.comp inv).comp
        ((LinearMap.id : E →ₗ[ℝ] E) - A.comp inv) =
      (LinearMap.id : E →ₗ[ℝ] E) - A.comp inv

namespace DrazinData

variable {A : E →ₗ[ℝ] E}
variable (D : DrazinData A)

/-- Dynamical semisimple/core projector. -/
def coreProj : E →ₗ[ℝ] E :=
  A.comp D.inv

/-- Dynamical nilpotent/horizon projector. -/
def nilProj : E →ₗ[ℝ] E :=
  (LinearMap.id : E →ₗ[ℝ] E) - A.comp D.inv

/-- The Drazin core projector is idempotent. -/
theorem coreProj_idempotent :
    D.coreProj.comp D.coreProj = D.coreProj :=
  D.core_idem

/-- The Drazin nilpotent/horizon projector is idempotent. -/
theorem nilProj_idempotent :
    D.nilProj.comp D.nilProj = D.nilProj :=
  D.nil_idem

end DrazinData

/-- Regular chamber of a determinant/norm potential. -/
def regularChamber
    (N : E → ℝ)
    (x : E) : Prop :=
  N x ≠ 0

/--
Split-Jordan logarithmic barrier potential.

This models the finite-dimensional Jordan dilaton/barrier sector.  It is not
asserted to be literally Perelman's full `W`-functional.
-/
def jordanPotential
    (N : E → ℝ)
    (x : E) : ℝ :=
  - Real.log |N x|

/--
Operatorial Perelman-like functional.

This is the analytic/thermodynamic flow functional.  The Jordan logarithmic
barrier may appear as one component, but this structure deliberately does not
identify the full Perelman `W`-functional with `-log |N|`.
-/
structure OperatorialWFunctional
    (N : E → ℝ) where
  /-- Installed finite-dimensional functional driving the smooth phase. -/
  W :
    E → ℝ

  /--
  Calibration saying how the Jordan barrier enters the installed functional.

  This is intentionally witness-gated: the full Perelman/Otto analytic model
  may contain curvature, heat-kernel, topological, Weyl, or entropy terms in
  addition to the Jordan barrier.
  -/
  jordan_barrier_component_law : Prop

  /-- Proof/certificate of the Jordan-barrier component law. -/
  jordan_barrier_component_certificate :
    jordan_barrier_component_law

namespace OperatorialWFunctional

variable {N : E → ℝ}
variable (Wop : OperatorialWFunctional N)

/-- The installed Jordan-barrier component law is available as a proof. -/
theorem jordan_barrier_component_valid :
    Wop.jordan_barrier_component_law :=
  Wop.jordan_barrier_component_certificate

end OperatorialWFunctional

/--
A finite-dimensional Hessian-gradient model.

`grad` is the gradient of the chosen potential with respect to the installed
Fisher/Hessian/Krein metric.  `lin` is the linearization used for Drazin
spectral surgery, such as Jordan multiplication `L_X` or a differential of an
adjoint map.
-/
structure HessianGradientModel
    (N : E → ℝ) where
  /-- Gradient in the selected finite-dimensional metric model. -/
  grad :
    (x : E) → regularChamber N x → E

  /-- Linearization used for Drazin surgery. -/
  lin :
    E → (E →ₗ[ℝ] E)

  /-- Drazin data for the chosen linearization. -/
  drazin :
    ∀ x : E, DrazinData (lin x)

/--
Algebraic spectral surgery: project the state to the Drazin core of its
linearization.
-/
def drazinSurgeryMap
    {N : E → ℝ}
    (M : HessianGradientModel N)
    (x : E) : E :=
  (DrazinData.coreProj (M.drazin x)) x

/--
Continuation/capping datum after Drazin spectral surgery.

The Drazin projector removes the nilpotent/generalized-zero sector of the
chosen linearization.  It does not by itself choose the next admissible chamber
or geometric cap.  That extra choice is recorded here.
-/
structure DrazinSurgeryContinuation
    (N : E → ℝ)
    (M : HessianGradientModel N) where
  /-- New admissible post-surgery chamber. -/
  postChamber :
    Set E

  /-- Projection/capping map into the post-surgery chamber. -/
  projectToPostChamber :
    E → E

  /-- The projected Drazin-core state lands in the post-surgery chamber. -/
  project_drazinCore_mem :
    ∀ x : E,
      projectToPostChamber (drazinSurgeryMap M x) ∈ postChamber

namespace DrazinSurgeryContinuation

variable {N : E → ℝ} {M : HessianGradientModel N}
variable (C : DrazinSurgeryContinuation N M)

/-- The post-surgery state after spectral reduction and chamber projection. -/
def continuedState
    (x : E) : E :=
  C.projectToPostChamber (drazinSurgeryMap M x)

/-- The continued state lies in the installed post-surgery chamber. -/
theorem continuedState_mem_postChamber
    (x : E) :
    C.continuedState x ∈ C.postChamber :=
  C.project_drazinCore_mem x

end DrazinSurgeryContinuation

/--
Operatorial stratified gradient flow with Drazin restart at the rank/divisor
boundary.

This is an ODE-level specification on a stratified charge/state space.  A
literal Ricci-flow PDE would require replacing `X : ℝ → E` by a field over a
base manifold and adding the induced metric/curvature API.
-/
structure StratifiedOperatorialFlow
    (N : E → ℝ)
    (X : ℝ → E) where
  /-- Installed Perelman/Otto-like analytic functional. -/
  wFunctional :
    OperatorialWFunctional N

  /-- Installed finite-dimensional Hessian-gradient model. -/
  model :
    HessianGradientModel N

  /--
  Post-surgery continuation datum.

  This separates Drazin spectral reduction from the model-specific choice of
  next chamber/cap.
  -/
  continuation :
    DrazinSurgeryContinuation N model

  /-- Smooth transport phase inside a regular chamber. -/
  smooth_phase :
    ∀ t : ℝ, ∀ h : regularChamber N (X t),
      HasDerivAt X (-(model.grad (X t) h)) t

  /-- Restart time after an algebraic surgery event. -/
  restart :
    ℝ → ℝ

  /-- The restart occurs strictly after the singular time. -/
  restart_gt :
    ∀ t : ℝ, t < restart t

  /-- Drazin spectral surgery at the determinant/rank boundary. -/
  surgery_phase :
    ∀ t : ℝ, ¬ regularChamber N (X t) →
      X (restart t) = continuation.continuedState (X t)

namespace StratifiedOperatorialFlow

variable {N : E → ℝ} {X : ℝ → E}
variable (F : StratifiedOperatorialFlow N X)

/-- The smooth chamber equation is the installed Hessian-gradient equation. -/
theorem hasDerivAt_eq_neg_grad
    (t : ℝ)
    (h : regularChamber N (X t)) :
    HasDerivAt X (-(F.model.grad (X t) h)) t :=
  F.smooth_phase t h

/-- At a rank/divisor boundary, the restart state is the Drazin core projection. -/
theorem restart_eq_drazinSurgery
    (t : ℝ)
    (h : ¬ regularChamber N (X t)) :
    X (F.restart t) = F.continuation.continuedState (X t) :=
  F.surgery_phase t h

/-- The restarted state lies in the installed post-surgery chamber. -/
theorem restart_mem_postChamber
    (t : ℝ)
    (h : ¬ regularChamber N (X t)) :
    X (F.restart t) ∈ F.continuation.postChamber := by
  rw [F.restart_eq_drazinSurgery t h]
  exact F.continuation.continuedState_mem_postChamber (X t)

/-- The Drazin core projector for the linearization at a state is idempotent. -/
theorem coreProjector_idempotent
    (x : E) :
    (DrazinData.coreProj (F.model.drazin x)).comp
        (DrazinData.coreProj (F.model.drazin x))
      =
    DrazinData.coreProj (F.model.drazin x) :=
  (F.model.drazin x).coreProj_idempotent

/-- The Drazin nilpotent/horizon projector for the linearization is idempotent. -/
theorem nilProjector_idempotent
    (x : E) :
    (DrazinData.nilProj (F.model.drazin x)).comp
        (DrazinData.nilProj (F.model.drazin x))
      =
    DrazinData.nilProj (F.model.drazin x) :=
  (F.model.drazin x).nilProj_idempotent

end StratifiedOperatorialFlow

end StratifiedHessianGradient

/-! ## 6. Three-category reduction triad -/

section ReductionTriad

/--
Three compatible reduction mechanisms, kept in their proper categories.

* `analyticReduction` is the Perelman/Otto/JKO smooth-flow readout.
* `algebraicReduction` is the Schur/Drazin spectral split into regular and
  nilpotent projectors.
* `automorphicBoundaryReduction` is the Siegel constant-term followed by a
  Hecke readout.
* `automorphicCuspReduction` subtracts a chosen Eisenstein/boundary lift before
  applying a Hecke/cuspidal readout.

This structure records analogy and compatibility data only.  It does not assert
that analytic flow, algebraic surgery, and automorphic boundary extraction are
literally the same theorem.
-/
structure ReductionTriad
    (AnalyticState AnalyticVelocity AlgOp Automorphic Boundary HeckeBoundary HeckeCusp :
      Type*)
    [Sub Automorphic] where
  /-- Analytic/variational reduction: smooth flow velocity/readout. -/
  analyticReduction :
    AnalyticState → AnalyticVelocity

  /--
  Algebraic reduction: regular/core projector and nilpotent/horizon projector.
  Morally this is `(AAᴰ, 1 - AAᴰ)` for a chosen linearization.
  -/
  algebraicReduction :
    AlgOp → AlgOp × AlgOp

  /-- Siegel constant term along the selected parabolic/unipotent radical. -/
  siegelConstantTerm :
    Automorphic → Boundary

  /-- Chosen Eisenstein/Klingen/theta lift of boundary data. -/
  eisensteinLift :
    Boundary → Automorphic

  /-- Hecke diagonalization/readout of the boundary scattering sector. -/
  heckeBoundary :
    Boundary → HeckeBoundary

  /-- Hecke/cuspidal readout after subtracting the selected boundary lift. -/
  heckeCusp :
    Automorphic → HeckeCusp

  /--
  Certificate that the chosen lift is a right inverse for the constant-term
  map on the installed boundary sector.

  Without this witness, `I - E_P Φ_P` is only a subtraction prescription, not a
  canonical cusp projector.
  -/
  constantTerm_eisensteinLift_law : Prop

  /-- Proof/certificate of the constant-term/lift law. -/
  constantTerm_eisensteinLift_certificate :
    constantTerm_eisensteinLift_law

namespace ReductionTriad

variable
    {AnalyticState AnalyticVelocity AlgOp Automorphic Boundary HeckeBoundary HeckeCusp :
      Type*}
    [Sub Automorphic]

variable
    (R : ReductionTriad
      AnalyticState AnalyticVelocity AlgOp Automorphic Boundary HeckeBoundary HeckeCusp)

/-- Boundary scattering readout: Hecke diagonalization after Siegel constant term. -/
def boundaryScattering
    (F : Automorphic) : HeckeBoundary :=
  R.heckeBoundary (R.siegelConstantTerm F)

/--
Cuspidal-core readout relative to the chosen Eisenstein/boundary lift.

This is `Π_Hecke (F - E_P Φ_P F)`.
-/
def cuspCore
    (F : Automorphic) : HeckeCusp :=
  R.heckeCusp (F - R.eisensteinLift (R.siegelConstantTerm F))

/-- The installed constant-term/lift law is available as a proof. -/
theorem constantTerm_eisensteinLift_valid :
    R.constantTerm_eisensteinLift_law :=
  R.constantTerm_eisensteinLift_certificate

/-- The regular/core algebraic projector readout. -/
def algebraicRegular
    (A : AlgOp) : AlgOp :=
  (R.algebraicReduction A).1

/-- The nilpotent/horizon algebraic projector readout. -/
def algebraicNilpotent
    (A : AlgOp) : AlgOp :=
  (R.algebraicReduction A).2

end ReductionTriad

end ReductionTriad

/-! ## 7. Owner targets -/

/-- Owner target for installing an operatorial Ricci/Otto flow. -/
def OperatorialRicciFlowOwnerTarget
    (State Op : Type*) [AddCommGroup State] [Module ℝ State]
    [Ring Op] [StarRing Op] : Prop :=
  Nonempty (OperatorialRicciFlow State Op)

/-- Owner target for installing Drazin-Perelman surgery on a flow. -/
def DrazinPerelmanSurgeryOwnerTarget
    {State Op : Type*} [AddCommGroup State] [Module ℝ State]
    [Ring Op] [StarRing Op]
    (F : OperatorialRicciFlow State Op) : Prop :=
  Nonempty (DrazinPerelmanSurgery F)

/-- Owner target for linking an operatorial flow horizon to an arithmetic horizon. -/
def OperatorialUnifiedHorizonBridgeOwnerTarget
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    {D : CubicJordanNormDatum J}
    {L : ScatteringLFunction E}
    {State Op : Type*} [AddCommGroup State] [Module ℝ State]
    [Ring Op] [StarRing Op]
    (F : OperatorialRicciFlow State Op)
    (W : UnifiedHorizonWitness J D L) : Prop :=
  Nonempty (OperatorialUnifiedHorizonBridge F W)

end InfoGeometry.Dynamics.OperatorialRicciFlow
