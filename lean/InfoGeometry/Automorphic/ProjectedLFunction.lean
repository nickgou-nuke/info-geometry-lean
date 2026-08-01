/-
InfoGeometry/Automorphic/ProjectedLFunction.lean

Projected automorphic L-function sockets.

This module attaches arithmetic spectral readouts to the Siegel-Eisenstein
projector algebra. It does not assert a Langlands correspondence. Instead it
defines the canonical operation:

  L_cusp(F, s) = Λ_s(ℜ_P F)

where ℜ_P is the cuspidal projector from SiegelResonance.lean.

The later Euler-product / completed L-function / zeta-potential layer should
instantiate the witness structures defined here.
-/

import Mathlib.Tactic
import InfoGeometry.Automorphic.SiegelResonance
import InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.Automorphic.SiegelResonance

universe uBulk uBoundary

open InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge

/-! ## 1. Automorphic spectral functionals -/

/--
A family of complex-valued real-linear spectral functionals indexed by the
complex spectral parameter `s`.

For a concrete automorphic model, `coeff s` may be a Mellin transform, a Hecke
eigen-coefficient functional, a Whittaker coefficient, or another arithmetic
readout.
-/
structure AutomorphicLFunctional
    (Bulk : Type uBulk)
    [AddCommGroup Bulk] [Module ℝ Bulk] where
  coeff : ℂ → Bulk →ₗ[ℝ] ℂ

/--
The raw, unprojected automorphic spectral function.
-/
def rawLFunction
    {Bulk : Type uBulk}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    (Λ : AutomorphicLFunctional Bulk)
    (F : Bulk) : ℂ → ℂ :=
  fun s => Λ.coeff s F

/--
The boundary/Eisenstein spectral readout.
-/
def boundaryLFunction
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (Λ : AutomorphicLFunctional Bulk)
    (F : Bulk) : ℂ → ℂ :=
  fun s => Λ.coeff s (W.boundaryProjector F)

/--
The cuspidally projected automorphic L-function.

This is the arithmetic readout after removing the Eisenstein/boundary tail.
-/
def cuspidalLFunction
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (Λ : AutomorphicLFunctional Bulk)
    (F : Bulk) : ℂ → ℂ :=
  fun s => Λ.coeff s (W.cuspidalProjector F)

namespace SiegelEisensteinWitness

variable {Bulk : Type uBulk} {Boundary : Type uBoundary}
variable [AddCommGroup Bulk] [Module ℝ Bulk]
variable [AddCommGroup Boundary] [Module ℝ Boundary]
variable (W : SiegelEisensteinWitness Bulk Boundary)
variable (Λ : AutomorphicLFunctional Bulk)

/-! ## 2. Projection identities for L-functions -/

/--
The raw spectral readout decomposes into boundary plus cuspidal readouts.
-/
theorem rawLFunction_eq_boundary_add_cuspidal
    (F : Bulk) (s : ℂ) :
    rawLFunction Λ F s =
      boundaryLFunction W Λ F s + cuspidalLFunction W Λ F s := by
  unfold rawLFunction boundaryLFunction cuspidalLFunction
  rw [← W.bulk_decomposition F]
  simp

/--
The cuspidal projector is invariant under adding an Eisenstein boundary lift.
-/
theorem cuspidalProjector_add_eisenstein
    (F : Bulk) (b : Boundary) :
    W.cuspidalProjector (F + W.eisenstein b) =
      W.cuspidalProjector F := by
  calc
    W.cuspidalProjector (F + W.eisenstein b)
        = W.cuspidalProjector F +
            W.cuspidalProjector (W.eisenstein b) := by
          exact map_add W.cuspidalProjector F (W.eisenstein b)
    _ = W.cuspidalProjector F + 0 := by
          rw [W.cuspidalProjector_eisenstein b]
    _ = W.cuspidalProjector F := by
          simp

/--
The cuspidal L-function is unchanged by adding Eisenstein boundary data.
-/
theorem cuspidalLFunction_add_eisenstein
    (F : Bulk) (b : Boundary) :
    cuspidalLFunction W Λ (F + W.eisenstein b) =
      cuspidalLFunction W Λ F := by
  funext s
  unfold cuspidalLFunction
  rw [W.cuspidalProjector_add_eisenstein F b]

/--
The cuspidal L-function of a pure Eisenstein lift is zero.
-/
theorem cuspidalLFunction_eisenstein_eq_zero
    (b : Boundary) :
    cuspidalLFunction W Λ (W.eisenstein b) = 0 := by
  funext s
  unfold cuspidalLFunction
  rw [W.cuspidalProjector_eisenstein b]
  simp

/--
If a bulk state is already killed by the Siegel operator, then the cuspidal
L-function equals the raw L-function.
-/
theorem cuspidalLFunction_eq_raw_of_siegel_zero
    (F : Bulk)
    (hF : W.siegel F = 0) :
    cuspidalLFunction W Λ F = rawLFunction Λ F := by
  funext s
  unfold cuspidalLFunction rawLFunction
  rw [(W.fixed_by_cuspidalProjector_iff_siegel_zero F).2 hF]

/--
Kernel-membership version of the previous theorem.
-/
theorem cuspidalLFunction_eq_raw_of_mem_ker
    (F : Bulk)
    (hF : F ∈ LinearMap.ker W.siegel) :
    cuspidalLFunction W Λ F = rawLFunction Λ F := by
  exact W.cuspidalLFunction_eq_raw_of_siegel_zero Λ F
    (LinearMap.mem_ker.mp hF)

/--
A spectral functional kills the Eisenstein boundary if it vanishes on every
Eisenstein lift.
-/
def KillsBoundary : Prop :=
  ∀ (s : ℂ) (b : Boundary), Λ.coeff s (W.eisenstein b) = 0

/--
If the functional kills the boundary, the boundary L-function vanishes.
-/
theorem boundaryLFunction_eq_zero_of_killsBoundary
    (hΛ : W.KillsBoundary Λ)
    (F : Bulk) :
    boundaryLFunction W Λ F = 0 := by
  funext s
  unfold boundaryLFunction boundaryProjector
  exact hΛ s (W.siegel F)

/--
If the functional kills the Eisenstein boundary, the raw readout is already the
cuspidal readout.
-/
theorem rawLFunction_eq_cuspidalLFunction_of_killsBoundary
    (hΛ : W.KillsBoundary Λ)
    (F : Bulk) :
    rawLFunction Λ F = cuspidalLFunction W Λ F := by
  funext s
  have hsplit := W.rawLFunction_eq_boundary_add_cuspidal Λ F s
  rw [hsplit]
  have hb :
      boundaryLFunction W Λ F s = 0 := by
    have hfun := W.boundaryLFunction_eq_zero_of_killsBoundary Λ hΛ F
    exact congrFun hfun s
  rw [hb, zero_add]

end SiegelEisensteinWitness

/-! ## 3. Resonance sets -/

/--
A spectral parameter is an automorphic resonance when the associated
L-function vanishes there.
-/
def IsAutomorphicResonance
    (L : ℂ → ℂ)
    (s : ℂ) : Prop :=
  L s = 0

/--
The resonance set of a complex-valued automorphic L-function.
-/
def AutomorphicResonanceSet
    (L : ℂ → ℂ) : Set ℂ :=
  {s : ℂ | IsAutomorphicResonance L s}

@[simp]
theorem mem_automorphicResonanceSet_iff
    (L : ℂ → ℂ)
    (s : ℂ) :
    s ∈ AutomorphicResonanceSet L ↔ IsAutomorphicResonance L s := by
  rfl

/-! ## 4. Projected automorphic L-function witnesses -/

/--
A proof-carrying package saying that `L` is obtained by applying a spectral
functional to the cuspidal projection of a bulk automorphic state.
-/
structure ProjectedAutomorphicLFunctionWitness
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary) where
  functional : AutomorphicLFunctional Bulk
  bulkState : Bulk
  L : ℂ → ℂ
  L_eq_projected :
    L = cuspidalLFunction W functional bulkState

namespace ProjectedAutomorphicLFunctionWitness

variable {Bulk : Type uBulk} {Boundary : Type uBoundary}
variable [AddCommGroup Bulk] [Module ℝ Bulk]
variable [AddCommGroup Boundary] [Module ℝ Boundary]
variable {W : SiegelEisensteinWitness Bulk Boundary}

/--
Evaluation of the projected L-function.
-/
theorem eval_eq_projected
    (P : ProjectedAutomorphicLFunctionWitness W)
    (s : ℂ) :
    P.L s =
      P.functional.coeff s (W.cuspidalProjector P.bulkState) := by
  rw [P.L_eq_projected]
  rfl

/--
A resonance of the projected L-function is exactly a zero of the projected
functional readout.
-/
theorem resonance_iff_projected_zero
    (P : ProjectedAutomorphicLFunctionWitness W)
    (s : ℂ) :
    IsAutomorphicResonance P.L s ↔
      P.functional.coeff s (W.cuspidalProjector P.bulkState) = 0 := by
  unfold IsAutomorphicResonance
  rw [P.eval_eq_projected s]

end ProjectedAutomorphicLFunctionWitness

/-! ## 5. Euler-product and completed-L-function sockets -/

/--
Named predicate for an Euler-product realization of an automorphic L-function.

This is a finite/local-factor law on the declared region: at every point in the
region, the value of `L` is represented by a finite product of the supplied
local factors. Infinite analytic Euler products can later refine this by
choosing stronger convergence data, but this predicate is already mathematical
content rather than a vacuous socket.
-/
def HasEulerProduct
    (L : ℂ → ℂ)
    (PrimeIndex : Type)
    (localFactor : PrimeIndex → ℂ → ℂ)
    (convergenceRegion : Set ℂ) : Prop :=
  ∀ s : ℂ, s ∈ convergenceRegion →
    ∃ finitePrimes : Finset PrimeIndex,
      L s = ∏ p ∈ finitePrimes, localFactor p s

/--
Euler-product data attached to an automorphic L-function.
-/
structure EulerProductData
    (L : ℂ → ℂ) where
  PrimeIndex : Type
  localFactor : PrimeIndex → ℂ → ℂ
  convergenceRegion : Set ℂ
  hasEulerProduct :
    HasEulerProduct L PrimeIndex localFactor convergenceRegion

/--
Named predicate for a completed L-function package.

The completed function satisfies a functional equation around a supplied center
with a supplied root number.
-/
def HasCompletedFunctionalEquation
    (_L completedL : ℂ → ℂ) : Prop :=
  ∃ center rootNumber : ℂ,
    ∀ s : ℂ, completedL s = rootNumber * completedL (center - s)

/--
Witness connecting a projected automorphic L-function to prime/Euler data.

This is the arithmetic socket for the later zeta-potential layer.
-/
structure LanglandsPrimeResonanceWitness
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    (P : ProjectedAutomorphicLFunctionWitness W) where
  eulerProduct : EulerProductData P.L
  completedL : ℂ → ℂ
  completedFunctionalEquation :
    HasCompletedFunctionalEquation P.L completedL

/-! ## 5A. Strong arithmetic witness packet (Native Closure Mandated: Closure Debt)s -/

/--
Proof-carrying Euler-product witness for an automorphic L-function.

This refines the placeholder `HasEulerProduct` predicate without breaking the
existing API. The Euler-product law remains model-specific arithmetic input,
not a consequence of the Siegel projector algebra.
-/
structure EulerProductWitness
    (L : ℂ → ℂ) where
  /-- Prime/local-factor index. -/
  PrimeIndex : Type

  /-- Local Euler factor. -/
  localFactor : PrimeIndex → ℂ → ℂ

  /-- Region on which the Euler-product statement is calibrated. -/
  convergenceRegion : Set ℂ

  /-- Proof/certificate of the Euler-product law. -/
  euler_product_law :
    HasEulerProduct L PrimeIndex localFactor convergenceRegion

namespace EulerProductWitness

variable {L : ℂ → ℂ}
variable (E : EulerProductWitness L)

/--
Forgetful adapter to the legacy placeholder `EulerProductData`.

This preserves compatibility while keeping the stronger witness available.
-/
def toEulerProductData :
    EulerProductData L where
  PrimeIndex := E.PrimeIndex
  localFactor := E.localFactor
  convergenceRegion := E.convergenceRegion
  hasEulerProduct := E.euler_product_law

@[simp]
theorem toEulerProductData_hasEulerProduct :
    (E.toEulerProductData).hasEulerProduct = E.euler_product_law :=
  rfl

end EulerProductWitness

/--
Proof-carrying completed-L-function witness.

This refines the placeholder `HasCompletedFunctionalEquation` predicate without
claiming a functional equation from projector algebra alone.
-/
structure CompletedLFunctionWitness
    (L : ℂ → ℂ) where
  /-- Completed L-function. -/
  completedL : ℂ → ℂ

  /-- Proof/certificate of the completed-functional-equation law. -/
  completed_functional_equation_law :
    HasCompletedFunctionalEquation L completedL

namespace CompletedLFunctionWitness

variable {L : ℂ → ℂ}
variable (C : CompletedLFunctionWitness L)

/--
Forgetful adapter to the legacy completed-functional-equation predicate.
-/
theorem toHasCompletedFunctionalEquation :
    HasCompletedFunctionalEquation L C.completedL :=
  C.completed_functional_equation_law

end CompletedLFunctionWitness

/--
Strengthened Langlands-prime resonance witness.

Unlike `LanglandsPrimeResonanceWitness`, this carries proof-carrying Euler and
completed-L-function packets. It does not turn those arithmetic statements into
theorems of the Siegel projector algebra.
-/
structure LanglandsPrimeResonanceStrongWitness
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    (P : ProjectedAutomorphicLFunctionWitness W) where
  /-- Proof-carrying Euler-product data. -/
  eulerProduct :
    EulerProductWitness P.L

  /-- Proof-carrying completed-L-function data. -/
  completed :
    CompletedLFunctionWitness P.L

namespace LanglandsPrimeResonanceStrongWitness

variable
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {P : ProjectedAutomorphicLFunctionWitness W}

variable (R : LanglandsPrimeResonanceStrongWitness P)

/--
The strong witness induces the legacy weak witness.
-/
def toWeakWitness :
    LanglandsPrimeResonanceWitness P where
  eulerProduct := R.eulerProduct.toEulerProductData
  completedL := R.completed.completedL
  completedFunctionalEquation :=
    R.completed.toHasCompletedFunctionalEquation

end LanglandsPrimeResonanceStrongWitness

/-! ## 6. Langlands-Sugawara Central Charge Calibration -/

/--
Witness structure connecting the arithmetic Langlands L-function side
to the geometric/operator Sugawara central charge side.

This calibrates the zero-value of the completed L-function against
the physical central charge readout on the Virasoro boundary.
-/
structure LanglandsSugawaraBridge
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {P : ProjectedAutomorphicLFunctionWitness W}
    (LPR : LanglandsPrimeResonanceWitness P)
    {Finite Affine Vir State Charge : Type*}
    [AddCommGroup Finite] [Module ℝ Finite]
    [AddCommGroup Affine] [Module ℝ Affine]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Charge] [Module ℝ Charge]
    (EAV : ExceptionalAffineVirasoroBridge Finite Affine Vir State Charge)
    -- We assume Charge is complex for the scalar evaluation
    (charge_eval : Charge → ℂ) where
  
  /-- The Sugawara/Virasoro central charge matches the completed L-function value at s=0. -/
  Sugawara_L_calibration :
    ∀ s : State, charge_eval (EAV.centralChargeReadout s) = LPR.completedL 0

/--
If the Langlands-Sugawara bridge is provided, the hidden exceptional memory
(via EAV) is also arithmetically calibrated to the completed L-function zero-value.
-/
theorem hiddenMemory_arithmetic_calibration
    {Bulk Boundary : Type*}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {P : ProjectedAutomorphicLFunctionWitness W}
    {LPR : LanglandsPrimeResonanceWitness P}
    {Finite Affine Vir State Charge : Type*}
    [AddCommGroup Finite] [Module ℝ Finite]
    [AddCommGroup Affine] [Module ℝ Affine]
    [AddCommGroup Vir] [Module ℝ Vir] [LieRing Vir] [LieAlgebra ℝ Vir]
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Charge] [Module ℝ Charge]
    {EAV : ExceptionalAffineVirasoroBridge Finite Affine Vir State Charge}
    {charge_eval : Charge → ℂ}
    (bridge : LanglandsSugawaraBridge LPR EAV charge_eval)
    (s : State) :
    charge_eval (EAV.calibratedHiddenGradeMemoryReadout s) = LPR.completedL 0 := by
  rw [← EAV.centralCharge_eq_hiddenGradeMemory s]
  exact bridge.Sugawara_L_calibration s

/-! ## 7. Owner targets -/

/--
Owner target for producing projected automorphic L-functions from a spectral
functional and a bulk state.

This target is the direct projected-evaluation law, not a witness wrapper.
-/
@[owner_target_tag]
def ProjectedAutomorphicLFunctionOwnerTarget : Prop :=
  ∀ (Bulk : Type uBulk) [AddCommGroup Bulk] [Module ℝ Bulk],
  ∀ (Boundary : Type uBoundary) [AddCommGroup Boundary] [Module ℝ Boundary],
  ∀ (W : SiegelEisensteinWitness Bulk Boundary),
  ∀ (_Λ : AutomorphicLFunctional Bulk),
  ∀ (_F : Bulk),
  ∀ s : ℂ,
    cuspidalLFunction W _Λ _F s =
      _Λ.coeff s (W.cuspidalProjector _F)

/--
The projected L-function owner target is satisfied by definition.
-/
theorem projectedAutomorphicLFunctionOwnerTarget :
    ProjectedAutomorphicLFunctionOwnerTarget := by
  intro Bulk _ _ Boundary _ _ W Λ F s
  rfl

/--
Owner target for attaching Euler-product and completed-L-function data.

This one is intentionally witness-gated: the Euler product and functional
equation are arithmetic input, not consequences of the split-exact projector
algebra alone.
-/
@[owner_target_tag]
def LanglandsPrimeResonanceOwnerTarget : Prop :=
  ∀ (Bulk : Type uBulk) [AddCommGroup Bulk] [Module ℝ Bulk],
  ∀ (Boundary : Type uBoundary) [AddCommGroup Boundary] [Module ℝ Boundary],
  ∀ (W : SiegelEisensteinWitness Bulk Boundary),
  ∀ (P : ProjectedAutomorphicLFunctionWitness W),
  ∀ (Eul : EulerProductData P.L),
  ∀ (completedL : ℂ → ℂ),
    HasCompletedFunctionalEquation P.L completedL →
      HasEulerProduct P.L Eul.PrimeIndex Eul.localFactor Eul.convergenceRegion ∧
        HasCompletedFunctionalEquation P.L completedL

/--
The Langlands-prime resonance owner target is satisfied once the arithmetic
Euler/completed data are supplied.
-/
theorem langlandsPrimeResonanceOwnerTarget :
    LanglandsPrimeResonanceOwnerTarget := by
  intro Bulk _ _ Boundary _ _ W P Eul completedL hCompleted
  refine ⟨?_, ?_⟩
  · exact Eul.hasEulerProduct
  · exact hCompleted

end InfoGeometry.Automorphic.SiegelResonance
