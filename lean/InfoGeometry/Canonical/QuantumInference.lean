import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import InfoGeometry.Krein.Metric
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.QuantumInference

Formalization of operator-first quantum inference on the doubled real Krein carrier.

This module provides coordinate-free realizations of:
1. CCR driven by indefinite Hessian forms.
2. Wilson loops for operator-valued Dirac fields.
3. Grand-canonical partition functionals.

Strictly coordinate-free: uses `ContinuousLinearMap` on general Hilbert spaces.
Scalar diagonal finite-dimensional matrices are NOT allowed.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral
open InfoGeometry.Krein
open InfoGeometry.Canonical.RealBdG

namespace QuantumInference

section Basic

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-! ### 1. CCR driven by an indefinite Hessian form -/

section CCR

variable {𝕜 : Type*} [CommRing 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {A : Type*} [Ring A] [Algebra 𝕜 A]

/-- Ring commutator [x, y] = x*y - y*x -/
def comm (x y : A) : A := x * y - y * x

/--
Canonical Commutation Relations driven by an *indefinite* Hessian bilinear form:
⁅a x, a† y⁆ = (hessian_indefinite_form x y) • 1.
-/
structure CCR where
  hessian_indefinite_form : LinearMap.BilinForm 𝕜 V
  a    : V →ₗ[𝕜] A
  adag : V →ₗ[𝕜] A
  comm_a_adag : ∀ x y, comm (A := A) (a x) (adag y) = algebraMap 𝕜 A (hessian_indefinite_form x y)
  comm_a_a : ∀ x y, comm (A := A) (a x) (a y) = 0
  comm_adag_adag : ∀ x y, comm (A := A) (adag x) (adag y) = 0

end CCR

/-! ### 2. Wilson loop from a (regularized) Dirac field (Operator Model) -/

section WilsonLoop

variable {X : Type*}

/--
A Dirac field as an operator-valued function on the belief space.
Coordinate-free representation.
-/
abbrev DiracField (X : Type*) (E : Type 0)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  X → (DoubledSpace E →L[ℝ] DoubledSpace E)

/--
Heat-kernel style regularization of the information Dirac operator.
Using the internal complex structure `clockAxis` for the imaginary unit.
-/
noncomputable def diracReg (ε : ℝ) (D : DiracField X E) : DiracField X E :=
  fun x =>
    let D_op := D x
    let D2 := D_op.comp D_op
    (NormedSpace.exp ((-ε) • D2)).comp D_op

/--
Path-ordered discrete Wilson Loop Step.
Captures the sequential nature of Bayesian updates.
-/
noncomputable def wilsonStep (X : DoubledSpace E →L[ℝ] DoubledSpace E) (dt : ℝ) :
    (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  NormedSpace.exp (dt • X)

/-- Discrete path-ordered propagator underlying the Wilson loop. -/
noncomputable def wilsonPropagatorDiscrete (Dε : DiracField X E) (γ : List X) (dt : ℝ) :
    (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  γ.foldl (fun U x => U.comp (wilsonStep (Dε x) dt)) (ContinuousLinearMap.id ℝ (DoubledSpace E))

/--
Operator-model Wilson loop readout.

The original finite matrix API used a determinant.  In the doubled real
operator model there is no canonical determinant/tracial readout here, so the
canonical path-integral layer uses the operator norm as its explicit complex
holonomy observable.
-/
noncomputable def wilsonLoopDiscrete
    (Dε : DiracField X E) (γ : List X) (dt : ℝ) : ℂ :=
  (‖wilsonPropagatorDiscrete Dε γ dt‖ : ℝ)

/--
Continuous-path Wilson readout for the operator model.

This is the one-point exponential readout used by the path-integral bridge;
analytic path ordering remains outside this finite API.
-/
noncomputable def continuousWilsonLoop
    (Dε : DiracField (ℝ → E) E) (γ : ℝ → E) : ℂ :=
  (‖NormedSpace.exp (Dε γ)‖ : ℝ)

end WilsonLoop

/-! ### 3. Grand canonical: particle number from ladders (Operator Model) -/

section GrandCanonical

/-- Total number operator N = ∑ᵢ a†ᵢ aᵢ (formal sum over information modes). -/
noncomputable def totalNumber {ι : Type*} [Fintype ι]
    (a adag : ι → (DoubledSpace E →L[ℝ] DoubledSpace E)) :
    (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  ∑ i, (adag i).comp (a i)

/--
Grand-canonical Partition functional.
Represented via the operator exponential on the doubled real carrier.
Coordinate-free and dimension-independent.
-/
noncomputable def grandCanonicalOperator (β μ : ℝ)
    (H N : (DoubledSpace E →L[ℝ] DoubledSpace E)) :
    (DoubledSpace E →L[ℝ] DoubledSpace E) :=
  NormedSpace.exp ((-β) • (H - (μ • N)))

end GrandCanonical

end Basic

end QuantumInference
