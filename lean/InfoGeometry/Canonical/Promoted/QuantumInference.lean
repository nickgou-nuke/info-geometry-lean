import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import InfoGeometry.Krein.Metric
import InfoGeometry.Canonical.Promoted.SpectralInference

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace InfoGeometry.Research.QuantumInference

/-! ### 1. CCR driven by an indefinite Hessian form -/

section CCR

variable {𝕜 : Type*} [CommRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {A : Type*} [Ring A] [Algebra 𝕜 A]

/-- Ring commutator [x, y] = x*y - y*x -/
def comm (x y : A) : A := x * y - y * x

/--
Canonical Commutation Relations driven by an *indefinite* Hessian bilinear form:
⁅a x, a† y⁆ = (hessianIndefiniteForm x y) • 1.
-/
structure CCR where
  hessianIndefiniteForm : LinearMap.BilinForm 𝕜 E
  a    : E →ₗ[𝕜] A
  adag : E →ₗ[𝕜] A
  comm_a_adag : ∀ x y, comm (A := A) (a x) (adag y) = algebraMap 𝕜 A (hessianIndefiniteForm x y)
  comm_a_a : ∀ x y, comm (A := A) (a x) (a y) = 0
  comm_adag_adag : ∀ x y, comm (A := A) (adag x) (adag y) = 0

end CCR

/-! ### 2. Wilson loop from a (regularized) Dirac field (matrix model) -/

section WilsonLoop

open Complex

variable {X : Type*}
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Dirac field as a matrix-valued function on the belief space. -/
abbrev DiracField (X : Type*) (n : Type*) := X → Matrix n n ℂ

/-- Heat-kernel style regularization of the information Dirac operator. -/
noncomputable def diracReg (ε : ℝ) (D : DiracField X n) : DiracField X n :=
  fun x => (NormedSpace.exp ((-ε : ℂ) • (D x * D x))) * (D x)

/--
Path-ordered discrete Wilson Loop.
W(γ₀…γₖ) = tr( Πᵢ exp(Dε(γᵢ) Δt) ).
Captures the sequential nature of Bayesian updates.
-/
noncomputable def wilsonStep (Dε : DiracField X n) (dt : ℂ) (x : X) : Matrix n n ℂ :=
  NormedSpace.exp (dt • Dε x)

/-- Discrete path-ordered propagator underlying the Wilson loop. -/
noncomputable def wilsonPropagatorDiscrete (Dε : DiracField X n) (γ : List X) (dt : ℂ) :
    Matrix n n ℂ :=
  γ.foldl (fun U x => U * wilsonStep Dε dt x) 1

noncomputable def wilsonLoopDiscrete (Dε : DiracField X n) (γ : List X) (dt : ℂ) : ℂ :=
  Matrix.trace (wilsonPropagatorDiscrete Dε γ dt)

/--
Formalization of the Path-Ordered Exponential (The Dyson Series).
Defined as the limit of the discrete Wilson loop as the partition 
of the path γ becomes infinitesimally fine.
This operator measures the total information holonomy.
-/
noncomputable def continuousWilsonLoop (Dε : DiracField (ℝ → X) n) (γ : ℝ → X) : ℂ :=
  -- Continuous surrogate: trace of the exponentiated regularized Dirac field on the path.
  Matrix.trace (NormedSpace.exp (Dε γ))

end WilsonLoop

/-! ### 3. Grand canonical: particle number from ladders -/

section GrandCanonical

open Complex

variable {n : Type*} [Fintype n] [DecidableEq n]
abbrev Op (n : Type*) [Fintype n] [DecidableEq n] := Matrix n n ℂ

/-- Total number operator N = ∑ᵢ a†ᵢ aᵢ (sum over finite information modes). -/
noncomputable def totalNumber {ι : Type*} [Fintype ι]
    (a adag : ι → Op n) : Op n :=
  ∑ i, (adag i) * (a i)

/-- Grand-canonical Partition Function: Z(β, μ) = tr( exp( -β (H - μ N) ) ). -/
noncomputable def grandCanonicalZ (β μ : ℂ) (H N : Op n) : ℂ :=
  Matrix.trace (NormedSpace.exp (-(β) • (H - μ • N)))

end GrandCanonical

end InfoGeometry.Research.QuantumInference
