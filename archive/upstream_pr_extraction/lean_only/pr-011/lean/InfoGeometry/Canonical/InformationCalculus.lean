import InfoGeometry.Canonical.YangMillsContinuum
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# InfoGeometry.Canonical.InformationCalculus

Moment/partition calculus for modular generators on doubled-space endomorphisms.

Core definitions:
- `informationPartitionFunction ω K τ = ω (exp (τ • K))`
- `logInformationPartitionFunction = log ∘ informationPartitionFunction`

Core theorems:
- evaluation at `τ = 0, 1`
- derivative at `τ = 0`
- log-partition derivative at `τ = 0` under explicit nonzero/normalization
  hypotheses.
-/

namespace InfoGeometry.Canonical.InformationCalculus

open InfoGeometry.Canonical.YangMillsContinuum

namespace ModularRadonNikodymData

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable local instance : NormedRing (EndH E) := inferInstance
noncomputable local instance : NormedAlgebra ℝ (EndH E) := inferInstance
noncomputable local instance : NormedSpace ℝ (EndH E) := inferInstance
local instance : IsTopologicalRing (EndH E) := inferInstance
local instance : CompleteSpace (EndH E) := inferInstance

/-- Modular moment/partition function `Z(τ) = ω(exp(τ • K))`. -/
noncomputable def informationPartitionFunction
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) (τ : ℝ) : ℝ :=
  ω (NormedSpace.exp (τ • K))

/-- Log-partition `log Z(τ)`. -/
noncomputable def logInformationPartitionFunction
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) (τ : ℝ) : ℝ :=
  Real.log (informationPartitionFunction ω K τ)

@[simp] theorem informationPartitionFunction_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    informationPartitionFunction ω K 0 = ω (1 : EndH E) := by
  simp [informationPartitionFunction]

@[simp] theorem informationPartitionFunction_one
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    informationPartitionFunction ω K 1 = ω (NormedSpace.exp K) := by
  simp [informationPartitionFunction]

/--
Derivative of the modular partition function at `τ = 0`:
`Z'(0) = ω(K)`.
-/
theorem hasDerivAt_informationPartitionFunction_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    HasDerivAt (fun τ : ℝ => informationPartitionFunction ω K τ) (ω K) 0 := by
  have hω : HasDerivAt (fun _ : ℝ => ω) (0 : EndH E →L[ℝ] ℝ) 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := ω))
  have hExp : HasDerivAt (fun τ : ℝ => NormedSpace.exp (τ • K)) K 0 := by
    simpa using (hasDerivAt_exp_smul_const (x := K) (t := (0 : ℝ)))
  have hApply :
      HasDerivAt
        (fun τ : ℝ => (fun _ : ℝ => ω) τ (NormedSpace.exp (τ • K)))
        ((0 : EndH E →L[ℝ] ℝ) (NormedSpace.exp (0 • K)) + ω K)
        0 :=
    hω.clm_apply hExp
  simpa [informationPartitionFunction] using hApply

/-- Scalar derivative corollary of `hasDerivAt_informationPartitionFunction_zero`. -/
theorem deriv_informationPartitionFunction_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    deriv (fun τ : ℝ => informationPartitionFunction ω K τ) 0 = ω K :=
  (hasDerivAt_informationPartitionFunction_zero (ω := ω) (K := K)).deriv

/--
Log-partition derivative at `τ = 0` under the nondegeneracy hypothesis
`ω(1) ≠ 0`.
-/
theorem hasDerivAt_logInformationPartitionFunction_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E)
    (hω1 : ω (1 : EndH E) ≠ 0) :
    HasDerivAt (fun τ : ℝ => logInformationPartitionFunction ω K τ)
      ((ω (1 : EndH E))⁻¹ * ω K) 0 := by
  have hPart :
      HasDerivAt (fun τ : ℝ => informationPartitionFunction ω K τ) (ω K) 0 :=
    hasDerivAt_informationPartitionFunction_zero (ω := ω) (K := K)
  have hLog :
      HasDerivAt Real.log ((informationPartitionFunction ω K 0)⁻¹)
        (informationPartitionFunction ω K 0) := by
    exact Real.hasDerivAt_log (by simpa using hω1)
  have hComp :
      HasDerivAt
        (fun τ : ℝ => Real.log (informationPartitionFunction ω K τ))
        ((informationPartitionFunction ω K 0)⁻¹ * ω K)
        0 :=
    hLog.comp 0 hPart
  simpa [logInformationPartitionFunction, informationPartitionFunction] using hComp

/--
Normalized-state specialization:
if `ω(1) = 1`, then `(log Z)'(0) = ω(K)`.
-/
  theorem hasDerivAt_logInformationPartitionFunction_zero_of_normalized
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E)
    (hω1 : ω (1 : EndH E) = 1) :
    HasDerivAt (fun τ : ℝ => logInformationPartitionFunction ω K τ) (ω K) 0 := by
  have hω1ne : ω (1 : EndH E) ≠ 0 := by simp [hω1]
  simpa [hω1] using
    (hasDerivAt_logInformationPartitionFunction_zero
      (ω := ω) (K := K) hω1ne)

/--
Continuum modular specialization:
`Z'(0) = ω(K_mod)` for the RN-derived modular Hamiltonian.
-/
theorem hasDerivAt_informationPartitionFunction_zero_modularHamiltonian
    (ω : EndH E →L[ℝ] ℝ) (M : ModularRadonNikodymData E) :
    HasDerivAt
      (fun τ : ℝ => informationPartitionFunction ω M.modularHamiltonian τ)
      (ω M.modularHamiltonian) 0 :=
  hasDerivAt_informationPartitionFunction_zero (ω := ω) (K := M.modularHamiltonian)

/--
Continuum modular specialization:
for normalized `ω`, `(log Z)'(0) = ω(K_mod)`.
-/
theorem hasDerivAt_logInformationPartitionFunction_zero_modularHamiltonian_of_normalized
    (ω : EndH E →L[ℝ] ℝ) (M : ModularRadonNikodymData E)
    (hω1 : ω (1 : EndH E) = 1) :
    HasDerivAt
      (fun τ : ℝ => logInformationPartitionFunction ω M.modularHamiltonian τ)
      (ω M.modularHamiltonian) 0 :=
  hasDerivAt_logInformationPartitionFunction_zero_of_normalized
    (ω := ω) (K := M.modularHamiltonian) hω1

end ModularRadonNikodymData

end InfoGeometry.Canonical.InformationCalculus
