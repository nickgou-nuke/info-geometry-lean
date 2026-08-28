import InfoGeometry.Canonical.YangMillsContinuum
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.InformationPartitionCore

Stable analytic core for moment/partition calculus on modular generators over
doubled-space endomorphisms.

This file owns only the lower partition/log-partition syntax and its derivative
lemmas. It keeps the established declaration names in the
`InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData` namespace
so downstream modules can be rerooted without renaming the theorem surface.
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
@[rep_depth operator]
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
Derivative of the partition function at an arbitrary parameter.  This is the
native Banach-algebra exponential derivative, followed by the continuous
linear readout; the factor order is retained.
-/
theorem hasDerivAt_informationPartitionFunction
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => informationPartitionFunction ω K s)
      (ω (NormedSpace.exp (τ • K) * K)) τ := by
  have hExp :
      HasDerivAt (fun s : ℝ => NormedSpace.exp (s • K))
        (NormedSpace.exp (τ • K) * K) τ :=
    hasDerivAt_exp_smul_const K τ
  simpa [informationPartitionFunction] using
    (hasDerivAt_const (x := τ) (c := ω)).clm_apply hExp

/-- The second derivative of the partition readout at the origin. -/
theorem deriv2_informationPartitionFunction_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    deriv (fun t : ℝ =>
      deriv (fun s : ℝ => informationPartitionFunction ω K s) t) 0 =
        ω (K * K) := by
  have hfirst : ∀ t : ℝ,
      deriv (fun s : ℝ => informationPartitionFunction ω K s) t =
        ω (NormedSpace.exp (t • K) * K) := by
    intro t
    exact (hasDerivAt_informationPartitionFunction (ω := ω) (K := K) t).deriv
  rw [show (fun t : ℝ =>
      deriv (fun s : ℝ => informationPartitionFunction ω K s) t) =
      (fun t : ℝ => ω (NormedSpace.exp (t • K) * K)) by
        funext t; exact hfirst t]
  have hExp := hasDerivAt_exp_smul_const K (0 : ℝ)
  have hMul :
      HasDerivAt (fun t : ℝ => NormedSpace.exp (t • K) * K) (K * K) 0 := by
    simpa using hExp.mul (hasDerivAt_const (x := (0 : ℝ)) (c := K))
  have hReadout := (hasDerivAt_const (x := (0 : ℝ)) (c := ω)).clm_apply hMul
  simpa using hReadout.deriv

/-- Third derivative of the operatorial partition readout at the origin. -/
theorem deriv3_informationPartitionFunction_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    deriv (fun t : ℝ =>
      deriv (fun s : ℝ =>
        deriv (fun u : ℝ => informationPartitionFunction ω K u) s) t) 0 =
      ω (K * K * K) := by
  have hfirst : ∀ t : ℝ,
      deriv (fun s : ℝ => informationPartitionFunction ω K s) t =
        ω (NormedSpace.exp (t • K) * K) := by
    intro t
    exact (hasDerivAt_informationPartitionFunction (ω := ω) (K := K) t).deriv
  have hsecond : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => ω (NormedSpace.exp (s • K) * K))
        (ω (NormedSpace.exp (t • K) * K * K)) t := by
    intro t
    have hExp := hasDerivAt_exp_smul_const K t
    have hMul : HasDerivAt
        (fun s : ℝ => NormedSpace.exp (s • K) * K)
        (NormedSpace.exp (t • K) * K * K) t := by
      simpa using hExp.mul (hasDerivAt_const (x := t) (c := K))
    simpa using (hasDerivAt_const (x := t) (c := ω)).clm_apply hMul
  have hsecond_eq : ∀ t : ℝ,
      deriv (fun s : ℝ =>
        deriv (fun u : ℝ => informationPartitionFunction ω K u) s) t =
        ω (NormedSpace.exp (t • K) * K * K) := by
    intro t
    rw [show (fun s : ℝ =>
        deriv (fun u : ℝ => informationPartitionFunction ω K u) s) =
        (fun s : ℝ => ω (NormedSpace.exp (s • K) * K)) by
          funext s
          exact hfirst s]
    exact (hsecond t).deriv
  rw [show (fun t : ℝ =>
      deriv (fun s : ℝ =>
        deriv (fun u : ℝ => informationPartitionFunction ω K u) s) t) =
      (fun t : ℝ => ω (NormedSpace.exp (t • K) * K * K)) by
        funext t
        exact hsecond_eq t]
  have hExp := hasDerivAt_exp_smul_const K (0 : ℝ)
  have hMul : HasDerivAt
      (fun t : ℝ => NormedSpace.exp (t • K) * K * K)
      (K * K * K) 0 := by
    simpa [mul_assoc] using
      (hExp.mul (hasDerivAt_const (x := (0 : ℝ)) (c := K))).mul
        (hasDerivAt_const (x := (0 : ℝ)) (c := K))
  simpa using ((hasDerivAt_const (x := (0 : ℝ)) (c := ω)).clm_apply hMul).deriv

/-- Fourth derivative of the operatorial partition readout at the origin. -/
theorem deriv4_informationPartitionFunction_zero
    (ω : EndH E →L[ℝ] ℝ) (K : EndH E) :
    deriv (fun t : ℝ =>
      deriv (fun s : ℝ =>
        deriv (fun u : ℝ =>
          deriv (fun v : ℝ => informationPartitionFunction ω K v) u) s) t) 0 =
      ω (K * K * K * K) := by
  have hfirst : ∀ t : ℝ,
      deriv (fun s : ℝ => informationPartitionFunction ω K s) t =
        ω (NormedSpace.exp (t • K) * K) := by
    intro t
    exact (hasDerivAt_informationPartitionFunction (ω := ω) (K := K) t).deriv
  have hsecond : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => ω (NormedSpace.exp (s • K) * K))
        (ω (NormedSpace.exp (t • K) * K * K)) t := by
    intro t
    have hExp := hasDerivAt_exp_smul_const K t
    have hMul : HasDerivAt
        (fun s : ℝ => NormedSpace.exp (s • K) * K)
        (NormedSpace.exp (t • K) * K * K) t := by
      simpa using hExp.mul (hasDerivAt_const (x := t) (c := K))
    simpa using (hasDerivAt_const (x := t) (c := ω)).clm_apply hMul
  have hsecond_eq : ∀ t : ℝ,
      deriv (fun s : ℝ =>
        deriv (fun u : ℝ => informationPartitionFunction ω K u) s) t =
        ω (NormedSpace.exp (t • K) * K * K) := by
    intro t
    rw [show (fun s : ℝ =>
        deriv (fun u : ℝ => informationPartitionFunction ω K u) s) =
        (fun s : ℝ => ω (NormedSpace.exp (s • K) * K)) by
          funext s
          exact hfirst s]
    exact (hsecond t).deriv
  have hthird : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => ω (NormedSpace.exp (s • K) * K * K))
        (ω (NormedSpace.exp (t • K) * K * K * K)) t := by
    intro t
    have hExp := hasDerivAt_exp_smul_const K t
    have hMul : HasDerivAt
        (fun s : ℝ => NormedSpace.exp (s • K) * K * K)
        (NormedSpace.exp (t • K) * K * K * K) t := by
      simpa [mul_assoc] using
        (hExp.mul (hasDerivAt_const (x := t) (c := K))).mul
          (hasDerivAt_const (x := t) (c := K))
    simpa using (hasDerivAt_const (x := t) (c := ω)).clm_apply hMul
  have hthird_eq : ∀ t : ℝ,
      deriv (fun s : ℝ =>
        deriv (fun u : ℝ =>
          deriv (fun v : ℝ => informationPartitionFunction ω K v) u) s) t =
        ω (NormedSpace.exp (t • K) * K * K * K) := by
    intro t
    rw [show (fun s : ℝ =>
        deriv (fun u : ℝ =>
          deriv (fun v : ℝ => informationPartitionFunction ω K v) u) s) =
        (fun s : ℝ => ω (NormedSpace.exp (s • K) * K * K)) by
          funext s
          exact hsecond_eq s]
    exact (hthird t).deriv
  rw [show (fun t : ℝ =>
      deriv (fun s : ℝ =>
        deriv (fun u : ℝ =>
          deriv (fun v : ℝ => informationPartitionFunction ω K v) u) s) t) =
      (fun t : ℝ => ω (NormedSpace.exp (t • K) * K * K * K)) by
        funext t
        exact hthird_eq t]
  have hExp := hasDerivAt_exp_smul_const K (0 : ℝ)
  have hMul : HasDerivAt
      (fun t : ℝ => NormedSpace.exp (t • K) * K * K * K)
      (K * K * K * K) 0 := by
    simpa [mul_assoc] using
      ((hExp.mul (hasDerivAt_const (x := (0 : ℝ)) (c := K))).mul
        (hasDerivAt_const (x := (0 : ℝ)) (c := K))).mul
          (hasDerivAt_const (x := (0 : ℝ)) (c := K))
  simpa using ((hasDerivAt_const (x := (0 : ℝ)) (c := ω)).clm_apply hMul).deriv

/-
  let Z : ℝ → ℝ := fun t => informationPartitionFunction ω K t
  have hZ : ∀ t : ℝ, HasDerivAt Z (ω (NormedSpace.exp (t • K) * K)) t := by
    intro t
    simpa [Z] using
      (hasDerivAt_informationPartitionFunction (ω := ω) (K := K) t)
  have hlogderiv : ∀ t : ℝ,
      deriv (fun s : ℝ => logInformationPartitionFunction ω K s) t =
        (Z t)⁻¹ * ω (NormedSpace.exp (t • K) * K) := by
    intro t
    have h := (hZ t).log (hne t)
    simpa [Z, logInformationPartitionFunction, informationPartitionFunction,
      div_eq_mul_inv, mul_comm] using h.deriv
  have hZprime : HasDerivAt
      (fun t : ℝ => ω (NormedSpace.exp (t • K) * K)) (ω (K * K)) 0 := by
    have hExp := hasDerivAt_exp_smul_const K (0 : ℝ)
    have hMul :
        HasDerivAt (fun t : ℝ => NormedSpace.exp (t • K) * K) (K * K) 0 := by
      simpa using hExp.mul (hasDerivAt_const (x := (0 : ℝ)) (c := K))
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := ω)).clm_apply hMul
  have hZ0 : HasDerivAt Z (ω K) 0 := by
    simpa [Z, hω1] using (hZ 0)
  have hinv := hZ0.inv (by simpa [Z, hω1] using hne 0)
  have hprod := hinv.mul hZprime
  rw [show (fun t : ℝ =>
      deriv (fun s : ℝ => logInformationPartitionFunction ω K s) t) =
      (fun t : ℝ => (Z t)⁻¹ * ω (NormedSpace.exp (t • K) * K)) by
        funext t; exact hlogderiv t]
  have hderiv := hprod.deriv
  have hZzero : Z 0 = 1 := by
    simp [Z, hω1]
  have hfun :
      (Z⁻¹ * (fun t : ℝ => ω (NormedSpace.exp (t • K) * K))) =
        (fun t : ℝ => (Z t)⁻¹ * ω (NormedSpace.exp (t • K) * K)) := by
    funext t
    rfl
  rw [← hfun]
  rw [hZzero] at hderiv
  simpa [informationPartitionFunction, pow_two,
    sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using hderiv
-/

/--
Log-partition derivative at `τ = 0` under the nondegeneracy property
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
