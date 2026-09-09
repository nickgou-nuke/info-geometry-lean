import InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
import Mathlib.Algebra.Colimit.Module

/-!
# Compatible noncommutative state nets on the matrix tower

This owner is the algebraic descent interface needed before any Gibbs/KMS
claim at nonzero inverse temperature.  A stage functional and its transition
compatibility are explicit inputs.  The direct-limit functional is then the
native universal `Module.DirectLimit.lift`; no density, exponential, or
positivity is inferred.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet

open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

abbrev Carrier := CuntzMatrixAlgebraicStarColimit.Carrier

abbrev StageFunctional := ∀ n : ℕ, MatrixStage n →ₗ[ℂ] ℂ

instance linearDirectedSystem :
    DirectedSystem MatrixStage
      (fun _ _ hij => (rawMap hij).toAlgHom.toLinearMap) where
  map_self := by
    intro i x
    exact congrArg (fun f => f x) (concreteMap_id i)
  map_map := by
    intro i j k hij hjk x
    simpa using congrArg (fun f => f x) (concreteMap_comp hij hjk)

def Compatible (φ : StageFunctional) : Prop :=
  ∀ {i j : ℕ} (hij : i ≤ j) (x : MatrixStage i),
    φ j (rawMap hij x) = φ i x

def colimitFunctional (φ : StageFunctional) (hφ : Compatible φ) : Carrier →ₗ[ℂ] ℂ :=
  DirectLimit.Module.lift ℂ ℕ MatrixStage
    (fun _ _ hij => (rawMap hij).toAlgHom.toLinearMap)
    φ
    (by
      intro i j hij x
      exact hφ hij x)

@[simp]
theorem colimitFunctional_stage (φ : StageFunctional) (hφ : Compatible φ)
    (n : ℕ) (x : MatrixStage n) :
    colimitFunctional φ hφ (stageInjection n x) = φ n x := by
  simpa [stageInjection] using
    (DirectLimit.Module.lift_of
      (R := ℂ) (ι := ℕ) (G := MatrixStage)
      (f := fun _ _ hij => (rawMap hij).toAlgHom.toLinearMap)
      φ (by intro i j hij x; exact hφ hij x) x)

theorem colimitFunctional_eq_of_stage_eq
    (φ ψ : StageFunctional) (hφ : Compatible φ) (hψ : Compatible ψ)
    (h : ∀ n x, φ n x = ψ n x) :
    colimitFunctional φ hφ = colimitFunctional ψ hψ := by
  apply LinearMap.ext
  intro y
  induction y using DirectLimit.induction with
  | _ n x =>
      change colimitFunctional φ hφ (stageInjection n x) =
        colimitFunctional ψ hψ (stageInjection n x)
      rw [colimitFunctional_stage, colimitFunctional_stage]
      exact h n x

def traceStageFunctional : StageFunctional := matrixTraceFunctional

theorem traceStageFunctional_compatible : Compatible traceStageFunctional := by
  intro i j hij x
  change matrixTraceFunctional j (rawMap hij x) = matrixTraceFunctional i x
  simpa [rawMap] using concreteMap_trace hij x

def traceColimitFunctional : Carrier →ₗ[ℂ] ℂ :=
  colimitFunctional traceStageFunctional traceStageFunctional_compatible

@[simp]
theorem traceColimitFunctional_stage (n : ℕ) (x : MatrixStage n) :
    traceColimitFunctional (stageInjection n x) = matrixTraceFunctional n x := by
  exact colimitFunctional_stage traceStageFunctional traceStageFunctional_compatible n x

theorem traceColimitFunctional_eq_traceFunctional :
    traceColimitFunctional = traceFunctional := by
  apply LinearMap.ext
  intro y
  induction y using DirectLimit.induction with
  | _ n x =>
      change traceColimitFunctional (stageInjection n x) =
        traceFunctional (stageInjection n x)
      rw [traceColimitFunctional_stage, traceFunctional_stage]
      rfl

def weightedStageFunctional (D : ∀ n : ℕ, MatrixStage n) : StageFunctional :=
  fun n => matrixTraceFunctional n ∘ₗ
    LinearMap.mulRight ℂ (D n)

@[simp]
theorem weightedStageFunctional_apply (D : ∀ n : ℕ, MatrixStage n)
    (n : ℕ) (x : MatrixStage n) :
    weightedStageFunctional D n x = matrixTraceFunctional n (x * D n) := by
  rfl

def WeightedCompatible (D : ∀ n : ℕ, MatrixStage n) : Prop :=
  Compatible (weightedStageFunctional D)

/-! A density net is compatible when it is transported by the same successor
embedding as the observable tower.  This is the exact finite hypothesis needed
for a Gibbs-weighted functional to descend; no exponential or Hamiltonian is
constructed here. -/

def DensityCompatible (D : ∀ n : ℕ, MatrixStage n) : Prop :=
  ∀ n, D (n + 1) = concreteStep n (D n)

/-! Every chosen stage-zero density has a canonical compatible transport along
the concrete matrix tower.  This supplies a genuine family, while leaving
positivity of the chosen density as an explicit finite hypothesis. -/

def propagatedDensity (D₀ : MatrixStage 0) : ∀ n, MatrixStage n
  | 0 => D₀
  | n + 1 => concreteStep n (propagatedDensity D₀ n)

theorem propagatedDensity_compatible (D₀ : MatrixStage 0) :
    DensityCompatible (propagatedDensity D₀) := by
  intro n
  rfl

theorem propagatedDensity_trace (D₀ : MatrixStage 0) (z : ℂ)
    (h₀ : matrixTraceFunctional 0 D₀ = z) :
    ∀ n, matrixTraceFunctional n (propagatedDensity D₀ n) = z
  | 0 => h₀
  | n + 1 => by
      rw [propagatedDensity]
      have htrace := concreteData.trace_compatible n
        (propagatedDensity D₀ n)
      simpa [matrixTraceState, matrixTraceFunctional] using
        htrace.trans (propagatedDensity_trace D₀ z h₀ n)

theorem weightedStageFunctional_compatible_of_density_compatible
    (D : ∀ n : ℕ, MatrixStage n) (hD : DensityCompatible D) :
    WeightedCompatible D := by
  intro i j hij x
  induction hij with
  | refl =>
      simp [rawMap, CuntzMatrixTraceTower.concreteMap_id]
  | @step j hij ih =>
      rw [weightedStageFunctional_apply, weightedStageFunctional_apply]
      rw [show rawMap (Nat.le.step hij) x =
        concreteStep j (rawMap hij x) by
          simpa [rawMap, CuntzMatrixTraceTower.concreteMap,
            CuntzMatrixTraceTower.map_succ] using
            congrArg (fun f => f x)
              (CuntzMatrixTraceTower.map_succ concreteData hij)]
      rw [hD j, ← map_mul]
      have htrace := concreteData.trace_compatible j (rawMap hij x * D j)
      change matrixTraceFunctional (j + 1)
          (concreteStep j (rawMap hij x * D j)) =
        matrixTraceFunctional i (x * D i)
      simpa [matrixTraceState, matrixTraceFunctional] using
        htrace.trans (by
          simpa [weightedStageFunctional_apply] using ih)

def weightedColimitFunctional (D : ∀ n : ℕ, MatrixStage n)
    (hD : WeightedCompatible D) : Carrier →ₗ[ℂ] ℂ :=
  colimitFunctional (weightedStageFunctional D) hD

def weightedColimitFunctional_of_density_compatible
    (D : ∀ n : ℕ, MatrixStage n) (hD : DensityCompatible D) :
    Carrier →ₗ[ℂ] ℂ :=
  weightedColimitFunctional D
    (weightedStageFunctional_compatible_of_density_compatible D hD)

@[simp]
theorem weightedColimitFunctional_stage (D : ∀ n : ℕ, MatrixStage n)
    (hD : WeightedCompatible D) (n : ℕ) (x : MatrixStage n) :
    weightedColimitFunctional D hD (stageInjection n x) =
      matrixTraceFunctional n (x * D n) := by
  exact colimitFunctional_stage (weightedStageFunctional D) hD n x |>.trans
    (weightedStageFunctional_apply D n x)

theorem weightedColimitFunctional_one
    (D : ∀ n : ℕ, MatrixStage n) (hD : WeightedCompatible D)
    (hOne : ∀ n, matrixTraceFunctional n (D n) = 1) :
    weightedColimitFunctional D hD (1 : Carrier) = 1 := by
  let hstage : ∀ n, weightedStageFunctional D n (1 : MatrixStage n) = 1 := by
    intro n
    simpa [weightedStageFunctional_apply] using hOne n
  have h := colimitFunctional_stage (weightedStageFunctional D) hD 0
    (1 : MatrixStage 0)
  simpa [stageInjection, DirectLimit.one_def, hstage] using h

theorem weightedColimitFunctional_positive
    (D : ∀ n : ℕ, MatrixStage n) (hD : WeightedCompatible D)
    (hPositive : ∀ n x,
      0 ≤ (matrixTraceFunctional n (star x * x * D n)).re)
    (x : Carrier) :
    0 ≤ (weightedColimitFunctional D hD (star x * x)).re := by
  induction x using DirectLimit.induction with
  | _ n a =>
      have harg :
          star (⟦⟨n, a⟩⟧ : Carrier) * (⟦⟨n, a⟩⟧ : Carrier) =
            stageInjection n (star a * a) := by
        change star (stageInjection n a) * stageInjection n a =
          stageInjection n (star a * a)
        rw [← stageInjection_star, ← stageInjection_mul]
      rw [harg]
      rw [weightedColimitFunctional_stage]
      exact hPositive n a

lemma matrixTraceFunctional_star_native (n : ℕ) (A : MatrixStage n) :
    matrixTraceFunctional n (star A) =
      star (matrixTraceFunctional n A) := by
  rw [matrixTraceFunctional_apply, matrixTraceFunctional_apply]
  have htrace : Matrix.trace (star A) = star (Matrix.trace A) := by
    rw [← Matrix.trace_conjTranspose]
    rfl
  rw [htrace]
  have hcoef : star (1 / (2 ^ n : ℂ)) = 1 / (2 ^ n : ℂ) := by
    have hcast : (1 / (2 ^ n : ℂ)) =
        ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast]
    simp
  rw [star_mul, hcoef]
  rw [mul_comm]

def normalizedWeightedStageFunctional (D : ∀ n : ℕ, MatrixStage n)
    (z : ℝ) : StageFunctional :=
  fun n => (z : ℂ)⁻¹ • weightedStageFunctional D n

def normalizedWeightedCompatible (D : ∀ n : ℕ, MatrixStage n)
    (z : ℝ) (hD : WeightedCompatible D) :
    Compatible (normalizedWeightedStageFunctional D z) := by
  intro i j hij x
  simp [normalizedWeightedStageFunctional, hD hij x]

def normalizedWeightedColimitFunctional (D : ∀ n : ℕ, MatrixStage n)
    (z : ℝ) (hD : WeightedCompatible D) : Carrier →ₗ[ℂ] ℂ :=
  colimitFunctional (normalizedWeightedStageFunctional D z)
    (normalizedWeightedCompatible D z hD)

@[simp]
theorem normalizedWeightedColimitFunctional_stage
    (D : ∀ n : ℕ, MatrixStage n) (z : ℝ) (hD : WeightedCompatible D)
    (n : ℕ) (x : MatrixStage n) :
    normalizedWeightedColimitFunctional D z hD (stageInjection n x) =
      (z : ℂ)⁻¹ * matrixTraceFunctional n (x * D n) := by
  simpa [normalizedWeightedColimitFunctional,
    normalizedWeightedStageFunctional, weightedStageFunctional_apply,
    smul_eq_mul] using
    (colimitFunctional_stage (normalizedWeightedStageFunctional D z)
      (normalizedWeightedCompatible D z hD) n x)

theorem normalizedWeightedColimitFunctional_one
    (D : ∀ n : ℕ, MatrixStage n) (z : ℝ) (hD : WeightedCompatible D)
    (hz : z ≠ 0) (hOne : ∀ n, matrixTraceFunctional n (D n) = (z : ℂ)) :
    normalizedWeightedColimitFunctional D z hD (1 : Carrier) = 1 := by
  have hstage : ∀ n,
      normalizedWeightedStageFunctional D z n (1 : MatrixStage n) = 1 := by
    intro n
    simp [normalizedWeightedStageFunctional, weightedStageFunctional_apply,
      hOne n, smul_eq_mul]
    exact inv_mul_cancel₀ (by exact_mod_cast hz)
  have h := colimitFunctional_stage
    (normalizedWeightedStageFunctional D z)
    (normalizedWeightedCompatible D z hD) 0 (1 : MatrixStage 0)
  simpa [normalizedWeightedColimitFunctional, stageInjection,
    DirectLimit.one_def, hstage] using h

theorem normalizedWeightedColimitFunctional_positive
    (D : ∀ n : ℕ, MatrixStage n) (z : ℝ) (hD : WeightedCompatible D)
    (hz : 0 < z)
    (hPositive : ∀ n x,
      0 ≤ (matrixTraceFunctional n (star x * x * D n)).re)
    (x : Carrier) :
    0 ≤ (normalizedWeightedColimitFunctional D z hD (star x * x)).re := by
  induction x using DirectLimit.induction with
  | _ n a =>
      have harg :
          star (⟦⟨n, a⟩⟧ : Carrier) * (⟦⟨n, a⟩⟧ : Carrier) =
            stageInjection n (star a * a) := by
        change star (stageInjection n a) * stageInjection n a =
          stageInjection n (star a * a)
        rw [← stageInjection_star, ← stageInjection_mul]
      rw [harg, normalizedWeightedColimitFunctional_stage]
      have hz' : 0 < z⁻¹ := inv_pos.mpr hz
      have hzcomplex : ((z : ℂ)⁻¹).re = z⁻¹ := by
        simp [Complex.inv_re, Complex.normSq]
      have hzcomplex_im : ((z : ℂ)⁻¹).im = 0 := by
        simp [Complex.inv_im, Complex.normSq]
      rw [Complex.mul_re, hzcomplex]
      simpa [hzcomplex_im] using
        mul_nonneg (le_of_lt hz') (hPositive n a)

theorem normalizedWeightedColimitFunctional_star
    (D : ∀ n : ℕ, MatrixStage n) (z : ℝ) (hD : WeightedCompatible D)
    (hSelfAdjoint : ∀ n, star (D n) = D n) (x : Carrier) :
    normalizedWeightedColimitFunctional D z hD (star x) =
      star (normalizedWeightedColimitFunctional D z hD x) := by
  induction x using DirectLimit.induction with
  | _ n a =>
      change normalizedWeightedColimitFunctional D z hD
          (star (stageInjection n a)) =
        star (normalizedWeightedColimitFunctional D z hD
          (stageInjection n a))
      rw [← stageInjection_star,
        normalizedWeightedColimitFunctional_stage,
        normalizedWeightedColimitFunctional_stage]
      have htrace :
          matrixTraceFunctional n (star a * D n) =
            star (matrixTraceFunctional n (a * D n)) := by
        have h := matrixTraceFunctional_star_native n (a * D n)
        rw [star_mul, hSelfAdjoint n] at h
        calc
          matrixTraceFunctional n (star a * D n) =
              matrixTraceFunctional n (D n * star a) := by
                simpa using Matrix.trace_mul_comm (star a) (D n)
          _ = star (matrixTraceFunctional n (a * D n)) := h
      rw [htrace]
      simp

/-! ### Explicit finite Gibbs nets

The following definitions specialize the generic descent interface to the
finite Gibbs functionals already proved in
`FiniteMatrixGibbsFunctional`.  Compatibility remains an explicit hypothesis:
the matrix-tower embedding alone does not imply it for an arbitrary
Hamiltonian family. -/

def gibbsStageFunctional
    (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ) : StageFunctional :=
  fun n => gibbsFunctional (H n) (hH n) β

/-! The density itself is functorial under the concrete matrix embedding.
This is the native CFC statement; compatibility of the normalized Gibbs
functionals still additionally requires the corresponding partition-function
transport, so it remains an explicit hypothesis below. -/

theorem gibbsDensity_concreteStep
    (n : ℕ) (H : MatrixStage n) (H' : MatrixStage (n + 1))
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (hstep : H' = concreteStep n H) (β : ℝ) :
    concreteStep n (gibbsDensity H hH β) = gibbsDensity H' hH' β := by
  subst H'
  change concreteStep n (hH.cfc (expWeight β)) = hH'.cfc (expWeight β)
  rw [← hH.cfc_eq, ← hH'.cfc_eq]
  exact StarAlgHom.map_cfc (concreteStep n) (expWeight β) H
    (by unfold expWeight; fun_prop)
    ((concreteStep n).toAlgHom.toLinearMap.continuous_of_finiteDimensional)
    hH hH'

theorem gibbsFunctional_concreteStep
    (n : ℕ) (H : MatrixStage n) (H' : MatrixStage (n + 1))
    (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (hstep : H' = concreteStep n H) (β : ℝ) (A : MatrixStage n) :
    gibbsFunctional H' hH' β (concreteStep n A) =
      gibbsFunctional H hH β A := by
  have hD : concreteStep n (gibbsDensity H hH β) =
      gibbsDensity H' hH' β :=
    gibbsDensity_concreteStep n H H' hH hH' hstep β
  rw [gibbsFunctional_apply, gibbsFunctional_apply, ← hD]
  rw [← map_mul]
  rw [concreteStep_trace]
  rw [concreteStep_trace]
  ring

theorem gibbsStageFunctional_compatible
    (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ)
    (hHamiltonian : ∀ n, H (n + 1) = concreteStep n (H n)) :
    Compatible (gibbsStageFunctional H hH β) := by
  intro i j hij x
  induction hij with
  | refl =>
      change gibbsFunctional (H i) (hH i) β
        (rawMap (le_refl i) x) = _
      rw [rawMap, concreteMap_id]
      rfl
  | @step j hij ih =>
      change gibbsFunctional (H (j + 1)) (hH (j + 1)) β
          ((map concreteData (Nat.le.step hij)) x) = _
      rw [map_succ concreteData hij]
      change gibbsFunctional (H (j + 1)) (hH (j + 1)) β
          (concreteStep j (rawMap hij x)) = _
      exact gibbsFunctional_concreteStep j (H j) (H (j + 1))
        (hH j) (hH (j + 1)) (hHamiltonian j) β (rawMap hij x) |>.trans ih

def gibbsColimitFunctional
    (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ)
    (hCompat : Compatible (gibbsStageFunctional H hH β)) : Carrier →ₗ[ℂ] ℂ :=
  colimitFunctional (gibbsStageFunctional H hH β) hCompat

@[simp]
theorem gibbsColimitFunctional_stage
    (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ)
    (hCompat : Compatible (gibbsStageFunctional H hH β))
    (n : ℕ) (x : MatrixStage n) :
    gibbsColimitFunctional H hH β hCompat (stageInjection n x) =
      gibbsFunctional (H n) (hH n) β x := by
  exact colimitFunctional_stage (gibbsStageFunctional H hH β) hCompat n x

theorem gibbsColimitFunctional_one
    (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ)
    (hCompat : Compatible (gibbsStageFunctional H hH β)) :
    gibbsColimitFunctional H hH β hCompat (1 : Carrier) = 1 := by
  let hstage : ∀ n,
      gibbsStageFunctional H hH β n (1 : MatrixStage n) = 1 := by
    intro n
    exact gibbsFunctional_one (H n) (hH n) β
  have h := colimitFunctional_stage (gibbsStageFunctional H hH β)
    hCompat 0 (1 : MatrixStage 0)
  simpa [gibbsColimitFunctional, stageInjection, DirectLimit.one_def, hstage] using h

theorem gibbsColimitFunctional_positive
    (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ)
    (hCompat : Compatible (gibbsStageFunctional H hH β))
    (x : Carrier) :
    0 ≤ (gibbsColimitFunctional H hH β hCompat (star x * x)).re := by
  induction x using DirectLimit.induction with
  | _ n a =>
      have harg :
          star (⟦⟨n, a⟩⟧ : Carrier) * (⟦⟨n, a⟩⟧ : Carrier) =
            stageInjection n (star a * a) := by
        change star (stageInjection n a) * stageInjection n a =
          stageInjection n (star a * a)
        rw [← stageInjection_star, ← stageInjection_mul]
      rw [harg, gibbsColimitFunctional_stage]
      exact gibbsFunctional_positive (H n) (hH n) β a

theorem gibbsColimitFunctional_star
    (H : ∀ n, MatrixStage n)
    (hH : ∀ n, (H n).IsHermitian) (β : ℝ)
    (hCompat : Compatible (gibbsStageFunctional H hH β))
    (x : Carrier) :
    gibbsColimitFunctional H hH β hCompat (star x) =
      star (gibbsColimitFunctional H hH β hCompat x) := by
  induction x using DirectLimit.induction with
  | _ n a =>
      change gibbsColimitFunctional H hH β hCompat
          (star (stageInjection n a)) =
        star (gibbsColimitFunctional H hH β hCompat
          (stageInjection n a))
      rw [← stageInjection_star,
        gibbsColimitFunctional_stage,
        gibbsColimitFunctional_stage]
      exact gibbsFunctional_star (H n) (hH n) β a

/-! ### A constructed nonzero-temperature family

The tensor embedding itself now constructs a compatible Hamiltonian family
from one self-adjoint stage-zero matrix.  This removes the need to postulate a
separate compatibility witness for this concrete family.
-/

def propagatedHamiltonian (H₀ : MatrixStage 0) : ∀ n, MatrixStage n
  | 0 => H₀
  | n + 1 => concreteStep n (propagatedHamiltonian H₀ n)

theorem propagatedHamiltonian_compatible (H₀ : MatrixStage 0) :
    ∀ n, propagatedHamiltonian H₀ (n + 1) =
      concreteStep n (propagatedHamiltonian H₀ n) := by
  intro n
  rfl

theorem propagatedHamiltonian_isHermitian
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) :
    ∀ n, (propagatedHamiltonian H₀ n).IsHermitian := by
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
      rw [propagatedHamiltonian]
      change star (concreteStep n (propagatedHamiltonian H₀ n)) =
        concreteStep n (propagatedHamiltonian H₀ n)
      rw [← map_star]
      exact congrArg (concreteStep n) ih

def propagatedHamiltonianGibbsColimit
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) : Carrier →ₗ[ℂ] ℂ :=
  gibbsColimitFunctional
    (propagatedHamiltonian H₀)
    (propagatedHamiltonian_isHermitian H₀ h₀) β
    (gibbsStageFunctional_compatible
      (propagatedHamiltonian H₀)
      (propagatedHamiltonian_isHermitian H₀ h₀) β
      (propagatedHamiltonian_compatible H₀))

theorem propagatedHamiltonianGibbsColimit_one
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) :
    propagatedHamiltonianGibbsColimit H₀ h₀ β (1 : Carrier) = 1 := by
  exact gibbsColimitFunctional_one
    (propagatedHamiltonian H₀)
    (propagatedHamiltonian_isHermitian H₀ h₀) β
    (gibbsStageFunctional_compatible
      (propagatedHamiltonian H₀)
      (propagatedHamiltonian_isHermitian H₀ h₀) β
      (propagatedHamiltonian_compatible H₀))

theorem propagatedHamiltonianGibbsColimit_positive
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) (x : Carrier) :
    0 ≤ (propagatedHamiltonianGibbsColimit H₀ h₀ β (star x * x)).re := by
  exact gibbsColimitFunctional_positive
    (propagatedHamiltonian H₀)
    (propagatedHamiltonian_isHermitian H₀ h₀) β
    (gibbsStageFunctional_compatible
      (propagatedHamiltonian H₀)
      (propagatedHamiltonian_isHermitian H₀ h₀) β
      (propagatedHamiltonian_compatible H₀)) x

theorem propagatedHamiltonianGibbsColimit_star
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) (x : Carrier) :
    propagatedHamiltonianGibbsColimit H₀ h₀ β (star x) =
      star (propagatedHamiltonianGibbsColimit H₀ h₀ β x) := by
  exact gibbsColimitFunctional_star
    (propagatedHamiltonian H₀)
    (propagatedHamiltonian_isHermitian H₀ h₀) β
    (gibbsStageFunctional_compatible
      (propagatedHamiltonian H₀)
      (propagatedHamiltonian_isHermitian H₀ h₀) β
      (propagatedHamiltonian_compatible H₀)) x

end InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
