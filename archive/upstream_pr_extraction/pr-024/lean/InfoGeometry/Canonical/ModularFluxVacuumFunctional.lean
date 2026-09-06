import Mathlib
import InfoGeometry.Canonical.SplitCliffordSourceWickBase

/-!
# InfoGeometry.Canonical.ModularFluxVacuumFunctional

Finite seed:
`ω_{Δ-1}(A) = ⟪Ω, A ((Δ - 1) Ω)⟫`, and if `Δ Ω = Ω` then this vanishes.

This file also records the concrete `M₂(ℝ)` split-Clifford seed used by the
local nilpotent modular flux model. The concrete section proves

`<0| A (Δ - 1) |0> = 0`

for every finite test matrix `A`, because `(Δ - 1)|0> = N|0> = 0`.

No Type III theorem, no predual topology, and no infinite-dimensional boundedness
claim is made here.
-/

namespace InfoGeometry.Canonical.ModularFluxVacuumFunctional

section Algebraic

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Centered modular flux operator `Δ - 1`. -/
def modularFlux (Δ : Module.End ℂ E) : Module.End ℂ E :=
  Δ - LinearMap.id

/-- Flux action seen at vector level. -/
def vacuumFluxAction (Ω : E) (A X : Module.End ℂ E) : E :=
  A (X Ω)

/-- If `Δ Ω = Ω`, then `A ((Δ - 1) Ω) = 0` for all test operators `A`. -/
theorem vacuumFluxAction_eq_zero_of_fixed
    (Δ : Module.End ℂ E) (Ω : E)
    (hfix : Δ Ω = Ω) :
    ∀ A : Module.End ℂ E, vacuumFluxAction Ω A (modularFlux Δ) = 0 := by
  intro A
  have hflux : modularFlux Δ Ω = 0 := by
    simp [modularFlux, hfix]
  simp [vacuumFluxAction, hflux]

end Algebraic

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Vector-functional pairing for the centered modular flux. -/
def vacuumFluxFunctional (Ω : E) (A X : Module.End ℂ E) : ℂ :=
  inner ℂ Ω (vacuumFluxAction Ω A X)

/-- Finite vacuum-functional annihilation for fixed vector `Ω`. -/
theorem vacuumFluxFunctional_eq_zero_of_fixed
    (Δ : Module.End ℂ E) (Ω : E)
    (hfix : Δ Ω = Ω) :
    ∀ A : Module.End ℂ E, vacuumFluxFunctional Ω A (modularFlux Δ) = 0 := by
  intro A
  have hact : vacuumFluxAction Ω A (modularFlux Δ) = 0 :=
    vacuumFluxAction_eq_zero_of_fixed (Δ := Δ) (Ω := Ω) hfix A
  simp [vacuumFluxFunctional, hact]

end InnerProduct

section ConcreteM2Seed

open Matrix
open InfoGeometry.Canonical.SplitCliffordSourceWickBase

/-- Local concrete matrix carrier for the finite seed. -/
abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The local nilpotent modular perturbation `Δ = 1 + N` in `M₂(ℝ)`. -/
def DeltaM2 : M2R :=
  (1 : M2R) + N

/-- The concrete modular flux `Δ - 1` is exactly the nilpotent atom `N`. -/
@[simp]
theorem DeltaM2_flux_eq_N :
    DeltaM2 - (1 : M2R) = N := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [DeltaM2, N]

/-- The concrete modular flux annihilates the split-Clifford vacuum. -/
@[simp]
theorem DeltaM2_flux_vac :
    (DeltaM2 - (1 : M2R)) * vac = 0 := by
  rw [DeltaM2_flux_eq_N]
  simpa [a] using vacuum_annihilation

/-- The concrete modular perturbation fixes the split-Clifford vacuum. -/
@[simp]
theorem DeltaM2_vac :
    DeltaM2 * vac = vac := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [DeltaM2, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

/--
Finite ket functional on `M₂(ℝ)` test operators:
`A ↦ <0| A w>`, implemented as extraction of the first coordinate.
-/
def ketFunctionalM2
    (w : Matrix (Fin 2) (Fin 1) ℝ) : M2R →ₗ[ℝ] ℝ where
  toFun A := (A * w) 0 0
  map_add' A B := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  map_smul' c A := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- The ordinary local vacuum functional `A ↦ <0|A|0>`. -/
def vacuumFunctionalM2 : M2R →ₗ[ℝ] ℝ :=
  ketFunctionalM2 vac

/-- The finite modular-flux vacuum functional `A ↦ <0|A(Δ-1)|0>`. -/
def modularFluxVacuumFunctionalM2 : M2R →ₗ[ℝ] ℝ :=
  ketFunctionalM2 ((DeltaM2 - (1 : M2R)) * vac)

/-- Evaluation formula for the concrete modular-flux vacuum functional. -/
@[simp]
theorem modularFluxVacuumFunctionalM2_apply
    (A : M2R) :
    modularFluxVacuumFunctionalM2 A =
      (A * ((DeltaM2 - (1 : M2R)) * vac)) 0 0 := by
  rfl

/--
The concrete modular-flux vacuum functional is identically zero.

This is the finite `M₂(ℝ)` theorem-level seed for
`<Ω| A (Δ - 1) |Ω> = 0` at the fixed vacuum point.
-/
theorem modularFluxVacuumFunctionalM2_apply_zero
    (A : M2R) :
    modularFluxVacuumFunctionalM2 A = 0 := by
  change (A * ((DeltaM2 - (1 : M2R)) * vac)) 0 0 = 0
  rw [DeltaM2_flux_vac]
  simp

/-- Linear-map form of the concrete zero-functional theorem. -/
theorem modularFluxVacuumFunctionalM2_eq_zero :
    modularFluxVacuumFunctionalM2 = 0 := by
  ext A
  exact modularFluxVacuumFunctionalM2_apply_zero A

/-- Applying `Δ` to the ket does not change the vacuum functional. -/
theorem ketFunctionalM2_Delta_vac_eq_vacuumFunctionalM2 :
    ketFunctionalM2 (DeltaM2 * vac) = vacuumFunctionalM2 := by
  rw [DeltaM2_vac]
  rfl

/-- Pointwise form: `<0|AΔ|0> = <0|A|0>`. -/
theorem vacuumFunctionalM2_Delta_apply
    (A : M2R) :
    ketFunctionalM2 (DeltaM2 * vac) A = vacuumFunctionalM2 A := by
  rw [ketFunctionalM2_Delta_vac_eq_vacuumFunctionalM2]

/-- Nilpotent local modular flow `E(t) = 1 + tN`. -/
def nilpotentFlowM2 (t : ℝ) : M2R :=
  (1 : M2R) + t • N

/-- The nilpotent flow starts at the identity. -/
@[simp]
theorem nilpotentFlowM2_zero :
    nilpotentFlowM2 0 = (1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [nilpotentFlowM2, N]

/-- At time `1`, the nilpotent flow is the modular perturbation `Δ`. -/
@[simp]
theorem nilpotentFlowM2_one :
    nilpotentFlowM2 1 = DeltaM2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [nilpotentFlowM2, DeltaM2, N]

/-- The nilpotent-flow flux annihilates the vacuum for every real parameter `t`. -/
theorem nilpotentFlowM2_flux_vacuum
    (t : ℝ) :
    (nilpotentFlowM2 t - (1 : M2R)) * vac = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [nilpotentFlowM2, N, vac, Matrix.mul_apply, Fin.sum_univ_two]

/-- The nilpotent-flow flux functional is zero for every `t`. -/
theorem nilpotentFlowM2_flux_functional_zero
    (t : ℝ) (A : M2R) :
    ketFunctionalM2 ((nilpotentFlowM2 t - (1 : M2R)) * vac) A = 0 := by
  change (A * ((nilpotentFlowM2 t - (1 : M2R)) * vac)) 0 0 = 0
  rw [nilpotentFlowM2_flux_vacuum]
  simp

end ConcreteM2Seed

end InfoGeometry.Canonical.ModularFluxVacuumFunctional
