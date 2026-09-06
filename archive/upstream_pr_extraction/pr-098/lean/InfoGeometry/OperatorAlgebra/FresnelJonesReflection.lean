/-
InfoGeometry/OperatorAlgebra/FresnelJonesReflection.lean

Fresnel/Jones reflection data.

The `s/p` basis is the Fresnel eigenbasis of a smooth isotropic interface.  The
`L/R` circular basis is the Cartan/helicity/chiral basis.  They are related,
but they are not the same basis.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FresnelJonesReflection

/-! ## 1. Two-component Jones carriers -/

/-- Two-component Jones vector. -/
abbrev JonesVector :=
  Fin 2 → ℂ

/-- Circular-basis two-component Jones vector. -/
abbrev CircularJonesVector :=
  Fin 2 → ℂ

/-- Index for the `s` Fresnel channel, also used as the first circular coordinate. -/
def sIndex : Fin 2 :=
  0

/-- Index for the `p` Fresnel channel, also used as the second circular coordinate. -/
def pIndex : Fin 2 :=
  1

/-! ## 2. Diagonal Fresnel operators and projectors -/

/--
Diagonal Jones operator in the `s/p` basis.
-/
def diagonalJones
    (r_s r_p : ℂ) : JonesVector →ₗ[ℂ] JonesVector where
  toFun E := fun i =>
    if i = sIndex then r_s * E sIndex else r_p * E pIndex
  map_add' := by
    intro E F
    ext i
    fin_cases i <;> simp [sIndex, pIndex, mul_add]
  map_smul' := by
    intro c E
    ext i
    fin_cases i <;> simp [sIndex, pIndex, mul_left_comm]

/-- The `s`-sector projector in the Fresnel `s/p` basis. -/
def sProjector : JonesVector →ₗ[ℂ] JonesVector :=
  diagonalJones 1 0

/-- The `p`-sector projector in the Fresnel `s/p` basis. -/
def pProjector : JonesVector →ₗ[ℂ] JonesVector :=
  diagonalJones 0 1

/-- The `s` Fresnel projector is idempotent. -/
theorem sProjector_idempotent :
    sProjector.comp sProjector = sProjector := by
  ext E i
  fin_cases i <;> simp [sProjector, diagonalJones, sIndex, pIndex]

/-- The `p` Fresnel projector is idempotent. -/
theorem pProjector_idempotent :
    pProjector.comp pProjector = pProjector := by
  ext E i
  fin_cases i <;> simp [pProjector, diagonalJones, sIndex, pIndex]

/-- The `s` and `p` projectors are disjoint in this order. -/
theorem sProjector_comp_pProjector :
    sProjector.comp pProjector = 0 := by
  ext E i
  fin_cases i <;> simp [sProjector, pProjector, diagonalJones, sIndex, pIndex]

/-- The `p` and `s` projectors are disjoint in this order. -/
theorem pProjector_comp_sProjector :
    pProjector.comp sProjector = 0 := by
  ext E i
  fin_cases i <;> simp [sProjector, pProjector, diagonalJones, sIndex, pIndex]

/-- The two Fresnel projectors sum to the identity. -/
theorem sProjector_add_pProjector :
    sProjector + pProjector = LinearMap.id := by
  ext E i
  fin_cases i <;> simp [sProjector, pProjector, diagonalJones, sIndex, pIndex]

/-! ## 3. Fresnel reflection data -/

/--
Fresnel reflection datum in the `s/p` basis.
-/
structure FresnelReflectionDatum where
  /-- `s`-polarized Fresnel amplitude. -/
  r_s : ℂ

  /-- `p`-polarized Fresnel amplitude. -/
  r_p : ℂ

namespace FresnelReflectionDatum

/-- The reflected Jones operator in the `s/p` Fresnel basis. -/
def operator
    (F : FresnelReflectionDatum) : JonesVector →ₗ[ℂ] JonesVector :=
  diagonalJones F.r_s F.r_p

/-- Brewster branch: the `p` reflection channel vanishes while `s` remains nonzero. -/
def IsBrewster
    (F : FresnelReflectionDatum) : Prop :=
  F.r_p = 0 ∧ F.r_s ≠ 0

/--
If the `p` coefficient vanishes, the Fresnel operator is a scalar multiple of
the `s` projector.
-/
theorem operator_eq_s_scalar_projector_of_rp_eq_zero
    (F : FresnelReflectionDatum)
    (hp : F.r_p = 0) :
    F.operator = F.r_s • sProjector := by
  ext E i
  fin_cases i <;> simp [operator, diagonalJones, sProjector, sIndex, pIndex, hp]

/-- A Jones vector is pure `s`-polarized if its `p` component vanishes. -/
def IsSPure
    (E : JonesVector) : Prop :=
  E pIndex = 0

/-- Brewster reflection produces pure `s`-polarized output. -/
theorem output_s_pure_of_brewster
    (F : FresnelReflectionDatum)
    (hF : F.IsBrewster)
    (E : JonesVector) :
    IsSPure (F.operator E) := by
  dsimp [IsSPure, operator, diagonalJones]
  simp [sIndex, pIndex, hF.1]

end FresnelReflectionDatum

/-! ## 4. Transparent-interface Fresnel coefficients -/

/-- Fresnel `s`-polarized reflection coefficient. -/
def fresnelRS
    (n₁ n₂ θᵢ θₜ : ℝ) : ℝ :=
  (n₁ * Real.cos θᵢ - n₂ * Real.cos θₜ) /
    (n₁ * Real.cos θᵢ + n₂ * Real.cos θₜ)

/-- Fresnel `p`-polarized reflection coefficient. -/
def fresnelRP
    (n₁ n₂ θᵢ θₜ : ℝ) : ℝ :=
  (n₂ * Real.cos θᵢ - n₁ * Real.cos θₜ) /
    (n₂ * Real.cos θᵢ + n₁ * Real.cos θₜ)

/-- If the Fresnel `p` numerator vanishes, then the `p` coefficient vanishes. -/
theorem fresnelRP_eq_zero_of_num_zero
    {n₁ n₂ θᵢ θₜ : ℝ}
    (hnum : n₂ * Real.cos θᵢ - n₁ * Real.cos θₜ = 0) :
    fresnelRP n₁ n₂ θᵢ θₜ = 0 := by
  simp [fresnelRP, hnum]

/-! ## 5. Total internal reflection retarder branch -/

/--
Total-internal-reflection phase-retarder branch.
-/
structure TotalInternalReflectionDatum extends FresnelReflectionDatum where
  /-- `s` channel phase. -/
  φ_s : ℝ

  /-- `p` channel phase. -/
  φ_p : ℝ

  /-- `s` coefficient is a unit phase. -/
  r_s_phase :
    r_s = Complex.exp (Complex.I * (φ_s : ℂ))

  /-- `p` coefficient is a unit phase. -/
  r_p_phase :
    r_p = Complex.exp (Complex.I * (φ_p : ℂ))

namespace TotalInternalReflectionDatum

/-- Relative retardance phase. -/
def relativePhase
    (T : TotalInternalReflectionDatum) : ℝ :=
  T.φ_p - T.φ_s

end TotalInternalReflectionDatum

/-! ## 6. Circular-basis lift -/

/--
The same smooth-interface reflection written in the circular `L/R` basis.

With the convention

`L = (s + i p) / sqrt 2`, `R = (s - i p) / sqrt 2`,

the diagonal `s/p` operator becomes the symmetric matrix with entries
`(r_s + r_p) / 2` and `(r_s - r_p) / 2`.
-/
def circularReflection
    (r_s r_p : ℂ) : CircularJonesVector →ₗ[ℂ] CircularJonesVector where
  toFun C := fun i =>
    if i = sIndex then
      ((r_s + r_p) / 2) * C sIndex + ((r_s - r_p) / 2) * C pIndex
    else
      ((r_s - r_p) / 2) * C sIndex + ((r_s + r_p) / 2) * C pIndex
  map_add' := by
    intro C D
    ext i
    fin_cases i <;>
      simp [sIndex, pIndex, mul_add, add_assoc, add_left_comm]
  map_smul' := by
    intro c C
    ext i
    fin_cases i <;>
      simp [sIndex, pIndex, mul_add, mul_left_comm]

/-- Equal Fresnel channels become a scalar operator in the circular basis. -/
theorem circularReflection_scalar_of_eq
    (r : ℂ) :
    circularReflection r r = r • LinearMap.id := by
  ext C i
  fin_cases i <;> simp [circularReflection, sIndex, pIndex]

/-- Brewster collapse in the first circular coordinate. -/
theorem circularReflection_brewster_apply_left
    (r_s : ℂ)
    (C : CircularJonesVector) :
    circularReflection r_s 0 C sIndex =
      (r_s / 2) * (C 0 + C 1) := by
  simp [circularReflection, sIndex, pIndex, mul_add]

/-- Brewster collapse in the second circular coordinate. -/
theorem circularReflection_brewster_apply_right
    (r_s : ℂ)
    (C : CircularJonesVector) :
    circularReflection r_s 0 C pIndex =
      (r_s / 2) * (C 0 + C 1) := by
  simp [circularReflection, sIndex, pIndex, mul_add]

/-! ## 7. Non-diagonal and non-Jones cases -/

/--
Anisotropic or basis-mixing reflection datum.

Unlike a smooth isotropic interface, this allows off-diagonal `s/p` coupling.
-/
structure AnisotropicReflectionDatum where
  r_ss : ℂ
  r_sp : ℂ
  r_ps : ℂ
  r_pp : ℂ
  jones : JonesVector →ₗ[ℂ] JonesVector

/--
Rough or depolarizing reflection channel.

This is intentionally not a pure Jones operator; concrete models should use
Stokes/Mueller or quantum-channel data.
-/
structure RoughReflectionChannelDatum where
  /-- Stokes/Mueller/channel state space. -/
  Stokes : Type*

  /-- Depolarizing channel. -/
  channel : Stokes → Stokes

  /-- Incidence planes are direction-dependent, so a single global `s/p` basis is invalid. -/
  directionDependentIncidencePlanes : Stokes → Prop

end InfoGeometry.OperatorAlgebra.FresnelJonesReflection
