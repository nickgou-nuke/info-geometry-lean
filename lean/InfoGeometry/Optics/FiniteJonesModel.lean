/-
InfoGeometry/Optics/FiniteJonesModel.lean

Finite-dimensional Jones model.

This module instantiates the operatorial Jones calibration layer in the
smallest concrete optical algebra:

  Jones2 = 2 x 2 complex matrices.

It proves the elementary s/p projector algebra and packages the Brewster
rank-collapse and retarder branches as concrete finite-dimensional events.
-/

import Mathlib
import InfoGeometry.Optics.JonesCalibration

noncomputable section

namespace InfoGeometry.Optics.FiniteJonesModel

open Matrix
open InfoGeometry.Optics.JonesCalibration

/-! ## 1. The finite Jones algebra -/

/-- Jones vectors. -/
abbrev JonesVec : Type :=
  Fin 2 → ℂ

/-- The concrete two-channel Jones algebra. -/
abbrev Jones2 : Type :=
  Matrix (Fin 2) (Fin 2) ℂ

/-- Jones matrices. -/
abbrev JonesMat : Type :=
  Jones2

/--
Diagonal Jones matrix.

The basis may be interpreted as either `0 = s`, `1 = p` for Fresnel reflection
or `0 = L`, `1 = R` for circular/chiral transport.
-/
def diagJones (a b : ℂ) : JonesMat :=
  fun i j =>
    if i = j then
      if i = 0 then a else b
    else 0

/-- The `s` polarization projector: `diag(1, 0)`. -/
def P_s : Jones2 :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1 else 0

/-- The `p` polarization projector: `diag(0, 1)`. -/
def P_p : Jones2 :=
  fun i j =>
    if i = 1 ∧ j = 1 then 1 else 0

/-- The first-channel projector: `s` in the Fresnel basis. -/
abbrev sProjector : JonesMat :=
  P_s

/-- The second-channel projector: `p` in the Fresnel basis. -/
abbrev pProjector : JonesMat :=
  P_p

/-- The local diagonal matrix agrees with the concrete projector expansion. -/
theorem diagJones_eq_finiteJonesReflector
    (a b : ℂ) :
    diagJones a b = a • P_s + b • P_p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagJones, P_s, P_p]

/-- The first-channel projector is `diag(1, 0)`. -/
theorem sProjector_eq_diagJones :
    sProjector = diagJones 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sProjector, P_s, diagJones]

/-- The second-channel projector is `diag(0, 1)`. -/
theorem pProjector_eq_diagJones :
    pProjector = diagJones 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pProjector, P_p, diagJones]

/-- The identity decomposition matrix: `P_s + P_p = 1`. -/
theorem P_s_add_P_p :
    P_s + P_p = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_s, P_p]

/-- The `s` projector is idempotent. -/
theorem P_s_idem :
    P_s * P_s = P_s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_s, Matrix.mul_apply]

/-- The `p` projector is idempotent. -/
theorem P_p_idem :
    P_p * P_p = P_p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_p, Matrix.mul_apply]

/-- The `s` and `p` branches are disjoint. -/
theorem P_s_mul_P_p :
    P_s * P_p = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_s, P_p, Matrix.mul_apply]

/-- The `p` and `s` branches are disjoint in the opposite order. -/
theorem P_p_mul_P_s :
    P_p * P_s = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P_s, P_p, Matrix.mul_apply]

/-- The concrete finite-dimensional `s/p` projector pair. -/
def finiteSPProjectorPair : SPProjectorPair Jones2 where
  P_s := P_s
  P_p := P_p
  P_s_idem := P_s_idem
  P_p_idem := P_p_idem
  s_p_disjoint := P_s_mul_P_p
  p_s_disjoint := P_p_mul_P_s
  sum_eq_one := P_s_add_P_p

/-! ## 2. Finite Jones reflector -/

/-- Finite Jones/Fresnel reflector: `R = r_s P_s + r_p P_p`. -/
def finiteJonesReflector
    (r_s r_p : ℂ) : Jones2 :=
  r_s • P_s + r_p • P_p

/-- The finite reflector is the corresponding diagonal Jones matrix. -/
theorem finiteJonesReflector_eq_diagJones
    (r_s r_p : ℂ) :
    finiteJonesReflector r_s r_p = diagJones r_s r_p := by
  exact (diagJones_eq_finiteJonesReflector r_s r_p).symm

/-- The finite reflector as an installed abstract Jones reflector. -/
def finiteJonesReflectorDatum
    (r_s r_p : ℂ) :
    JonesReflector Jones2 where
  projectors := finiteSPProjectorPair
  coeffs :=
    { r_s := r_s
      r_p := r_p
      fresnel_law := True
      fresnel_certificate := trivial }

/--
The operator attached to the abstract reflector is the concrete finite
reflector.
-/
theorem finiteJonesReflector_R
    (r_s r_p : ℂ) :
    (finiteJonesReflectorDatum r_s r_p).R =
      finiteJonesReflector r_s r_p := by
  rfl

/-! ## 3. Brewster rank collapse -/

/-- Brewster coefficients: `p` channel killed, `s` channel survives. -/
def IsFiniteBrewster
    (r_s r_p : ℂ) : Prop :=
  r_p = 0 ∧ r_s ≠ 0

/-- Brewster reflection matrix: the `p` channel is killed. -/
def brewsterMatrix
    (r_s : ℂ) : JonesMat :=
  diagJones r_s 0

/--
The concrete Brewster predicate is exactly the abstract coefficient predicate
for the installed finite reflector.
-/
theorem finiteJonesReflector_isBrewsterBranch_iff
    (r_s r_p : ℂ) :
    (finiteJonesReflectorDatum r_s r_p).IsBrewsterBranch ↔
      IsFiniteBrewster r_s r_p := by
  rfl

/-- At Brewster collapse, the Jones operator is a scalar multiple of `P_s`. -/
theorem finiteJonesReflector_brewster_eq
    {r_s r_p : ℂ}
    (hB : IsFiniteBrewster r_s r_p) :
    finiteJonesReflector r_s r_p = r_s • P_s := by
  rcases hB with ⟨hrp, _hrs⟩
  simp [finiteJonesReflector, hrp]

/--
At Brewster reflection, the reflected Jones matrix is a scaled first-channel
projector.
-/
theorem brewster_eq_scaled_sProjector
    (r_s : ℂ) :
    brewsterMatrix r_s = r_s • sProjector := by
  simp [brewsterMatrix, diagJones_eq_finiteJonesReflector]

/-- Brewster reflection kills the `p` sector. -/
@[simp]
theorem brewster_kills_p
    (r_s : ℂ) :
    brewsterMatrix r_s * pProjector = 0 := by
  rw [brewster_eq_scaled_sProjector]
  calc
    (r_s • sProjector) * pProjector
        = r_s • (sProjector * pProjector) := by
            rw [smul_mul_assoc]
    _ = r_s • 0 := by
            rw [P_s_mul_P_p]
    _ = 0 := by
            simp

/-- Brewster reflection is supported on the `s` sector. -/
@[simp]
theorem brewster_supported_on_s
    (r_s : ℂ) :
    brewsterMatrix r_s * sProjector = brewsterMatrix r_s := by
  rw [brewster_eq_scaled_sProjector]
  calc
    (r_s • sProjector) * sProjector
        = r_s • (sProjector * sProjector) := by
            rw [smul_mul_assoc]
    _ = r_s • sProjector := by
            rw [P_s_idem]

/-- The `s` sector acts as the core support for Brewster reflection. -/
@[simp]
theorem sProjector_supports_brewster
    (r_s : ℂ) :
    sProjector * brewsterMatrix r_s = brewsterMatrix r_s := by
  rw [brewster_eq_scaled_sProjector]
  calc
    sProjector * (r_s • sProjector)
        = r_s • (sProjector * sProjector) := by
            rw [mul_smul_comm]
    _ = r_s • sProjector := by
            rw [P_s_idem]

/-- Candidate Drazin inverse for a Brewster reflector: `R_D = r_s^{-1} P_s`. -/
def brewsterDrazinInverse
    (r_s : ℂ) : Jones2 :=
  r_s⁻¹ • P_s

/-- Drazin/core inverse of the Brewster reflection on the surviving `s` sector. -/
abbrev brewsterCoreInverse
    (r_s : ℂ) : JonesMat :=
  brewsterDrazinInverse r_s

/--
For nonzero `r_s`, the Brewster Drazin core projector is `P_s`.

This is the finite-dimensional optical version of `R R_D = P_s`.
-/
theorem brewster_core_projector_eq_P_s
    {r_s : ℂ}
    (hrs : r_s ≠ 0) :
    (r_s • P_s) * brewsterDrazinInverse r_s = P_s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [
      brewsterDrazinInverse,
      P_s,
      Matrix.mul_apply,
      hrs
    ]

/--
Brewster reflection composed with its core inverse recovers the core projector.
-/
theorem brewster_mul_coreInverse_eq_sProjector
    {r_s : ℂ}
    (hrs : r_s ≠ 0) :
    brewsterMatrix r_s * brewsterCoreInverse r_s = sProjector := by
  rw [brewster_eq_scaled_sProjector]
  exact brewster_core_projector_eq_P_s hrs

/-- The core inverse kills the killed `p` sector. -/
@[simp]
theorem brewsterCoreInverse_kills_p
    (r_s : ℂ) :
    brewsterCoreInverse r_s * pProjector = 0 := by
  dsimp [brewsterCoreInverse, brewsterDrazinInverse]
  calc
    (r_s⁻¹ • P_s) * P_p
        = r_s⁻¹ • (P_s * P_p) := by
            rw [smul_mul_assoc]
    _ = r_s⁻¹ • 0 := by
            rw [P_s_mul_P_p]
    _ = 0 := by
            simp

/-- The abstract Brewster core identity specializes to the finite model. -/
theorem finiteJonesReflector_brewster_core_eq_P_s
    {r_s r_p : ℂ}
    (hB : IsFiniteBrewster r_s r_p) :
    (finiteJonesReflectorDatum r_s r_p).R *
        (finiteJonesReflectorDatum r_s r_p).brewsterCoreInverse =
      P_s := by
  simpa [finiteJonesReflectorDatum] using
    (finiteJonesReflectorDatum r_s r_p).R_mul_brewsterCoreInverse_eq_Ps hB

/-- The killed Brewster branch is `P_p`: `1 - P_s = P_p`. -/
theorem brewster_nil_projector_eq_P_p :
    1 - P_s = P_p := by
  rw [← P_s_add_P_p]
  abel

/-! ## 4. Bundled finite Brewster-Drazin witness -/

/--
Finite-dimensional Brewster-Drazin witness.

This is the concrete optical instantiation of the algebraic slogan:

`Brewster reflection = scaled core projector + killed p-sector`.
-/
structure BrewsterDrazinWitness where
  rs : ℂ
  rs_ne_zero : rs ≠ 0

  R : JonesMat := brewsterMatrix rs
  Pcore : JonesMat := sProjector
  Pnil : JonesMat := pProjector
  RD : JonesMat := brewsterCoreInverse rs

  Pcore_idem :
    Pcore * Pcore = Pcore
  Pnil_idem :
    Pnil * Pnil = Pnil
  complementary :
    Pcore + Pnil = 1
  disjoint_left :
    Pcore * Pnil = 0
  disjoint_right :
    Pnil * Pcore = 0
  R_kills_nil :
    R * Pnil = 0
  R_supported_on_core :
    R * Pcore = R
  core_identity :
    R * RD = Pcore
  RD_kills_nil :
    RD * Pnil = 0

/-- Constructor for the finite Brewster-Drazin witness. -/
def brewsterDrazinWitness
    (rs : ℂ)
    (hrs : rs ≠ 0) :
    BrewsterDrazinWitness where
  rs := rs
  rs_ne_zero := hrs
  Pcore_idem := by
    exact P_s_idem
  Pnil_idem := by
    exact P_p_idem
  complementary := by
    exact P_s_add_P_p
  disjoint_left := by
    exact P_s_mul_P_p
  disjoint_right := by
    exact P_p_mul_P_s
  R_kills_nil := by
    exact brewster_kills_p rs
  R_supported_on_core := by
    exact brewster_supported_on_s rs
  core_identity := by
    exact brewster_mul_coreInverse_eq_sProjector hrs
  RD_kills_nil := by
    exact brewsterCoreInverse_kills_p rs

namespace BrewsterDrazinWitness

/-- The reflected core is the first polarization sector. -/
theorem reflected_core
    (B : BrewsterDrazinWitness) :
    B.R * B.RD = B.Pcore :=
  B.core_identity

/-- The killed optical sector is the second polarization sector. -/
theorem killed_sector
    (B : BrewsterDrazinWitness) :
    B.R * B.Pnil = 0 :=
  B.R_kills_nil

end BrewsterDrazinWitness

/-! ## 5. Retarder branch -/

/--
A finite retarder branch.

This records the lossless coefficient condition `‖r_s‖ = ‖r_p‖ = 1`.
-/
structure FiniteRetarderBranch where
  r_s : ℂ
  r_p : ℂ

  norm_r_s :
    ‖r_s‖ = 1

  norm_r_p :
    ‖r_p‖ = 1

/-- The Jones operator of a finite retarder branch. -/
def FiniteRetarderBranch.R
    (B : FiniteRetarderBranch) : Jones2 :=
  finiteJonesReflector B.r_s B.r_p

/--
Retarder branch has no Brewster rank collapse if both amplitudes have unit
norm.

This theorem records only the coefficient-level obstruction to Brewster
collapse; unitarity or norm preservation belongs to a later Hilbert-space
calibration.
-/
theorem retarder_not_brewster
    (B : FiniteRetarderBranch) :
    ¬ IsFiniteBrewster B.r_s B.r_p := by
  intro h
  rcases h with ⟨hrp, _hrs⟩
  have hp_norm : ‖B.r_p‖ = 0 := by
    simp [hrp]
  rw [B.norm_r_p] at hp_norm
  norm_num at hp_norm

/-! ## 6. Owner target -/

/-- Owner target for the finite Jones model. -/
def FiniteJonesModelOwnerTarget : Prop :=
  Nonempty (SPProjectorPair Jones2) ∧
    ∀ rs : ℂ, rs ≠ 0 → Nonempty BrewsterDrazinWitness

/--
The finite Jones model owner target is realized by the concrete `s/p`
projectors.
-/
theorem finiteJonesModelOwnerTarget :
    FiniteJonesModelOwnerTarget :=
  ⟨⟨finiteSPProjectorPair⟩, fun rs hrs => ⟨brewsterDrazinWitness rs hrs⟩⟩

end InfoGeometry.Optics.FiniteJonesModel
