/-
InfoGeometry/Optics/FiniteJonesStinespringConstructive.lean

Constructive finite Stinespring block-column audit for phase-free diagonal
lossy Jones channels.

This module removes the explicit isometry hypotheses from the finite optical
Stinespring layer.

Instead of supplying hidden amplitudes `v_s`, `v_p` plus laws

  |r_s|^2 + |v_s|^2 = 1,
  |r_p|^2 + |v_p|^2 = 1,

we parameterize the visible/hidden amplitudes by real angles:

  r_s = cos theta_s,   v_s = sin theta_s,
  r_p = cos theta_p,   v_p = sin theta_p.

The first-column Stinespring identity

  R^H R + V^H V = I

and therefore the optical defect identity

  I - R^H R = V^H V

are then proved constructively from `cos^2 + sin^2 = 1`.

This is the finite optical audit:

  visible absorption = hidden environment gain.

This file does not claim an arbitrary lossy Jones channel and does not claim a
full 4x4 unitary dilation unless such a theorem/property is supplied
separately.
-/

import Mathlib.Tactic
import InfoGeometry.Optics.FiniteJonesModel
import InfoGeometry.Optics.FiniteJonesStinespring

noncomputable section

open scoped Matrix

namespace InfoGeometry.Optics.FiniteJonesStinespringConstructive

open InfoGeometry.Optics.FiniteJonesModel

/-! ## 1. Complexified real trigonometric amplitudes -/

/-- Complex amplitude obtained from a real cosine. -/
@[simp] def cosC (θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ)

/-- Complex amplitude obtained from a real sine. -/
@[simp] def sinC (θ : ℝ) : ℂ :=
  (Real.sin θ : ℂ)

/--
The channelwise Stinespring identity:

`|cos θ|^2 + |sin θ|^2 = 1`.
-/
theorem cosC_star_mul_add_sinC_star_mul
    (θ : ℝ) :
    star (cosC θ) * cosC θ + star (sinC θ) * sinC θ = 1 := by
  have h :=
    congrArg (fun x : ℝ => (x : ℂ)) (Real.cos_sq_add_sin_sq θ)
  have hcos : star (cosC θ) = cosC θ := by
    unfold cosC
    rw [Complex.star_def, Complex.conj_ofReal]
  have hsin : star (sinC θ) = sinC θ := by
    unfold sinC
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [hcos, hsin]
  unfold cosC sinC
  simpa [sq] using h

/--
The visible scalar defect equals the hidden scalar gain:

`1 - |cos θ|^2 = |sin θ|^2`.
-/
theorem scalar_defect_eq_hidden_gain
    (θ : ℝ) :
    1 - star (cosC θ) * cosC θ =
      star (sinC θ) * sinC θ := by
  calc
    1 - star (cosC θ) * cosC θ
        =
      (star (cosC θ) * cosC θ +
          star (sinC θ) * sinC θ) -
        star (cosC θ) * cosC θ := by
          rw [cosC_star_mul_add_sinC_star_mul θ]
    _ = star (sinC θ) * sinC θ := by
          ring

/-! ## 2. Visible and hidden Jones blocks -/

/--
Visible Jones block:

`R = diag(cos theta_s, cos theta_p)`.
-/
def visibleBlock
    (θs θp : ℝ) : JonesMat :=
  diagJones (cosC θs) (cosC θp)

/--
Hidden/environment coupling block:

`V = diag(sin theta_s, sin theta_p)`.
-/
def hiddenBlock
    (θs θp : ℝ) : JonesMat :=
  diagJones (sinC θs) (sinC θp)

/-! ## 3. Constructive finite Stinespring channel -/

/--
Constructive phase-free diagonal Jones/Stinespring channel.

The only parameters are real angles. No isometry law is supplied as a field.
-/
structure ConstructiveJonesStinespring where
  θs : ℝ
  θp : ℝ

namespace ConstructiveJonesStinespring

variable (D : ConstructiveJonesStinespring)

/-- Visible block `R`. -/
def R : JonesMat :=
  visibleBlock D.θs D.θp

/-- Hidden block `V`. -/
def V : JonesMat :=
  hiddenBlock D.θs D.θp

/-- Visible optical defect `I - R^H R`. -/
def visibleDefect : JonesMat :=
  InfoGeometry.Optics.FiniteJonesStinespring.opticalDefect D.R

/-- Hidden environment gain `V^H V`. -/
def environmentGain : JonesMat :=
  InfoGeometry.Optics.FiniteJonesStinespring.hiddenGain D.V

/--
Constructive first-column Stinespring identity:

`R^H R + V^H V = I`.

This is proved from the two scalar trigonometric identities.
-/
theorem blockColumn_isometry :
    D.Rᴴ * D.R + D.Vᴴ * D.V = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [R, V, visibleBlock, hiddenBlock, diagJones, Matrix.mul_apply]
      using cosC_star_mul_add_sinC_star_mul D.θs
  · simp [R, V, visibleBlock, hiddenBlock, diagJones, Matrix.mul_apply]
  · simp [R, V, visibleBlock, hiddenBlock, diagJones, Matrix.mul_apply]
  · simpa [R, V, visibleBlock, hiddenBlock, diagJones, Matrix.mul_apply]
      using cosC_star_mul_add_sinC_star_mul D.θp

/--
The constructive diagonal channel as a proof-carrying first-column
Stinespring isometry.

This is the bridge into `FiniteJonesStinespring` and downstream Bregman
modules.
-/
def toStinespringIsometry :
    InfoGeometry.Optics.FiniteJonesStinespring.StinespringIsometry JonesMat :=
  ⟨⟨D.R, D.V⟩, D.blockColumn_isometry⟩

@[simp]
theorem toStinespringIsometry_R :
    D.toStinespringIsometry.R = D.R :=
  rfl

@[simp]
theorem toStinespringIsometry_V :
    D.toStinespringIsometry.V = D.V :=
  rfl

/--
The constructive channel inherits the existing finite Stinespring defect audit.
-/
theorem toStinespring_defect_eq_hiddenGain :
    InfoGeometry.Optics.FiniteJonesStinespring.opticalDefect
        D.toStinespringIsometry.R =
      InfoGeometry.Optics.FiniteJonesStinespring.hiddenGain
        D.toStinespringIsometry.V :=
  D.toStinespringIsometry.defect_eq_hiddenGain

/--
The visible optical defect equals the hidden environment gain.

This is constructive: it follows from the trigonometric identity
`cos^2 + sin^2 = 1`, via the first-column isometry theorem.
-/
theorem visibleDefect_eq_environmentGain :
    D.visibleDefect = D.environmentGain := by
  simpa [visibleDefect, environmentGain] using D.toStinespring_defect_eq_hiddenGain

/--
Visible defect vanishes iff hidden environment gain vanishes.
-/
theorem visibleDefect_eq_zero_iff_environmentGain_eq_zero :
    D.visibleDefect = 0 ↔ D.environmentGain = 0 := by
  rw [D.visibleDefect_eq_environmentGain]

/--
If the hidden environment gain vanishes, the visible defect vanishes.
-/
theorem visibleDefect_eq_zero_of_environmentGain_eq_zero
    (h : D.environmentGain = 0) :
    D.visibleDefect = 0 := by
  rwa [D.visibleDefect_eq_environmentGain]

/--
If the visible defect vanishes, the hidden environment gain vanishes.
-/
theorem environmentGain_eq_zero_of_visibleDefect_eq_zero
    (h : D.visibleDefect = 0) :
    D.environmentGain = 0 := by
  rwa [D.visibleDefect_eq_environmentGain] at h

end ConstructiveJonesStinespring

/-! ## 4. Explicit doubled 4x4 Julia block matrix -/

/--
Visible/hidden ports for the finite Stinespring block matrix.
-/
inductive Port where
  | visible
  | hidden
deriving DecidableEq, Fintype, Repr

/--
Doubled Jones index:

`visible-s`, `visible-p`, `hidden-s`, `hidden-p`.
-/
abbrev DilatedIndex : Type :=
  Port × Fin 2

/--
A concrete `4 x 4` dilated Jones matrix.
-/
abbrev DilatedJonesMat : Type :=
  Matrix DilatedIndex DilatedIndex ℂ

/--
Explicit Julia/Halmos dilation:

  U = [[R, -V^H],
       [V,  R^H]]

for the constructive visible/hidden pair.

This definition only constructs the block matrix. Full `4 x 4` unitarity is
not claimed here unless a separate theorem/property is supplied.
-/
def juliaBlockMatrix
    (D : ConstructiveJonesStinespring) : DilatedJonesMat
  | (Port.visible, i), (Port.visible, j) =>
      D.R i j
  | (Port.visible, i), (Port.hidden, j) =>
      -(D.Vᴴ i j)
  | (Port.hidden, i), (Port.visible, j) =>
      D.V i j
  | (Port.hidden, i), (Port.hidden, j) =>
      D.Rᴴ i j

/--
Deprecated/safe alias: this is only a block matrix, not a property unitary
dilation unless a separate unitarity theorem is supplied.
-/
abbrev juliaDilation :=
  juliaBlockMatrix

namespace ConstructiveJonesStinespring

/--
The visible-visible block of the Julia dilation is `R`.
-/
theorem julia_visible_visible_block
    (D : ConstructiveJonesStinespring)
    (i j : Fin 2) :
    juliaBlockMatrix D (Port.visible, i) (Port.visible, j) =
      D.R i j :=
  rfl

/--
The hidden-visible block of the Julia dilation is `V`.
-/
theorem julia_hidden_visible_block
    (D : ConstructiveJonesStinespring)
    (i j : Fin 2) :
    juliaBlockMatrix D (Port.hidden, i) (Port.visible, j) =
      D.V i j :=
  rfl

/--
The visible-hidden block of the Julia dilation is `-V^H`.
-/
theorem julia_visible_hidden_block
    (D : ConstructiveJonesStinespring)
    (i j : Fin 2) :
    juliaBlockMatrix D (Port.visible, i) (Port.hidden, j) =
      -(D.Vᴴ i j) :=
  rfl

/--
The hidden-hidden block of the Julia dilation is `R^H`.
-/
theorem julia_hidden_hidden_block
    (D : ConstructiveJonesStinespring)
    (i j : Fin 2) :
    juliaBlockMatrix D (Port.hidden, i) (Port.hidden, j) =
      D.Rᴴ i j :=
  rfl

end ConstructiveJonesStinespring

/-! ## 5. Scalar readout: visible loss equals hidden gain -/

/-! A scalar defect readout is the function it evaluates. -/
abbrev DefectReadout := JonesMat → ℝ

namespace DefectReadout

variable (H : DefectReadout)

/--
Visible defect readout.
-/
def visibleLoss
    (D : ConstructiveJonesStinespring) : ℝ :=
  H D.visibleDefect

/--
Hidden environment gain readout.
-/
def hiddenEnvironmentGain
    (D : ConstructiveJonesStinespring) : ℝ :=
  H D.environmentGain

/--
Every scalar readout assigns equal values to visible loss and hidden gain,
because the matrices are equal.
-/
theorem visibleLoss_eq_hiddenEnvironmentGain
    (D : ConstructiveJonesStinespring) :
    DefectReadout.visibleLoss H D = DefectReadout.hiddenEnvironmentGain H D := by
  dsimp [visibleLoss, hiddenEnvironmentGain]
  rw [D.visibleDefect_eq_environmentGain]

end DefectReadout

/-! ## 6. Concrete channel intensities -/

/--
Visible s-channel intensity.
-/
def visibleSIntensity
    (D : ConstructiveJonesStinespring) : ℝ :=
  Real.cos D.θs ^ 2

/--
Visible p-channel intensity.
-/
def visiblePIntensity
    (D : ConstructiveJonesStinespring) : ℝ :=
  Real.cos D.θp ^ 2

/--
Hidden s-channel intensity.
-/
def hiddenSIntensity
    (D : ConstructiveJonesStinespring) : ℝ :=
  Real.sin D.θs ^ 2

/--
Hidden p-channel intensity.
-/
def hiddenPIntensity
    (D : ConstructiveJonesStinespring) : ℝ :=
  Real.sin D.θp ^ 2

/--
s-channel visible + hidden intensity is conserved.
-/
theorem s_intensity_conserved
    (D : ConstructiveJonesStinespring) :
    visibleSIntensity D + hiddenSIntensity D = 1 := by
  dsimp [visibleSIntensity, hiddenSIntensity]
  exact Real.cos_sq_add_sin_sq D.θs

/--
p-channel visible + hidden intensity is conserved.
-/
theorem p_intensity_conserved
    (D : ConstructiveJonesStinespring) :
    visiblePIntensity D + hiddenPIntensity D = 1 := by
  dsimp [visiblePIntensity, hiddenPIntensity]
  exact Real.cos_sq_add_sin_sq D.θp

/-! ## 7. Constructive finite absorptivity -/

/-- Hidden s-channel intensity is nonnegative. -/
theorem hiddenSIntensity_nonneg
    (D : ConstructiveJonesStinespring) :
    0 ≤ hiddenSIntensity D := by
  dsimp [hiddenSIntensity]
  positivity

/-- Hidden p-channel intensity is nonnegative. -/
theorem hiddenPIntensity_nonneg
    (D : ConstructiveJonesStinespring) :
    0 ≤ hiddenPIntensity D := by
  dsimp [hiddenPIntensity]
  positivity

/--
s-channel visible defect equals hidden intensity:

`1 - cos(theta_s)^2 = sin(theta_s)^2`.
-/
theorem s_visible_defect_eq_hiddenIntensity
    (D : ConstructiveJonesStinespring) :
    1 - visibleSIntensity D = hiddenSIntensity D := by
  have h := s_intensity_conserved D
  dsimp [visibleSIntensity, hiddenSIntensity] at h ⊢
  nlinarith

/--
p-channel visible defect equals hidden intensity:

`1 - cos(theta_p)^2 = sin(theta_p)^2`.
-/
theorem p_visible_defect_eq_hiddenIntensity
    (D : ConstructiveJonesStinespring) :
    1 - visiblePIntensity D = hiddenPIntensity D := by
  have h := p_intensity_conserved D
  dsimp [visiblePIntensity, hiddenPIntensity] at h ⊢
  nlinarith

/-- s-channel visible defect is nonnegative. -/
theorem s_visible_defect_nonneg
    (D : ConstructiveJonesStinespring) :
    0 ≤ 1 - visibleSIntensity D := by
  rw [s_visible_defect_eq_hiddenIntensity D]
  exact hiddenSIntensity_nonneg D

/-- p-channel visible defect is nonnegative. -/
theorem p_visible_defect_nonneg
    (D : ConstructiveJonesStinespring) :
    0 ≤ 1 - visiblePIntensity D := by
  rw [p_visible_defect_eq_hiddenIntensity D]
  exact hiddenPIntensity_nonneg D

/-! ## 8. Bounded finite intensities -/

/-- Visible s-channel intensity is nonnegative. -/
theorem visibleSIntensity_nonneg
    (D : ConstructiveJonesStinespring) :
    0 ≤ visibleSIntensity D := by
  dsimp [visibleSIntensity]
  positivity

/-- Visible p-channel intensity is nonnegative. -/
theorem visiblePIntensity_nonneg
    (D : ConstructiveJonesStinespring) :
    0 ≤ visiblePIntensity D := by
  dsimp [visiblePIntensity]
  positivity

/-- s-channel visible intensity is at most one. -/
theorem visibleSIntensity_le_one
    (D : ConstructiveJonesStinespring) :
    visibleSIntensity D ≤ 1 := by
  have h := s_visible_defect_nonneg D
  linarith

/-- p-channel visible intensity is at most one. -/
theorem visiblePIntensity_le_one
    (D : ConstructiveJonesStinespring) :
    visiblePIntensity D ≤ 1 := by
  have h := p_visible_defect_nonneg D
  linarith

/-- s-channel hidden intensity is at most one. -/
theorem hiddenSIntensity_le_one
    (D : ConstructiveJonesStinespring) :
    hiddenSIntensity D ≤ 1 := by
  have h := s_intensity_conserved D
  have hvis : 0 ≤ visibleSIntensity D := visibleSIntensity_nonneg D
  linarith

/-- p-channel hidden intensity is at most one. -/
theorem hiddenPIntensity_le_one
    (D : ConstructiveJonesStinespring) :
    hiddenPIntensity D ≤ 1 := by
  have h := p_intensity_conserved D
  have hvis : 0 ≤ visiblePIntensity D := visiblePIntensity_nonneg D
  linarith

end InfoGeometry.Optics.FiniteJonesStinespringConstructive
