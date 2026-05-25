import InfoGeometry.Projective.SplitOctonions.ZornInstance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Projective.SplitOctonions.ZornLogVolume

Zorn determinant as logarithmic relative-volume potential.

This file proves the concrete reconciliation:

* multiplicative determinant character;
* additive negative-log cocycle;
* Zorn determinant scaling;
* negative log determinant as a barrier/log-volume potential;
* dimension-8 volume Jacobian exponent `4`.

No new projective structure is introduced.
-/

namespace InfoGeometry.Projective.SplitOctonions

noncomputable section

/-- Negative logarithm of a positive multiplicative quantity. -/
def negLog (x : ℝ) : ℝ :=
  - Real.log x

/--
Negative logarithm turns multiplication of positive scalars into addition.

This is the scalar algebra behind determinant-character cocycles and
Radon--Nikodym log-density transformations.
-/
theorem negLog_mul_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    negLog (x * y) = negLog x + negLog y := by
  unfold negLog
  rw [Real.log_mul]
  · ring
  · exact hx.ne'
  · exact hy.ne'

/--
A positive multiplicative character gives an additive negative-log character.

If `χ(gh)=χ(g)χ(h)`, then `-log χ(gh)=-log χ(g)-log χ(h)`,
written additively as `negLog χ(gh)=negLog χ(g)+negLog χ(h)`.
-/
def negLogCharacter {G : Type*} (χ : G → ℝ) (g : G) : ℝ :=
  negLog (χ g)

theorem negLogCharacter_mul
    {G : Type*} [Mul G]
    (χ : G → ℝ)
    (hχ_mul : ∀ g h : G, χ (g * h) = χ g * χ h)
    (hχ_pos : ∀ g : G, 0 < χ g)
    (g h : G) :
    negLogCharacter χ (g * h) =
      negLogCharacter χ g + negLogCharacter χ h := by
  unfold negLogCharacter
  rw [hχ_mul]
  exact negLog_mul_of_pos (hχ_pos g) (hχ_pos h)

/--
For an 8-dimensional quadratic determinant character, the induced volume
Jacobian scales as `χ^4`.

This is the formal placeholder for the standard fact:
if a quadratic form scales by `χ` in dimension `8`, then volume scales by
`χ^(8/2)=χ^4`.
-/
def zornVolumeJacobian {G : Type*} (χ : G → ℝ) (g : G) : ℝ :=
  (χ g) ^ 4

/-- Negative logarithmic Zorn volume Jacobian. -/
def zornNegLogVolumeJacobian {G : Type*} (χ : G → ℝ) (g : G) : ℝ :=
  negLog (zornVolumeJacobian χ g)

/--
The negative logarithmic Zorn volume Jacobian is additive under composition
of determinant characters.
-/
theorem zornNegLogVolumeJacobian_mul
    {G : Type*} [Mul G]
    (χ : G → ℝ)
    (hχ_mul : ∀ g h : G, χ (g * h) = χ g * χ h)
    (hχ_pos : ∀ g : G, 0 < χ g)
    (g h : G) :
    zornNegLogVolumeJacobian χ (g * h) =
      zornNegLogVolumeJacobian χ g +
        zornNegLogVolumeJacobian χ h := by
  unfold zornNegLogVolumeJacobian zornVolumeJacobian
  rw [hχ_mul]
  have hpow :
      (χ g * χ h) ^ 4 = (χ g) ^ 4 * (χ h) ^ 4 := by
    ring
  rw [hpow]
  exact negLog_mul_of_pos
    (pow_pos (hχ_pos g) 4)
    (pow_pos (hχ_pos h) 4)

namespace ZornCell

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/--
Zorn log barrier / negative logarithmic determinant.

This is meaningful on the positive determinant domain
`0 < detZ B X`; at the null shell `detZ B X = 0`, the intended barrier
interpretation is divergence to `+∞`, which is not represented by this total
real-valued function.
-/
def zornLogBarrier
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X : ZornCell ℝ V) : ℝ :=
  negLog (ZornCell.detZ B X)

/--
The Zorn log barrier under componentwise unit scaling.

Since the existing Zorn instance proves

`detZ (u • X) = u^2 detZ X`,

the logarithmic barrier transforms by

`F(u • X) = F(X) - 2 log u`

for positive `u` and positive determinant.
-/
theorem zornLogBarrier_scalarScale
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) (X : ZornCell ℝ V)
    (hu : 0 < (u : ℝ))
    (hdet : 0 < ZornCell.detZ B X) :
    zornLogBarrier B (ZornCell.scalarScale u X) =
      zornLogBarrier B X - 2 * Real.log (u : ℝ) := by
  unfold zornLogBarrier negLog
  rw [ZornCell.detZ_scalarScale]
  rw [pow_two]
  rw [Real.log_mul]
  · rw [Real.log_mul]
    · ring
    · exact hu.ne'
    · exact hu.ne'
  · exact mul_ne_zero hu.ne' hu.ne'
  · exact hdet.ne'

/--
Equivalent additive-cocycle form of the previous theorem.

The logarithmic change of Zorn barrier under positive unit scaling is exactly
`-2 log u`.
-/
theorem zornLogBarrier_scalarScale_sub
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) (X : ZornCell ℝ V)
    (hu : 0 < (u : ℝ))
    (hdet : 0 < ZornCell.detZ B X) :
    zornLogBarrier B (ZornCell.scalarScale u X) -
        zornLogBarrier B X =
      -2 * Real.log (u : ℝ) := by
  rw [zornLogBarrier_scalarScale B u X hu hdet]
  ring

/--
For Zorn cells, the determinant scaling character of componentwise unit
scaling is `u ↦ u^2`.

This is the determinant-character readout corresponding to the already-proved
determinant scaling theorem.
-/
def scalarScaleDetCharacter (u : ℝˣ) : ℝ :=
  (u : ℝ) ^ 2

/--
The determinant character of componentwise unit scaling is multiplicative.
-/
theorem scalarScaleDetCharacter_mul (u v : ℝˣ) :
    scalarScaleDetCharacter (u * v) =
      scalarScaleDetCharacter u * scalarScaleDetCharacter v := by
  unfold scalarScaleDetCharacter
  simp
  ring

/--
If the determinant character is interpreted as a quadratic conformal factor on
the Zorn determinant, the induced 8-volume Jacobian has exponent `4`.

For componentwise scaling this gives `(u^2)^4 = u^8`.
-/
theorem scalarScale_volumeJacobian_eq_eight_power
    (u : ℝˣ) :
    zornVolumeJacobian scalarScaleDetCharacter u =
      (u : ℝ) ^ 8 := by
  unfold zornVolumeJacobian scalarScaleDetCharacter
  ring

/--
The negative logarithmic 8-volume Jacobian for componentwise Zorn scaling is
`-8 log u`, for positive `u`.

This is the formal Radon--Nikodym/log-volume-change statement attached to the
Zorn determinant character.
-/
theorem scalarScale_negLogVolumeJacobian_eq
    (u : ℝˣ) (hu : 0 < (u : ℝ)) :
    zornNegLogVolumeJacobian scalarScaleDetCharacter u =
      -8 * Real.log (u : ℝ) := by
  let _ := hu
  unfold zornNegLogVolumeJacobian
  rw [scalarScale_volumeJacobian_eq_eight_power]
  unfold negLog
  rw [Real.log_pow]
  ring

end ZornCell

end

end InfoGeometry.Projective.SplitOctonions
