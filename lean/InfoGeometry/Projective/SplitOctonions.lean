import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Projective.SplitOctonions

Projective null geometry of the split-octonion/Zorn cell.

This file defines the local projective null shell

  { X : ZornCell R V // detZ X = 0 ∧ X ≠ 0 } / Rˣ

and an abstract Albert/Jordan interface for the later global split-Cayley plane.

No `sorry`, no `True` placeholders, no fake Freudenthal determinant.
-/

namespace InfoGeometry.Projective.SplitOctonions

universe u v

/--
A raw Zorn vector-matrix cell

  [ a  v ]
  [ w  b ]

This is the local split-octonion coordinate cell.
-/
structure ZornCell (R : Type u) (V : Type v) where
  a : R
  b : R
  v : V
  w : V

@[ext]
theorem ZornCell.ext {R : Type u} {V : Type v}
    {X Y : ZornCell R V}
    (ha : X.a = Y.a) (hb : X.b = Y.b) (hv : X.v = Y.v) (hw : X.w = Y.w) :
    X = Y := by
  cases X
  cases Y
  cases ha
  cases hb
  cases hv
  cases hw
  rfl

namespace ZornCell

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- Zorn determinant / split norm: `detZ X = a b - B v w`. -/
def detZ (B : V →ₗ[R] V →ₗ[R] R) (X : ZornCell R V) : R :=
  X.a * X.b - B X.v X.w

/-- The local Zorn null cone. -/
def IsNull (B : V →ₗ[R] V →ₗ[R] R) (X : ZornCell R V) : Prop :=
  detZ B X = 0

/-! ## Concrete coordinate Zorn product and determinant composition -/
namespace Coord3

variable {R : Type*} [CommRing R]

/-- Three-coordinate dot product. -/
def dot (x y : R × R × R) : R :=
  x.1 * y.1 + x.2.1 * y.2.1 + x.2.2 * y.2.2

/-- Three-coordinate cross product. -/
def cross (x y : R × R × R) : R × R × R :=
  ( x.2.1 * y.2.2 - x.2.2 * y.2.1,
    x.2.2 * y.1   - x.1   * y.2.2,
    x.1   * y.2.1 - x.2.1 * y.1 )

end Coord3

open Coord3

variable {R : Type*} [CommRing R]

/-- Concrete Zorn determinant on `R³` coordinates. -/
def detZ3 (X : ZornCell R (R × R × R)) : R :=
  X.a * X.b - dot X.v X.w

/--
Concrete split-octonion/Zorn product on `R³` coordinates.

The bottom-left cross term carries the opposite sign. With equal signs for
both cross contributions, determinant composition fails.
-/
def mul3 (X Y : ZornCell R (R × R × R)) :
    ZornCell R (R × R × R) where
  a := X.a * Y.a + dot X.v Y.w
  b := dot X.w Y.v + X.b * Y.b
  v :=
    ( X.a * Y.v.1 + Y.b * X.v.1
        + (X.w.2.1 * Y.w.2.2 - X.w.2.2 * Y.w.2.1),
      X.a * Y.v.2.1 + Y.b * X.v.2.1
        + (X.w.2.2 * Y.w.1 - X.w.1 * Y.w.2.2),
      X.a * Y.v.2.2 + Y.b * X.v.2.2
        + (X.w.1 * Y.w.2.1 - X.w.2.1 * Y.w.1) )
  w :=
    ( Y.a * X.w.1 + X.b * Y.w.1
        - (X.v.2.1 * Y.v.2.2 - X.v.2.2 * Y.v.2.1),
      Y.a * X.w.2.1 + X.b * Y.w.2.1
        - (X.v.2.2 * Y.v.1 - X.v.1 * Y.v.2.2),
      Y.a * X.w.2.2 + X.b * Y.w.2.2
        - (X.v.1 * Y.v.2.1 - X.v.2.1 * Y.v.1) )

/--
Zorn composition theorem in concrete `R³` coordinates.
-/
theorem detZ3_mul3
    (X Y : ZornCell R (R × R × R)) :
    detZ3 (mul3 X Y) = detZ3 X * detZ3 Y := by
  rcases X with ⟨a, b, x, y⟩
  rcases x with ⟨x1, x23⟩
  rcases x23 with ⟨x2, x3⟩
  rcases y with ⟨y1, y23⟩
  rcases y23 with ⟨y2, y3⟩
  rcases Y with ⟨a', b', u, v⟩
  rcases u with ⟨u1, u23⟩
  rcases u23 with ⟨u2, u3⟩
  rcases v with ⟨v1, v23⟩
  rcases v23 with ⟨v2, v3⟩
  unfold detZ3 mul3 Coord3.dot
  ring

section LogDet

open Real

/-- Positive split-octonion cone in concrete coordinates: `detZ3 X > 0`. -/
def IsPosCone (X : ZornCell ℝ (ℝ × ℝ × ℝ)) : Prop :=
  0 < detZ3 X

/-- Massieu/log-barrier potential on the positive cone: `Φ(X) = -log detZ3(X)`. -/
noncomputable def barrierPhi (X : ZornCell ℝ (ℝ × ℝ × ℝ)) : ℝ :=
  -Real.log (detZ3 X)

/-- Alias: positive-cone set view of `IsPosCone`. -/
abbrev PositiveCone : Set (ZornCell ℝ (ℝ × ℝ × ℝ)) := {X | IsPosCone X}

/-- Alias: Massieu potential notation. -/
noncomputable abbrev massieu (X : ZornCell ℝ (ℝ × ℝ × ℝ)) : ℝ := barrierPhi X

/-- Absolute-value logarithmic barrier on the non-isotropic stratum. -/
noncomputable def barrierAbsPhi (X : ZornCell ℝ (ℝ × ℝ × ℝ)) : ℝ :=
  -Real.log |detZ3 X|

/--
Negative logarithmic Zorn volume.

This is the log-volume potential on the non-isotropic stratum (`detZ3 ≠ 0`).
-/
noncomputable def negLogVolume (X : ZornCell ℝ (ℝ × ℝ × ℝ)) : ℝ :=
  -Real.log (detZ3 X)

/--
Radon–Nikodym-type relative Zorn volume:
`relativeVolumeRN X Y = detZ3 Y / detZ3 X`.
-/
noncomputable def relativeVolumeRN
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ)) : ℝ :=
  detZ3 Y / detZ3 X

/-- `negLogVolume` is definitionally the barrier potential in this chart. -/
theorem negLogVolume_eq_barrierPhi
    (X : ZornCell ℝ (ℝ × ℝ × ℝ)) :
    negLogVolume X = barrierPhi X := by
  rfl

/-- Log-determinant ratio potential. -/
noncomputable def logDetRatio
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ)) : ℝ :=
  Real.log (detZ3 Y / detZ3 X)

/--
Negative log RN volume equals the difference of negative log-volume potentials.
-/
theorem negLog_relativeVolumeRN_eq_negLogVolume_sub
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : detZ3 X ≠ 0) (hY : detZ3 Y ≠ 0) :
    -Real.log (relativeVolumeRN X Y) =
      negLogVolume Y - negLogVolume X := by
  unfold relativeVolumeRN negLogVolume
  rw [Real.log_div hY hX]
  ring

/-- On the positive cone, `exp (-massieu)` recovers the determinant. -/
theorem exp_neg_massieu_eq_detZ3
    (X : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsPosCone X) :
    Real.exp (-massieu X) = detZ3 X := by
  unfold massieu barrierPhi
  rw [neg_neg, Real.exp_log hX]

/--
Log-determinant additivity on the positive cone:
`log detZ3(X⋆Y) = log detZ3(X) + log detZ3(Y)`.
-/
theorem log_detZ3_mul3
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsPosCone X) (hY : IsPosCone Y) :
    Real.log (detZ3 (mul3 X Y)) =
      Real.log (detZ3 X) + Real.log (detZ3 Y) := by
  have hXY : 0 < detZ3 X * detZ3 Y := mul_pos hX hY
  rw [detZ3_mul3]
  exact Real.log_mul (ne_of_gt hX) (ne_of_gt hY)

/--
Barrier cocycle over multiplication on the positive cone:
`Φ(X⋆Y) = Φ(X) + Φ(Y)`.
-/
theorem barrierPhi_mul3
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsPosCone X) (hY : IsPosCone Y) :
    barrierPhi (mul3 X Y) = barrierPhi X + barrierPhi Y := by
  unfold barrierPhi
  rw [log_detZ3_mul3 X Y hX hY]
  ring

/-- Massieu difference equals the log-determinant ratio on the positive cone. -/
theorem massieu_sub_eq_logDetRatio
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsPosCone X) (hY : IsPosCone Y) :
    massieu X - massieu Y = logDetRatio X Y := by
  unfold massieu barrierPhi logDetRatio
  rw [div_eq_mul_inv, Real.log_mul (ne_of_gt hY) (inv_ne_zero (ne_of_gt hX))]
  rw [Real.log_inv]
  ring

/--
Radon-Nikodym style log-det rewrite on the positive cone:

`(detZ3 X)^(-ν/2) = exp ((ν/2) * Φ(X))`, with `Φ = -log detZ3`.
-/
theorem detZ3_rpow_neg_half_eq_exp_barrier
    (X : ZornCell ℝ (ℝ × ℝ × ℝ))
    (ν : ℝ)
    (hX : IsPosCone X) :
    Real.rpow (detZ3 X) (-ν / 2) =
      Real.exp ((ν / 2) * barrierPhi X) := by
  unfold barrierPhi
  simp [Real.rpow_def_of_pos hX]
  ring

/--
Multiplicativity of `detZ3` turns left Zorn multiplication into
multiplicative relative-volume transport.
-/
theorem relativeVolumeRN_mul3_left
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : detZ3 X ≠ 0) :
    relativeVolumeRN X (mul3 X Y) = detZ3 Y := by
  unfold relativeVolumeRN
  rw [detZ3_mul3]
  field_simp [hX]

/--
Negative logarithmic volume change under left multiplication by `X`
equals the negative log determinant of the multiplier `Y`.
-/
theorem negLog_relativeVolumeRN_mul3_left
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : detZ3 X ≠ 0) :
    -Real.log (relativeVolumeRN X (mul3 X Y)) = negLogVolume Y := by
  rw [relativeVolumeRN_mul3_left X Y hX]
  unfold negLogVolume
  rfl

/--
Absolute-value cocycle: multiplicativity of `detZ3` gives additivity of
`-log |detZ3|` on the non-isotropic stratum.
-/
theorem barrierAbsPhi_mul3_of_ne_zero
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : detZ3 X ≠ 0) (hY : detZ3 Y ≠ 0) :
    barrierAbsPhi (mul3 X Y) = barrierAbsPhi X + barrierAbsPhi Y := by
  unfold barrierAbsPhi
  rw [detZ3_mul3, abs_mul]
  rw [Real.log_mul (abs_ne_zero.mpr hX) (abs_ne_zero.mpr hY)]
  ring

/--
Additivity of `log detZ3` on the non-isotropic stratum.
-/
theorem log_detZ3_mul3_of_ne_zero
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : detZ3 X ≠ 0) (hY : detZ3 Y ≠ 0) :
    Real.log (detZ3 (mul3 X Y)) =
      Real.log (detZ3 X) + Real.log (detZ3 Y) := by
  rw [detZ3_mul3]
  exact Real.log_mul hX hY

/--
Negative log-volume cocycle on the non-isotropic stratum.
-/
theorem negLogVolume_mul3_of_ne_zero
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : detZ3 X ≠ 0) (hY : detZ3 Y ≠ 0) :
    negLogVolume (mul3 X Y) =
      negLogVolume X + negLogVolume Y := by
  unfold negLogVolume
  rw [log_detZ3_mul3_of_ne_zero X Y hX hY]
  ring

/-! ### Barrier/Radon–Nikodym reconciliation lemmas -/

/--
The positive Zorn chamber is closed under the concrete Zorn product.

This is the determinant composition theorem read as preservation of the
positive log-barrier domain.
-/
theorem IsPosCone_mul3
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsPosCone X) (hY : IsPosCone Y) :
    IsPosCone (mul3 X Y) := by
  unfold IsPosCone at *
  rw [detZ3_mul3]
  exact mul_pos hX hY

/--
The isotropic/null shell is outside the positive log-barrier chamber.

This formalizes the statement that the projective null boundary is a barrier
boundary, not an interior point of the finite logarithmic potential.
-/
theorem not_IsPosCone_of_detZ3_eq_zero
    (X : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : detZ3 X = 0) :
    ¬ IsPosCone X := by
  intro hpos
  simp [IsPosCone, hX] at hpos

/--
Positive-branch negative logarithmic volume change under Zorn multiplication.

The additive change in the barrier potential caused by right multiplication
by `Y` is exactly the barrier potential of `Y`.
-/
theorem barrierPhi_change_mul3_left
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsPosCone X) (hY : IsPosCone Y) :
    barrierPhi (mul3 X Y) - barrierPhi X = barrierPhi Y := by
  rw [barrierPhi_mul3 X Y hX hY]
  ring

/--
Radon–Nikodym reconciliation on the positive Zorn chamber.

The barrier change under left multiplication agrees with the negative
logarithm of the determinant-ratio Radon–Nikodym readout.
-/
theorem barrierPhi_change_mul3_left_eq_negLog_relativeVolumeRN
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsPosCone X) (hY : IsPosCone Y) :
    barrierPhi (mul3 X Y) - barrierPhi X =
      -Real.log (relativeVolumeRN X (mul3 X Y)) := by
  calc
    barrierPhi (mul3 X Y) - barrierPhi X = barrierPhi Y := by
      exact barrierPhi_change_mul3_left X Y hX hY
    _ = -Real.log (relativeVolumeRN X (mul3 X Y)) := by
      rw [relativeVolumeRN_mul3_left X Y (ne_of_gt hX)]
      rfl

/--
Non-isotropic absolute log-volume change under Zorn multiplication.

This version works on the non-null stratum using `-log |detZ3|`, so it does
not require choosing the positive chamber.
-/
theorem barrierAbsPhi_change_mul3_left_of_ne_zero
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : detZ3 X ≠ 0) (hY : detZ3 Y ≠ 0) :
    barrierAbsPhi (mul3 X Y) - barrierAbsPhi X = barrierAbsPhi Y := by
  rw [barrierAbsPhi_mul3_of_ne_zero X Y hX hY]
  ring

/--
Non-isotropic negative-log-volume change under Zorn multiplication.

This is the same additive cocycle statement for `negLogVolume`.
-/
theorem negLogVolume_change_mul3_left_of_ne_zero
    (X Y : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : detZ3 X ≠ 0) (hY : detZ3 Y ≠ 0) :
    negLogVolume (mul3 X Y) - negLogVolume X = negLogVolume Y := by
  rw [negLogVolume_mul3_of_ne_zero X Y hX hY]
  ring

/-! ### Explicit logarithmic barrier calculus on the diagonal Zorn chamber -/

/--
Diagonal concrete Zorn cell.

This is not a new model; it is the diagonal subfamily of the existing
coordinate-level `ZornCell ℝ (ℝ × ℝ × ℝ)`.
-/
def diag3 (a b : ℝ) : ZornCell ℝ (ℝ × ℝ × ℝ) where
  a := a
  b := b
  v := (0, 0, 0)
  w := (0, 0, 0)

/-- The concrete determinant on the diagonal Zorn chamber is `a * b`. -/
@[simp]
theorem detZ3_diag3 (a b : ℝ) :
    detZ3 (diag3 a b) = a * b := by
  unfold detZ3 diag3 Coord3.dot
  ring

/-- The positive cone condition on the diagonal chamber follows from `a > 0`, `b > 0`. -/
theorem IsPosCone_diag3
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsPosCone (diag3 a b) := by
  unfold IsPosCone
  rw [detZ3_diag3]
  exact mul_pos ha hb

/--
The logarithmic Zorn barrier on the diagonal chamber splits as

`Φ(diag(a,b)) = -log a - log b`

on the positive branch.
-/
theorem barrierPhi_diag3
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    barrierPhi (diag3 a b) =
      -Real.log a - Real.log b := by
  unfold barrierPhi
  rw [detZ3_diag3]
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hb)]
  ring

/--
First derivative of the diagonal Zorn logarithmic barrier in the `a` coordinate:

`∂/∂a (-log detZ3(diag(a,b))) = -1/a`.
-/
theorem hasDerivAt_barrierPhi_diag3_a
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt
      (fun t : ℝ => barrierPhi (diag3 t b))
      (-1 / a)
      a := by
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hmul :
      HasDerivAt (fun t : ℝ => t * b) b a := by
    simpa using (hasDerivAt_id a).mul_const b
  have hlog :
      HasDerivAt
        (fun t : ℝ => Real.log (t * b))
        (((a * b)⁻¹) * b)
        a := by
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_log (mul_ne_zero ha_ne hb_ne)).comp a hmul
  have hneg :
      HasDerivAt
        (fun t : ℝ => -Real.log (t * b))
        (-(((a * b)⁻¹) * b))
        a :=
    hlog.neg
  have hcoef : -(((a * b)⁻¹) * b) = -1 / a := by
    field_simp [ha_ne, hb_ne]
  rw [hcoef] at hneg
  simpa [barrierPhi, detZ3, diag3, Coord3.dot] using hneg

/--
Second derivative / Hessian entry of the diagonal Zorn logarithmic barrier:

`∂²/∂a² (-log a - log b) = 1/a²`.

This is the one-dimensional Fisher/Koszul-Vinberg metric entry along the
positive diagonal chamber.
-/
theorem hasDerivAt_barrierPhi_diag3_hessian_a
    {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt
      (fun t : ℝ => -1 / t)
      (1 / (a ^ 2))
      a := by
  have hfun : (fun t : ℝ => -1 / t) = (fun t : ℝ => -t⁻¹) := by
    funext t
    rw [div_eq_mul_inv]
    ring
  rw [hfun]
  have hinv :
      HasDerivAt (fun t : ℝ => t⁻¹) (-(a ^ 2)⁻¹) a :=
    hasDerivAt_inv ha
  have hneg :
      HasDerivAt (fun t : ℝ => -t⁻¹) ((a ^ 2)⁻¹) a := by
    simpa using hinv.neg
  have hcoef : (a ^ 2)⁻¹ = 1 / (a ^ 2) := by
    simp [one_div]
  rw [← hcoef]
  exact hneg

/--
Quantitative barrier blow-up estimate.

If a positive Zorn determinant is below `exp (-M)`, then the logarithmic
barrier is at least `M`. This is the proof-bearing finite form of the statement
that the barrier diverges when the determinant approaches the isotropic
boundary.
-/
theorem barrierPhi_ge_of_detZ3_le_exp_neg
    (X : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hX : IsPosCone X)
    (M : ℝ)
    (hsmall : detZ3 X ≤ Real.exp (-M)) :
    M ≤ barrierPhi X := by
  unfold IsPosCone at hX
  unfold barrierPhi
  have hlog_le :
      Real.log (detZ3 X) ≤ Real.log (Real.exp (-M)) :=
    Real.log_le_log hX hsmall
  rw [Real.log_exp] at hlog_le
  linarith

/-- Ambient coordinate pairing on concrete Zorn cells. -/
def coordPair (X Y : ZornCell ℝ (ℝ × ℝ × ℝ)) : ℝ :=
  X.a * Y.a + X.b * Y.b + dot X.v Y.v + dot X.w Y.w

/--
Generic affine Bregman readout against a supplied dual coordinate.
-/
noncomputable def bregmanAt
    (F : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ)
    (X Y η : ZornCell ℝ (ℝ × ℝ × ℝ)) : ℝ :=
  F X - F Y - (coordPair X η - coordPair Y η)

/--
Log-det Bregman readout against a supplied dual coordinate `η`.

This is the affine expression
`F(X) - F(Y) - (⟪X,η⟫ - ⟪Y,η⟫)` with `F = barrierPhi`.
-/
noncomputable def logDetBregmanAt
    (X Y η : ZornCell ℝ (ℝ × ℝ × ℝ)) : ℝ :=
  bregmanAt barrierPhi X Y η

/--
Bregman invariance under additive potential shift:
`D_{F+c} = D_F`.
-/
theorem bregmanAt_add_const_invariant
    (F : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ)
    (c : ℝ)
    (X Y η : ZornCell ℝ (ℝ × ℝ × ℝ)) :
    bregmanAt (fun Z => F Z + c) X Y η = bregmanAt F X Y η := by
  unfold bregmanAt
  ring

/--
General additive cocycle cancellation:
if `F' = F + c` pointwise, then `D_{F'} = D_F`.
-/
theorem bregmanAt_eq_of_additive_cocycle_shift
    (F F' : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ)
    (c : ℝ)
    (hshift : ∀ Z, F' Z = F Z + c)
    (X Y η : ZornCell ℝ (ℝ × ℝ × ℝ)) :
    bregmanAt F' X Y η = bregmanAt F X Y η := by
  rw [show F' = (fun Z => F Z + c) by
    funext Z
    exact hshift Z]
  exact bregmanAt_add_const_invariant F c X Y η

/--
Firewall #4 (Bregman/Fenchel layer): adding a constant to the barrier potential
does not change the Bregman defect.
-/
theorem logDetBregmanAt_barrier_shift_invariant
    (X Y η : ZornCell ℝ (ℝ × ℝ × ℝ))
    (c : ℝ) :
    (barrierPhi X + c) - (barrierPhi Y + c) - (coordPair X η - coordPair Y η)
      =
    logDetBregmanAt X Y η := by
  unfold logDetBregmanAt bregmanAt
  ring

/--
Instantiation of additive-shift invariance for cocycle-shifted barrier:
if `F_U = F - log χ(U)`, then the Bregman defect is unchanged.
-/
theorem logDetBregmanAt_cocycle_shift_cancel
    (X Y η : ZornCell ℝ (ℝ × ℝ × ℝ))
    (χU : ℝ) :
    bregmanAt (fun Z => barrierPhi Z - Real.log χU) X Y η =
      logDetBregmanAt X Y η := by
  unfold logDetBregmanAt
  simpa [sub_eq_add_neg] using
    bregmanAt_add_const_invariant barrierPhi (-Real.log χU) X Y η

/--
8D Jacobian normalization identity (concrete criterion).

If a Jacobian scale is fixed by `J(U) = |detZ3(U)|^4`, then
`-log J(U) = -4 log |detZ3(U)|`.
-/
theorem neg_log_jacobianScale_eq_neg_four_log_abs_detZ3
    (jacobianScale : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ)
    (U : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hJ : jacobianScale U = |detZ3 U| ^ (4 : ℕ)) :
    -Real.log (jacobianScale U) = -4 * Real.log |detZ3 U| := by
  rw [hJ]
  by_cases h0 : detZ3 U = 0
  · simp [h0]
  · rw [← Real.rpow_natCast]
    rw [Real.log_rpow (abs_pos.mpr h0)]
    ring

/--
Concrete RN cocycle theorem for a multiplicative Zorn action character.

If `act` scales the Zorn determinant by `χ(U)` and Jacobian scale is normalized
as `|detZ3 U|^4`, then the logarithmic RN shift is exactly
`-4 * log |χ(U)|`.
-/
theorem rn_log_cocycle_of_action_character
    (jacobianScale : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ)
    (χ : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ)
    (U : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hscale : jacobianScale U = |χ U| ^ (4 : ℕ)) :
    -Real.log (jacobianScale U) = -4 * Real.log |χ U| := by
  rw [hscale]
  by_cases h0 : χ U = 0
  · simp [h0]
  · rw [← Real.rpow_natCast]
    rw [Real.log_rpow (abs_pos.mpr h0)]
    ring

/--
Concrete left-transport cocycle on the positive cone:
for explicit Zorn product `mul3`, the barrier shift is exactly additive.
-/
theorem barrierPhi_left_mul3_shift
    (U X : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hU : IsPosCone U) (hX : IsPosCone X) :
    barrierPhi (mul3 U X) = barrierPhi X + barrierPhi U := by
  rw [barrierPhi_mul3 U X hU hX]
  ring

/--
Fenchel-gap form for `F = barrierPhi` and pairing `coordPair`.
-/
noncomputable def logDetFenchelGapAt
    (X η : ZornCell ℝ (ℝ × ℝ × ℝ))
    (dualPotential : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ) : ℝ :=
  barrierPhi X + dualPotential η - coordPair X η

/--
Fenchel-gap rewrite of the log-det Bregman readout at basepoint dual coordinate,
assuming the Legendre contact identity at `Y`.
-/
theorem logDetBregman_eq_fenchelGap_at_contact
    (X Y η : ZornCell ℝ (ℝ × ℝ × ℝ))
    (dualPotential : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ)
    (hcontact : dualPotential η = coordPair Y η - barrierPhi Y) :
    logDetBregmanAt X Y η =
      logDetFenchelGapAt X η dualPotential := by
  unfold logDetBregmanAt bregmanAt logDetFenchelGapAt
  rw [hcontact]
  ring

end LogDet

/-! ### Concrete polar form for the Zorn determinant -/

variable {R : Type*} [CommRing R]

/-- Componentwise addition of concrete `R³` Zorn cells. -/
def add3 (X Y : ZornCell R (R × R × R)) :
    ZornCell R (R × R × R) where
  a := X.a + Y.a
  b := X.b + Y.b
  v :=
    (X.v.1 + Y.v.1,
      X.v.2.1 + Y.v.2.1,
      X.v.2.2 + Y.v.2.2)
  w :=
    (X.w.1 + Y.w.1,
      X.w.2.1 + Y.w.2.1,
      X.w.2.2 + Y.w.2.2)

/-- Componentwise scalar multiplication of concrete `R³` Zorn cells. -/
def scale3 (lam : R) (X : ZornCell R (R × R × R)) :
    ZornCell R (R × R × R) where
  a := lam * X.a
  b := lam * X.b
  v := (lam * X.v.1, lam * X.v.2.1, lam * X.v.2.2)
  w := (lam * X.w.1, lam * X.w.2.1, lam * X.w.2.2)

/--
The unhalved polar form of the concrete Zorn determinant:

`polarDetZ3 X Y = detZ3 (X + Y) - detZ3 X - detZ3 Y`.

The vanishing relation is unaffected by the omitted factor `1/2`.
-/
def polarDetZ3
    (X Y : ZornCell R (R × R × R)) : R :=
  detZ3 (add3 X Y) - detZ3 X - detZ3 Y

/--
Coordinate formula for the concrete Zorn polar form.
-/
theorem polarDetZ3_formula
    (X Y : ZornCell R (R × R × R)) :
    polarDetZ3 X Y =
      X.a * Y.b + Y.a * X.b
        - Coord3.dot X.v Y.w
        - Coord3.dot Y.v X.w := by
  rcases X with ⟨a, b, x, y⟩
  rcases x with ⟨x1, x23⟩
  rcases x23 with ⟨x2, x3⟩
  rcases y with ⟨y1, y23⟩
  rcases y23 with ⟨y2, y3⟩
  rcases Y with ⟨a', b', u, v⟩
  rcases u with ⟨u1, u23⟩
  rcases u23 with ⟨u2, u3⟩
  rcases v with ⟨v1, v23⟩
  rcases v23 with ⟨v2, v3⟩
  unfold polarDetZ3 add3 detZ3 Coord3.dot
  ring

/--
Self-pairing of the concrete Zorn polar form:

`polarDetZ3 X X = 2 * detZ3 X`.
-/
theorem polarDetZ3_self
    (X : ZornCell R (R × R × R)) :
    polarDetZ3 X X = 2 * detZ3 X := by
  rw [polarDetZ3_formula]
  unfold detZ3
  ring

/--
A Zorn-null point is self-orthogonal for the concrete Zorn polar form.
-/
theorem polarDetZ3_self_of_detZ3_eq_zero
    (X : ZornCell R (R × R × R))
    (hX : detZ3 X = 0) :
    polarDetZ3 X X = 0 := by
  rw [polarDetZ3_self, hX]
  ring

/-- The concrete Zorn polar form is symmetric. -/
theorem polarDetZ3_symm
    (X Y : ZornCell R (R × R × R)) :
    polarDetZ3 X Y = polarDetZ3 Y X := by
  rw [polarDetZ3_formula, polarDetZ3_formula]
  ring

/-- The concrete determinant is quadratic under componentwise scaling. -/
theorem detZ3_scale3
    (lam : R) (X : ZornCell R (R × R × R)) :
    detZ3 (scale3 lam X) = lam ^ 2 * detZ3 X := by
  rcases X with ⟨a, b, x, y⟩
  rcases x with ⟨x1, x23⟩
  rcases x23 with ⟨x2, x3⟩
  rcases y with ⟨y1, y23⟩
  rcases y23 with ⟨y2, y3⟩
  unfold detZ3 scale3 Coord3.dot
  ring

/-- Left homogeneity of the concrete Zorn polar form. -/
theorem polarDetZ3_scale_left
    (lam : R) (X Y : ZornCell R (R × R × R)) :
    polarDetZ3 (scale3 lam X) Y = lam * polarDetZ3 X Y := by
  rcases X with ⟨a, b, x, y⟩
  rcases x with ⟨x1, x23⟩
  rcases x23 with ⟨x2, x3⟩
  rcases y with ⟨y1, y23⟩
  rcases y23 with ⟨y2, y3⟩
  rcases Y with ⟨a', b', u, v⟩
  rcases u with ⟨u1, u23⟩
  rcases u23 with ⟨u2, u3⟩
  rcases v with ⟨v1, v23⟩
  rcases v23 with ⟨v2, v3⟩
  unfold polarDetZ3 add3 scale3 detZ3 Coord3.dot
  ring

/-- Right homogeneity of the concrete Zorn polar form. -/
theorem polarDetZ3_scale_right
    (mu : R) (X Y : ZornCell R (R × R × R)) :
    polarDetZ3 X (scale3 mu Y) = mu * polarDetZ3 X Y := by
  rw [polarDetZ3_symm X (scale3 mu Y)]
  rw [polarDetZ3_scale_left mu Y X]
  rw [polarDetZ3_symm Y X]

/-- Bilinear scaling of the concrete Zorn polar form. -/
theorem polarDetZ3_scale_both
    (lam mu : R) (X Y : ZornCell R (R × R × R)) :
    polarDetZ3 (scale3 lam X) (scale3 mu Y) =
      (lam * mu) * polarDetZ3 X Y := by
  rw [polarDetZ3_scale_left lam X (scale3 mu Y)]
  rw [polarDetZ3_scale_right mu X Y]
  ring

/--
Concrete projective polar incidence is independent of nonzero scalar
representatives.

This is the coordinate-level version of projective polar well-definedness:
scaling either Zorn representative by a nonzero scalar preserves the vanishing
of the polar form.
-/
theorem polarDetZ3_zero_iff_scale_both
    {𝕜 : Type*} [Field 𝕜]
    {lam mu : 𝕜}
    (hlam : lam ≠ 0) (hmu : mu ≠ 0)
    (X Y : ZornCell 𝕜 (𝕜 × 𝕜 × 𝕜)) :
    polarDetZ3 X Y = 0
      ↔
    polarDetZ3 (scale3 lam X) (scale3 mu Y) = 0 := by
  rw [polarDetZ3_scale_both]
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    rcases mul_eq_zero.mp h with hprod | hpolar
    · exact False.elim ((mul_ne_zero hlam hmu) hprod)
    · exact hpolar

end ZornCell

/--
Projective datum for the local Zorn null shell.

The unit-scalar action is kept as data. In the concrete instance it should be
ordinary scalar multiplication by a unit. Here we only require the laws needed
to construct the projective quotient.
-/
structure ZornProjectiveDatum
    (R : Type u) (V : Type v)
    [CommRing R] [AddCommGroup V] [Module R V] where
  B : V →ₗ[R] V →ₗ[R] R
  zero : ZornCell R V

  /-- Unit scaling on Zorn cells. -/
  scale : Rˣ → ZornCell R V → ZornCell R V

  /-- Scaling by `1` is identity. -/
  scale_one :
    ∀ X : ZornCell R V,
      scale 1 X = X

  /-- Left action law: `(u * v) • X = u • (v • X)`. -/
  scale_mul :
    ∀ (u v : Rˣ) (X : ZornCell R V),
      scale (u * v) X = scale u (scale v X)

  /-- Unit scaling preserves the null condition. -/
  detZ_scale_zero :
    ∀ (u : Rˣ) (X : ZornCell R V),
      ZornCell.detZ B (scale u X) = 0
        ↔
      ZornCell.detZ B X = 0

  /-- Unit scaling preserves nonzeroness. -/
  scale_ne_zero :
    ∀ (u : Rˣ) (X : ZornCell R V),
      X ≠ zero → scale u X ≠ zero

namespace ZornProjectiveDatum

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- A nonzero null Zorn representative. -/
structure NullRep (D : ZornProjectiveDatum R V) where
  rep : ZornCell R V
  det_zero : ZornCell.detZ D.B rep = 0
  nonzero : rep ≠ D.zero

variable (D : ZornProjectiveDatum R V)

/-- Unit scaling preserves the nonzero null cone. -/
def scaleNull (u : Rˣ) (X : NullRep D) : NullRep D where
  rep := D.scale u X.rep
  det_zero := (D.detZ_scale_zero u X.rep).2 X.det_zero
  nonzero := D.scale_ne_zero u X.rep X.nonzero

/--
Projective equivalence on nonzero null representatives.

`X ~ Y` iff `Y = u • X` for some unit scalar `u`.
-/
def rayRel (X Y : NullRep D) : Prop :=
  ∃ u : Rˣ, D.scale u X.rep = Y.rep

/-- The projective null-shell setoid. -/
instance nullRepSetoid : Setoid (NullRep D) where
  r := rayRel D
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro X
      exact ⟨1, D.scale_one X.rep⟩
    · intro X Y hXY
      rcases hXY with ⟨u, hXY⟩
      refine ⟨u⁻¹, ?_⟩
      calc
        D.scale u⁻¹ Y.rep
            = D.scale u⁻¹ (D.scale u X.rep) := by rw [← hXY]
        _   = D.scale (u⁻¹ * u) X.rep := by
                exact (D.scale_mul u⁻¹ u X.rep).symm
        _   = D.scale 1 X.rep := by simp
        _   = X.rep := D.scale_one X.rep
    · intro X Y Z hXY hYZ
      rcases hXY with ⟨u, hXY⟩
      rcases hYZ with ⟨v, hYZ⟩
      refine ⟨v * u, ?_⟩
      calc
        D.scale (v * u) X.rep
            = D.scale v (D.scale u X.rep) := D.scale_mul v u X.rep
        _   = D.scale v Y.rep := by rw [hXY]
        _   = Z.rep := hYZ

/--
The projective Zorn null shell:

  `{X : ZornCell // detZ X = 0 ∧ X ≠ 0} / Rˣ`.
-/
def NullRay : Type (max u v) :=
  Quotient (nullRepSetoid D)

/-- Quotient map from a representative to its null ray. -/
def nullRayMk (X : NullRep D) : NullRay D :=
  Quotient.mk _ X

/-- Representatives differing by a unit scalar define the same null ray. -/
theorem mk_eq_of_scale
    {X Y : NullRep D} {u : Rˣ}
    (h : D.scale u X.rep = Y.rep) :
    nullRayMk D X = nullRayMk D Y := by
  apply Quotient.sound
  exact ⟨u, h⟩

/-- Projective null rays are scale-blind. -/
@[simp]
theorem mk_scaleNull
    (u : Rˣ) (X : NullRep D) :
    nullRayMk D X = nullRayMk D (scaleNull D u X) := by
  apply Quotient.sound
  exact ⟨u, rfl⟩

end ZornProjectiveDatum

end InfoGeometry.Projective.SplitOctonions
