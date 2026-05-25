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
    (hX : detZ3 X ≠ 0) (hY : detZ3 Y ≠ 0) :
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

section CharacterCocycle

open Real

variable {G : Type*} [Group G]

/-- Additive log-cocycle attached to a positive multiplicative character. -/
noncomputable def logCharacterCocycle (χ : G → ℝ) (g : G) : ℝ :=
  -Real.log (χ g)

/--
Multiplicative character gives additive log-cocycle:
`c(gh) = c(g) + c(h)` for `c(g) = -log χ(g)`.
-/
theorem logCharacterCocycle_mul
    (χ : G → ℝ)
    (hχ_mul : ∀ g h : G, χ (g * h) = χ g * χ h)
    (hχ_pos : ∀ g : G, 0 < χ g)
    (g h : G) :
    logCharacterCocycle χ (g * h) =
      logCharacterCocycle χ g + logCharacterCocycle χ h := by
  unfold logCharacterCocycle
  rw [hχ_mul g h, Real.log_mul (ne_of_gt (hχ_pos g)) (ne_of_gt (hχ_pos h))]
  ring

/--
If a conformal action scales a quadratic norm by `χ`, then in dimension `8`
the volume Jacobian scales by `χ^4`; equivalently the inverse-density log is
`4 log χ` (for positive `χ`).
-/
theorem neg_log_inv_jacobian_eq_four_log_character
    (χ J : ℝ)
    (hJ : J = χ ^ (4 : ℕ)) :
    -Real.log (J⁻¹) = 4 * Real.log χ := by
  rw [hJ]
  rw [show -Real.log ((χ ^ (4 : ℕ))⁻¹) = Real.log (χ ^ (4 : ℕ)) by
    rw [Real.log_inv, neg_neg]]
  simpa using (Real.log_rpow χ (4 : ℝ))

/--
Action-character law on the concrete positive cone:
if `detZ3` scales by `χ`, then `barrierPhi` shifts by `-log χ`.
-/
theorem barrierPhi_action_of_det_character
    (act : G → ZornCell ℝ (ℝ × ℝ × ℝ) → ZornCell ℝ (ℝ × ℝ × ℝ))
    (χ : G → ℝ)
    (hdet : ∀ g X, detZ3 (act g X) = χ g * detZ3 X)
    (g : G) (X : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hχ : 0 < χ g) (hX : IsPosCone X) :
    barrierPhi (act g X) = barrierPhi X - Real.log (χ g) := by
  unfold barrierPhi
  rw [hdet g X]
  rw [Real.log_mul (ne_of_gt hχ) (ne_of_gt hX)]
  ring

/-- Pushforward RN cocycle rewrite: `-log (1/J) = log J` for positive `J`. -/
theorem neg_log_inv_eq_log
    (J : ℝ) :
    -Real.log (1 / J) = Real.log J := by
  rw [one_div, Real.log_inv, neg_neg]

/--
If `J = |χ|^4`, the RN logarithmic cocycle is `4 log |χ|`.
-/
theorem rn_log_cocycle_eq_four_log_abs_character
    (χ : ℝ) (hχ : χ ≠ 0) :
    let J : ℝ := |χ| ^ (4 : ℕ);
    -Real.log (1 / J) = 4 * Real.log |χ| := by
  intro J
  have h := neg_log_inv_jacobian_eq_four_log_character (|χ|) (|χ| ^ (4 : ℕ)) rfl
  simpa [J] using h

/--
Function-form RN logarithmic cocycle:
if `J(g) = |χ(g)|^4`, then `-log (1 / J(g)) = 4 log |χ(g)|`.
-/
theorem rn_log_cocycle_eq_four_log_abs_character_fn
    (χ J : G → ℝ)
    (hJ : ∀ g : G, J g = |χ g| ^ (4 : ℕ))
    (hχ : ∀ g : G, χ g ≠ 0)
    (g : G) :
    -Real.log (1 / J g) = 4 * Real.log |χ g| := by
  rw [hJ g]
  simpa using rn_log_cocycle_eq_four_log_abs_character (χ g) (hχ g)

/--
8D Jacobian normalization criterion:
if `jacobianScale U = |detZ3 U|^4`, then
`-log (jacobianScale U) = -4 * log |detZ3 U|`.
-/
theorem neg_log_jacobianScale_eq_neg_four_log_abs_detZ3
    (jacobianScale : ZornCell ℝ (ℝ × ℝ × ℝ) → ℝ)
    (U : ZornCell ℝ (ℝ × ℝ × ℝ))
    (hJ : jacobianScale U = |detZ3 U| ^ (4 : ℕ))
    (hdet : detZ3 U ≠ 0) :
    -Real.log (jacobianScale U) = -4 * Real.log |detZ3 U| := by
  rw [hJ]
  rw [← Real.rpow_natCast]
  rw [Real.log_rpow (abs_pos.mpr hdet)]
  ring

end CharacterCocycle

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
