import Mathlib

/-!
# Concrete finite Jones Bregman heat

This module installs an explicit quadratic Bregman potential for the finite
two-channel Jones loss branch.

The finite branch is intentionally concrete: nonnegativity is proved from the
closed formula for the quadratic Bregman divergence, and the visible/hidden heat
audit is proved from the two scalar Stinespring isometry laws.
-/

noncomputable section

namespace InfoGeometry.Optics.FiniteJonesBregman

/-! ## Concrete two-channel loss space -/

/--
Two-channel real loss/gain point.

The `s` and `p` fields are the two polarization-channel components.
-/
structure LossPoint where
  s : ℝ
  p : ℝ
deriving DecidableEq

namespace LossPoint

/-- Zero loss/gain point. -/
def zero : LossPoint where
  s := 0
  p := 0

instance : Zero LossPoint where
  zero := zero

@[simp] theorem zero_s :
    (0 : LossPoint).s = 0 :=
  rfl

@[simp] theorem zero_p :
    (0 : LossPoint).p = 0 :=
  rfl

/-- Difference of two loss points. -/
def sub (X Y : LossPoint) : LossPoint where
  s := X.s - Y.s
  p := X.p - Y.p

@[simp] theorem sub_s (X Y : LossPoint) :
    (sub X Y).s = X.s - Y.s :=
  rfl

@[simp] theorem sub_p (X Y : LossPoint) :
    (sub X Y).p = X.p - Y.p :=
  rfl

@[ext] theorem ext {X Y : LossPoint}
    (hs : X.s = Y.s)
    (hp : X.p = Y.p) :
    X = Y := by
  cases X
  cases Y
  simp_all

end LossPoint

/-! ## Explicit quadratic potential -/

/--
Concrete quadratic information potential:

`Phi(X) = 1/2 * (X.s^2 + X.p^2)`.
-/
def quadraticPotential
    (X : LossPoint) : ℝ :=
  (X.s ^ 2 + X.p ^ 2) / 2

/--
Gradient pairing at `Y` applied to direction `H`:

`dPhi_Y(H) = Y.s * H.s + Y.p * H.p`.
-/
def quadraticGradientPairing
    (Y H : LossPoint) : ℝ :=
  Y.s * H.s + Y.p * H.p

/--
Concrete quadratic Bregman divergence:

`D_Phi(X || Y) = Phi(X) - Phi(Y) - dPhi_Y(X - Y)`.
-/
def quadraticBregman
    (X Y : LossPoint) : ℝ :=
  quadraticPotential X -
    quadraticPotential Y -
      quadraticGradientPairing Y (LossPoint.sub X Y)

/-- Closed form of the quadratic Bregman divergence. -/
theorem quadraticBregman_eq_half_sq_dist
    (X Y : LossPoint) :
    quadraticBregman X Y =
      ((X.s - Y.s) ^ 2 + (X.p - Y.p) ^ 2) / 2 := by
  dsimp [
    quadraticBregman,
    quadraticPotential,
    quadraticGradientPairing,
    LossPoint.sub
  ]
  ring

/-- Quadratic Bregman divergence is nonnegative. -/
theorem quadraticBregman_nonneg
    (X Y : LossPoint) :
    0 ≤ quadraticBregman X Y := by
  rw [quadraticBregman_eq_half_sq_dist]
  nlinarith [sq_nonneg (X.s - Y.s), sq_nonneg (X.p - Y.p)]

/-- Quadratic Bregman divergence vanishes on the diagonal. -/
@[simp] theorem quadraticBregman_self
    (X : LossPoint) :
    quadraticBregman X X = 0 := by
  rw [quadraticBregman_eq_half_sq_dist]
  ring

/-- Bregman heat relative to the zero-loss reference point. -/
def bregmanHeatAtZero
    (X : LossPoint) : ℝ :=
  quadraticBregman X 0

/-- Closed form for Bregman heat at zero. -/
theorem bregmanHeatAtZero_eq
    (X : LossPoint) :
    bregmanHeatAtZero X =
      (X.s ^ 2 + X.p ^ 2) / 2 := by
  dsimp [bregmanHeatAtZero]
  rw [quadraticBregman_eq_half_sq_dist]
  simp

/-- Bregman heat at zero is nonnegative. -/
theorem bregmanHeatAtZero_nonneg
    (X : LossPoint) :
    0 ≤ bregmanHeatAtZero X :=
  quadraticBregman_nonneg X 0

@[simp] theorem bregmanHeatAtZero_zero :
    bregmanHeatAtZero 0 = 0 := by
  simp [bregmanHeatAtZero]

/-! ## Real diagonal finite Stinespring audit -/

/--
Concrete real diagonal Stinespring audit.

Visible amplitudes are `r_s`, `r_p`; hidden/environment amplitudes are `v_s`,
`v_p`.  The two scalar isometry laws say

`r_s^2 + v_s^2 = 1` and `r_p^2 + v_p^2 = 1`.
-/
structure RealDiagonalStinespringAudit where
  r_s : ℝ
  r_p : ℝ
  v_s : ℝ
  v_p : ℝ
  s_isometry :
    r_s ^ 2 + v_s ^ 2 = 1
  p_isometry :
    r_p ^ 2 + v_p ^ 2 = 1

namespace RealDiagonalStinespringAudit

variable (A : RealDiagonalStinespringAudit)

/-- Visible loss point: `(1 - r_s^2, 1 - r_p^2)`. -/
def visibleLossPoint : LossPoint where
  s := 1 - A.r_s ^ 2
  p := 1 - A.r_p ^ 2

/-- Hidden gain point: `(v_s^2, v_p^2)`. -/
def hiddenGainPoint : LossPoint where
  s := A.v_s ^ 2
  p := A.v_p ^ 2

/-- Visible loss equals hidden gain, componentwise. -/
theorem visibleLossPoint_eq_hiddenGainPoint :
    A.visibleLossPoint = A.hiddenGainPoint := by
  ext
  · dsimp [visibleLossPoint, hiddenGainPoint]
    nlinarith [A.s_isometry]
  · dsimp [visibleLossPoint, hiddenGainPoint]
    nlinarith [A.p_isometry]

/-- Visible Bregman heat. -/
def visibleBregmanHeat : ℝ :=
  bregmanHeatAtZero A.visibleLossPoint

/-- Hidden Bregman heat. -/
def hiddenBregmanHeat : ℝ :=
  bregmanHeatAtZero A.hiddenGainPoint

/-- Visible Bregman heat equals hidden Bregman heat. -/
theorem visibleBregmanHeat_eq_hiddenBregmanHeat :
    A.visibleBregmanHeat = A.hiddenBregmanHeat := by
  dsimp [visibleBregmanHeat, hiddenBregmanHeat]
  rw [A.visibleLossPoint_eq_hiddenGainPoint]

/-- Visible Bregman heat is nonnegative. -/
theorem visibleBregmanHeat_nonneg :
    0 ≤ A.visibleBregmanHeat :=
  bregmanHeatAtZero_nonneg A.visibleLossPoint

/-- Hidden Bregman heat is nonnegative. -/
theorem hiddenBregmanHeat_nonneg :
    0 ≤ A.hiddenBregmanHeat :=
  bregmanHeatAtZero_nonneg A.hiddenGainPoint

/-- If the hidden/environment amplitudes vanish, the hidden Bregman heat vanishes. -/
theorem hiddenBregmanHeat_eq_zero_of_hidden_zero
    (hs : A.v_s = 0)
    (hp : A.v_p = 0) :
    A.hiddenBregmanHeat = 0 := by
  dsimp [
    hiddenBregmanHeat,
    hiddenGainPoint,
    bregmanHeatAtZero,
    quadraticBregman,
    quadraticPotential,
    quadraticGradientPairing,
    LossPoint.sub
  ]
  rw [hs, hp]
  norm_num

/-- If the hidden/environment amplitudes vanish, the visible Bregman heat vanishes. -/
theorem visibleBregmanHeat_eq_zero_of_hidden_zero
    (hs : A.v_s = 0)
    (hp : A.v_p = 0) :
    A.visibleBregmanHeat = 0 := by
  rw [A.visibleBregmanHeat_eq_hiddenBregmanHeat]
  exact A.hiddenBregmanHeat_eq_zero_of_hidden_zero hs hp

end RealDiagonalStinespringAudit

/-! ## Finite Jones Bregman audit package -/

/--
Concrete finite Jones Bregman audit.

This packages the real diagonal Stinespring audit and its constructive Bregman
heat equality.
-/
structure FiniteJonesBregmanAudit where
  audit : RealDiagonalStinespringAudit

namespace FiniteJonesBregmanAudit

variable (A : FiniteJonesBregmanAudit)

/-- The finite Jones Bregman audit equation. -/
theorem visible_heat_eq_hidden_heat :
    A.audit.visibleBregmanHeat =
      A.audit.hiddenBregmanHeat :=
  A.audit.visibleBregmanHeat_eq_hiddenBregmanHeat

/-- Visible heat is nonnegative. -/
theorem visible_heat_nonneg :
    0 ≤ A.audit.visibleBregmanHeat :=
  A.audit.visibleBregmanHeat_nonneg

/-- Hidden heat is nonnegative. -/
theorem hidden_heat_nonneg :
    0 ≤ A.audit.hiddenBregmanHeat :=
  A.audit.hiddenBregmanHeat_nonneg

end FiniteJonesBregmanAudit

/-! ## Owner targets discharged constructively -/

/--
Owner target for a concrete finite quadratic Bregman potential.

This is no longer witness-gated: the potential is explicitly constructed above.
-/
def FiniteQuadraticBregmanOwnerTarget : Prop :=
  ∀ X Y : LossPoint,
    0 ≤ quadraticBregman X Y

/-- Constructive proof of the finite quadratic Bregman owner target. -/
theorem finiteQuadraticBregmanOwnerTarget :
    FiniteQuadraticBregmanOwnerTarget := by
  intro X Y
  exact quadraticBregman_nonneg X Y

/-- Owner target for concrete finite Jones Bregman heat accounting. -/
def FiniteJonesBregmanAuditOwnerTarget : Prop :=
  ∀ A : RealDiagonalStinespringAudit,
    A.visibleBregmanHeat =
      A.hiddenBregmanHeat ∧
    0 ≤ A.visibleBregmanHeat ∧
    0 ≤ A.hiddenBregmanHeat

/-- Constructive proof of the finite Jones Bregman audit owner target. -/
theorem finiteJonesBregmanAuditOwnerTarget :
    FiniteJonesBregmanAuditOwnerTarget := by
  intro A
  exact
    ⟨A.visibleBregmanHeat_eq_hiddenBregmanHeat,
     A.visibleBregmanHeat_nonneg,
     A.hiddenBregmanHeat_nonneg⟩

end InfoGeometry.Optics.FiniteJonesBregman
