import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Cartan.Involution
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.KKTCore

Split-operator KKT core induced by the existing real split `Cl(1,1)` seed.

The grading is carried by the Clifford involution `eps`. This yields the
adjacent three-channel decomposition of the endomorphism algebra into:

- `g₁`: plus-to-minus channel,
- `g₀`: block-diagonal channel,
- `g₋₁`: minus-to-plus channel.

This file proves the exact closure facts needed later for the generalized
inverse and Fredholm corridors.
-/

namespace KKTCore

open InfoGeometry.Cartan
open InfoGeometry.Quantum

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H
local notation "IdH" => ContinuousLinearMap.id ℝ H

/-- The `+1` spectral projector of the split Clifford grading. -/
@[rep_depth krein]
noncomputable def plusProjector (X : RealSplitCl11Action H) : EndH :=
  (⅟ (2 : ℝ)) • (IdH + X.eps)

/-- The `-1` spectral projector of the split Clifford grading. -/
@[rep_depth krein]
noncomputable def minusProjector (X : RealSplitCl11Action H) : EndH :=
  (⅟ (2 : ℝ)) • (IdH - X.eps)

/-- Grade-zero block-diagonal channel. -/
@[rep_depth krein]
noncomputable def gZeroPart (X : RealSplitCl11Action H) (A : EndH) : EndH :=
  plusProjector X * A * plusProjector X + minusProjector X * A * minusProjector X

/-- Grade `+1` off-diagonal projection. -/
@[rep_depth krein]
noncomputable def gOnePart (X : RealSplitCl11Action H) (A : EndH) : EndH :=
  plusProjector X * A * minusProjector X

/-- Grade `-1` off-diagonal projection. -/
@[rep_depth krein]
noncomputable def gNegOnePart (X : RealSplitCl11Action H) (A : EndH) : EndH :=
  minusProjector X * A * plusProjector X

/-- Circularly polarized `u+` channel (plus-to-minus). -/
@[rep_depth krein]
noncomputable def uPlus (X : RealSplitCl11Action H) (A : EndH) : EndH :=
  gOnePart X A

/-- Circularly polarized `u-` channel (minus-to-plus). -/
@[rep_depth krein]
noncomputable def uMinus (X : RealSplitCl11Action H) (A : EndH) : EndH :=
  gNegOnePart X A

/-- The `u+` channel is exactly the `g₁` off-diagonal channel. -/
@[rep_depth krein, simp]
theorem uPlus_eq_gOnePart
    (X : RealSplitCl11Action H) (A : EndH) :
    uPlus X A = gOnePart X A := rfl

/-- The `u-` channel is exactly the `g₋₁` off-diagonal channel. -/
@[rep_depth krein, simp]
theorem uMinus_eq_gNegOnePart
    (X : RealSplitCl11Action H) (A : EndH) :
    uMinus X A = gNegOnePart X A := rfl

/-- Ordinary commutator in the endomorphism algebra. -/
@[rep_depth krein]
noncomputable def commutator (A B : EndH) : EndH :=
  A * B - B * A

/-- Clifford grading conjugation on the endomorphism algebra. -/
@[rep_depth krein]
noncomputable def epsConj (X : RealSplitCl11Action H) (A : EndH) : EndH :=
  X.eps * A * X.eps

/-- Exact grade-zero channel membership. -/
@[rep_depth krein]
def IsGZero (X : RealSplitCl11Action H) (A : EndH) : Prop :=
  gZeroPart X A = A

/-- Exact grade `+1` channel membership. -/
@[rep_depth krein]
def IsGOne (X : RealSplitCl11Action H) (A : EndH) : Prop :=
  gOnePart X A = A

/-- Exact grade `-1` channel membership. -/
@[rep_depth krein]
def IsGNegOne (X : RealSplitCl11Action H) (A : EndH) : Prop :=
  gNegOnePart X A = A

/-- The Clifford grading involution is a Cartan involution. -/
theorem RealSplitCl11Action.eps_is_cartan (X : RealSplitCl11Action H) :
    IsCartanInvolution X.eps.toLinearMap := by
  exact congrArg ContinuousLinearMap.toLinearMap X.eps_sq

@[rep_depth krein] theorem plusProjector_idempotent
    (X : RealSplitCl11Action H) :
    plusProjector X * plusProjector X = plusProjector X := by
  apply ContinuousLinearMap.ext
  intro u
  have h :=
    LinearMap.congr_fun
      (Pplus_idempotent X.eps.toLinearMap (RealSplitCl11Action.eps_is_cartan X)) u
  simp [plusProjector, Pplus] at h ⊢
  exact h

@[rep_depth krein] theorem minusProjector_idempotent
    (X : RealSplitCl11Action H) :
    minusProjector X * minusProjector X = minusProjector X := by
  apply ContinuousLinearMap.ext
  intro u
  have h :=
    LinearMap.congr_fun
      (Pminus_idempotent X.eps.toLinearMap (RealSplitCl11Action.eps_is_cartan X)) u
  simp [minusProjector, Pminus] at h ⊢
  exact h

@[rep_depth krein] theorem plusProjector_add_minusProjector
    (X : RealSplitCl11Action H) :
    plusProjector X + minusProjector X = IdH := by
  apply ContinuousLinearMap.ext
  intro u
  have h := LinearMap.congr_fun (Pplus_add_Pminus_eq_id X.eps.toLinearMap) u
  simp [plusProjector, minusProjector, Pplus, Pminus] at h ⊢
  exact h

@[rep_depth krein] theorem eps_mul_plusProjector
    (X : RealSplitCl11Action H) :
    X.eps * plusProjector X = plusProjector X := by
  apply ContinuousLinearMap.ext
  intro u
  have hs : X.eps (X.eps u) = u := X.eps_sq_apply u
  calc
    X.eps (plusProjector X u)
        = (⅟ (2 : ℝ)) • (X.eps u + X.eps (X.eps u)) := by
            simp [plusProjector]
    _ = (⅟ (2 : ℝ)) • (u + X.eps u) := by rw [hs]; abel_nf
    _ = plusProjector X u := by simp [plusProjector, add_comm]

@[rep_depth krein] theorem plusProjector_mul_eps
    (X : RealSplitCl11Action H) :
    plusProjector X * X.eps = plusProjector X := by
  apply ContinuousLinearMap.ext
  intro u
  have hs : X.eps (X.eps u) = u := X.eps_sq_apply u
  calc
    plusProjector X (X.eps u)
        = (⅟ (2 : ℝ)) • (X.eps u + X.eps (X.eps u)) := by
            simp [plusProjector]
    _ = (⅟ (2 : ℝ)) • (u + X.eps u) := by rw [hs]; abel_nf
    _ = plusProjector X u := by simp [plusProjector, add_comm]

@[rep_depth krein] theorem eps_mul_minusProjector
    (X : RealSplitCl11Action H) :
    X.eps * minusProjector X = -minusProjector X := by
  apply ContinuousLinearMap.ext
  intro u
  have hs : X.eps (X.eps u) = u := X.eps_sq_apply u
  calc
    X.eps (minusProjector X u)
        = (⅟ (2 : ℝ)) • (X.eps u - X.eps (X.eps u)) := by
            simp [minusProjector]
    _ = (⅟ (2 : ℝ)) • (X.eps u - u) := by rw [hs]
    _ = -minusProjector X u := by
          simp [minusProjector, sub_eq_add_neg]

@[rep_depth krein] theorem minusProjector_mul_eps
    (X : RealSplitCl11Action H) :
    minusProjector X * X.eps = -minusProjector X := by
  apply ContinuousLinearMap.ext
  intro u
  have hs : X.eps (X.eps u) = u := X.eps_sq_apply u
  calc
    minusProjector X (X.eps u)
        = (⅟ (2 : ℝ)) • (X.eps u - X.eps (X.eps u)) := by
            simp [minusProjector]
    _ = (⅟ (2 : ℝ)) • (X.eps u - u) := by rw [hs]
    _ = -minusProjector X u := by
          simp [minusProjector, sub_eq_add_neg]

@[rep_depth krein] theorem plusProjector_mul_minusProjector
    (X : RealSplitCl11Action H) :
    plusProjector X * minusProjector X = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have h : X.eps (minusProjector X u) = -(minusProjector X u) := by
    simpa using congrArg (fun F : EndH => F u) (eps_mul_minusProjector X)
  calc
    plusProjector X (minusProjector X u)
        = (⅟ (2 : ℝ)) • (minusProjector X u + X.eps (minusProjector X u)) := by
            simp [plusProjector]
    _ = (⅟ (2 : ℝ)) • (minusProjector X u + -(minusProjector X u)) := by rw [h]
    _ = 0 := by simp

@[rep_depth krein] theorem minusProjector_mul_plusProjector
    (X : RealSplitCl11Action H) :
    minusProjector X * plusProjector X = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  calc
    minusProjector X (plusProjector X u)
        = (⅟ (2 : ℝ)) • (plusProjector X u - X.eps (plusProjector X u)) := by
            simp [minusProjector]
    _ = (⅟ (2 : ℝ)) • (plusProjector X u - plusProjector X u) := by
          have h : X.eps (plusProjector X u) = plusProjector X u := by
            simpa using congrArg (fun F : EndH => F u) (eps_mul_plusProjector X)
          rw [h]
    _ = 0 := by simp

@[rep_depth krein, simp] theorem gZeroPart_add
    (X : RealSplitCl11Action H) (A B : EndH) :
    gZeroPart X (A + B) = gZeroPart X A + gZeroPart X B := by
  simp [gZeroPart, add_mul, mul_add, add_assoc, add_left_comm, add_comm]

@[rep_depth krein, simp] theorem gZeroPart_smul
    (X : RealSplitCl11Action H) (r : ℝ) (A : EndH) :
    gZeroPart X (r • A) = r • gZeroPart X A := by
  simp [gZeroPart]

@[rep_depth krein, simp] theorem gOnePart_add
    (X : RealSplitCl11Action H) (A B : EndH) :
    gOnePart X (A + B) = gOnePart X A + gOnePart X B := by
  simp [gOnePart, add_mul, mul_add]

@[rep_depth krein, simp] theorem gOnePart_smul
    (X : RealSplitCl11Action H) (r : ℝ) (A : EndH) :
    gOnePart X (r • A) = r • gOnePart X A := by
  simp [gOnePart]

@[rep_depth krein, simp] theorem gNegOnePart_add
    (X : RealSplitCl11Action H) (A B : EndH) :
    gNegOnePart X (A + B) = gNegOnePart X A + gNegOnePart X B := by
  simp [gNegOnePart, add_mul, mul_add]

@[rep_depth krein, simp] theorem gNegOnePart_smul
    (X : RealSplitCl11Action H) (r : ℝ) (A : EndH) :
    gNegOnePart X (r • A) = r • gNegOnePart X A := by
  simp [gNegOnePart]

@[rep_depth krein] theorem decompose
    (X : RealSplitCl11Action H) (A : EndH) :
    A = gZeroPart X A + gOnePart X A + gNegOnePart X A := by
  let Pp := plusProjector X
  let Pm := minusProjector X
  have hsum : Pp + Pm = IdH := plusProjector_add_minusProjector X
  have hsum1 : Pp + Pm = (1 : EndH) := by simpa using hsum
  calc
    A = (1 : EndH) * A * (1 : EndH) := by simp
    _ = (Pp + Pm) * A * (1 : EndH) := by rw [hsum1]
    _ = (Pp + Pm) * A * (Pp + Pm) := by rw [hsum1]
    _ = gZeroPart X A + gOnePart X A + gNegOnePart X A := by
          simp [gZeroPart, gOnePart, gNegOnePart, Pp, Pm, mul_add, add_mul,
            add_assoc, add_left_comm, add_comm]

@[rep_depth krein] theorem gOnePart_gZeroPart_eq_zero
    (X : RealSplitCl11Action H) (A : EndH) :
    gOnePart X (gZeroPart X A) = 0 := by
  unfold gOnePart gZeroPart
  calc
    plusProjector X *
        (plusProjector X * A * plusProjector X
          + minusProjector X * A * minusProjector X) *
        minusProjector X
        =
          plusProjector X * plusProjector X * A * plusProjector X * minusProjector X
            + plusProjector X * minusProjector X * A * minusProjector X * minusProjector X := by
              simp [mul_add, add_mul, mul_assoc]
    _ = 0 := by
          simp [plusProjector_mul_minusProjector, mul_assoc]

@[rep_depth krein] theorem gNegOnePart_gZeroPart_eq_zero
    (X : RealSplitCl11Action H) (A : EndH) :
    gNegOnePart X (gZeroPart X A) = 0 := by
  unfold gNegOnePart gZeroPart
  calc
    minusProjector X *
        (plusProjector X * A * plusProjector X
          + minusProjector X * A * minusProjector X) *
        plusProjector X
        =
          minusProjector X * plusProjector X * A * plusProjector X * plusProjector X
            + minusProjector X * minusProjector X * A * minusProjector X * plusProjector X := by
              simp [mul_add, add_mul, mul_assoc]
    _ = 0 := by
          simp [minusProjector_mul_plusProjector, mul_assoc]

@[rep_depth krein] theorem gOnePart_eq_zero_of_isGZero
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : IsGZero X A) :
    gOnePart X A = 0 := by
  unfold IsGZero at hA
  simpa [hA] using gOnePart_gZeroPart_eq_zero (X := X) (A := A)

@[rep_depth krein] theorem gNegOnePart_eq_zero_of_isGZero
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : IsGZero X A) :
    gNegOnePart X A = 0 := by
  unfold IsGZero at hA
  simpa [hA] using gNegOnePart_gZeroPart_eq_zero (X := X) (A := A)

@[rep_depth krein] theorem eq_gZeroPart_of_isGZero
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : IsGZero X A) :
    A = gZeroPart X A := by
  exact hA.symm

@[rep_depth krein] theorem eq_diagonal_blocks_of_isGZero
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : IsGZero X A) :
    A = plusProjector X * A * plusProjector X
      + minusProjector X * A * minusProjector X := by
  simpa [gZeroPart] using eq_gZeroPart_of_isGZero (X := X) (A := A) hA

@[rep_depth krein] theorem plusProjector_mul_mul_minusProjector_eq_zero_of_isGZero
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : IsGZero X A) :
    plusProjector X * A * minusProjector X = 0 := by
  simpa [gOnePart, mul_assoc] using gOnePart_eq_zero_of_isGZero (X := X) (A := A) hA

@[rep_depth krein] theorem minusProjector_mul_mul_plusProjector_eq_zero_of_isGZero
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : IsGZero X A) :
    minusProjector X * A * plusProjector X = 0 := by
  simpa [gNegOnePart, mul_assoc] using gNegOnePart_eq_zero_of_isGZero (X := X) (A := A) hA

@[rep_depth krein] theorem gOnePart_mul_gOnePart_eq_zero
    (X : RealSplitCl11Action H) (A B : EndH) :
    gOnePart X A * gOnePart X B = 0 := by
  calc
    gOnePart X A * gOnePart X B
        = plusProjector X * A * (minusProjector X * plusProjector X) * B * minusProjector X := by
            simp [gOnePart, mul_assoc]
    _ = 0 := by
          rw [minusProjector_mul_plusProjector]
          simp

@[rep_depth krein] theorem gNegOnePart_mul_gNegOnePart_eq_zero
    (X : RealSplitCl11Action H) (A B : EndH) :
    gNegOnePart X A * gNegOnePart X B = 0 := by
  calc
    gNegOnePart X A * gNegOnePart X B
        = minusProjector X * A * (plusProjector X * minusProjector X) * B * plusProjector X := by
            simp [gNegOnePart, mul_assoc]
    _ = 0 := by
          rw [plusProjector_mul_minusProjector]
          simp

/--
Circularly polarized `u+` channel is nilpotent under channel multiplication.
-/
@[rep_depth krein]
theorem uPlus_mul_uPlus_eq_zero
    (X : RealSplitCl11Action H) (A B : EndH) :
    uPlus X A * uPlus X B = 0 := by
  simpa [uPlus] using gOnePart_mul_gOnePart_eq_zero (X := X) A B

/--
Circularly polarized `u-` channel is nilpotent under channel multiplication.
-/
@[rep_depth krein]
theorem uMinus_mul_uMinus_eq_zero
    (X : RealSplitCl11Action H) (A B : EndH) :
    uMinus X A * uMinus X B = 0 := by
  simpa [uMinus] using gNegOnePart_mul_gNegOnePart_eq_zero (X := X) A B

@[rep_depth krein] theorem gOnePart_mul_gOnePart_gNegOnePart_eq_zero
    (X : RealSplitCl11Action H) (A B : EndH) :
    gOnePart X (gOnePart X A * gNegOnePart X B) = 0 := by
  unfold gOnePart gNegOnePart
  calc
    plusProjector X * (plusProjector X * A * minusProjector X * (minusProjector X * B * plusProjector X)) *
        minusProjector X
        = plusProjector X * plusProjector X * A * minusProjector X * minusProjector X * B *
            (plusProjector X * minusProjector X) := by
              simp [mul_assoc]
    _ = 0 := by
          rw [plusProjector_mul_minusProjector]
          simp

@[rep_depth krein] theorem gNegOnePart_mul_gOnePart_gNegOnePart_eq_zero
    (X : RealSplitCl11Action H) (A B : EndH) :
    gNegOnePart X (gOnePart X A * gNegOnePart X B) = 0 := by
  unfold gOnePart gNegOnePart
  calc
    minusProjector X * (plusProjector X * A * minusProjector X * (minusProjector X * B * plusProjector X)) *
        plusProjector X
        = (minusProjector X * plusProjector X) * A * minusProjector X * minusProjector X * B *
            plusProjector X * plusProjector X := by
              simp [mul_assoc]
    _ = 0 := by
          rw [minusProjector_mul_plusProjector]
          simp

@[rep_depth krein] theorem plusProjector_mul_eq_mul_plusProjector_of_eps_commute
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : X.eps * A = A * X.eps) :
    plusProjector X * A = A * plusProjector X := by
  apply ContinuousLinearMap.ext
  intro u
  have hcomm : X.eps (A u) = A (X.eps u) := by
    exact congrArg (fun F : EndH => F u) hA
  calc
    plusProjector X (A u)
        = (⅟ (2 : ℝ)) • (A u + X.eps (A u)) := by
            simp [plusProjector]
    _ = (⅟ (2 : ℝ)) • (A u + A (X.eps u)) := by rw [hcomm]
    _ = A (plusProjector X u) := by
          simp [plusProjector, map_add]

@[rep_depth krein] theorem minusProjector_mul_eq_mul_minusProjector_of_eps_commute
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : X.eps * A = A * X.eps) :
    minusProjector X * A = A * minusProjector X := by
  apply ContinuousLinearMap.ext
  intro u
  have hcomm : X.eps (A u) = A (X.eps u) := by
    exact congrArg (fun F : EndH => F u) hA
  calc
    minusProjector X (A u)
        = (⅟ (2 : ℝ)) • (A u - X.eps (A u)) := by
            simp [minusProjector]
    _ = (⅟ (2 : ℝ)) • (A u - A (X.eps u)) := by rw [hcomm]
    _ = A (minusProjector X u) := by
          simp [minusProjector, sub_eq_add_neg, map_add]

@[rep_depth krein] theorem isGZero_of_eps_commute
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : X.eps * A = A * X.eps) :
    IsGZero X A := by
  unfold IsGZero gZeroPart
  rw [plusProjector_mul_eq_mul_plusProjector_of_eps_commute (X := X) hA,
    minusProjector_mul_eq_mul_minusProjector_of_eps_commute (X := X) hA]
  calc
    A * plusProjector X * plusProjector X + A * minusProjector X * minusProjector X
        = A * (plusProjector X * plusProjector X) + A * (minusProjector X * minusProjector X) := by
            simp [mul_assoc]
    _ = A * plusProjector X + A * minusProjector X := by
          rw [plusProjector_idempotent, minusProjector_idempotent]
    _ = A * (plusProjector X + minusProjector X) := by
          rw [mul_add]
    _ = A := by
          rw [plusProjector_add_minusProjector]
          change A.comp (ContinuousLinearMap.id ℝ H) = A
          simp

@[rep_depth krein] theorem plusProjector_mul_eq_mul_minusProjector_of_eps_anticommute
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : X.eps * A = -(A * X.eps)) :
    plusProjector X * A = A * minusProjector X := by
  apply ContinuousLinearMap.ext
  intro u
  have hanti : X.eps (A u) = -A (X.eps u) := by
    exact congrArg (fun F : EndH => F u) hA
  calc
    plusProjector X (A u)
        = (⅟ (2 : ℝ)) • (A u + X.eps (A u)) := by
            simp [plusProjector]
    _ = (⅟ (2 : ℝ)) • (A u - A (X.eps u)) := by
          rw [hanti]
          simp [sub_eq_add_neg]
    _ = A (minusProjector X u) := by
          simp [minusProjector, sub_eq_add_neg, map_add]

@[rep_depth krein] theorem minusProjector_mul_eq_mul_plusProjector_of_eps_anticommute
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : X.eps * A = -(A * X.eps)) :
    minusProjector X * A = A * plusProjector X := by
  apply ContinuousLinearMap.ext
  intro u
  have hanti : X.eps (A u) = -A (X.eps u) := by
    exact congrArg (fun F : EndH => F u) hA
  calc
    minusProjector X (A u)
        = (⅟ (2 : ℝ)) • (A u - X.eps (A u)) := by
            simp [minusProjector]
    _ = (⅟ (2 : ℝ)) • (A u + A (X.eps u)) := by
          rw [hanti]
          simp [sub_eq_add_neg]
    _ = A (plusProjector X u) := by
          simp [plusProjector, map_add]

@[rep_depth krein] theorem isGZero_of_epsConj_eq
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : epsConj X A = A) :
    IsGZero X A := by
  have hcomm : X.eps * A = A * X.eps := by
    apply ContinuousLinearMap.ext
    intro u
    have hBase : X.eps (A (X.eps u)) = A u := by
      simpa [epsConj, mul_assoc] using congrArg (fun F : EndH => F u) hA
    have hApply := congrArg X.eps hBase
    simpa [X.eps_sq_apply, mul_assoc] using hApply.symm
  exact isGZero_of_eps_commute (X := X) hcomm

@[rep_depth krein] theorem gZeroPart_eq_zero_of_epsConj_neg
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : epsConj X A = -A) :
    gZeroPart X A = 0 := by
  have hanti : X.eps * A = -(A * X.eps) := by
    apply ContinuousLinearMap.ext
    intro u
    have hBase : X.eps (A (X.eps u)) = -A u := by
      simpa [epsConj, mul_assoc] using congrArg (fun F : EndH => F u) hA
    have hApply := congrArg X.eps hBase
    have hStep : A (X.eps u) = -(X.eps (A u)) := by
      simpa [X.eps_sq_apply, mul_assoc] using hApply
    have hNeg := congrArg Neg.neg hStep
    simpa using hNeg.symm
  unfold gZeroPart
  rw [plusProjector_mul_eq_mul_minusProjector_of_eps_anticommute (X := X) hanti,
    minusProjector_mul_eq_mul_plusProjector_of_eps_anticommute (X := X) hanti]
  rw [mul_assoc, mul_assoc, plusProjector_mul_minusProjector, minusProjector_mul_plusProjector]
  simp

@[rep_depth krein] theorem gOnePart_add_gNegOnePart_eq_of_epsConj_neg
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : epsConj X A = -A) :
    A = gOnePart X A + gNegOnePart X A := by
  have hDecomp := decompose X A
  rw [gZeroPart_eq_zero_of_epsConj_neg (X := X) hA] at hDecomp
  simpa [add_assoc] using hDecomp

@[rep_depth krein] theorem gOnePart_mul_gNegOnePart_isGZero
    (X : RealSplitCl11Action H) (A B : EndH) :
    IsGZero X (gOnePart X A * gNegOnePart X B) := by
  have hOne : gOnePart X (gOnePart X A * gNegOnePart X B) = 0 :=
    gOnePart_mul_gOnePart_gNegOnePart_eq_zero X A B
  have hNeg : gNegOnePart X (gOnePart X A * gNegOnePart X B) = 0 :=
    gNegOnePart_mul_gOnePart_gNegOnePart_eq_zero X A B
  have hDecomp := decompose X (gOnePart X A * gNegOnePart X B)
  unfold IsGZero
  rw [hOne, hNeg] at hDecomp
  have hEq : gOnePart X A * gNegOnePart X B = gZeroPart X (gOnePart X A * gNegOnePart X B) := by
    simpa [add_assoc] using hDecomp
  exact hEq.symm

@[rep_depth krein] theorem gNegOnePart_mul_gOnePart_isGZero
    (X : RealSplitCl11Action H) (A B : EndH) :
    IsGZero X (gNegOnePart X A * gOnePart X B) := by
  have hOne : gOnePart X (gNegOnePart X A * gOnePart X B) = 0 := by
    unfold gOnePart gNegOnePart
    calc
      plusProjector X * (minusProjector X * A * plusProjector X * (plusProjector X * B * minusProjector X)) *
          minusProjector X
          = (plusProjector X * minusProjector X) * A * plusProjector X * plusProjector X * B *
              minusProjector X * minusProjector X := by
                simp [mul_assoc]
      _ = 0 := by
            rw [plusProjector_mul_minusProjector]
            simp
  have hNeg : gNegOnePart X (gNegOnePart X A * gOnePart X B) = 0 := by
    unfold gOnePart gNegOnePart
    calc
          minusProjector X * (minusProjector X * A * plusProjector X * (plusProjector X * B * minusProjector X)) *
              plusProjector X
          = minusProjector X * minusProjector X * A * plusProjector X * plusProjector X * B *
              (minusProjector X * plusProjector X) := by
                simp [mul_assoc]
      _ = 0 := by
            rw [minusProjector_mul_plusProjector]
            simp
  have hDecomp := decompose X (gNegOnePart X A * gOnePart X B)
  unfold IsGZero
  rw [hOne, hNeg] at hDecomp
  have hEq : gNegOnePart X A * gOnePart X B = gZeroPart X (gNegOnePart X A * gOnePart X B) := by
    simpa [add_assoc] using hDecomp
  exact hEq.symm

@[rep_depth krein] theorem isGZero_sub
    (X : RealSplitCl11Action H) {A B : EndH}
    (hA : IsGZero X A) (hB : IsGZero X B) :
    IsGZero X (A - B) := by
  unfold IsGZero at hA hB ⊢
  have hneg : gZeroPart X (-B) = -B := by
    calc
      gZeroPart X (-B) = (-1 : ℝ) • gZeroPart X B := by
        simpa using gZeroPart_smul X (-1 : ℝ) B
      _ = -B := by rw [hB]; simp
  calc
    gZeroPart X (A - B) = gZeroPart X A + gZeroPart X (-B) := by
      simp [sub_eq_add_neg]
    _ = A + (-B) := by rw [hA, hneg]
    _ = A - B := by simp [sub_eq_add_neg]

@[rep_depth krein] theorem isGZero_add
    (X : RealSplitCl11Action H) {A B : EndH}
    (hA : IsGZero X A) (hB : IsGZero X B) :
    IsGZero X (A + B) := by
  unfold IsGZero at hA hB ⊢
  simp [gZeroPart_add, hA, hB]

@[rep_depth krein] theorem isGZero_smul
    (X : RealSplitCl11Action H) (r : ℝ) {A : EndH}
    (hA : IsGZero X A) :
    IsGZero X (r • A) := by
  unfold IsGZero at *
  simp [hA]

@[rep_depth krein] theorem commutator_gOne_gNegOne_isGZero
    (X : RealSplitCl11Action H) (A B : EndH) :
    IsGZero X (commutator (gOnePart X A) (gNegOnePart X B)) := by
  unfold commutator
  apply isGZero_sub (X := X)
  · exact gOnePart_mul_gNegOnePart_isGZero X A B
  · exact gNegOnePart_mul_gOnePart_isGZero X B A

/--
Circularly polarized commutator closes in the `g₀` channel.
-/
@[rep_depth krein]
theorem commutator_uPlus_uMinus_isGZero
    (X : RealSplitCl11Action H) (A B : EndH) :
    IsGZero X (commutator (uPlus X A) (uMinus X B)) := by
  simpa [uPlus, uMinus] using
    (commutator_gOne_gNegOne_isGZero (X := X) A B)

/--
Symmetry-adapted KKT closure packet:

* positive circular-polarized odd channel is square-zero;
* negative circular-polarized odd channel is square-zero;
* mixed commutator closes in the even (`g₀`) channel.

This is the operator-level closure statement behind the chiral-anomaly
isolation mechanism in the split `TKK/KKT` lane.
-/
@[rep_depth krein]
theorem chiral_polarized_kkt_closure_packet
    (X : RealSplitCl11Action H) (A B : EndH) :
    uPlus X A * uPlus X B = 0 ∧
    uMinus X A * uMinus X B = 0 ∧
    IsGZero X (commutator (uPlus X A) (uMinus X B)) := by
  refine ⟨uPlus_mul_uPlus_eq_zero (X := X) A B, ?_, ?_⟩
  · exact uMinus_mul_uMinus_eq_zero (X := X) A B
  · exact commutator_uPlus_uMinus_isGZero (X := X) A B

/--
Odd-lane anticommutator collapse:
both same-chirality odd anticommutators vanish.
-/
@[rep_depth krein]
theorem chiral_odd_anticommutator_zero
    (X : RealSplitCl11Action H) (A B : EndH) :
    (uPlus X A * uPlus X B + uPlus X B * uPlus X A = 0) ∧
    (uMinus X A * uMinus X B + uMinus X B * uMinus X A = 0) := by
  constructor
  ·
    rw [uPlus_mul_uPlus_eq_zero (X := X) A B, uPlus_mul_uPlus_eq_zero (X := X) B A]
    simp
  ·
    rw [uMinus_mul_uMinus_eq_zero (X := X) A B, uMinus_mul_uMinus_eq_zero (X := X) B A]
    simp

/--
Mixed odd anticommutator closes in the even (`g₀`) lane.
-/
@[rep_depth krein]
theorem anticommutator_uPlus_uMinus_isGZero
    (X : RealSplitCl11Action H) (A B : EndH) :
    IsGZero X (uPlus X A * uMinus X B + uMinus X B * uPlus X A) := by
  apply isGZero_add (X := X)
  · simpa [uPlus, uMinus] using gOnePart_mul_gNegOnePart_isGZero (X := X) A B
  · simpa [uPlus, uMinus] using gNegOnePart_mul_gOnePart_isGZero (X := X) B A

/--
Symmetry-adapted odd/even closure package for the split `TKK/KKT` lane.

It combines:
* same-chirality odd nilpotency;
* mixed odd commutator closure into `g₀`;
* mixed odd anticommutator closure into `g₀`.
-/
@[rep_depth krein]
theorem chiral_superclosure_packet
    (X : RealSplitCl11Action H) (A B : EndH) :
    uPlus X A * uPlus X B = 0 ∧
    uMinus X A * uMinus X B = 0 ∧
    IsGZero X (commutator (uPlus X A) (uMinus X B)) ∧
    IsGZero X (uPlus X A * uMinus X B + uMinus X B * uPlus X A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact uPlus_mul_uPlus_eq_zero (X := X) A B
  · exact uMinus_mul_uMinus_eq_zero (X := X) A B
  · exact commutator_uPlus_uMinus_isGZero (X := X) A B
  · exact anticommutator_uPlus_uMinus_isGZero (X := X) A B

@[rep_depth krein] theorem commutator_isGZero_of_isGOne_of_isGNegOne
    (X : RealSplitCl11Action H) {A B : EndH}
    (hA : IsGOne X A) (hB : IsGNegOne X B) :
    IsGZero X (commutator A B) := by
  rw [← hA, ← hB]
  exact commutator_gOne_gNegOne_isGZero (X := X) A B

@[rep_depth krein] theorem eps_mul_eq_neg_mul_eps_of_isGOne
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : IsGOne X A) :
    X.eps * A = -(A * X.eps) := by
  rw [← hA]
  unfold gOnePart
  calc
    X.eps * (plusProjector X * A * minusProjector X)
        = (X.eps * plusProjector X) * A * minusProjector X := by simp [mul_assoc]
    _ = plusProjector X * A * minusProjector X := by rw [eps_mul_plusProjector]
    _ = -((plusProjector X * A * minusProjector X) * X.eps) := by
          simp [mul_assoc, minusProjector_mul_eps]

@[rep_depth krein] theorem eps_mul_eq_neg_mul_eps_of_isGNegOne
    (X : RealSplitCl11Action H) {A : EndH}
    (hA : IsGNegOne X A) :
    X.eps * A = -(A * X.eps) := by
  rw [← hA]
  unfold gNegOnePart
  calc
    X.eps * (minusProjector X * A * plusProjector X)
        = (X.eps * minusProjector X) * A * plusProjector X := by simp [mul_assoc]
    _ = ((-minusProjector X) * A) * plusProjector X := by rw [eps_mul_minusProjector]
    _ = -(minusProjector X * A * plusProjector X) := by simp [mul_assoc]
    _ = -((minusProjector X * A * plusProjector X) * X.eps) := by
          simp [mul_assoc, plusProjector_mul_eps]

end Core

end KKTCore
