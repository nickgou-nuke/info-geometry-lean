/-
InfoGeometry/Optics/FiniteJonesBregman.lean

Constructive finite Bregman heat for Jones/Stinespring channels.

This module eliminates the vague statement:

  "optical heat is Bregman divergence"

in the finite Jones branch.

For the first concrete finite model, the potential is the Frobenius quadratic
potential

  Phi(X) = 1/2 ||X||_F^2

on `2 x 2` Jones matrices, with real Frobenius pairing

  <X,Y>_F = sum_ij Re(X_ij)Re(Y_ij) + Im(X_ij)Im(Y_ij).

The Bregman divergence is proved constructively to be

  DPhi(X,Y) = 1/2 ||X-Y||_F^2 >= 0.

Combined with finite Stinespring accounting,

  I - R^dagger R = V^dagger V,

this gives a proved finite heat readout:

  Heat = DPhi(I-R^dagger R,0) = DPhi(V^dagger V,0).
-/

import Mathlib.Tactic
import InfoGeometry.Optics.FiniteJonesStinespring

noncomputable section

namespace InfoGeometry.Optics.FiniteJonesBregman

open InfoGeometry.Optics.FiniteJonesModel
open InfoGeometry.Optics.FiniteJonesStinespring

/-! ## 1. Constructive Frobenius pairing -/

/--
Real inner product on one complex scalar, written constructively.

This avoids relying on a global Hilbert-Schmidt API.
-/
def complexRealInner
    (z w : ℂ) : ℝ :=
  z.re * w.re + z.im * w.im

/--
Squared complex magnitude, written constructively.
-/
def complexSqNorm
    (z : ℂ) : ℝ :=
  complexRealInner z z

/--
Nonnegativity of the squared complex magnitude.
-/
theorem complexSqNorm_nonneg
    (z : ℂ) :
    0 ≤ complexSqNorm z := by
  dsimp [complexSqNorm, complexRealInner]
  exact add_nonneg (mul_self_nonneg z.re) (mul_self_nonneg z.im)

/--
Finite Frobenius real pairing on Jones matrices.
-/
def frobeniusInner
    (X Y : JonesMat) : ℝ :=
  Finset.univ.sum fun i : Fin 2 =>
    Finset.univ.sum fun j : Fin 2 =>
      complexRealInner (X i j) (Y i j)

/--
Finite Frobenius square norm.
-/
def frobeniusSq
    (X : JonesMat) : ℝ :=
  frobeniusInner X X

/--
The Frobenius square norm is nonnegative.
-/
theorem frobeniusSq_nonneg
    (X : JonesMat) :
    0 ≤ frobeniusSq X := by
  dsimp [frobeniusSq, frobeniusInner]
  apply Finset.sum_nonneg
  intro i _hi
  apply Finset.sum_nonneg
  intro j _hj
  exact complexSqNorm_nonneg (X i j)

/-! ## 2. Quadratic potential and Bregman divergence -/

/--
Quadratic Frobenius potential:

`Phi(X) = 1/2 ||X||_F^2`.
-/
def frobeniusPotential
    (X : JonesMat) : ℝ :=
  (1 / 2 : ℝ) * frobeniusSq X

/--
The gradient of `Phi(X)=1/2||X||^2` at `Y`, represented as the linear readout
`Z |-> <Y,Z>`.

This is not a differentiability theorem; it is the finite quadratic gradient
readout used in the Bregman formula.
-/
def frobeniusGradientAt
    (Y : JonesMat) : JonesMat → ℝ :=
  fun Z => frobeniusInner Y Z

/--
Raw Bregman divergence from the potential and gradient readout:

`DPhi(X,Y)=Phi(X)-Phi(Y)-<Y,X-Y>`.
-/
def frobeniusBregmanRaw
    (X Y : JonesMat) : ℝ :=
  frobeniusPotential X -
    frobeniusPotential Y -
      frobeniusGradientAt Y (X - Y)

/--
Closed-form quadratic Bregman divergence:

`DPhi(X,Y)=1/2||X-Y||_F^2`.
-/
def frobeniusBregman
    (X Y : JonesMat) : ℝ :=
  (1 / 2 : ℝ) * frobeniusSq (X - Y)

/--
Constructive algebraic reduction of the raw Bregman formula to the closed
quadratic form.
-/
theorem frobeniusBregmanRaw_eq_frobeniusBregman
    (X Y : JonesMat) :
    frobeniusBregmanRaw X Y =
      frobeniusBregman X Y := by
  simp [
    frobeniusBregmanRaw,
    frobeniusBregman,
    frobeniusPotential,
    frobeniusGradientAt,
    frobeniusSq,
    frobeniusInner,
    complexRealInner,
    Fin.sum_univ_two
  ]
  ring

/--
The finite Frobenius Bregman divergence is nonnegative.
-/
theorem frobeniusBregman_nonneg
    (X Y : JonesMat) :
    0 ≤ frobeniusBregman X Y := by
  dsimp [frobeniusBregman]
  exact mul_nonneg (by norm_num) (frobeniusSq_nonneg (X - Y))

/--
Self-divergence vanishes.
-/
@[simp]
theorem frobeniusBregman_self
    (X : JonesMat) :
    frobeniusBregman X X = 0 := by
  simp [
    frobeniusBregman,
    frobeniusSq,
    frobeniusInner,
    complexRealInner
  ]

/--
If two Jones states agree, their Frobenius Bregman divergence vanishes.
-/
theorem frobeniusBregman_eq_zero_of_eq
    {X Y : JonesMat}
    (h : X = Y) :
    frobeniusBregman X Y = 0 := by
  rw [h]
  simp

/--
Distance-to-zero form.
-/
theorem frobeniusBregman_to_zero
    (X : JonesMat) :
    frobeniusBregman X 0 =
      frobeniusPotential X := by
  simp [
    frobeniusBregman,
    frobeniusPotential,
    frobeniusSq,
    frobeniusInner,
    complexRealInner
  ]

/-! ## 3. Finite Jones heat from Stinespring defect -/

/--
Finite Stinespring heat readout.

Heat is the Bregman distance from the visible optical defect to the zero-defect
state:

`Heat = DPhi(I - R^dagger R, 0)`.
-/
def finiteStinespringHeat
    (S : StinespringIsometry JonesMat) : ℝ :=
  frobeniusBregman (opticalDefect S.R) 0

/--
Finite Stinespring heat is nonnegative.
-/
theorem finiteStinespringHeat_nonneg
    (S : StinespringIsometry JonesMat) :
    0 ≤ finiteStinespringHeat S :=
  frobeniusBregman_nonneg _ _

/--
If the hidden environment channel is zero, the finite heat vanishes.
-/
theorem finiteStinespringHeat_eq_zero_of_environment_zero
    (S : StinespringIsometry JonesMat)
    (hV : S.V = 0) :
    finiteStinespringHeat S = 0 := by
  dsimp [finiteStinespringHeat]
  rw [S.defect_eq_zero_of_hidden_zero hV]
  simp

/--
The finite Stinespring heat can be computed from the hidden environment gain:

`Heat = DPhi(V^dagger V,0)`.
-/
theorem finiteStinespringHeat_eq_hiddenGainBregman
    (S : StinespringIsometry JonesMat) :
    finiteStinespringHeat S =
      frobeniusBregman (star S.V * S.V) 0 := by
  dsimp [finiteStinespringHeat]
  rw [S.defect_eq_hiddenGain]
  dsimp [hiddenGain]

/--
Equivalent potential form of the hidden-gain heat readout.
-/
theorem finiteStinespringHeat_eq_hiddenGainPotential
    (S : StinespringIsometry JonesMat) :
    finiteStinespringHeat S =
      frobeniusPotential (star S.V * S.V) := by
  rw [finiteStinespringHeat_eq_hiddenGainBregman]
  exact frobeniusBregman_to_zero _

/-! ## 4. Diagonal finite Jones channel version -/

/--
Heat readout for a diagonal finite Jones channel.

Visible channel:

`R = diag(r_s,r_p)`.

Hidden coupling:

`V = diag(v_s,v_p)`.
-/
def diagonalJonesHeat
    (r_s r_p v_s v_p : ℂ)
    (h_s : star r_s * r_s + star v_s * v_s = 1)
    (h_p : star r_p * r_p + star v_p * v_p = 1) : ℝ :=
  finiteStinespringHeat
    (diagonalStinespringIsometry r_s r_p v_s v_p h_s h_p)

/--
Diagonal heat is nonnegative.
-/
theorem diagonalJonesHeat_nonneg
    (r_s r_p v_s v_p : ℂ)
    (h_s : star r_s * r_s + star v_s * v_s = 1)
    (h_p : star r_p * r_p + star v_p * v_p = 1) :
    0 ≤ diagonalJonesHeat r_s r_p v_s v_p h_s h_p :=
  finiteStinespringHeat_nonneg
    (diagonalStinespringIsometry r_s r_p v_s v_p h_s h_p)

/--
Diagonal heat can be computed from the hidden diagonal environment gain.
-/
theorem diagonalJonesHeat_eq_hiddenGainBregman
    (r_s r_p v_s v_p : ℂ)
    (h_s : star r_s * r_s + star v_s * v_s = 1)
    (h_p : star r_p * r_p + star v_p * v_p = 1) :
    diagonalJonesHeat r_s r_p v_s v_p h_s h_p =
      frobeniusBregman
        (star (diagJones v_s v_p) * diagJones v_s v_p)
        0 := by
  dsimp [diagonalJonesHeat]
  exact
    finiteStinespringHeat_eq_hiddenGainBregman
      (diagonalStinespringIsometry r_s r_p v_s v_p h_s h_p)

/--
Diagonal heat can be computed as the potential of hidden gain.
-/
theorem diagonalJonesHeat_eq_hiddenGainPotential
    (r_s r_p v_s v_p : ℂ)
    (h_s : star r_s * r_s + star v_s * v_s = 1)
    (h_p : star r_p * r_p + star v_p * v_p = 1) :
    diagonalJonesHeat r_s r_p v_s v_p h_s h_p =
      frobeniusPotential
        (star (diagJones v_s v_p) * diagJones v_s v_p) := by
  rw [diagonalJonesHeat_eq_hiddenGainBregman]
  exact frobeniusBregman_to_zero _

end InfoGeometry.Optics.FiniteJonesBregman
