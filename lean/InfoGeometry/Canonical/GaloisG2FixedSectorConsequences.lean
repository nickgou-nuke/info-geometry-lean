/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.AlbertCayleyDickson
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic

/-!
# Algebraic consequences of the owner Zorn symmetries

This file uses the `OpZornMatrix` carrier and its `skewCross` multiplication
from `AlbertCayleyDickson`. It proves an unnormalised additive reconstruction,
the characteristic-sensitive description of a Klein fixed locus, and the
matrix multiplication law for the x-axis sector. It makes no GNS, K-theory,
or classification claim.
-/

universe u

namespace InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion

namespace GaloisG2FixedSectorConsequences

variable {A : Type u} [Ring A]

/-- The three unnormalised sign-symmetry traces. -/
def piX (X : OpZornMatrix A) : OpZornMatrix A := X + zornKleinX X
def piY (X : OpZornMatrix A) : OpZornMatrix A := X + zornKleinY X
def piZ (X : OpZornMatrix A) : OpZornMatrix A := X + zornKleinZ X

/-- The unnormalised four-element average. It is a scaled averaging map, not
an idempotent projector over arbitrary characteristics. -/
def piV₄ (X : OpZornMatrix A) : OpZornMatrix A :=
  X + zornKleinX X + zornKleinY X + zornKleinZ X

/-- The three pairwise sign-trace outputs are fixed by their corresponding
owner symmetries. These identities do not assert that the fixed loci contain
only the indicated axis coordinates. -/
theorem pi_fixed (X : OpZornMatrix A) :
    zornKleinX (piX X) = piX X ∧
    zornKleinY (piY X) = piY X ∧
    zornKleinZ (piZ X) = piZ X := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext <;>
    simp [piX, piY, piZ, zornKleinX, zornGradeParity, zornKleinY,
      zornKleinZ, OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ]

/-- The unnormalised sign traces reconstruct twice the original operator.
No division by 2 or 4 is used. -/
theorem unnormalised_galois_sector_reconstruction (X : OpZornMatrix A) :
    piX X + piY X + piZ X - piV₄ X = X + X := by
  simp only [piX, piY, piZ, piV₄]
  abel

/-- Under additive 2-torsion-freeness, the fixed locus of the x-sign symmetry
is exactly the x-axis coordinate sector. Without this hypothesis, for example
in characteristic two, the equality need not hold. -/
theorem zornKleinX_fixed_iff_of_noTwoTorsion
    (X : OpZornMatrix A)
    (h₂ : ∀ a : A, a + a = 0 → a = 0) :
    zornKleinX X = X ↔
      X.v.y = 0 ∧ X.v.z = 0 ∧ X.w.y = 0 ∧ X.w.z = 0 := by
  constructor
  · intro h
    have hvy : -X.v.y = X.v.y := by
      have h' := congrArg (fun Y : OpZornMatrix A => Y.v.y) h
      simpa [zornKleinX, zornGradeParity, OpVec3.gradeParity] using h'
    have hvz : -X.v.z = X.v.z := by
      have h' := congrArg (fun Y : OpZornMatrix A => Y.v.z) h
      simpa [zornKleinX, zornGradeParity, OpVec3.gradeParity] using h'
    have hwy : -X.w.y = X.w.y := by
      have h' := congrArg (fun Y : OpZornMatrix A => Y.w.y) h
      simpa [zornKleinX, zornGradeParity, OpVec3.gradeParity] using h'
    have hwz : -X.w.z = X.w.z := by
      have h' := congrArg (fun Y : OpZornMatrix A => Y.w.z) h
      simpa [zornKleinX, zornGradeParity, OpVec3.gradeParity] using h'
    have hvy' : X.v.y + X.v.y = 0 := by
      calc
        X.v.y + X.v.y = -X.v.y + X.v.y := (congrArg (fun t : A => t + X.v.y) hvy).symm
        _ = 0 := neg_add_cancel _
    have hvz' : X.v.z + X.v.z = 0 := by
      calc
        X.v.z + X.v.z = -X.v.z + X.v.z := (congrArg (fun t : A => t + X.v.z) hvz).symm
        _ = 0 := neg_add_cancel _
    have hwy' : X.w.y + X.w.y = 0 := by
      calc
        X.w.y + X.w.y = -X.w.y + X.w.y := (congrArg (fun t : A => t + X.w.y) hwy).symm
        _ = 0 := neg_add_cancel _
    have hwz' : X.w.z + X.w.z = 0 := by
      calc
        X.w.z + X.w.z = -X.w.z + X.w.z := (congrArg (fun t : A => t + X.w.z) hwz).symm
        _ = 0 := neg_add_cancel _
    exact ⟨h₂ _ hvy', h₂ _ hvz', h₂ _ hwy', h₂ _ hwz'⟩
  · rintro ⟨hvy, hvz, hwy, hwz⟩
    ext <;>
      simp [zornKleinX, zornGradeParity, OpVec3.gradeParity, hvy, hvz, hwy, hwz]

/-- In characteristic two, negation fixes every coefficient, so the owner
double-sign maps collapse pointwise to the identity. Noncommutativity of the
coefficient ring does not prevent this characteristic obstruction. -/
theorem neg_eq_self_of_two_eq_zero (htwo : (2 : A) = 0) (a : A) : -a = a := by
  apply neg_eq_iff_add_eq_zero.mpr
  calc
    a + a = (2 : A) * a := by noncomm_ring
    _ = 0 := by rw [htwo]; simp

/-- All three owner Klein transformations are the identity in characteristic
two. In particular, the formulas alone do not define a faithful `V₄` action
over every coefficient ring. -/
theorem zornKlein_maps_collapse_of_two_eq_zero (htwo : (2 : A) = 0)
    (X : OpZornMatrix A) :
    zornKleinX X = X ∧ zornKleinY X = X ∧ zornKleinZ X = X := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext <;>
    simp [zornKleinX, zornGradeParity, zornKleinY, zornKleinZ,
      OpVec3.gradeParity, OpVec3.kleinY, OpVec3.kleinZ,
      neg_eq_self_of_two_eq_zero htwo]

/-- The coefficient ring `M₂(ℤ/2)` is noncommutative, witnessed by its two
opposite off-diagonal matrix units. -/
theorem matrixTwoZModTwo_noncommutative :
    ∃ a b : Matrix (Fin 2) (Fin 2) (ZMod 2), a * b ≠ b * a := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  decide

/-- The collapse theorem applies to the actual owner Zorn carrier over the
noncommutative matrix operator ring `M₂(ℤ/2)`. -/
theorem zornKlein_maps_collapse_on_matrix_operator_ring
    (X : OpZornMatrix (Matrix (Fin 2) (Fin 2) (ZMod 2))) :
    zornKleinX X = X ∧ zornKleinY X = X ∧ zornKleinZ X = X := by
  have htwo : (2 : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  exact zornKlein_maps_collapse_of_two_eq_zero htwo X

/-- The owner quartic nucleus extraction is the scaled output `4 • G₀`, not
an unconditionally faithful projector. In the noncommutative matrix
coefficient ring `M₂(ℤ/2)`, it annihilates the nonzero grade-zero element
`opGradeZero 1 0`, because four is zero in characteristic two. -/
theorem quartic_gradeZero_extraction_matrix_counterexample :
    let X : OpZornMatrix (Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
      opGradeZero 1 0
    let D₁ := opEulerFiveGrading X
    let D₂ := opEulerFiveGrading D₁
    let D₃ := opEulerFiveGrading D₂
    let D₄ := opEulerFiveGrading D₃
    X ≠ 0 ∧ D₄ - (D₂ + D₂ + D₂ + D₂ + D₂) + (X + X + X + X) = 0 := by
  intro X D₁ D₂ D₃ D₄
  constructor
  · intro h
    have h₁ := congrArg OpZornMatrix.a h
    have hone : (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) ≠ 0 := by
      intro hz
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 2) => M 0 0) hz
      norm_num at h00
    exact hone (by simpa [X, opGradeZero, opCartanDiag] using h₁)
  · have honeadd :
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) + 1 = 0 := by
      have hadd : (1 : ZMod 2) + 1 = 0 := by decide
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.one_apply, hadd]
      · simp [Matrix.one_apply, hij]
    have hX₂ : X + X = 0 := by
      apply OpZornMatrix.ext
      · simpa [X, opCartanDiag] using honeadd
      · ext <;> simp [X, opCartanDiag]
      · ext <;> simp [X, opCartanDiag]
      · simp [X, opCartanDiag]
    have hX₄ : X + X + X + X = 0 := by
      calc
        X + X + X + X = (X + X) + (X + X) := by abel
        _ = 0 := by rw [hX₂]; simp
    have hD₁ : D₁ = 0 := by
      ext <;> simp [D₁, X, opEulerFiveGrading, opCartanDiag]
    have hD₂ : D₂ = 0 := by
      ext <;> simp [D₂, hD₁, opEulerFiveGrading]
    have hD₃ : D₃ = 0 := by
      ext <;> simp [D₃, hD₂, opEulerFiveGrading]
    have hD₄ : D₄ = 0 := by
      ext <;> simp [D₄, hD₃, opEulerFiveGrading]
    calc
      D₄ - (D₂ + D₂ + D₂ + D₂ + D₂) + (X + X + X + X) = 0 := by
        rw [hD₄, hD₂, hX₄]
        simp

/-- The quartic Euler polynomial detects a zero grade-zero component exactly
when the coefficient ring has no additive 4-torsion. The owner polynomial
identity gives four copies of `opGradeZero X.a X.b`; the hypothesis is used
only to recover the component from that multiple. -/
theorem quartic_gradeZero_extraction_zero_iff_of_noFourTorsion
    (X : OpZornMatrix A)
    (h₄ : ∀ a : A, a + a + a + a = 0 → a = 0) :
    let D₁ := opEulerFiveGrading X
    let D₂ := opEulerFiveGrading D₁
    let D₃ := opEulerFiveGrading D₂
    let D₄ := opEulerFiveGrading D₃
    D₄ - (D₂ + D₂ + D₂ + D₂ + D₂) + (X + X + X + X) = 0 ↔
      X.a = 0 ∧ X.b = 0 := by
  intro D₁ D₂ D₃ D₄
  constructor
  · intro h
    have hspec := fiveGraded_operator_characteristic_polynomial_and_spectral_projectors X
    rcases hspec with ⟨_, hextract, _, _, _⟩
    rw [hextract] at h
    have ha₄ : X.a + X.a + X.a + X.a = 0 := by
      have hcoord := congrArg OpZornMatrix.a h
      simpa [opGradeZero, opCartanDiag] using hcoord
    have hb₄ : X.b + X.b + X.b + X.b = 0 := by
      have hcoord := congrArg OpZornMatrix.b h
      simpa [opGradeZero, opCartanDiag] using hcoord
    exact ⟨h₄ X.a ha₄, h₄ X.b hb₄⟩
  · rintro ⟨ha, hb⟩
    have hspec := fiveGraded_operator_characteristic_polynomial_and_spectral_projectors X
    rcases hspec with ⟨_, hextract, _, _, _⟩
    have hgrade : opGradeZero X.a X.b = 0 := by
      ext <;> simp [opGradeZero, opCartanDiag, ha, hb]
    rw [hextract, hgrade]
    simp

/-- The owner x-axis sector has an explicit faithful matrix encoding. The
minus sign in the upper-right entry is forced by the owner Zorn product. -/
def axisXMatrix (a v w b : A) : Matrix (Fin 2) (Fin 2) A :=
  !![a, -v; w, b]

/-- The inverse coordinate map for `axisXMatrix`. -/
def axisXCoordinates (M : Matrix (Fin 2) (Fin 2) A) : OpZornMatrix A :=
  quatSubalgX (M 0 0) (-M 0 1) (M 1 0) (M 1 1)

@[simp] theorem axisXCoordinates_matrix (a v w b : A) :
    axisXCoordinates (axisXMatrix a v w b) = quatSubalgX a v w b := by
  ext <;> simp [axisXCoordinates, axisXMatrix, quatSubalgX]

@[simp] theorem axisXMatrix_coordinates (M : Matrix (Fin 2) (Fin 2) A) :
    axisXMatrix (axisXCoordinates M).a (OpVec3.x (axisXCoordinates M).v)
      (OpVec3.x (axisXCoordinates M).w) (axisXCoordinates M).b = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisXCoordinates, axisXMatrix, quatSubalgX]

/-- Multiplication on the owner x-axis sector is transported exactly to
ordinary multiplication in `M₂(A)` by the sign-correct encoding. -/
theorem axisXMatrix_mul (a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ : A) :
    axisXMatrix
      (quatSubalgX a₁ v₁ w₁ b₁ * quatSubalgX a₂ v₂ w₂ b₂).a
      (OpVec3.x (quatSubalgX a₁ v₁ w₁ b₁ * quatSubalgX a₂ v₂ w₂ b₂).v)
      (OpVec3.x (quatSubalgX a₁ v₁ w₁ b₁ * quatSubalgX a₂ v₂ w₂ b₂).w)
      (quatSubalgX a₁ v₁ w₁ b₁ * quatSubalgX a₂ v₂ w₂ b₂).b =
    axisXMatrix a₁ v₁ w₁ b₁ * axisXMatrix a₂ v₂ w₂ b₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisXMatrix, quatSubalgX, Matrix.mul_apply, Fin.sum_univ_succ,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    abel

/-- The channel carrier is the subtype of owner Zorn matrices whose off-axis
coordinates vanish. It is intentionally not identified with the entire
`zornKleinX` fixed locus unless additive 2-torsion is absent. -/
def IsKleinXChannel (X : OpZornMatrix A) : Prop :=
  X.v.y = 0 ∧ X.v.z = 0 ∧ X.w.y = 0 ∧ X.w.z = 0

abbrev KleinXChannel := {X : OpZornMatrix A // IsKleinXChannel X}

def channelToMatrix (X : KleinXChannel (A := A)) : Matrix (Fin 2) (Fin 2) A :=
  axisXMatrix X.val.a X.val.v.x X.val.w.x X.val.b

def matrixToChannel (M : Matrix (Fin 2) (Fin 2) A) : KleinXChannel (A := A) :=
  ⟨axisXCoordinates M, by simp [axisXCoordinates, quatSubalgX, IsKleinXChannel]⟩

/-- The x-channel coordinates are bijective with matrices, using the sign
forced by the canonical owner product. -/
def channelEquivMatrix : KleinXChannel (A := A) ≃ Matrix (Fin 2) (Fin 2) A where
  toFun := channelToMatrix
  invFun := matrixToChannel
  left_inv X := by
    apply Subtype.ext
    have hX : X.val = quatSubalgX X.val.a X.val.v.x X.val.w.x X.val.b := by
      rcases X.prop with ⟨hvy, hvz, hwy, hwz⟩
      ext <;> simp [quatSubalgX, hvy, hvz, hwy, hwz]
    change axisXCoordinates (axisXMatrix X.val.a X.val.v.x X.val.w.x X.val.b) = X.val
    rw [axisXCoordinates_matrix]
    exact hX.symm
  right_inv M := axisXMatrix_coordinates M

/- The subtype ring is transported once, at namespace scope, so the operations
used by downstream theorems are available while their types are elaborated. -/
noncomputable instance channelRing : Ring (KleinXChannel (A := A)) :=
  Equiv.ring (channelEquivMatrix (A := A))

/-- Ring equivalence to matrices. The transported product is checked against
the owner product by `channel_mul_val_eq_owner` below. -/
noncomputable def channelRingEquivMatrix :
    KleinXChannel (A := A) ≃+* Matrix (Fin 2) (Fin 2) A :=
  Equiv.ringEquiv (channelEquivMatrix (A := A))

/-- The coordinate channel is closed under the actual owner Zorn product. -/
theorem isKleinXChannel_mul {X Y : OpZornMatrix A}
    (hX : IsKleinXChannel X) (hY : IsKleinXChannel Y) :
    IsKleinXChannel (X * Y) := by
  rcases hX with ⟨hx₁, hx₂, hx₃, hx₄⟩
  rcases hY with ⟨hy₁, hy₂, hy₃, hy₄⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [OpZornMatrix.mul_v, OpZornMatrix.mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale, hx₁, hx₂, hx₃, hx₄,
      hy₁, hy₂, hy₃, hy₄]

/-- The subtype element represented by the ambient product of two channels. -/
def ownerMulChannel (X Y : KleinXChannel (A := A)) : KleinXChannel (A := A) :=
  ⟨X.val * Y.val, isKleinXChannel_mul X.property Y.property⟩

/-- The matrix coordinates of `ownerMulChannel` are the ordinary matrix
product, for arbitrary noncommutative coefficient ring `A`. -/
theorem channelToMatrix_ownerMul (X Y : KleinXChannel (A := A)) :
    channelToMatrix (ownerMulChannel X Y) = channelToMatrix X * channelToMatrix Y := by
  have hX : X.val = quatSubalgX X.val.a X.val.v.x X.val.w.x X.val.b := by
    rcases X.property with ⟨hvy, hvz, hwy, hwz⟩
    ext <;> simp [quatSubalgX, hvy, hvz, hwy, hwz]
  have hY : Y.val = quatSubalgX Y.val.a Y.val.v.x Y.val.w.x Y.val.b := by
    rcases Y.property with ⟨hvy, hvz, hwy, hwz⟩
    ext <;> simp [quatSubalgX, hvy, hvz, hwy, hwz]
  change axisXMatrix (X.val * Y.val).a (OpVec3.x (X.val * Y.val).v)
      (OpVec3.x (X.val * Y.val).w) (X.val * Y.val).b =
    axisXMatrix X.val.a X.val.v.x X.val.w.x X.val.b *
      axisXMatrix Y.val.a Y.val.v.x Y.val.w.x Y.val.b
  rw [hX, hY]
  exact axisXMatrix_mul _ _ _ _ _ _ _ _

/-- Multiplication in the transported subtype ring agrees with the actual
ambient Zorn product. Thus the ring equivalence is an isomorphism of the
associative owner channel, not merely a transported ring on the same carrier. -/
theorem channel_mul_val_eq_owner (X Y : KleinXChannel (A := A)) :
    (X * Y).val = X.val * Y.val := by
  have hsub : X * Y = ownerMulChannel X Y := by
    apply (channelRingEquivMatrix (A := A)).injective
    calc
      channelRingEquivMatrix (X * Y) =
          channelRingEquivMatrix X * channelRingEquivMatrix Y :=
        (channelRingEquivMatrix (A := A)).map_mul X Y
      _ = channelRingEquivMatrix (ownerMulChannel X Y) := by
        change channelToMatrix X * channelToMatrix Y = channelToMatrix (ownerMulChannel X Y)
        exact (channelToMatrix_ownerMul X Y).symm
  exact congrArg Subtype.val hsub

/-- The owner already proves strict associativity on all three axis sectors
and on the triality-fixed singlet sector; this theorem records the scope of
the x-axis instance using that proof. -/
theorem axisX_associator_zero
    (a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ a₃ v₃ w₃ b₃ : A) :
    opAssociator (quatSubalgX a₁ v₁ w₁ b₁)
      (quatSubalgX a₂ v₂ w₂ b₂) (quatSubalgX a₃ v₃ w₃ b₃) = 0 := by
  have h := three_quaternion_galois_subalgebras_and_riccati_axis_decoupling
    a₁ v₁ w₁ b₁ a₂ v₂ w₂ b₂ a₃ v₃ w₃ b₃ 0 0 0 0 0 0 0 0 0 0 0
  exact h.2.2.2.1

end GaloisG2FixedSectorConsequences

end InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
