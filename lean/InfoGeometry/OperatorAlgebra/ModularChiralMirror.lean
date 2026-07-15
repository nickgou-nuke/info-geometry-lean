/-
InfoGeometry/OperatorAlgebra/ModularChiralMirror.lean

Modular mirroring of chiral charge.

Tomita modular conjugation supplies a mirror between an algebra and its
commutant.  Whether that mirror preserves or reverses chirality is additional
sign data.  This module records the chirality-flipping case:

  J * chi = - chi * J.

When `J² = 1`, the mirror swaps the half-projectors

  P_L = (1 + chi) / 2,    P_R = (1 - chi) / 2.

This is a bridge datum, not a global theorem about every modular conjugation.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.ChiralPolarization
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ModularChiralMirror

/-! ## 1. Chiral half-projectors -/

/--
The left chiral half-projector associated to a grading `chi`.

This is the algebraic formula `(1 + chi) / 2`.  Idempotence is intentionally
not assumed here; it follows in concrete settings from `chi² = 1`.
-/
def leftChiralProjector
    (Op : Type*) [Ring Op] [Algebra ℝ Op]
    (chi : Op) : Op :=
  (1 / 2 : ℝ) • ((1 : Op) + chi)

/--
The right chiral half-projector associated to a grading `chi`.

This is the algebraic formula `(1 - chi) / 2`.
-/
def rightChiralProjector
    (Op : Type*) [Ring Op] [Algebra ℝ Op]
    (chi : Op) : Op :=
  (1 / 2 : ℝ) • ((1 : Op) - chi)

/-! ## 2. Modular mirror sign datum -/

/--
A low-level modular mirror sign witness for fixed operators `J` and `chi`.

This is the pure sign relation.  It does not require scalar structure or
projectors; those enter in `ModularChiralMirrorDatum`.
-/
structure ModularChiralMirrorSign
    (Op : Type*) [Monoid Op] [Neg Op]
    (J chi : Op) where
  /-- `J² = 1`. -/
  J_square :
    J * J = 1

  /-- `chi² = 1`. -/
  chi_square :
    chi * chi = 1

  /-- Chirality-flipping sign relation. -/
  J_flips_chi :
    J * chi = -(chi * J)

namespace ModularChiralMirrorSign

variable {Op : Type*} [Monoid Op] [Neg Op]
variable {J chi : Op}

/-- Re-export the chirality-flipping relation. -/
theorem anticomm
    (S : ModularChiralMirrorSign Op J chi) :
    J * chi = -(chi * J) :=
  S.J_flips_chi

end ModularChiralMirrorSign

/--
A modular mirror flips chirality if it anticommutes with the chiral grading.

The field `J_square` models the common involutive case `J² = 1`.  The field
`chi_square` records that `chi` is a grading.  The swap theorems below use the
anticommutation law; the conjugation theorems additionally use `J_square`.
-/
structure ModularChiralMirrorDatum
    (Op : Type*) [Ring Op] [Algebra ℝ Op] where
  /-- Modular mirror / CPT reflection. -/
  J : Op

  /-- Chiral grading. -/
  chi : Op

  /-- `J² = 1`. -/
  J_square :
    J * J = 1

  /-- `chi² = 1`. -/
  chi_square :
    chi * chi = 1

  /-- Chirality-flipping sign relation. -/
  J_flips_chi :
    J * chi = -(chi * J)

namespace ModularChiralMirrorDatum

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]
variable (M : ModularChiralMirrorDatum Op)

/-- The left chiral projector of the datum. -/
def P_left : Op :=
  leftChiralProjector Op M.chi

/-- The right chiral projector of the datum. -/
def P_right : Op :=
  rightChiralProjector Op M.chi

/-- The underlying low-level sign witness. -/
def sign : ModularChiralMirrorSign Op M.J M.chi where
  J_square := M.J_square
  chi_square := M.chi_square
  J_flips_chi := M.J_flips_chi

/-- Re-export the chirality-flipping relation. -/
theorem J_chi_anticomm :
    M.J * M.chi = -(M.chi * M.J) :=
  M.J_flips_chi

/-- The opposite anticommutation relation. -/
theorem chi_J_anticomm :
    M.chi * M.J = -(M.J * M.chi) := by
  rw [M.J_chi_anticomm]
  simp

/--
The mirror sends the left numerator to the right numerator:

`J(1 + χ) = (1 - χ)J`.
-/
theorem J_mul_one_add_chi :
    M.J * ((1 : Op) + M.chi) =
      ((1 : Op) - M.chi) * M.J := by
  calc
    M.J * ((1 : Op) + M.chi)
        = M.J * 1 + M.J * M.chi := by
            rw [mul_add]
    _ = M.J + M.J * M.chi := by
            rw [mul_one]
    _ = M.J + -(M.chi * M.J) := by
            rw [M.J_chi_anticomm]
    _ = M.J - M.chi * M.J := by
            simp [sub_eq_add_neg]
    _ = (1 : Op) * M.J - M.chi * M.J := by
            rw [one_mul]
    _ = ((1 : Op) - M.chi) * M.J := by
            rw [sub_mul]

/--
The mirror sends the right numerator to the left numerator:

`J(1 - χ) = (1 + χ)J`.
-/
theorem J_mul_one_sub_chi :
    M.J * ((1 : Op) - M.chi) =
      ((1 : Op) + M.chi) * M.J := by
  calc
    M.J * ((1 : Op) - M.chi)
        = M.J * 1 - M.J * M.chi := by
            rw [mul_sub]
    _ = M.J - M.J * M.chi := by
            rw [mul_one]
    _ = M.J - (-(M.chi * M.J)) := by
            rw [M.J_chi_anticomm]
    _ = M.J + M.chi * M.J := by
            simp
    _ = (1 : Op) * M.J + M.chi * M.J := by
            rw [one_mul]
    _ = ((1 : Op) + M.chi) * M.J := by
            rw [add_mul]

/--
The modular mirror sends the left projector through to the right projector:

`J * P_L = P_R * J`.
-/
theorem J_mul_P_left_eq_P_right_mul_J :
    M.J * M.P_left = M.P_right * M.J := by
  calc
    M.J * M.P_left
        = (1 / 2 : ℝ) • (M.J * ((1 : Op) + M.chi)) := by
            rw [P_left, leftChiralProjector]
            exact mul_smul_comm (1 / 2 : ℝ) M.J ((1 : Op) + M.chi)
    _ = (1 / 2 : ℝ) • (M.J + M.J * M.chi) := by
            rw [mul_add, mul_one]
    _ = (1 / 2 : ℝ) • (M.J - M.chi * M.J) := by
            rw [M.J_chi_anticomm]
            simp [sub_eq_add_neg]
    _ = (1 / 2 : ℝ) • (((1 : Op) - M.chi) * M.J) := by
            rw [sub_mul, one_mul]
    _ = M.P_right * M.J := by
            rw [P_right, rightChiralProjector]
            exact (smul_mul_assoc (1 / 2 : ℝ) ((1 : Op) - M.chi) M.J).symm

/--
The modular mirror sends the left projector to the right projector:

`J P_L = P_R J`.
-/
theorem J_mul_P_left :
    M.J * M.P_left = M.P_right * M.J :=
  M.J_mul_P_left_eq_P_right_mul_J

/--
The modular mirror sends the right projector through to the left projector:

`J * P_R = P_L * J`.
-/
theorem J_mul_P_right_eq_P_left_mul_J :
    M.J * M.P_right = M.P_left * M.J := by
  calc
    M.J * M.P_right
        = (1 / 2 : ℝ) • (M.J * ((1 : Op) - M.chi)) := by
            rw [P_right, rightChiralProjector]
            exact mul_smul_comm (1 / 2 : ℝ) M.J ((1 : Op) - M.chi)
    _ = (1 / 2 : ℝ) • (M.J - M.J * M.chi) := by
            rw [mul_sub, mul_one]
    _ = (1 / 2 : ℝ) • (M.J + M.chi * M.J) := by
            rw [M.J_chi_anticomm]
            simp [sub_eq_add_neg]
    _ = (1 / 2 : ℝ) • (((1 : Op) + M.chi) * M.J) := by
            rw [add_mul, one_mul]
    _ = M.P_left * M.J := by
            rw [P_left, leftChiralProjector]
            exact (smul_mul_assoc (1 / 2 : ℝ) ((1 : Op) + M.chi) M.J).symm

/--
The modular mirror sends the right projector to the left projector:

`J P_R = P_L J`.
-/
theorem J_mul_P_right :
    M.J * M.P_right = M.P_left * M.J :=
  M.J_mul_P_right_eq_P_left_mul_J

/--
Conjugating the left projector by an involutive mirror gives the right
projector.
-/
theorem J_conj_P_left :
    M.J * M.P_left * M.J = M.P_right := by
  calc
    M.J * M.P_left * M.J
        = (M.P_right * M.J) * M.J := by
            rw [M.J_mul_P_left_eq_P_right_mul_J]
    _ = M.P_right * (M.J * M.J) := by
            rw [mul_assoc]
    _ = M.P_right := by
            rw [M.J_square, mul_one]

/--
Conjugating the right projector by an involutive mirror gives the left
projector.
-/
theorem J_conj_P_right :
    M.J * M.P_right * M.J = M.P_left := by
  calc
    M.J * M.P_right * M.J
        = (M.P_left * M.J) * M.J := by
            rw [M.J_mul_P_right_eq_P_left_mul_J]
    _ = M.P_left * (M.J * M.J) := by
            rw [mul_assoc]
    _ = M.P_left := by
            rw [M.J_square, mul_one]

/--
The modular mirror conjugates chiral charge to its negative.
-/
theorem J_conj_chi :
    M.J * M.chi * M.J = -M.chi := by
  calc
    M.J * M.chi * M.J
        = (-(M.chi * M.J)) * M.J := by
            rw [M.J_chi_anticomm]
    _ = -(M.chi * (M.J * M.J)) := by
            rw [neg_mul, mul_assoc]
    _ = -M.chi := by
            rw [M.J_square, mul_one]

/--
Conjugation by `J` flips the chiral grading:

`J χ J = -χ`.
-/
theorem J_mul_chi_mul_J_eq_neg_chi :
    M.J * M.chi * M.J = -M.chi :=
  M.J_conj_chi

end ModularChiralMirrorDatum

/-! ## 3. Real-linear representation-level mirror datum -/

namespace Linear

/--
A real-linear modular mirror flips chirality if it anticommutes with the
chiral grading.

This is the unbounded-free algebraic representation layer: no topology or
continuity is required, and composition is explicit through `LinearMap.comp`.
-/
structure LinearDatum
    (X : Type*) [AddCommGroup X] [Module ℝ X] where
  /-- Modular mirror / real structure. -/
  J : X →ₗ[ℝ] X

  /-- Chiral grading. -/
  chi : X →ₗ[ℝ] X

  /-- `J² = 1`. -/
  J_square :
    J.comp J = LinearMap.id

  /-- `χ² = 1`. -/
  chi_square :
    chi.comp chi = LinearMap.id

  /-- `Jχ = -χJ`: the mirror flips chirality. -/
  J_flips_chi :
    J.comp chi = -(chi.comp J)

namespace LinearDatum

variable
    {X : Type*} [AddCommGroup X] [Module ℝ X]

variable (M : LinearDatum X)

/-- Pointwise form of `J² = 1`. -/
theorem J_square_apply
    (x : X) :
    M.J (M.J x) = x := by
  have h := congrArg (fun T : X →ₗ[ℝ] X => T x) M.J_square
  simpa [LinearMap.comp_apply] using h

/-- Pointwise form of `χ² = 1`. -/
theorem chi_square_apply
    (x : X) :
    M.chi (M.chi x) = x := by
  have h := congrArg (fun T : X →ₗ[ℝ] X => T x) M.chi_square
  simpa [LinearMap.comp_apply] using h

/-- Pointwise form of `Jχ = -χJ`. -/
theorem J_chi_apply
    (x : X) :
    M.J (M.chi x) = -M.chi (M.J x) := by
  have h := congrArg (fun T : X →ₗ[ℝ] X => T x) M.J_flips_chi
  simpa [LinearMap.comp_apply] using h

/-- Equivalent pointwise form `χJ = -Jχ`. -/
theorem chi_J_apply
    (x : X) :
    M.chi (M.J x) = -M.J (M.chi x) := by
  rw [M.J_chi_apply x]
  simp

/-- Left chiral projector, `(1 + χ) / 2`. -/
def P_left : X →ₗ[ℝ] X :=
  (1 / 2 : ℝ) • ((LinearMap.id : X →ₗ[ℝ] X) + M.chi)

/-- Right chiral projector, `(1 - χ) / 2`. -/
def P_right : X →ₗ[ℝ] X :=
  (1 / 2 : ℝ) • ((LinearMap.id : X →ₗ[ℝ] X) - M.chi)

/--
The modular mirror sends the left projector to the right projector:

`J ∘ P_left = P_right ∘ J`.
-/
theorem J_comp_P_left :
    M.J.comp M.P_left = M.P_right.comp M.J := by
  ext x
  simp [P_left, P_right, M.J_chi_apply, sub_eq_add_neg]

/--
The modular mirror sends the right projector to the left projector:

`J ∘ P_right = P_left ∘ J`.
-/
theorem J_comp_P_right :
    M.J.comp M.P_right = M.P_left.comp M.J := by
  ext x
  simp [P_left, P_right, M.J_chi_apply, sub_eq_add_neg]

/--
Conjugation by the modular mirror sends the left projector to the right
projector.
-/
theorem J_conj_P_left :
    (M.J.comp M.P_left).comp M.J = M.P_right := by
  ext x
  have h := congrArg (fun T : X →ₗ[ℝ] X => T (M.J x)) M.J_comp_P_left
  simpa [LinearMap.comp_apply, M.J_square_apply] using h

/--
Conjugation by the modular mirror sends the right projector to the left
projector.
-/
theorem J_conj_P_right :
    (M.J.comp M.P_right).comp M.J = M.P_left := by
  ext x
  have h := congrArg (fun T : X →ₗ[ℝ] X => T (M.J x)) M.J_comp_P_right
  simpa [LinearMap.comp_apply, M.J_square_apply] using h

/-- A vector is left-supported when `P_left x = x`. -/
def IsLeftSupported
    (x : X) : Prop :=
  M.P_left x = x

/-- A vector is right-supported when `P_right x = x`. -/
def IsRightSupported
    (x : X) : Prop :=
  M.P_right x = x

/--
The modular mirror sends left-supported vectors to right-supported vectors.
-/
theorem mirror_left_supported
    (x : X)
    (hx : M.IsLeftSupported x) :
    M.IsRightSupported (M.J x) := by
  dsimp [IsLeftSupported, IsRightSupported] at hx ⊢
  have h := congrArg (fun y : X => M.J y) hx
  have hswap := congrArg (fun T : X →ₗ[ℝ] X => T x) M.J_comp_P_left
  simpa [LinearMap.comp_apply] using hswap.symm.trans h

/--
The modular mirror sends right-supported vectors to left-supported vectors.
-/
theorem mirror_right_supported
    (x : X)
    (hx : M.IsRightSupported x) :
    M.IsLeftSupported (M.J x) := by
  dsimp [IsLeftSupported, IsRightSupported] at hx ⊢
  have h := congrArg (fun y : X => M.J y) hx
  have hswap := congrArg (fun T : X →ₗ[ℝ] X => T x) M.J_comp_P_right
  simpa [LinearMap.comp_apply] using hswap.symm.trans h

end LinearDatum

end Linear

/-! ## 4. Real-linear Hilbert-space mirror datum -/

namespace RealLinear

/-- Bounded real-linear endomorphisms. -/
abbrev EndR
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/--
A real-linear modular mirror flips chirality if it anticommutes with the chiral
grading.

`J` should be read as modular conjugation / CPT mirror, represented
real-linearly.  `chi` is the chiral grading, satisfying `χ² = 1`.  The relation

`J.comp chi = -(chi.comp J)`

is the real-linear encoding of `Jχ = -χJ`.
-/
structure ModularChiralMirrorDatum
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Modular mirror / real structure. -/
  J : EndR H

  /-- Chiral grading. -/
  chi : EndR H

  /-- `J² = 1`. -/
  J_square :
    J.comp J = ContinuousLinearMap.id ℝ H

  /-- `χ² = 1`. -/
  chi_square :
    chi.comp chi = ContinuousLinearMap.id ℝ H

  /-- `Jχ = -χJ`: the mirror flips chirality. -/
  J_flips_chi :
    J.comp chi = -(chi.comp J)

namespace ModularChiralMirrorDatum

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (M : ModularChiralMirrorDatum H)

/-! ### Pointwise operator laws -/

/-- Pointwise form of `J² = 1`. -/
theorem J_square_apply
    (v : H) :
    M.J (M.J v) = v := by
  have h := congrArg (fun T : EndR H => T v) M.J_square
  simpa [ContinuousLinearMap.comp_apply] using h

/-- Pointwise form of `χ² = 1`. -/
theorem chi_square_apply
    (v : H) :
    M.chi (M.chi v) = v := by
  have h := congrArg (fun T : EndR H => T v) M.chi_square
  simpa [ContinuousLinearMap.comp_apply] using h

/-- Pointwise form of `Jχ = -χJ`. -/
theorem J_chi_apply
    (v : H) :
    M.J (M.chi v) = -M.chi (M.J v) := by
  have h := congrArg (fun T : EndR H => T v) M.J_flips_chi
  simpa [ContinuousLinearMap.comp_apply] using h

/-- Equivalent pointwise form `χJ = -Jχ`. -/
theorem chi_J_apply
    (v : H) :
    M.chi (M.J v) = -M.J (M.chi v) := by
  rw [M.J_chi_apply v]
  simp

/--
Conjugation form:

`J χ J = -χ`.

Since `J² = 1`, this is the same as `J χ J⁻¹ = -χ`.
-/
theorem J_conj_chi :
    (M.J.comp M.chi).comp M.J = -M.chi := by
  ext v
  simp [ContinuousLinearMap.comp_apply, M.chi_J_apply, M.J_square_apply]

/-! ### Chiral projectors -/

/-- Left chiral projector, `(1 + χ) / 2`. -/
def Pleft : EndR H :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ H + M.chi)

/-- Right chiral projector, `(1 - χ) / 2`. -/
def Pright : EndR H :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ H - M.chi)

/--
The modular mirror sends the left projector to the right projector:

`J ∘ Pleft = Pright ∘ J`.
-/
theorem J_comp_Pleft :
    M.J.comp M.Pleft = M.Pright.comp M.J := by
  ext v
  simp [
    Pleft,
    Pright,
    M.J_chi_apply,
    sub_eq_add_neg
  ]

/--
The modular mirror sends the right projector to the left projector:

`J ∘ Pright = Pleft ∘ J`.
-/
theorem J_comp_Pright :
    M.J.comp M.Pright = M.Pleft.comp M.J := by
  ext v
  simp [
    Pleft,
    Pright,
    M.J_chi_apply,
    sub_eq_add_neg
  ]

/--
Conjugation by the modular mirror sends the left projector to the right
projector:

`J ∘ Pleft ∘ J = Pright`.

Since `J² = 1`, this is the same as `J Pleft J⁻¹ = Pright`.
-/
theorem J_conj_Pleft :
    (M.J.comp M.Pleft).comp M.J = M.Pright := by
  ext v
  have h := congrArg (fun T : EndR H => T (M.J v)) M.J_comp_Pleft
  simpa [ContinuousLinearMap.comp_apply, M.J_square_apply] using h

/--
Conjugation by the modular mirror sends the right projector to the left
projector:

`J ∘ Pright ∘ J = Pleft`.

Since `J² = 1`, this is the same as `J Pright J⁻¹ = Pleft`.
-/
theorem J_conj_Pright :
    (M.J.comp M.Pright).comp M.J = M.Pleft := by
  ext v
  have h := congrArg (fun T : EndR H => T (M.J v)) M.J_comp_Pright
  simpa [ContinuousLinearMap.comp_apply, M.J_square_apply] using h

/--
The chiral grading is the difference of the left/right projectors:

`Pleft - Pright = χ`.
-/
theorem Pleft_sub_Pright :
    M.Pleft - M.Pright = M.chi := by
  ext v
  simp [Pleft, Pright, sub_eq_add_neg]
  module

/--
The projectors sum to the identity:

`Pleft + Pright = 1`.
-/
theorem Pleft_add_Pright :
    M.Pleft + M.Pright = ContinuousLinearMap.id ℝ H := by
  ext v
  simp [Pleft, Pright, sub_eq_add_neg]
  module

/-- Left projector idempotence. -/
theorem Pleft_idempotent :
    M.Pleft.comp M.Pleft = M.Pleft := by
  ext v
  have hχχ : M.chi (M.chi v) = v :=
    M.chi_square_apply v
  simp [Pleft, hχχ]
  module

/-- Right projector idempotence. -/
theorem Pright_idempotent :
    M.Pright.comp M.Pright = M.Pright := by
  ext v
  have hχχ : M.chi (M.chi v) = v :=
    M.chi_square_apply v
  simp [Pright, hχχ]
  module

/-- The two chiral projectors are disjoint on the left. -/
theorem Pleft_comp_Pright :
    M.Pleft.comp M.Pright = 0 := by
  ext v
  have hχχ : M.chi (M.chi v) = v :=
    M.chi_square_apply v
  simp [Pleft, Pright, hχχ, sub_eq_add_neg]
  module

/-- The two chiral projectors are disjoint on the right. -/
theorem Pright_comp_Pleft :
    M.Pright.comp M.Pleft = 0 := by
  ext v
  have hχχ : M.chi (M.chi v) = v :=
    M.chi_square_apply v
  simp [Pleft, Pright, hχχ, sub_eq_add_neg]
  module

/-! ### Chiral charge readout -/

/--
Metric preservation by a real-linear mirror.

For a Krein implementation, replace this with the repository's indefinite
Krein pairing. At this abstract Hilbert layer, it uses the ambient real inner
product.
-/
def MetricPreserving
    (T : EndR H) : Prop :=
  ∀ v w : H,
    inner (𝕜 := ℝ) (T v) (T w) =
      inner (𝕜 := ℝ) v w

/--
Chiral charge readout:

`qχ(v) = ⟪v, χ v⟫`.
-/
def chiralCharge
    (v : H) : ℝ :=
  inner (𝕜 := ℝ) v (M.chi v)

/--
If the modular mirror preserves the metric and flips the chiral grading, then
the chiral charge changes sign under the mirror:

`qχ(Jv) = -qχ(v)`.
-/
theorem chiralCharge_J
    (hJmetric : MetricPreserving M.J)
    (v : H) :
    M.chiralCharge (M.J v) = -M.chiralCharge v := by
  calc
    M.chiralCharge (M.J v)
        = inner (𝕜 := ℝ) (M.J v) (M.chi (M.J v)) := by
            rfl
    _ = inner (𝕜 := ℝ) (M.J v) (-M.J (M.chi v)) := by
            rw [M.chi_J_apply v]
    _ = -inner (𝕜 := ℝ) (M.J v) (M.J (M.chi v)) := by
            simp
    _ = -inner (𝕜 := ℝ) v (M.chi v) := by
            rw [hJmetric v (M.chi v)]
    _ = -M.chiralCharge v := by
            rfl

end ModularChiralMirrorDatum

/-! ### Metric-preserving charge readout datum -/

/--
A carrier-level modular mirror and chiral grading.

This is the vector-space form of the algebraic datum. It additionally records
that `J` preserves the real metric, so chiral charge readouts change sign under
`J`.
-/
structure ModularChiralChargeDatum
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Modular mirror / CPT reflection. -/
  J : EndR H

  /-- Chiral grading / charge operator. -/
  chi : EndR H

  /-- `J² = 1`. -/
  J_square :
    J.comp J = ContinuousLinearMap.id ℝ H

  /-- `χ² = 1`. -/
  chi_square :
    chi.comp chi = ContinuousLinearMap.id ℝ H

  /-- `Jχ = -χJ`. -/
  J_chi_anticomm :
    J.comp chi = -(chi.comp J)

  /-- `J` preserves the real metric. -/
  J_isometry :
    ∀ v w : H,
      inner (𝕜 := ℝ) (J v) (J w) =
        inner (𝕜 := ℝ) v w

namespace ModularChiralChargeDatum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (M : ModularChiralChargeDatum H)

/--
Opposite orientation of the anticommutation relation:

`χJ = -Jχ`.
-/
theorem chi_J_anticomm :
    M.chi.comp M.J = -(M.J.comp M.chi) := by
  rw [M.J_chi_anticomm]
  simp

/-- Pointwise form of `χJ = -Jχ`. -/
theorem chi_J_apply
    (v : H) :
    M.chi (M.J v) = -M.J (M.chi v) := by
  have h := congrArg (fun T : EndR H => T v) M.chi_J_anticomm
  simpa [ContinuousLinearMap.comp_apply] using h

/--
Chiral charge readout:

`qχ(v) = ⟪v, χv⟫`.
-/
def chiralCharge
    (v : H) : ℝ :=
  inner (𝕜 := ℝ) v (M.chi v)

/--
The modular mirror flips the chiral charge readout:

`qχ(Jv) = -qχ(v)`.
-/
theorem chiralCharge_J
    (v : H) :
    M.chiralCharge (M.J v) = -M.chiralCharge v := by
  calc
    M.chiralCharge (M.J v)
        = inner (𝕜 := ℝ) (M.J v) (M.chi (M.J v)) := by
            rfl
    _ = inner (𝕜 := ℝ) (M.J v) (-M.J (M.chi v)) := by
            rw [M.chi_J_apply v]
    _ = -inner (𝕜 := ℝ) (M.J v) (M.J (M.chi v)) := by
            simp
    _ = -inner (𝕜 := ℝ) v (M.chi v) := by
            rw [M.J_isometry v (M.chi v)]
    _ = -M.chiralCharge v := by
            rfl

end ModularChiralChargeDatum

/-! ### Algebra/commutant chiral mirroring socket -/

/--
A proof-carrying statement that the modular mirror routes the algebra side to
the commutant side and flips chirality.

This combines the Tomita routing statement with the chiral sign datum. The
actual theorem `J M J = M'` belongs to the concrete Tomita representation.
-/
structure AlgebraCommutantChiralMirror
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Op : Type*) where
  /-- Chiral mirror datum on the carrier. -/
  mirror :
    ModularChiralMirrorDatum H

  /-- Algebra-side predicate. -/
  InAlgebra : Op → Prop

  /-- Commutant-side predicate. -/
  InCommutant : Op → Prop

  /--
  Tomita routing certificate: algebra-side data mirror into the commutant side.
  This is a socket for `J M J = M'`.
  -/
  algebra_mirrors_to_commutant : Prop

  /--
  Chirality flips under the modular mirror.
  This is supplied by `mirror.J_flips_chi`, but is exposed as a named
  representation-level certificate.
  -/
  mirror_flips_chiral_charge : Prop

/--
Real-linear modular mirroring of chiral projectors.

Once the sign datum `Jχ = -χJ` and the involution laws are supplied, Lean proves
that the modular mirror exchanges the left and right chiral projectors.
-/
theorem modularChiralMirrorOwnerTarget :
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
  ∀ M : ModularChiralMirrorDatum H,
    M.J.comp M.Pleft = M.Pright.comp M.J ∧
    M.J.comp M.Pright = M.Pleft.comp M.J ∧
    (M.J.comp M.Pleft).comp M.J = M.Pright ∧
    (M.J.comp M.Pright).comp M.J = M.Pleft := by
  intro H _ _ M
  exact ⟨
    M.J_comp_Pleft,
    M.J_comp_Pright,
    M.J_conj_Pleft,
    M.J_conj_Pright
  ⟩

/-- Disambiguated theorem surface for the real-linear modular chiral mirror. -/
theorem realLinearModularChiralMirrorOwnerTarget :
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
  ∀ M : ModularChiralMirrorDatum H,
    M.J.comp M.Pleft = M.Pright.comp M.J ∧
    M.J.comp M.Pright = M.Pleft.comp M.J ∧
    (M.J.comp M.Pleft).comp M.J = M.Pright ∧
    (M.J.comp M.Pright).comp M.J = M.Pleft :=
  modularChiralMirrorOwnerTarget

end RealLinear

/-! ## 4. Sign-datum version: preserve or flip chirality -/

/--
The KO/chiral mirror sign.

`preserves` means `Jχ = χJ`.
`flips` means `Jχ = -χJ`.
-/
inductive ChiralMirrorSign where
  | preserves
  | flips
deriving DecidableEq, Repr

/--
A sign-sensitive chiral mirror relation.

This is the exact abstraction corresponding to the real spectral triple sign

`Jγ = ε'' γJ`.
-/
def ChiralMirrorRelation
    {Op : Type*} [Ring Op]
    (sign : ChiralMirrorSign)
    (J chi : Op) : Prop :=
  match sign with
  | ChiralMirrorSign.preserves => J * chi = chi * J
  | ChiralMirrorSign.flips => J * chi = -(chi * J)

/--
A sign-carrying mirror datum.

This records whether the modular mirror preserves or flips chirality.
-/
structure SignedModularChiralMirrorDatum
    (Op : Type*) [Ring Op] where
  /-- Modular mirror / real structure. -/
  J : Op

  /-- Chiral grading. -/
  chi : Op

  /-- KO/chiral mirror sign. -/
  sign : ChiralMirrorSign

  /-- `J² = 1`. -/
  J_square :
    J * J = 1

  /-- `χ² = 1`. -/
  chi_square :
    chi * chi = 1

  /-- Sign-sensitive relation `Jχ = ε''χJ`. -/
  relation :
    ChiralMirrorRelation sign J chi

/--
A sign datum recording whether a modular mirror preserves or flips chirality.

This looser socket exposes both branches as implication fields, which is handy
when a concrete model carries the sign as ordinary data rather than by matching
on `ChiralMirrorRelation`.
-/
structure ModularChiralSignDatum
    (Op : Type*) [Ring Op] where
  /-- Modular mirror / real structure. -/
  J : Op

  /-- Chiral grading. -/
  chi : Op

  /-- KO/chiral mirror sign. -/
  sign : ChiralMirrorSign

  /-- Preservation branch: `Jχ = χJ`. -/
  preserves_relation :
    sign = ChiralMirrorSign.preserves →
      J * chi = chi * J

  /-- Flipping branch: `Jχ = -χJ`. -/
  flips_relation :
    sign = ChiralMirrorSign.flips →
      J * chi = -(chi * J)

/-! ## 5. Owner targets -/

/--
Owner target for supplying a modular chiral mirror in a concrete algebraic
model.
-/
def ModularChiralMirrorOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℝ Op] : Prop :=
  ∀ M : ModularChiralMirrorDatum Op,
    M.J * M.J = 1 ∧
      M.chi * M.chi = 1 ∧
      M.J * M.chi = -(M.chi * M.J) ∧
      M.J * ((1 : Op) + M.chi) = ((1 : Op) - M.chi) * M.J

/--
Disambiguated name for the algebraic modular chiral mirror owner target.
-/
def AlgebraicModularChiralMirrorOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℝ Op] : Prop :=
  ModularChiralMirrorOwnerTarget Op

end ModularChiralMirror
