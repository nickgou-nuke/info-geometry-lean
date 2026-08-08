/-
InfoGeometry/OperatorAlgebra/CPTSymmetryBranch.lean

CPT/PCT symmetry branch.

This module packages the branch where a Tomita modular mirror is interpreted
as a CPT/PCT-type mirror, with phase reversal and an explicit KO/chiral sign.

The chiral sign is data.  Tomita theory supplies the algebra/commutant mirror;
it does not by itself decide whether the mirror preserves or flips chirality.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ModularSignCPT
import InfoGeometry.OperatorAlgebra.ModularChiralMirror
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CPTSymmetryBranch

open InfoGeometry.OperatorAlgebra.ModularSignCPT
open InfoGeometry.OperatorAlgebra.ModularChiralMirror

/-! ## 1. Chiral mirror signs -/

/-- Real scalar value of a chiral mirror sign. -/
def chiralSignToReal : ChiralMirrorSign → ℝ
  | .preserves => 1
  | .flips => -1

@[simp]
theorem chiralSignToReal_preserves :
    chiralSignToReal .preserves = 1 :=
  rfl

@[simp]
theorem chiralSignToReal_flips :
    chiralSignToReal .flips = -1 :=
  rfl

/-! ## 2. Real-linear CPT branch -/

/-- Real bounded endomorphisms. -/
abbrev EndR
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/-! ## 2. Chiral-flipping modular CPT mirror -/

/-- Left chiral projector from a grading: `P_L = (1 / 2) • (1 + chi)`. -/
def leftProjector
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (chi : EndR H) : EndR H :=
  (1 / 2 : ℝ) • ((ContinuousLinearMap.id ℝ H) + chi)

/-- Right chiral projector from a grading: `P_R = (1 / 2) • (1 - chi)`. -/
def rightProjector
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (chi : EndR H) : EndR H :=
  (1 / 2 : ℝ) • ((ContinuousLinearMap.id ℝ H) - chi)

/-- A real chiral grading. -/
structure ChiralGrading
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- Chiral grading. -/
  chi : EndR H

  /-- `chi² = 1`. -/
  chi_square :
    chi.comp chi = ContinuousLinearMap.id ℝ H

/--
A modular/CPT mirror on the chiral-flipping branch.

The key sign datum is `J chi = -chi J`.
-/
structure ModularChiralCPTMirror
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Modular conjugation / CPT mirror. -/
  J : EndR H

  /-- Chiral grading. -/
  grading : ChiralGrading H

  /-- `J² = 1`. -/
  J_square :
    J.comp J = ContinuousLinearMap.id ℝ H

  /-- Chiral flip relation: `J chi = -chi J`. -/
  J_flips_chi :
    J.comp grading.chi = -(grading.chi.comp J)

  /-- Metric preservation of the CPT mirror. -/
  J_metric :
    ∀ v w : H,
      inner (𝕜 := ℝ) (J v) (J w) =
        inner (𝕜 := ℝ) v w

namespace ModularChiralCPTMirror

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (C : ModularChiralCPTMirror H)

/-- Left chiral projector attached to the branch. -/
def PL : EndR H :=
  leftProjector C.grading.chi

/-- Right chiral projector attached to the branch. -/
def PR : EndR H :=
  rightProjector C.grading.chi

/-- Pointwise chiral-flip relation. -/
theorem J_flips_chi_apply
    (v : H) :
    C.J (C.grading.chi v) = -C.grading.chi (C.J v) := by
  have h := congrArg (fun T : EndR H => T v) C.J_flips_chi
  simpa [ContinuousLinearMap.comp_apply] using h

/-- The modular/CPT mirror sends the left projector to the right projector. -/
theorem J_comp_PL_eq_PR_comp_J :
    C.J.comp C.PL = C.PR.comp C.J := by
  ext v
  simp [
    PL,
    PR,
    leftProjector,
    rightProjector,
    C.J_flips_chi_apply,
    sub_eq_add_neg
  ]

/-- The modular/CPT mirror sends the right projector to the left projector. -/
theorem J_comp_PR_eq_PL_comp_J :
    C.J.comp C.PR = C.PL.comp C.J := by
  ext v
  simp [
    PL,
    PR,
    leftProjector,
    rightProjector,
    C.J_flips_chi_apply,
    sub_eq_add_neg
  ]

/-- Chiral charge readout. -/
def chiralCharge
    (v : H) : ℝ :=
  inner (𝕜 := ℝ) v (C.grading.chi v)

/-- The modular/CPT mirror flips the chiral charge. -/
theorem chiralCharge_J
    (v : H) :
    C.chiralCharge (C.J v) = -C.chiralCharge v := by
  have hχJ : C.grading.chi (C.J v) = -C.J (C.grading.chi v) := by
    have h := C.J_flips_chi_apply v
    simpa using congrArg Neg.neg h.symm
  calc
    C.chiralCharge (C.J v)
        = inner (𝕜 := ℝ) (C.J v) (C.grading.chi (C.J v)) := by
            rfl
    _ = inner (𝕜 := ℝ) (C.J v) (-C.J (C.grading.chi v)) := by
            rw [hχJ]
    _ = -inner (𝕜 := ℝ) (C.J v) (C.J (C.grading.chi v)) := by
            simp
    _ = -inner (𝕜 := ℝ) v (C.grading.chi v) := by
            rw [C.J_metric v (C.grading.chi v)]
    _ = -C.chiralCharge v := by
            rfl

end ModularChiralCPTMirror

/--
Real-linear CPT/PCT symmetry branch.

`J` is the modular/CPT mirror, `K` is the phase axis, and `chi` is the chiral
grading.  The phase reversal and chiral sign are separate fields: reversing
the phase axis does not automatically force chirality to flip.
-/
structure RealLinearCPTBranch
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- Modular mirror / CPT reflection. -/
  J : EndR H

  /-- Hestenes phase axis. -/
  K : EndR H

  /-- Chiral grading. -/
  chi : EndR H

  /-- `J² = 1`. -/
  J_square :
    J.comp J = 1

  /-- `K² = -1`. -/
  K_square :
    K.comp K = -1

  /-- `χ² = 1`. -/
  chi_square :
    chi.comp chi = 1

  /-- CPT/real structure is anti-linear relative to the phase axis. -/
  J_reverses_phase :
    J.comp K = -(K.comp J)

  /-- KO/chiral sign branch. -/
  chiralSign : ChiralMirrorSign

  /-- KO/chiral sign relation: `Jχ = ε'' χJ`. -/
  J_chi_relation :
    J.comp chi =
      chiralSignToReal chiralSign • (chi.comp J)

namespace RealLinearCPTBranch

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

variable (C : RealLinearCPTBranch H)

/-- Left chiral projector, `(1 + χ) / 2`. -/
def P_left : EndR H :=
  (1 / 2 : ℝ) • (1 + C.chi)

/-- Right chiral projector, `(1 - χ) / 2`. -/
def P_right : EndR H :=
  (1 / 2 : ℝ) • (1 - C.chi)

/-- Pointwise form of the preserving chiral sign branch. -/
theorem J_chi_apply_of_preserves
    (h : C.chiralSign = ChiralMirrorSign.preserves)
    (v : H) :
    C.J (C.chi v) = C.chi (C.J v) := by
  have hrel :
      C.J.comp C.chi = C.chi.comp C.J := by
    simpa [h] using C.J_chi_relation
  have hv := congrArg (fun T : EndR H => T v) hrel
  simpa [ContinuousLinearMap.comp_apply] using hv

/-- Pointwise form of the flipping chiral sign branch. -/
theorem J_chi_apply_of_flips
    (h : C.chiralSign = ChiralMirrorSign.flips)
    (v : H) :
    C.J (C.chi v) = -C.chi (C.J v) := by
  have hrel :
      C.J.comp C.chi = -(C.chi.comp C.J) := by
    simpa [h] using C.J_chi_relation
  have hv := congrArg (fun T : EndR H => T v) hrel
  simpa [ContinuousLinearMap.comp_apply] using hv

/--
If the KO/chiral sign preserves chirality, the CPT mirror preserves the left
projector.
-/
theorem preserves_P_left_of_preserves
    (h : C.chiralSign = ChiralMirrorSign.preserves) :
    C.J.comp C.P_left = C.P_left.comp C.J := by
  ext v
  simp [P_left, C.J_chi_apply_of_preserves h v]

/--
If the KO/chiral sign preserves chirality, the CPT mirror preserves the right
projector.
-/
theorem preserves_P_right_of_preserves
    (h : C.chiralSign = ChiralMirrorSign.preserves) :
    C.J.comp C.P_right = C.P_right.comp C.J := by
  ext v
  simp [
    P_right,
    C.J_chi_apply_of_preserves h v,
    sub_eq_add_neg
  ]

/--
If the KO/chiral sign flips chirality, the CPT mirror swaps the left projector
with the right projector.
-/
theorem swaps_P_left_of_flips
    (h : C.chiralSign = ChiralMirrorSign.flips) :
    C.J.comp C.P_left = C.P_right.comp C.J := by
  ext v
  simp [
    P_left,
    P_right,
    C.J_chi_apply_of_flips h v,
    sub_eq_add_neg
  ]

/--
If the KO/chiral sign flips chirality, the CPT mirror swaps the right projector
with the left projector.
-/
theorem swaps_P_right_of_flips
    (h : C.chiralSign = ChiralMirrorSign.flips) :
    C.J.comp C.P_right = C.P_left.comp C.J := by
  ext v
  simp [
    P_left,
    P_right,
    C.J_chi_apply_of_flips h v,
    sub_eq_add_neg
  ]

/-- Pointwise form of `J² = 1`. -/
theorem J_square_apply
    (v : H) :
    C.J (C.J v) = v := by
  have hv := congrArg (fun T : EndR H => T v) C.J_square
  simpa [ContinuousLinearMap.comp_apply] using hv

/--
In the flipping branch, conjugation by the CPT mirror sends the left projector
to the right projector.
-/
theorem conj_P_left_of_flips
    (h : C.chiralSign = ChiralMirrorSign.flips) :
    (C.J.comp C.P_left).comp C.J = C.P_right := by
  ext v
  have hs := congrArg (fun T : EndR H => T (C.J v)) (C.swaps_P_left_of_flips h)
  simpa [ContinuousLinearMap.comp_apply, C.J_square_apply] using hs

/--
In the flipping branch, conjugation by the CPT mirror sends the right projector
to the left projector.
-/
theorem conj_P_right_of_flips
    (h : C.chiralSign = ChiralMirrorSign.flips) :
    (C.J.comp C.P_right).comp C.J = C.P_left := by
  ext v
  have hs := congrArg (fun T : EndR H => T (C.J v)) (C.swaps_P_right_of_flips h)
  simpa [ContinuousLinearMap.comp_apply, C.J_square_apply] using hs

end RealLinearCPTBranch

/-! ## 3. Algebraic CPT branch -/

/--
A calibrated modular-CPT branch in an abstract real operator algebra.

This packages the Tomita/CPT mirror, the modular sign, the emergent Hestenes
phase axis, and the chirality-flipping KO sign.  This is the algebraic
mechanism; representation-specific Tomita or physical CPT calibration belongs
in the concrete owner file that proves it.
-/
structure CPTBranch
    (Op : Type*) [Ring Op] [Algebra ℝ Op] where
  /-- Modular/CPT mirror. -/
  J : Op

  /-- Modular sign or parity. -/
  eps : Op

  /-- Chiral grading. -/
  chi : Op

  /-- Emergent Hestenes phase axis. -/
  Kmod : Op

  /-- `J² = 1`. -/
  J_square :
    J * J = 1

  /-- `ε² = 1` on the active modular sector. -/
  eps_square :
    eps * eps = 1

  /-- `χ² = 1`. -/
  chi_square :
    chi * chi = 1

  /-- Modular sign reversal: `Jε = -εJ`. -/
  J_flips_eps :
    J * eps = -(eps * J)

  /-- Chirality reversal: `Jχ = -χJ`. -/
  J_flips_chi :
    J * chi = -(chi * J)

  /-- Emergent phase axis: `Kmod = Jε`. -/
  Kmod_eq :
    Kmod = J * eps

  /-- The emergent phase squares to `-1`. -/
  Kmod_square :
    Kmod * Kmod = -1

namespace CPTBranch

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]
variable (C : CPTBranch Op)

/-- Left chiral projector. -/
def P_left : Op :=
  (1 / 2 : ℝ) • ((1 : Op) + C.chi)

/-- Right chiral projector. -/
def P_right : Op :=
  (1 / 2 : ℝ) • ((1 : Op) - C.chi)

/-- The CPT mirror sends the left chiral numerator to the right one. -/
theorem J_mul_one_add_chi :
    C.J * ((1 : Op) + C.chi) =
      ((1 : Op) - C.chi) * C.J := by
  calc
    C.J * ((1 : Op) + C.chi)
        = C.J * 1 + C.J * C.chi := by
            rw [mul_add]
    _ = C.J + C.J * C.chi := by
            rw [mul_one]
    _ = C.J + -(C.chi * C.J) := by
            rw [C.J_flips_chi]
    _ = C.J - C.chi * C.J := by
            simp [sub_eq_add_neg]
    _ = (1 : Op) * C.J - C.chi * C.J := by
            rw [one_mul]
    _ = ((1 : Op) - C.chi) * C.J := by
            rw [sub_mul]

/-- The CPT mirror sends the right chiral numerator to the left one. -/
theorem J_mul_one_sub_chi :
    C.J * ((1 : Op) - C.chi) =
      ((1 : Op) + C.chi) * C.J := by
  calc
    C.J * ((1 : Op) - C.chi)
        = C.J * 1 - C.J * C.chi := by
            rw [mul_sub]
    _ = C.J - C.J * C.chi := by
            rw [mul_one]
    _ = C.J - (-(C.chi * C.J)) := by
            rw [C.J_flips_chi]
    _ = C.J + C.chi * C.J := by
            simp
    _ = (1 : Op) * C.J + C.chi * C.J := by
            rw [one_mul]
    _ = ((1 : Op) + C.chi) * C.J := by
            rw [add_mul]

/-- CPT sends the left chiral projector to the right one: `J P_L = P_R J`. -/
theorem J_mul_P_left :
    C.J * C.P_left = C.P_right * C.J := by
  calc
    C.J * C.P_left
        = (1 / 2 : ℝ) • (C.J * ((1 : Op) + C.chi)) := by
            rw [P_left]
            exact mul_smul_comm (1 / 2 : ℝ) C.J ((1 : Op) + C.chi)
    _ = (1 / 2 : ℝ) • (((1 : Op) - C.chi) * C.J) := by
            rw [C.J_mul_one_add_chi]
    _ = C.P_right * C.J := by
            rw [P_right]
            exact (smul_mul_assoc (1 / 2 : ℝ) ((1 : Op) - C.chi) C.J).symm

/-- CPT sends the right chiral projector to the left one: `J P_R = P_L J`. -/
theorem J_mul_P_right :
    C.J * C.P_right = C.P_left * C.J := by
  calc
    C.J * C.P_right
        = (1 / 2 : ℝ) • (C.J * ((1 : Op) - C.chi)) := by
            rw [P_right]
            exact mul_smul_comm (1 / 2 : ℝ) C.J ((1 : Op) - C.chi)
    _ = (1 / 2 : ℝ) • (((1 : Op) + C.chi) * C.J) := by
            rw [C.J_mul_one_sub_chi]
    _ = C.P_left * C.J := by
            rw [P_left]
            exact (smul_mul_assoc (1 / 2 : ℝ) ((1 : Op) + C.chi) C.J).symm

/-- Conjugation by CPT sends the left chiral projector to the right one. -/
theorem J_conj_P_left :
    C.J * C.P_left * C.J = C.P_right := by
  calc
    C.J * C.P_left * C.J
        = (C.P_right * C.J) * C.J := by
            rw [C.J_mul_P_left]
    _ = C.P_right * (C.J * C.J) := by
            rw [mul_assoc]
    _ = C.P_right * 1 := by
            rw [C.J_square]
    _ = C.P_right := by
            rw [mul_one]

/-- Conjugation by CPT sends the right chiral projector to the left one. -/
theorem J_conj_P_right :
    C.J * C.P_right * C.J = C.P_left := by
  calc
    C.J * C.P_right * C.J
        = (C.P_left * C.J) * C.J := by
            rw [C.J_mul_P_right]
    _ = C.P_left * (C.J * C.J) := by
            rw [mul_assoc]
    _ = C.P_left * 1 := by
            rw [C.J_square]
    _ = C.P_left := by
            rw [mul_one]

/-- Conjugation by CPT flips the chiral grading. -/
theorem J_conj_chi :
    C.J * C.chi * C.J = -C.chi := by
  calc
    C.J * C.chi * C.J
        = (-(C.chi * C.J)) * C.J := by
            rw [C.J_flips_chi]
    _ = -(C.chi * (C.J * C.J)) := by
            rw [neg_mul, mul_assoc]
    _ = -(C.chi * 1) := by
            rw [C.J_square]
    _ = -C.chi := by
            rw [mul_one]

end CPTBranch

/-! ## 4. Algebra/commutant routing socket -/

/--
Algebra/commutant routing for the CPT chiral-flip branch.

This is an algebraic socket for the statement:

`α_J(M) = M'` and `α_J(P_L) = P_R`.
-/
structure CPTAlgebraCommutantBranch
    (Op : Type*) [Ring Op] where
  /-- Algebra-side predicate. -/
  InAlgebra : Op → Prop

  /-- Commutant-side predicate. -/
  InCommutant : Op → Prop

  /-- Algebra-side left projector. -/
  P_left : Op

  /-- Commutant-side right projector. -/
  P_right : Op

  /-- Multiplicative/additive CPT mirror on represented operators. -/
  alphaJ : Op →+* Op

  /-- Tomita routing property: algebra-side elements mirror into the commutant. -/
  alphaJ_maps_algebra_to_commutant :
    ∀ a : Op, InAlgebra a → InCommutant (alphaJ a)

  /-- Chiral-flip property: the left projector mirrors to the right projector. -/
  alphaJ_P_left :
    alphaJ P_left = P_right

namespace CPTAlgebraCommutantBranch

variable {Op : Type*} [Ring Op]
variable (B : CPTAlgebraCommutantBranch Op)

/-- Left support in the algebra-side chiral sector. -/
def IsLeftSupported
    (a : Op) : Prop :=
  B.P_left * a = a

/-- Right support in the commutant-side chiral sector. -/
def IsRightSupported
    (a : Op) : Prop :=
  B.P_right * a = a

/--
A left-supported algebra-side element mirrors to a right-supported commutant
element.
-/
theorem maps_left_algebra_to_right_commutant
    {a : Op}
    (haM : B.InAlgebra a)
    (haL : B.IsLeftSupported a) :
    B.InCommutant (B.alphaJ a) ∧ B.IsRightSupported (B.alphaJ a) := by
  constructor
  · exact B.alphaJ_maps_algebra_to_commutant a haM
  · dsimp [IsRightSupported, IsLeftSupported] at haL ⊢
    calc
      B.P_right * B.alphaJ a
          = B.alphaJ B.P_left * B.alphaJ a := by
              rw [B.alphaJ_P_left]
      _ = B.alphaJ (B.P_left * a) := by
              exact (B.alphaJ.map_mul B.P_left a).symm
      _ = B.alphaJ a := by
              rw [haL]

end CPTAlgebraCommutantBranch

/-! ## 5. Integrated modular/chiral CPT branch -/

/--
Integrated CPT symmetry branch.

This branch identifies the modular mirror from the modular-sign CPT structure
with the mirror in the real-linear chiral mirror structure.
-/
structure IntegratedCPTSymmetryBranch
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /--
  Modular sign/CPT algebra:

  `eps = sign(log Delta)`, `J = modular mirror`, `Kmod = J eps`.
  -/
  modularCPT :
    ModularSignCPTDatum H

  /--
  Chiral mirror structure:

  `chi² = 1` and `J chi = -chi J`.
  -/
  chiralMirror :
    RealLinear.ModularChiralMirrorDatum H

  /-- The modular mirror used in both structures is the same operator. -/
  J_agrees :
    chiralMirror.J = modularCPT.J

  /--
  The CPT mirror preserves the real metric.

  In a Krein implementation this should be replaced by preservation of the
  repository's indefinite Krein pairing.
  -/
  J_metric_preserving :
    RealLinear.ModularChiralMirrorDatum.MetricPreserving chiralMirror.J

namespace IntegratedCPTSymmetryBranch

variable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (C : IntegratedCPTSymmetryBranch H)

/-! ### Modular sign and phase consequences -/

/-- The emergent CPT/Hestenes phase axis is `Kmod = J eps`. -/
theorem Kmod_eq_J_eps :
    C.modularCPT.Kmod =
      C.modularCPT.J.comp C.modularCPT.eps :=
  C.modularCPT.Kmod_eq

/-- The emergent CPT/Hestenes phase axis squares to `-1`. -/
theorem Kmod_square :
    C.modularCPT.Kmod.comp C.modularCPT.Kmod =
      -(1 : EndR H) :=
  C.modularCPT.Kmod_square

/-- The modular mirror anticommutes with the modular sign. -/
theorem J_eps_anticomm :
    C.modularCPT.J.comp C.modularCPT.eps =
      -(C.modularCPT.eps.comp C.modularCPT.J) :=
  C.modularCPT.J_eps_anticomm

/-! ### Chiral mirror consequences -/

/-- The modular CPT mirror anticommutes with the chiral grading. -/
theorem J_flips_chi :
    C.modularCPT.J.comp C.chiralMirror.chi =
      -(C.chiralMirror.chi.comp C.modularCPT.J) := by
  rw [← C.J_agrees]
  exact C.chiralMirror.J_flips_chi

/--
The CPT mirror sends the left chiral projector to the right one:

`J ∘ Pleft = Pright ∘ J`.
-/
theorem J_comp_Pleft :
    C.modularCPT.J.comp C.chiralMirror.Pleft =
      C.chiralMirror.Pright.comp C.modularCPT.J := by
  rw [← C.J_agrees]
  exact C.chiralMirror.J_comp_Pleft

/--
The CPT mirror sends the right chiral projector to the left one:

`J ∘ Pright = Pleft ∘ J`.
-/
theorem J_comp_Pright :
    C.modularCPT.J.comp C.chiralMirror.Pright =
      C.chiralMirror.Pleft.comp C.modularCPT.J := by
  rw [← C.J_agrees]
  exact C.chiralMirror.J_comp_Pright

/--
Conjugation by CPT sends the left projector to the right projector:

`J ∘ Pleft ∘ J = Pright`.
-/
theorem J_conj_Pleft :
    (C.modularCPT.J.comp C.chiralMirror.Pleft).comp C.modularCPT.J =
      C.chiralMirror.Pright := by
  rw [← C.J_agrees]
  exact C.chiralMirror.J_conj_Pleft

/--
Conjugation by CPT sends the right projector to the left projector:

`J ∘ Pright ∘ J = Pleft`.
-/
theorem J_conj_Pright :
    (C.modularCPT.J.comp C.chiralMirror.Pright).comp C.modularCPT.J =
      C.chiralMirror.Pleft := by
  rw [← C.J_agrees]
  exact C.chiralMirror.J_conj_Pright

/-! ### Chiral charge sign reversal -/

/--
The chiral charge readout flips under CPT:

`q_chi(Jv) = -q_chi(v)`.
-/
theorem chiralCharge_CPT
    (v : H) :
    C.chiralMirror.chiralCharge (C.modularCPT.J v) =
      -C.chiralMirror.chiralCharge v := by
  rw [← C.J_agrees]
  exact C.chiralMirror.chiralCharge_J C.J_metric_preserving v

/-! ### Summary theorem -/

/--
The CPT branch exchanges left and right chiral sectors and flips the chiral
charge readout.
-/
theorem CPT_exchanges_chiral_sectors :
    C.modularCPT.J.comp C.chiralMirror.Pleft =
        C.chiralMirror.Pright.comp C.modularCPT.J ∧
    C.modularCPT.J.comp C.chiralMirror.Pright =
        C.chiralMirror.Pleft.comp C.modularCPT.J ∧
    (∀ v : H,
      C.chiralMirror.chiralCharge (C.modularCPT.J v) =
        -C.chiralMirror.chiralCharge v) := by
  exact ⟨
    C.J_comp_Pleft,
    C.J_comp_Pright,
    C.chiralCharge_CPT
  ⟩

end IntegratedCPTSymmetryBranch

/-! ## 6. Owner targets -/

/--
Owner target for the integrated CPT symmetry branch.

Once the modular-sign CPT structure, chiral mirror structure, and calibration
fields are supplied, the left/right exchange and charge flip statements are
theorems.
-/
@[owner_target_tag]
def CPTSymmetryBranchOwnerTarget : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
  ∀ C : IntegratedCPTSymmetryBranch H,
    C.modularCPT.J.comp C.chiralMirror.Pleft =
        C.chiralMirror.Pright.comp C.modularCPT.J ∧
    C.modularCPT.J.comp C.chiralMirror.Pright =
        C.chiralMirror.Pleft.comp C.modularCPT.J ∧
    (∀ v : H,
      C.chiralMirror.chiralCharge (C.modularCPT.J v) =
        -C.chiralMirror.chiralCharge v)

/--
The CPT branch owner target is proved from the modular sign and chiral mirror
data.
-/
theorem cptSymmetryBranchOwnerTarget :
    CPTSymmetryBranchOwnerTarget := by
  intro H _ _ C
  exact C.CPT_exchanges_chiral_sectors

end InfoGeometry.OperatorAlgebra.CPTSymmetryBranch
