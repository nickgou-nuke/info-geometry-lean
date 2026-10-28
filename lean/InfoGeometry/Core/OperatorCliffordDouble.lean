/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Clifford doubling of arbitrary module endomorphisms

Native products and coproducts identify four unrestricted endomorphism blocks
with the full endomorphism space of the doubled module. The simultaneous lift
is a faithful algebra homomorphism. Its image commutes with two concrete
square-one anticommuting generators.

The two Dirac operators retain arbitrary noncommuting endomorphisms as their
coefficients. Their squares retain the commutator, and their ordered mixed
products retain the anticommutator. Projection onto the actual off-diagonal
blocks detects precisely when the square correction vanishes.
-/

namespace InfoGeometry.Core.OperatorCliffordDouble

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Four unrestricted blocks acting on the doubled module. -/
def block (A B C D : Module.End R M) : Module.End R (M × M) :=
  (A.coprod B).prod (C.coprod D)

@[simp]
theorem block_apply (A B C D : Module.End R M) (x : M × M) :
    block A B C D x = (A x.1 + B x.2, C x.1 + D x.2) :=
  rfl

/-- The native product/coproduct equivalences cover the full doubled
endomorphism space. -/
def blockEquiv :
    ((Module.End R M × Module.End R M) ×
      (Module.End R M × Module.End R M)) ≃ₗ[R]
        Module.End R (M × M) :=
  ((LinearMap.coprodEquiv R).prodCongr
      (LinearMap.coprodEquiv R)).trans
    (LinearMap.prodEquiv R)

@[simp]
theorem blockEquiv_apply (A B C D : Module.End R M) :
    blockEquiv ((A, B), (C, D)) = block A B C D :=
  rfl

/-- Equality of full doubled operators is equality of all four blocks. -/
@[simp]
theorem block_inj {A B C D A' B' C' D' : Module.End R M} :
    block A B C D = block A' B' C' D' ↔
      A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  change blockEquiv ((A, B), (C, D)) =
      blockEquiv ((A', B'), (C', D')) ↔ _
  rw [(blockEquiv (R := R) (M := M)).injective.eq_iff]
  simp only [Prod.mk.injEq, and_assoc]

theorem exists_block (T : Module.End R (M × M)) :
    ∃ A B C D : Module.End R M, block A B C D = T := by
  obtain ⟨⟨⟨A, B⟩, ⟨C, D⟩⟩, h⟩ :=
    (blockEquiv (R := R) (M := M)).surjective T
  exact ⟨A, B, C, D, h⟩

@[simp]
theorem block_zero :
    block (0 : Module.End R M) 0 0 0 = 0 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext <;> simp

@[simp]
theorem block_one :
    block (1 : Module.End R M) 0 0 1 = 1 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext <;> simp

theorem block_add (A B C D A' B' C' D' : Module.End R M) :
    block A B C D + block A' B' C' D' =
      block (A + A') (B + B') (C + C') (D + D') := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext <;> simp <;> abel

theorem block_neg (A B C D : Module.End R M) :
    -block A B C D = block (-A) (-B) (-C) (-D) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext <;> simp <;> abel

theorem block_sub (A B C D A' B' C' D' : Module.End R M) :
    block A B C D - block A' B' C' D' =
      block (A - A') (B - B') (C - C') (D - D') := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext <;> simp <;> abel

/-- Ordered block multiplication in the full noncommutative endomorphism ring. -/
theorem block_mul (A B C D A' B' C' D' : Module.End R M) :
    block A B C D * block A' B' C' D' =
      block (A * A' + B * C') (A * B' + B * D')
        (C * A' + D * C') (C * B' + D * D') := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext <;>
    simp only [Module.End.mul_apply, block_apply, LinearMap.add_apply, map_add] <;>
    abel

/-- The upper-right block, extracted by native injection and projection. -/
def upperRight (T : Module.End R (M × M)) : Module.End R M :=
  (LinearMap.fst R M M).comp (T.comp (LinearMap.inr R M M))

/-- The lower-left block, extracted by native injection and projection. -/
def lowerLeft (T : Module.End R (M × M)) : Module.End R M :=
  (LinearMap.snd R M M).comp (T.comp (LinearMap.inl R M M))

@[simp]
theorem upperRight_block (A B C D : Module.End R M) :
    upperRight (block A B C D) = B := by
  apply LinearMap.ext
  intro x
  simp [upperRight]

@[simp]
theorem lowerLeft_block (A B C D : Module.End R M) :
    lowerLeft (block A B C D) = C := by
  apply LinearMap.ext
  intro x
  simp [lowerLeft]

/-- Simultaneous action on both summands, using native algebra homomorphisms. -/
def lift : Module.End R M →ₐ[R] Module.End R (M × M) :=
  (LinearMap.prodMapAlgHom R M M).comp
    ((AlgHom.id R (Module.End R M)).prod
      (AlgHom.id R (Module.End R M)))

@[simp]
theorem lift_apply (A : Module.End R M) (x : M × M) :
    lift A x = (A x.1, A x.2) :=
  rfl

theorem lift_eq_block (A : Module.End R M) :
    lift A = block A 0 0 A := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext <;> simp

/-- No endomorphism information is lost by simultaneous lifting. -/
theorem lift_injective :
    Function.Injective (lift (R := R) (M := M)) := by
  intro A B h
  apply LinearMap.ext
  intro x
  have hx := congrArg
    (fun T : Module.End R (M × M) => (T (x, 0)).1) h
  simpa only [lift_apply] using hx

@[simp]
theorem lift_eq_lift_iff (A B : Module.End R M) :
    lift A = lift B ↔ A = B :=
  (lift_injective (R := R) (M := M)).eq_iff

/-- Faithfulness reflects commutation of the original full endomorphisms. -/
@[simp]
theorem lift_commute_iff (A B : Module.End R M) :
    Commute (lift A) (lift B) ↔ Commute A B := by
  change lift A * lift B = lift B * lift A ↔ A * B = B * A
  rw [← map_mul, ← map_mul, lift_eq_lift_iff]

/-- The grading generator on the doubled module. -/
def gamma1 : Module.End R (M × M) :=
  block 1 0 0 (-1)

/-- The exchange generator on the doubled module. -/
def gamma2 : Module.End R (M × M) :=
  block 0 1 1 0

@[simp]
theorem gamma1_apply (x : M × M) :
    gamma1 (R := R) x = (x.1, -x.2) := by
  simp [gamma1]

@[simp]
theorem gamma2_apply (x : M × M) :
    gamma2 (R := R) x = (x.2, x.1) := by
  simp [gamma2]

@[simp]
theorem gamma1_sq :
    gamma1 (R := R) (M := M) ^ 2 = 1 := by
  simp [gamma1, pow_two, block_mul]

@[simp]
theorem gamma2_sq :
    gamma2 (R := R) (M := M) ^ 2 = 1 := by
  simp [gamma2, pow_two, block_mul]

/-- The generators anticommute without any hypothesis on operator coefficients. -/
theorem gamma1_mul_gamma2 :
    gamma1 (R := R) (M := M) * gamma2 = -(gamma2 * gamma1) := by
  simp [gamma1, gamma2, block_mul, block_neg]

theorem gamma1_mul_gamma2_add_gamma2_mul_gamma1 :
    gamma1 (R := R) (M := M) * gamma2 + gamma2 * gamma1 = 0 := by
  rw [gamma1_mul_gamma2]
  exact neg_add_cancel _

/-- Every simultaneous lift commutes with the grading generator. -/
theorem lift_commute_gamma1 (A : Module.End R M) :
    Commute (lift A) gamma1 := by
  change lift A * gamma1 = gamma1 * lift A
  simp [lift_eq_block, gamma1, block_mul]

/-- Every simultaneous lift commutes with the exchange generator. -/
theorem lift_commute_gamma2 (A : Module.End R M) :
    Commute (lift A) gamma2 := by
  change lift A * gamma2 = gamma2 * lift A
  simp [lift_eq_block, gamma2, block_mul]

/-- The plus Dirac operator with arbitrary full endomorphism coefficients. -/
def diracPlus (A B : Module.End R M) : Module.End R (M × M) :=
  block A B B (-A)

/-- The minus Dirac operator with arbitrary full endomorphism coefficients. -/
def diracMinus (A B : Module.End R M) : Module.End R (M × M) :=
  block A (-B) (-B) (-A)

theorem diracPlus_eq_lift (A B : Module.End R M) :
    diracPlus A B = lift A * gamma1 + lift B * gamma2 := by
  simp [diracPlus, lift_eq_block, gamma1, gamma2, block_mul, block_add]

theorem diracMinus_eq_lift (A B : Module.End R M) :
    diracMinus A B = lift A * gamma1 - lift B * gamma2 := by
  simp [diracMinus, lift_eq_block, gamma1, gamma2, block_mul, block_sub]

/-- The plus square retains the exact commutator in both off-diagonal blocks. -/
theorem diracPlus_sq (A B : Module.End R M) :
    diracPlus A B ^ 2 =
      block (A ^ 2 + B ^ 2) (A * B - B * A)
        (-(A * B - B * A)) (A ^ 2 + B ^ 2) := by
  simp only [diracPlus, pow_two, block_mul]
  apply block_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

/-- Reversing the exchange coefficient reverses the commutator correction. -/
theorem diracMinus_sq (A B : Module.End R M) :
    diracMinus A B ^ 2 =
      block (A ^ 2 + B ^ 2) (-(A * B - B * A))
        (A * B - B * A) (A ^ 2 + B ^ 2) := by
  simp only [diracMinus, pow_two, block_mul]
  apply block_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

/-- Plus-times-minus retains the negative anticommutator in its upper-right block. -/
theorem diracPlus_mul_diracMinus (A B : Module.End R M) :
    diracPlus A B * diracMinus A B =
      block (A ^ 2 - B ^ 2) (-(A * B + B * A))
        (A * B + B * A) (A ^ 2 - B ^ 2) := by
  simp only [diracPlus, diracMinus, block_mul]
  apply block_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

/-- Minus-times-plus retains the positive anticommutator in its upper-right block. -/
theorem diracMinus_mul_diracPlus (A B : Module.End R M) :
    diracMinus A B * diracPlus A B =
      block (A ^ 2 - B ^ 2) (A * B + B * A)
        (-(A * B + B * A)) (A ^ 2 - B ^ 2) := by
  simp only [diracPlus, diracMinus, block_mul]
  apply block_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

theorem diracPlus_sq_eq_lift_add (A B : Module.End R M) :
    diracPlus A B ^ 2 =
      lift (A ^ 2 + B ^ 2) + lift (A * B - B * A) * (gamma1 * gamma2) := by
  rw [diracPlus_sq]
  simp [lift_eq_block, gamma1, gamma2, block_mul, block_add]

theorem diracMinus_sq_eq_lift_sub (A B : Module.End R M) :
    diracMinus A B ^ 2 =
      lift (A ^ 2 + B ^ 2) - lift (A * B - B * A) * (gamma1 * gamma2) := by
  rw [diracMinus_sq]
  simp [lift_eq_block, gamma1, gamma2, block_mul, block_sub]

theorem diracPlus_mul_diracMinus_eq_lift_sub (A B : Module.End R M) :
    diracPlus A B * diracMinus A B =
      lift (A ^ 2 - B ^ 2) - lift (A * B + B * A) * (gamma1 * gamma2) := by
  rw [diracPlus_mul_diracMinus]
  simp [lift_eq_block, gamma1, gamma2, block_mul, block_sub]

theorem diracMinus_mul_diracPlus_eq_lift_add (A B : Module.End R M) :
    diracMinus A B * diracPlus A B =
      lift (A ^ 2 - B ^ 2) + lift (A * B + B * A) * (gamma1 * gamma2) := by
  rw [diracMinus_mul_diracPlus]
  simp [lift_eq_block, gamma1, gamma2, block_mul, block_add]

@[simp]
theorem upperRight_diracPlus_sq (A B : Module.End R M) :
    upperRight (diracPlus A B ^ 2) = A * B - B * A := by
  rw [diracPlus_sq, upperRight_block]

@[simp]
theorem lowerLeft_diracPlus_sq (A B : Module.End R M) :
    lowerLeft (diracPlus A B ^ 2) = -(A * B - B * A) := by
  rw [diracPlus_sq, lowerLeft_block]

/-- Vanishing of the actual upper-right square block detects commutation. -/
theorem upperRight_diracPlus_sq_eq_zero_iff (A B : Module.End R M) :
    upperRight (diracPlus A B ^ 2) = 0 ↔ Commute A B := by
  rw [upperRight_diracPlus_sq]
  change A * B - B * A = 0 ↔ A * B = B * A
  exact sub_eq_zero

/-- Both off-diagonal square blocks vanish exactly for commuting coefficients. -/
theorem diracPlus_sq_offDiagonal_eq_zero_iff (A B : Module.End R M) :
    (upperRight (diracPlus A B ^ 2) = 0 ∧
      lowerLeft (diracPlus A B ^ 2) = 0) ↔ Commute A B := by
  rw [upperRight_diracPlus_sq, lowerLeft_diracPlus_sq, neg_eq_zero, and_self]
  change A * B - B * A = 0 ↔ A * B = B * A
  exact sub_eq_zero

/-- The square equals the simultaneous sum-of-squares lift precisely when
the original endomorphisms commute. -/
theorem diracPlus_sq_eq_lift_iff (A B : Module.End R M) :
    diracPlus A B ^ 2 = lift (A ^ 2 + B ^ 2) ↔ Commute A B := by
  constructor
  · intro h
    apply (upperRight_diracPlus_sq_eq_zero_iff A B).mp
    rw [h, lift_eq_block, upperRight_block]
  · intro h
    change A * B = B * A at h
    simp [diracPlus_sq, lift_eq_block, h]

end InfoGeometry.Core.OperatorCliffordDouble
