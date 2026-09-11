import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Generic composition triality closure

This file records only the algebraic triality identity and its closure under
componentwise commutator.  It does not identify a particular composition
algebra or a magic-square Lie algebra.
-/

namespace InfoGeometry.Exceptional.CompositionTriality

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

/-- A bilinear multiplication together with three endomorphisms satisfying
the triality derivation identity. -/
structure TrialityTriple (mul : A →ₗ[R] A →ₗ[R] A) where
  t₁ : Module.End R A
  t₂ : Module.End R A
  t₃ : Module.End R A
  triality : ∀ x y, t₁ (mul x y) = mul (t₂ x) y + mul x (t₃ y)

namespace TrialityTriple

variable {mul : A →ₗ[R] A →ₗ[R] A}

@[ext] theorem ext {T U : TrialityTriple mul}
    (h₁ : T.t₁ = U.t₁) (h₂ : T.t₂ = U.t₂) (h₃ : T.t₃ = U.t₃) :
    T = U := by
  cases T with
  | mk t₁ t₂ t₃ hT =>
    cases U with
    | mk u₁ u₂ u₃ hU =>
      simp_all

noncomputable def zero : TrialityTriple mul where
  t₁ := 0
  t₂ := 0
  t₃ := 0
  triality := by
    intro x y
    change 0 = mul 0 y + mul x 0
    simp

noncomputable def add (T U : TrialityTriple mul) : TrialityTriple mul where
  t₁ := T.t₁ + U.t₁
  t₂ := T.t₂ + U.t₂
  t₃ := T.t₃ + U.t₃
  triality := by
    intro x y
    simp only [LinearMap.add_apply, map_add]
    rw [T.triality, U.triality]
    abel

noncomputable def neg (T : TrialityTriple mul) : TrialityTriple mul where
  t₁ := -T.t₁
  t₂ := -T.t₂
  t₃ := -T.t₃
  triality := by
    intro x y
    simp only [LinearMap.neg_apply, map_neg]
    rw [T.triality]
    abel

noncomputable def smul (r : R) (T : TrialityTriple mul) : TrialityTriple mul where
  t₁ := r • T.t₁
  t₂ := r • T.t₂
  t₃ := r • T.t₃
  triality := by
    intro x y
    simp only [LinearMap.smul_apply, map_smul]
    rw [T.triality]
    module

noncomputable instance : Zero (TrialityTriple mul) := ⟨zero⟩
noncomputable instance : Add (TrialityTriple mul) := ⟨add⟩
noncomputable instance : Neg (TrialityTriple mul) := ⟨neg⟩
noncomputable instance : SMul R (TrialityTriple mul) := ⟨smul⟩

noncomputable instance : AddCommGroup (TrialityTriple mul) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc T U V := by
    apply TrialityTriple.ext <;> dsimp [add]
    all_goals exact add_assoc _ _ _
  zero_add T := by
    apply TrialityTriple.ext <;> dsimp [zero, add]
    all_goals exact zero_add _
  add_zero T := by
    apply TrialityTriple.ext <;> dsimp [zero, add]
    all_goals exact add_zero _
  neg_add_cancel T := by
    apply TrialityTriple.ext <;> dsimp [neg, add]
    all_goals exact neg_add_cancel _
  add_comm T U := by
    apply TrialityTriple.ext <;> dsimp [add]
    all_goals exact add_comm _ _

noncomputable instance : Module R (TrialityTriple mul) where
  one_smul T := by
    apply TrialityTriple.ext <;> dsimp [smul]
    all_goals exact one_smul _ _
  mul_smul r s T := by
    apply TrialityTriple.ext <;> dsimp [smul]
    all_goals exact mul_smul _ _ _
  smul_zero r := by
    apply TrialityTriple.ext <;> dsimp [smul, zero]
    all_goals exact smul_zero _
  smul_add r T U := by
    apply TrialityTriple.ext <;> dsimp [smul, add]
    all_goals exact smul_add _ _ _
  add_smul r s T := by
    apply TrialityTriple.ext <;> dsimp [smul, add]
    all_goals exact add_smul _ _ _
  zero_smul T := by
    apply TrialityTriple.ext <;> dsimp [smul]
    all_goals exact zero_smul _ _

/-- The ordinary commutator in an endomorphism ring. -/
def endCommutator (S T : Module.End R A) : Module.End R A :=
  S * T - T * S

theorem endCommutator_jacobi (S T U : Module.End R A) :
    endCommutator (endCommutator S T) U +
        endCommutator (endCommutator T U) S +
        endCommutator (endCommutator U S) T = 0 := by
  simp only [endCommutator]
  noncomm_ring

/-- Componentwise commutator of two triality triples. -/
def commutator (T U : TrialityTriple mul) : TrialityTriple mul where
  t₁ := T.t₁ * U.t₁ - U.t₁ * T.t₁
  t₂ := T.t₂ * U.t₂ - U.t₂ * T.t₂
  t₃ := T.t₃ * U.t₃ - U.t₃ * T.t₃
  triality := by
    intro x y
    change
      T.t₁ (U.t₁ (mul x y)) - U.t₁ (T.t₁ (mul x y)) =
        mul (T.t₂ (U.t₂ x) - U.t₂ (T.t₂ x)) y +
          mul x (T.t₃ (U.t₃ y) - U.t₃ (T.t₃ y))
    calc
      _ = T.t₁ (mul (U.t₂ x) y + mul x (U.t₃ y)) -
          U.t₁ (mul (T.t₂ x) y + mul x (T.t₃ y)) := by
            rw [U.triality x y, T.triality x y]
      _ = (mul (T.t₂ (U.t₂ x)) y +
            mul (U.t₂ x) (T.t₃ y) +
            mul (T.t₂ x) (U.t₃ y) +
            mul x (T.t₃ (U.t₃ y))) -
          (mul (U.t₂ (T.t₂ x)) y +
            mul (T.t₂ x) (U.t₃ y) +
            mul (U.t₂ x) (T.t₃ y) +
            mul x (U.t₃ (T.t₃ y))) := by
              simp only [map_add]
              rw [T.triality (U.t₂ x) y, T.triality x (U.t₃ y),
                U.triality (T.t₂ x) y, U.triality x (T.t₃ y)]
              abel
      _ = _ := by
            have h₁ :
                mul (T.t₂ (U.t₂ x) - U.t₂ (T.t₂ x)) y =
                  mul (T.t₂ (U.t₂ x)) y -
                    mul (U.t₂ (T.t₂ x)) y := by
              exact congrArg (fun f : A →ₗ[R] A => f y)
                (mul.map_sub _ _)
            have h₂ :
                mul x (T.t₃ (U.t₃ y) - U.t₃ (T.t₃ y)) =
                  mul x (T.t₃ (U.t₃ y)) -
                    mul x (U.t₃ (T.t₃ y)) := by
              exact (mul x).map_sub _ _
            rw [h₁, h₂]
            abel

@[simp] theorem commutator_t₁ (T U : TrialityTriple mul) :
    (commutator T U).t₁ = T.t₁ * U.t₁ - U.t₁ * T.t₁ := rfl

@[simp] theorem commutator_t₂ (T U : TrialityTriple mul) :
    (commutator T U).t₂ = T.t₂ * U.t₂ - U.t₂ * T.t₂ := rfl

@[simp] theorem commutator_t₃ (T U : TrialityTriple mul) :
    (commutator T U).t₃ = T.t₃ * U.t₃ - U.t₃ * T.t₃ := rfl

theorem commutator_skew (T U : TrialityTriple mul) :
    commutator T U = -commutator U T := by
  apply TrialityTriple.ext
  · change T.t₁ * U.t₁ - U.t₁ * T.t₁ =
      -(U.t₁ * T.t₁ - T.t₁ * U.t₁)
    noncomm_ring
  · change T.t₂ * U.t₂ - U.t₂ * T.t₂ =
      -(U.t₂ * T.t₂ - T.t₂ * U.t₂)
    noncomm_ring
  · change T.t₃ * U.t₃ - U.t₃ * T.t₃ =
      -(U.t₃ * T.t₃ - T.t₃ * U.t₃)
    noncomm_ring

theorem commutator_self (T : TrialityTriple mul) :
    commutator T T = 0 := by
  apply TrialityTriple.ext <;> change _ = 0
  all_goals simp [commutator]

theorem commutator_add_left (T U V : TrialityTriple mul) :
    commutator (T + U) V = commutator T V + commutator U V := by
  apply TrialityTriple.ext
  · change (T.t₁ + U.t₁) * V.t₁ - V.t₁ * (T.t₁ + U.t₁) =
      (T.t₁ * V.t₁ - V.t₁ * T.t₁) +
        (U.t₁ * V.t₁ - V.t₁ * U.t₁)
    noncomm_ring
  · change (T.t₂ + U.t₂) * V.t₂ - V.t₂ * (T.t₂ + U.t₂) =
      (T.t₂ * V.t₂ - V.t₂ * T.t₂) +
        (U.t₂ * V.t₂ - V.t₂ * U.t₂)
    noncomm_ring
  · change (T.t₃ + U.t₃) * V.t₃ - V.t₃ * (T.t₃ + U.t₃) =
      (T.t₃ * V.t₃ - V.t₃ * T.t₃) +
        (U.t₃ * V.t₃ - V.t₃ * U.t₃)
    noncomm_ring

theorem commutator_add_right (T U V : TrialityTriple mul) :
    commutator T (U + V) = commutator T U + commutator T V := by
  apply TrialityTriple.ext
  · change T.t₁ * (U.t₁ + V.t₁) - (U.t₁ + V.t₁) * T.t₁ =
      (T.t₁ * U.t₁ - U.t₁ * T.t₁) +
        (T.t₁ * V.t₁ - V.t₁ * T.t₁)
    noncomm_ring
  · change T.t₂ * (U.t₂ + V.t₂) - (U.t₂ + V.t₂) * T.t₂ =
      (T.t₂ * U.t₂ - U.t₂ * T.t₂) +
        (T.t₂ * V.t₂ - V.t₂ * T.t₂)
    noncomm_ring
  · change T.t₃ * (U.t₃ + V.t₃) - (U.t₃ + V.t₃) * T.t₃ =
      (T.t₃ * U.t₃ - U.t₃ * T.t₃) +
        (T.t₃ * V.t₃ - V.t₃ * T.t₃)
    noncomm_ring

theorem commutator_smul_left (r : R) (T U : TrialityTriple mul) :
    commutator (r • T) U = r • commutator T U := by
  apply TrialityTriple.ext
  · change (r • T.t₁) * U.t₁ - U.t₁ * (r • T.t₁) =
      r • (T.t₁ * U.t₁ - U.t₁ * T.t₁)
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub]
  · change (r • T.t₂) * U.t₂ - U.t₂ * (r • T.t₂) =
      r • (T.t₂ * U.t₂ - U.t₂ * T.t₂)
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub]
  · change (r • T.t₃) * U.t₃ - U.t₃ * (r • T.t₃) =
      r • (T.t₃ * U.t₃ - U.t₃ * T.t₃)
    simp only [smul_mul_assoc, mul_smul_comm, smul_sub]

theorem commutator_smul_right (r : R) (T U : TrialityTriple mul) :
    commutator T (r • U) = r • commutator T U := by
  apply TrialityTriple.ext
  · change T.t₁ * (r • U.t₁) - (r • U.t₁) * T.t₁ =
      r • (T.t₁ * U.t₁ - U.t₁ * T.t₁)
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  · change T.t₂ * (r • U.t₂) - (r • U.t₂) * T.t₂ =
      r • (T.t₂ * U.t₂ - U.t₂ * T.t₂)
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  · change T.t₃ * (r • U.t₃) - (r • U.t₃) * T.t₃ =
      r • (T.t₃ * U.t₃ - U.t₃ * T.t₃)
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

theorem commutator_neg_left (T U : TrialityTriple mul) :
    commutator (-T) U = -commutator T U := by
  apply TrialityTriple.ext
  · change (-T.t₁) * U.t₁ - U.t₁ * (-T.t₁) =
      -(T.t₁ * U.t₁ - U.t₁ * T.t₁)
    noncomm_ring
  · change (-T.t₂) * U.t₂ - U.t₂ * (-T.t₂) =
      -(T.t₂ * U.t₂ - U.t₂ * T.t₂)
    noncomm_ring
  · change (-T.t₃) * U.t₃ - U.t₃ * (-T.t₃) =
      -(T.t₃ * U.t₃ - U.t₃ * T.t₃)
    noncomm_ring

theorem commutator_neg_right (T U : TrialityTriple mul) :
    commutator T (-U) = -commutator T U := by
  apply TrialityTriple.ext
  · change T.t₁ * (-U.t₁) - (-U.t₁) * T.t₁ =
      -(T.t₁ * U.t₁ - U.t₁ * T.t₁)
    noncomm_ring
  · change T.t₂ * (-U.t₂) - (-U.t₂) * T.t₂ =
      -(T.t₂ * U.t₂ - U.t₂ * T.t₂)
    noncomm_ring
  · change T.t₃ * (-U.t₃) - (-U.t₃) * T.t₃ =
      -(T.t₃ * U.t₃ - U.t₃ * T.t₃)
    noncomm_ring
theorem commutator_jacobi (T U V : TrialityTriple mul) :
    commutator (commutator T U) V +
        commutator (commutator U V) T +
        commutator (commutator V T) U = 0 := by
  apply TrialityTriple.ext <;> dsimp [commutator, zero, add]
  · exact endCommutator_jacobi T.t₁ U.t₁ V.t₁
  · exact endCommutator_jacobi T.t₂ U.t₂ V.t₂
  · exact endCommutator_jacobi T.t₃ U.t₃ V.t₃

noncomputable instance : LieRing (TrialityTriple mul) where
  bracket := commutator
  add_lie := commutator_add_left
  lie_add := commutator_add_right
  lie_self := commutator_self
  leibniz_lie := by
    intro T U V
    have h := commutator_jacobi T U V
    rw [commutator_skew (commutator U V) T] at h
    rw [commutator_skew V T, commutator_neg_left] at h
    rw [commutator_skew (commutator T V) U] at h
    have h' := congrArg (fun X => -X) h
    simp only [neg_zero] at h'
    have h'' :
        commutator T (commutator U V) -
            (commutator (commutator T U) V +
              commutator U (commutator T V)) = 0 := by
      calc
        _ = -commutator (commutator T U) V +
              (commutator T (commutator U V) -
                commutator U (commutator T V)) := by abel
        _ = 0 := by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    exact sub_eq_zero.mp h''

noncomputable instance : LieAlgebra R (TrialityTriple mul) :=
  LieAlgebra.mk (by
    intro r T U
    exact commutator_smul_right r T U)

end TrialityTriple

end InfoGeometry.Exceptional.CompositionTriality
