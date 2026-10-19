/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

/-!
# Раздел 124: Спектрална Дуалност на Грам, Теорема на Кейли–Хамилтон и Проектор на Мур–Пенроуз в Cℓ(1,1)
Target: `InfoGeometry/QuantumContext/FresnelGramMoorePenroseProjector.lean`
Ref: `QMS-DIR-SEC124-GRAM-MOORE-PENROSE-CL11-2026-OCT-16`

Разширява изоморфизма от Раздел 122 (`FresnelCl11MatrixIsomorphism.lean`) и доказва:
1. Изоспектралност на левия проектор на Грам G_L = M · Mᵀ (базис на процепите)
   и десния проектор на Грам G_R = Mᵀ · M (базис на Френеловите квадратури):
   Tr(G_L) = Tr(G_R) = I_+ + I_-   и   det(G_L) = det(G_R) = H_{(+,-)}².
2. Симплектично тъждество на адюнкта adj(M) в Cℓ(1,1):
   M · adj(M) = adj(M) · M = H_{(+,-)} · 𝟙₂,
   откъдето в центъра x = 0 (ψ_+ = ψ_- = ψ₀) матрицата M е точен делител на нулата:
   M(ψ₀, ψ₀) · adj(M(ψ₀, ψ₀)) = 0!
3. Теорема на Кейли–Хамилтон за матрицата на Грам G_L:
   G_L² = (I_+ + I_-) · G_L - H_{(+,-)}² · 𝟙₂.
4. Редукция до идемпотентен проектор на Мур–Пенроуз / Дразин в центъра x = 0:
   G_L(ψ₀, ψ₀)² = (2 I₀) · G_L(ψ₀, ψ₀).
5. Индекс-свободна формула за вероятността на Ахаронов–Бом чрез оператора на размяна σ₁:
   P_AB = Tr((𝟙₂ + c · σ₁) · G_L) + 2 s · det(M).
-/

namespace InfoGeometry.QuantumContext.FresnelGramProjector

variable {R : Type*} [CommRing R]

/-! ### 1. Френелови Квадратури и Матрична Алгебра Cℓ(1,1) ≅ M₂(R) -/

@[ext]
structure FresnelSlitAmp (R : Type*) where
  cQuad : R
  sQuad : R
  deriving DecidableEq, Repr, Inhabited

namespace FresnelSlitAmp

variable {R : Type*} [CommRing R]

def canonicalFresnelSlitAmpInt : FresnelSlitAmp ℤ := ⟨3, 4⟩

theorem canonicalFresnelSlitAmpInt_nondegenerate :
    canonicalFresnelSlitAmpInt ≠ default := by decide

def intensity (ψ : FresnelSlitAmp R) : R :=
  ψ.cQuad * ψ.cQuad + ψ.sQuad * ψ.sQuad

def yangSymmetricG (ψ_pos ψ_neg : FresnelSlitAmp R) : R :=
  ψ_pos.cQuad * ψ_neg.cQuad + ψ_pos.sQuad * ψ_neg.sQuad

def yinSymplecticH (ψ_pos ψ_neg : FresnelSlitAmp R) : R :=
  ψ_pos.cQuad * ψ_neg.sQuad - ψ_pos.sQuad * ψ_neg.cQuad

theorem yinSymplecticH_noncommutative_int :
    ∃ ψ₁ ψ₂ : FresnelSlitAmp ℤ, yinSymplecticH ψ₁ ψ₂ ≠ yinSymplecticH ψ₂ ψ₁ :=
  ⟨⟨1, 0⟩, ⟨0, 1⟩, by decide⟩

end FresnelSlitAmp

@[ext]
structure Cl11Op (R : Type*) where
  m11 : R
  m12 : R
  m21 : R
  m22 : R
  deriving DecidableEq, Repr, Inhabited

namespace Cl11Op

variable {R : Type*} [CommRing R]

def canonicalCl11OpInt : Cl11Op ℤ := ⟨1, 2, 3, 4⟩

theorem canonicalCl11OpInt_nondegenerate :
    canonicalCl11OpInt ≠ default := by decide

def zero : Cl11Op R := ⟨0, 0, 0, 0⟩
def one  : Cl11Op R := ⟨1, 0, 0, 1⟩

/-- Оператор на Паули–Клифорд σ₁ за размяна на двата процепа (+ ↔ -). -/
def sigma1 : Cl11Op R := ⟨0, 1, 1, 0⟩

def add (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 + B.m11, A.m12 + B.m12, A.m21 + B.m21, A.m22 + B.m22⟩

def sub (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 - B.m11, A.m12 - B.m12, A.m21 - B.m21, A.m22 - B.m22⟩

def scale (c : R) (A : Cl11Op R) : Cl11Op R :=
  ⟨c * A.m11, c * A.m12, c * A.m21, c * A.m22⟩

def mul (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 * B.m11 + A.m12 * B.m21,
   A.m11 * B.m12 + A.m12 * B.m22,
   A.m21 * B.m11 + A.m22 * B.m21,
   A.m21 * B.m12 + A.m22 * B.m22⟩

theorem mul_noncommutative_int :
    ∃ A B : Cl11Op ℤ, mul A B ≠ mul B A :=
  ⟨⟨0, 1, 1, 0⟩, ⟨1, 0, 0, -1⟩, by decide⟩

def transpose (A : Cl11Op R) : Cl11Op R :=
  ⟨A.m11, A.m21, A.m12, A.m22⟩

/-- Класически симплектичен адюнкт (кофакторна транспонирана матрица) в M₂(R). -/
def adjugate (A : Cl11Op R) : Cl11Op R :=
  ⟨A.m22, -A.m12, -A.m21, A.m11⟩

def trace (A : Cl11Op R) : R :=
  A.m11 + A.m22

def det (A : Cl11Op R) : R :=
  A.m11 * A.m22 - A.m12 * A.m21

/-- Влагане на двойката амплитуди на Френел в Cℓ(1,1). -/
def embedFresnelPair (ψ_pos ψ_neg : FresnelSlitAmp R) : Cl11Op R :=
  ⟨ψ_pos.cQuad, ψ_pos.sQuad, ψ_neg.cQuad, ψ_neg.sQuad⟩

/-- Ляв оператор на Грам G_L = M · Mᵀ (действащ в базиса на процепите +, -). -/
def leftGram (ψ_pos ψ_neg : FresnelSlitAmp R) : Cl11Op R :=
  let M := embedFresnelPair ψ_pos ψ_neg
  mul M (transpose M)

/-- Десен оператор на Грам G_R = Mᵀ · M (действащ в базиса на квадратурите C, S). -/
def rightGram (ψ_pos ψ_neg : FresnelSlitAmp R) : Cl11Op R :=
  let M := embedFresnelPair ψ_pos ψ_neg
  mul (transpose M) M

/-! ### 2. Теорема 1: Изоспектралност на Левия и Десния Проектор на Грам -/

/-- Левият и десният оператор на Грам имат тъждествено равна следа I_+ + I_-. -/
theorem left_right_gram_trace_eq (ψ_pos ψ_neg : FresnelSlitAmp R) :
    trace (leftGram ψ_pos ψ_neg) = trace (rightGram ψ_pos ψ_neg) ∧
    trace (leftGram ψ_pos ψ_neg) =
      FresnelSlitAmp.intensity ψ_pos + FresnelSlitAmp.intensity ψ_neg := by
  constructor
  · dsimp [leftGram, rightGram, embedFresnelPair, mul, transpose, trace]
    ring
  · dsimp [leftGram, embedFresnelPair, mul, transpose, trace, FresnelSlitAmp.intensity]

/-- Левият и десният оператор на Грам имат тъждествено равна детерминанта H_{(+,-)}². -/
theorem left_right_gram_det_eq (ψ_pos ψ_neg : FresnelSlitAmp R) :
    det (leftGram ψ_pos ψ_neg) = det (rightGram ψ_pos ψ_neg) ∧
    det (leftGram ψ_pos ψ_neg) =
      FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg *
        FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg := by
  constructor
  · dsimp [leftGram, rightGram, embedFresnelPair, mul, transpose, det]
    ring
  · dsimp [leftGram, embedFresnelPair, mul, transpose, det, FresnelSlitAmp.yinSymplecticH]
    ring

/-! ### 3. Теорема 2: Симплектичен Адюнкт и Светлинен Делител на Нулата в Центъра x = 0 -/

/--
За всяка двойка процепи произведението на M със симплектичния ѝ адюнкт adj(M)
е скаларно кратно на единичния оператор, претеглено с Ин холономията H_{(+,-)}:
M · adj(M) = H_{(+,-)} · 𝟙₂   и   adj(M) · M = H_{(+,-)} · 𝟙₂.
-/
theorem mul_adjugate_eq_yin_smul_one (ψ_pos ψ_neg : FresnelSlitAmp R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    mul M (adjugate M) = scale (FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg) one ∧
    mul (adjugate M) M = scale (FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg) one := by
  constructor
  · dsimp [embedFresnelPair, mul, adjugate, scale, one, FresnelSlitAmp.yinSymplecticH]
    ext <;> ring
  · dsimp [embedFresnelPair, mul, adjugate, scale, one, FresnelSlitAmp.yinSymplecticH]
    ext <;> ring

/--
В симетричния център на екрана x = 0 (ψ_+ = ψ_- = ψ₀), матрицата на Френел M(ψ₀, ψ₀)
се анулира от собствения си симплектичен адюнкт (точен делител на нулата в Cℓ(1,1)):
M(ψ₀, ψ₀) · adj(M(ψ₀, ψ₀)) = 0!
-/
theorem origin_fresnel_matrix_is_zero_divisor (ψ₀ : FresnelSlitAmp R) :
    let M₀ := embedFresnelPair ψ₀ ψ₀
    mul M₀ (adjugate M₀) = zero ∧ mul (adjugate M₀) M₀ = zero := by
  constructor
  · dsimp [embedFresnelPair, mul, adjugate, zero]
    ext <;> ring
  · dsimp [embedFresnelPair, mul, adjugate, zero]
    ext <;> ring

/-! ### 4. Теорема 3: Кейли–Хамилтон и Идемпотентен Проектор на Мур–Пенроуз при x = 0 -/

/--
Теорема на Кейли–Хамилтон за матрицата на Грам G_L:
G_L² = (I_+ + I_-) · G_L - H_{(+,-)}² · 𝟙₂.
-/
theorem gram_cayley_hamilton_identity (ψ_pos ψ_neg : FresnelSlitAmp R) :
    let G_L := leftGram ψ_pos ψ_neg
    let I_sum := FresnelSlitAmp.intensity ψ_pos + FresnelSlitAmp.intensity ψ_neg
    let H_sq := FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg *
                  FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg
    mul G_L G_L = sub (scale I_sum G_L) (scale H_sq one) := by
  dsimp [leftGram, embedFresnelPair, mul, transpose, sub, scale, one,
         FresnelSlitAmp.intensity, FresnelSlitAmp.yinSymplecticH]
  ext <;> ring

/--
Редукция до Идемпотентен Проектор на Мур–Пенроуз / Дразин в центъра x = 0:
В симетричния център (ψ_+ = ψ_- = ψ₀), където H_{(+,-)} = 0 и I_+ = I_- = I₀,
матрицата на Грам удовлетворява точното идемпотентно уравнение на проектор:
G_L(ψ₀, ψ₀)² = (2 I₀) · G_L(ψ₀, ψ₀)!
-/
theorem origin_gram_is_scaled_idempotent_projector (ψ₀ : FresnelSlitAmp R) :
    let G₀ := leftGram ψ₀ ψ₀
    mul G₀ G₀ = scale (2 * FresnelSlitAmp.intensity ψ₀) G₀ := by
  dsimp [leftGram, embedFresnelPair, mul, transpose, scale, FresnelSlitAmp.intensity]
  ext <;> ring

/-! ### 5. Теорема 4: Индекс-Свободна Следова Формула за Вероятността на Ахаронов–Бом -/

/-- Следата на σ₁ · G_L изолира точно удвоената симетрична Ян интерференция 2 G_{(+,-)}. -/
@[simp]
theorem trace_sigma1_mul_gram_eq_two_yang (ψ_pos ψ_neg : FresnelSlitAmp R) :
    trace (mul sigma1 (leftGram ψ_pos ψ_neg)) =
      2 * FresnelSlitAmp.yangSymmetricG ψ_pos ψ_neg := by
  dsimp [sigma1, leftGram, embedFresnelPair, mul, transpose, trace,
         FresnelSlitAmp.yangSymmetricG]
  ring

/--
Пълната преходна вероятност на Ахаронов–Бом P_AB се записва изцяло чрез
следата на оператора на Грам G_L и детерминантата на M:
P_AB = Tr((𝟙₂ + c · σ₁) · G_L) + 2 s · det(M).
-/
theorem ab_prob_index_free_trace_formula (ψ_pos ψ_neg : FresnelSlitAmp R) (c s : R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    let G_L := leftGram ψ_pos ψ_neg
    trace (mul (add one (scale c sigma1)) G_L) + 2 * s * det M =
      FresnelSlitAmp.intensity ψ_pos + FresnelSlitAmp.intensity ψ_neg +
      2 * c * FresnelSlitAmp.yangSymmetricG ψ_pos ψ_neg +
      2 * s * FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg := by
  dsimp [embedFresnelPair, leftGram, one, sigma1, add, scale, mul, transpose, trace, det,
         FresnelSlitAmp.intensity, FresnelSlitAmp.yangSymmetricG, FresnelSlitAmp.yinSymplecticH]
  ring

end Cl11Op

/-! ### 6. Главен Синтез на Раздел 124 -/

theorem fresnel_gram_projector_synthesis
    (ψ_pos ψ_neg ψ₀ : FresnelSlitAmp R) (c s : R) :
    (Cl11Op.trace (Cl11Op.leftGram ψ_pos ψ_neg) = Cl11Op.trace (Cl11Op.rightGram ψ_pos ψ_neg) ∧
     Cl11Op.det (Cl11Op.leftGram ψ_pos ψ_neg) = Cl11Op.det (Cl11Op.rightGram ψ_pos ψ_neg)) ∧
    Cl11Op.mul (Cl11Op.embedFresnelPair ψ₀ ψ₀) (Cl11Op.adjugate (Cl11Op.embedFresnelPair ψ₀ ψ₀)) =
      Cl11Op.zero ∧
    Cl11Op.mul (Cl11Op.leftGram ψ₀ ψ₀) (Cl11Op.leftGram ψ₀ ψ₀) =
      Cl11Op.scale (2 * FresnelSlitAmp.intensity ψ₀) (Cl11Op.leftGram ψ₀ ψ₀) ∧
    Cl11Op.trace
        (Cl11Op.mul (Cl11Op.add Cl11Op.one (Cl11Op.scale c Cl11Op.sigma1))
          (Cl11Op.leftGram ψ_pos ψ_neg)) +
      2 * s * Cl11Op.det (Cl11Op.embedFresnelPair ψ_pos ψ_neg) =
      FresnelSlitAmp.intensity ψ_pos + FresnelSlitAmp.intensity ψ_neg +
      2 * c * FresnelSlitAmp.yangSymmetricG ψ_pos ψ_neg +
      2 * s * FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg :=
  ⟨⟨(Cl11Op.left_right_gram_trace_eq ψ_pos ψ_neg).1,
    (Cl11Op.left_right_gram_det_eq ψ_pos ψ_neg).1⟩,
   (Cl11Op.origin_fresnel_matrix_is_zero_divisor ψ₀).1,
   Cl11Op.origin_gram_is_scaled_idempotent_projector ψ₀,
   Cl11Op.ab_prob_index_free_trace_formula ψ_pos ψ_neg c s⟩

end InfoGeometry.QuantumContext.FresnelGramProjector
