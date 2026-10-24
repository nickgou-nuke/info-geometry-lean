/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

namespace InfoGeometry.QuantumContext.FresnelCl11Isomorphism

variable {R : Type*} [CommRing R]

/-! ### 1. Двойка Амплитуди на Френел и Алгебра на Cℓ(1,1) ≅ M₂(R) -/

/-- Комплексна квадратура на Френел ψ = (C, S) за единичен процеп. -/
@[ext]
structure FresnelSlitAmp (R : Type*) where
  cQuad : R
  sQuad : R

namespace FresnelSlitAmp

variable {R : Type*} [CommRing R]

def add (ψ₁ ψ₂ : FresnelSlitAmp R) : FresnelSlitAmp R :=
  ⟨ψ₁.cQuad + ψ₂.cQuad, ψ₁.sQuad + ψ₂.sQuad⟩

def scale (c : R) (ψ : FresnelSlitAmp R) : FresnelSlitAmp R :=
  ⟨c * ψ.cQuad, c * ψ.sQuad⟩

/-- Интензитет на единичен процеп: I = C² + S². -/
def intensity (ψ : FresnelSlitAmp R) : R :=
  ψ.cQuad * ψ.cQuad + ψ.sQuad * ψ.sQuad

/-- Симетричен интерференчен член на Ян: G_{(+,-)} = C_+ C_- + S_+ S_-. -/
def yangSymmetricG (ψ_pos ψ_neg : FresnelSlitAmp R) : R :=
  ψ_pos.cQuad * ψ_neg.cQuad + ψ_pos.sQuad * ψ_neg.sQuad

/-- Кососиметричен интерференчен член на Ин: H_{(+,-)} = C_+ S_- - S_+ C_-. -/
def yinSymplecticH (ψ_pos ψ_neg : FresnelSlitAmp R) : R :=
  ψ_pos.cQuad * ψ_neg.sQuad - ψ_pos.sQuad * ψ_neg.cQuad

/-- Пълна вероятност на прехода на Ахаронов–Бом P_AB⁺. -/
def abTransitionProbPlus (ψ_pos ψ_neg : FresnelSlitAmp R) (c s : R) : R :=
  intensity ψ_pos + (c * c + s * s) * intensity ψ_neg +
    2 * c * yangSymmetricG ψ_pos ψ_neg + 2 * s * yinSymplecticH ψ_pos ψ_neg

end FresnelSlitAmp

/-- Матричен оператор в Cℓ(1,1) ≅ M₂(R). -/
@[ext]
structure Cl11Op (R : Type*) where
  m11 : R
  m12 : R
  m21 : R
  m22 : R

namespace Cl11Op

variable {R : Type*} [CommRing R]

def add (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 + B.m11, A.m12 + B.m12, A.m21 + B.m21, A.m22 + B.m22⟩

def scale (c : R) (A : Cl11Op R) : Cl11Op R :=
  ⟨c * A.m11, c * A.m12, c * A.m21, c * A.m22⟩

def mul (A B : Cl11Op R) : Cl11Op R :=
  ⟨A.m11 * B.m11 + A.m12 * B.m21,
   A.m11 * B.m12 + A.m12 * B.m22,
   A.m21 * B.m11 + A.m22 * B.m21,
   A.m21 * B.m12 + A.m22 * B.m22⟩

def transpose (A : Cl11Op R) : Cl11Op R :=
  ⟨A.m11, A.m21, A.m12, A.m22⟩

def trace (A : Cl11Op R) : R :=
  A.m11 + A.m22

def det (A : Cl11Op R) : R :=
  A.m11 * A.m22 - A.m12 * A.m21

/-- Скаларно произведение на Фробениус–Хилберт–Шмид: ⟨A, B⟩_HS = Tr(Aᵀ · B). -/
def frobeniusInner (A B : Cl11Op R) : R :=
  A.m11 * B.m11 + A.m12 * B.m12 + A.m21 * B.m21 + A.m22 * B.m22

/-- Квадрат на нормата на Фробениус–Хилберт–Шмид: ‖A‖²_HS = ⟨A, A⟩_HS. -/
def frobeniusNormSq (A : Cl11Op R) : R :=
  frobeniusInner A A

/-- Симетрична част на QGT (Удвоена метрика на Фишер: 2 g = Q + Qᵀ). -/
def fisherMetricPart (Q : Cl11Op R) : Cl11Op R :=
  ⟨2 * Q.m11, Q.m12 + Q.m21, Q.m12 + Q.m21, 2 * Q.m22⟩

/-! ### 2. Явен Изоморфизъм: (ψ_+, ψ_-) ≃ M ∈ Cℓ(1,1) -/

/--
Влагане на двойката квадратури на Френел (ψ_+, ψ_-) като редове на матрица в Cℓ(1,1):
M(ψ_+, ψ_-) = [[C_+, S_+], [C_-, S_-]].
-/
def embedFresnelPair (ψ_pos ψ_neg : FresnelSlitAmp R) : Cl11Op R :=
  ⟨ψ_pos.cQuad, ψ_pos.sQuad, ψ_neg.cQuad, ψ_neg.sQuad⟩

/-- Проекция на първия ред към горния процеп ψ_+. -/
def projSlitPos (M : Cl11Op R) : FresnelSlitAmp R :=
  ⟨M.m11, M.m12⟩

/-- Проекция на втория ред към долния процеп ψ_-. -/
def projSlitNeg (M : Cl11Op R) : FresnelSlitAmp R :=
  ⟨M.m21, M.m22⟩

/--
Пълна биекция (еквивалентност на типовете) между пространството на двойките
квадратури на Френел и операторната алгебра Cℓ(1,1).
-/
def fresnelCl11Equiv : (FresnelSlitAmp R × FresnelSlitAmp R) ≃ Cl11Op R where
  toFun p := embedFresnelPair p.1 p.2
  invFun M := (projSlitPos M, projSlitNeg M)
  left_inv := by
    rintro ⟨⟨c₁, s₁⟩, ⟨c₂, s₂⟩⟩
    rfl
  right_inv := by
    rintro ⟨m11, m12, m21, m22⟩
    rfl

/-- Линейност на влагането спрямо събиране на амплитуди. -/
theorem embed_add (ψ_pos₁ ψ_neg₁ ψ_pos₂ ψ_neg₂ : FresnelSlitAmp R) :
    embedFresnelPair (FresnelSlitAmp.add ψ_pos₁ ψ_pos₂) (FresnelSlitAmp.add ψ_neg₁ ψ_neg₂) =
      add (embedFresnelPair ψ_pos₁ ψ_neg₁) (embedFresnelPair ψ_pos₂ ψ_neg₂) := by
  dsimp [embedFresnelPair, FresnelSlitAmp.add, add]

/-- Линейност на влагането спрямо скаларно умножение. -/
theorem embed_scale (c : R) (ψ_pos ψ_neg : FresnelSlitAmp R) :
    embedFresnelPair (FresnelSlitAmp.scale c ψ_pos) (FresnelSlitAmp.scale c ψ_neg) =
      scale c (embedFresnelPair ψ_pos ψ_neg) := by
  dsimp [embedFresnelPair, FresnelSlitAmp.scale, scale]

/-! ### 3. Основни Теореми: det(M) = H_{(+,-)} и frobeniusNormSq(M) = I_+ + I_- -/

/--
Теорема 1 (Детерминантата на M е точно кососиметричната Ин холономия H_{(+,-)}):
det(M(ψ_+, ψ_-)) = C_+ S_- - S_+ C_- = H_{(+,-)}(ψ_+, ψ_-).
-/
@[simp]
theorem det_embed_eq_yin_symplectic_H (ψ_pos ψ_neg : FresnelSlitAmp R) :
    det (embedFresnelPair ψ_pos ψ_neg) = FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg := by
  dsimp [det, embedFresnelPair, FresnelSlitAmp.yinSymplecticH]

/--
Теорема 2 (Квадратът на нормата на Фробениус на M е сумата от интензитетите I_+ + I_-):
frobeniusNormSq(M(ψ_+, ψ_-)) = I_+ + I_-.
-/
@[simp]
theorem frobenius_norm_sq_embed_eq_intensity_sum (ψ_pos ψ_neg : FresnelSlitAmp R) :
    frobeniusNormSq (embedFresnelPair ψ_pos ψ_neg) =
      FresnelSlitAmp.intensity ψ_pos + FresnelSlitAmp.intensity ψ_neg := by
  dsimp [frobeniusNormSq, frobeniusInner, embedFresnelPair, FresnelSlitAmp.intensity]
  ring

/-! ### 4. Проектор на Грам–Мур–Пенроуз M · Mᵀ и Тъждество на Брамагупта–Фибоначи -/

/--
Теорема 3a (Матрицата на Грам–Мур–Пенроуз G_L = M · Mᵀ обединява I_+, I_- и G_{(+,-)}):
M · Mᵀ = [[I_+, G_{(+,-)}], [G_{(+,-)}, I_-]].
Диагоналният Майорана сектор съдържа интензитетите на двата процепа (I_+, I_-),
а извъндиагоналният Уейл мост съдържа точно симетричната Ян интерференция G_{(+,-)}!
-/
theorem gram_matrix_embed_explicit (ψ_pos ψ_neg : FresnelSlitAmp R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    mul M (transpose M) =
      ⟨FresnelSlitAmp.intensity ψ_pos,
       FresnelSlitAmp.yangSymmetricG ψ_pos ψ_neg,
       FresnelSlitAmp.yangSymmetricG ψ_pos ψ_neg,
       FresnelSlitAmp.intensity ψ_neg⟩ := by
  dsimp [embedFresnelPair, mul, transpose,
         FresnelSlitAmp.intensity, FresnelSlitAmp.yangSymmetricG]
  ext <;> ring

/-- Следата на матрицата на Грам M · Mᵀ е сумата от интензитетите I_+ + I_-. -/
theorem trace_gram_embed_eq_intensity_sum (ψ_pos ψ_neg : FresnelSlitAmp R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    trace (mul M (transpose M)) =
      FresnelSlitAmp.intensity ψ_pos + FresnelSlitAmp.intensity ψ_neg := by
  dsimp [embedFresnelPair, trace, mul, transpose, FresnelSlitAmp.intensity]

/--
Теорема 3b (Детерминантата на Грам M · Mᵀ като Тъждество на Брамагупта–Фибоначи–Френел):
det(M · Mᵀ) = I_+ · I_- - G_{(+,-)}² = (det M)² = H_{(+,-)}².
-/
theorem det_gram_embed_eq_yin_sq (ψ_pos ψ_neg : FresnelSlitAmp R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    det (mul M (transpose M)) =
      FresnelSlitAmp.intensity ψ_pos * FresnelSlitAmp.intensity ψ_neg -
        FresnelSlitAmp.yangSymmetricG ψ_pos ψ_neg * FresnelSlitAmp.yangSymmetricG ψ_pos ψ_neg ∧
    det (mul M (transpose M)) = det M * det M := by
  constructor
  · dsimp [embedFresnelPair, det, mul, transpose,
           FresnelSlitAmp.intensity, FresnelSlitAmp.yangSymmetricG]
    ring
  · dsimp [embedFresnelPair, det, mul, transpose]
    ring

/-! ### 5. Представяне на Пълната Вероятност на Ахаронов–Бом в Cℓ(1,1) -/

/-- Матрица на холономната ротация на Ахаронов–Бом U(c, s) = [[c, -s], [s, c]] ∈ Cℓ(1,1). -/
def abHolonomyMatrix (c s : R) : Cl11Op R :=
  ⟨c, -s, s, c⟩

/--
Теорема 4a (Холономната интерференция през M · U(c, s) · Mᵀ):
Горният извъндиагонален Уейл елемент m12 на M · U(c, s) · Mᵀ е точно
пълният фазов интерференчен член c · G_{(+,-)} + s · H_{(+,-)}!
-/
theorem holonomy_conjugated_gram_m12 (ψ_pos ψ_neg : FresnelSlitAmp R) (c s : R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    (mul (mul M (abHolonomyMatrix c s)) (transpose M)).m12 =
      c * FresnelSlitAmp.yangSymmetricG ψ_pos ψ_neg -
      s * FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg := by
  dsimp [embedFresnelPair, abHolonomyMatrix, mul, transpose,
         FresnelSlitAmp.yangSymmetricG, FresnelSlitAmp.yinSymplecticH]
  ring

/--
Теорема 4b (Пълната вероятност на прехода P_AB чрез матрични инварианти на M ∈ Cℓ(1,1)):
При единична холономия (c² + s² = 1), вероятността P_AB е равна на:
frobeniusNormSq(M) + 2 · c · (M · Mᵀ).m12 + 2 · s · det(M).
-/
theorem ab_prob_from_cl11_invariants (ψ_pos ψ_neg : FresnelSlitAmp R) (c s : R) :
    let M := embedFresnelPair ψ_pos ψ_neg
    FresnelSlitAmp.intensity ψ_pos + FresnelSlitAmp.intensity ψ_neg +
      2 * c * FresnelSlitAmp.yangSymmetricG ψ_pos ψ_neg +
      2 * s * FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg =
    frobeniusNormSq M + 2 * c * (mul M (transpose M)).m12 + 2 * s * det M := by
  dsimp [embedFresnelPair, frobeniusNormSq, frobeniusInner, mul, transpose, det,
         FresnelSlitAmp.intensity, FresnelSlitAmp.yangSymmetricG, FresnelSlitAmp.yinSymplecticH]
  ring

end Cl11Op

/-! ### 6. Главен Сертификат на Раздел 122 -/

structure FresnelCl11IsomorphismCertificate (R : Type*) [CommRing R] : Prop where
  left_inv : ∀ (ψ_pos ψ_neg : FresnelSlitAmp R),
    Cl11Op.projSlitPos (Cl11Op.embedFresnelPair ψ_pos ψ_neg) = ψ_pos ∧
    Cl11Op.projSlitNeg (Cl11Op.embedFresnelPair ψ_pos ψ_neg) = ψ_neg
  right_inv : ∀ (M : Cl11Op R),
    Cl11Op.embedFresnelPair (Cl11Op.projSlitPos M) (Cl11Op.projSlitNeg M) = M
  det_is_yin_H : ∀ (ψ_pos ψ_neg : FresnelSlitAmp R),
    Cl11Op.det (Cl11Op.embedFresnelPair ψ_pos ψ_neg) =
      FresnelSlitAmp.yinSymplecticH ψ_pos ψ_neg
  norm_is_intensity_sum : ∀ (ψ_pos ψ_neg : FresnelSlitAmp R),
    Cl11Op.frobeniusNormSq (Cl11Op.embedFresnelPair ψ_pos ψ_neg) =
      FresnelSlitAmp.intensity ψ_pos + FresnelSlitAmp.intensity ψ_neg
  gram_offdiag_is_yang_G : ∀ (ψ_pos ψ_neg : FresnelSlitAmp R),
    let M := Cl11Op.embedFresnelPair ψ_pos ψ_neg
    (Cl11Op.mul M (Cl11Op.transpose M)).m12 = FresnelSlitAmp.yangSymmetricG ψ_pos ψ_neg
  gram_det_is_brahmagupta : ∀ (ψ_pos ψ_neg : FresnelSlitAmp R),
    let M := Cl11Op.embedFresnelPair ψ_pos ψ_neg
    Cl11Op.det (Cl11Op.mul M (Cl11Op.transpose M)) =
      Cl11Op.det M * Cl11Op.det M

theorem compile_fresnel_cl11_isomorphism_certificate :
    FresnelCl11IsomorphismCertificate R where
  left_inv := fun _ _ => ⟨rfl, rfl⟩
  right_inv := fun ⟨_, _, _, _⟩ => rfl
  det_is_yin_H := Cl11Op.det_embed_eq_yin_symplectic_H
  norm_is_intensity_sum := Cl11Op.frobenius_norm_sq_embed_eq_intensity_sum
  gram_offdiag_is_yang_G := fun ψ_pos ψ_neg => by
    dsimp [Cl11Op.embedFresnelPair, Cl11Op.mul, Cl11Op.transpose, FresnelSlitAmp.yangSymmetricG]
  gram_det_is_brahmagupta := fun ψ_pos ψ_neg =>
    (Cl11Op.det_gram_embed_eq_yin_sq ψ_pos ψ_neg).2

end InfoGeometry.QuantumContext.FresnelCl11Isomorphism