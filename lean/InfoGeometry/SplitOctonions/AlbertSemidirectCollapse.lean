import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace InfoGeometry.AlbertSemidirectCollapse

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R]

/-! ### 1. Октонионен модел: Разцепване на 1D реална и 7D имагинерна част -/

/-- Октонион над пръстен R, представен чрез скаларна реална част и 7 имагинерни координати. -/
@[ext]
structure Octonion (R : Type*) where
  re : R
  im : Fin 7 → R

/-- Чисто имагинерен октонион (реалната част е строго 0). -/
def isPureImaginary (o : Octonion R) : Prop :=
  o.re = 0

/-! ### 2. Алгебра на Алберт: 27-измерно представяне -/

/-- Елемент от 27-измерната Алгебра на Алберт J₃(𝕆). -/
@[ext]
structure AlbertMatrix (R : Type*) where
  diag : Fin 3 → R
  off : Fin 3 → Octonion R

/-! ### 3. 21D Неасоциативен Идеал и 6D Реално Симетрично Пространство -/

/-- 21-измерният имагинерен идеал I: Състои се от 3 чисто имагинерни октониона (3 × 7 = 21 дименсии). -/
@[ext]
structure ImaginaryIdeal21 (R : Type*) where
  off_im : Fin 3 → Fin 7 → R

/-- 6-измерното реално симетрично пространство Sym₃(R). -/
@[ext]
structure RealSymmetricMatrix3 (R : Type*) where
  diag : Fin 3 → R
  off : Fin 3 → R

/-- Полудиректно разцепване на Алгебрата на Алберт: J₃(𝕆) ≅ I₂₁ ⋊ Sym₃(R). -/
@[ext]
structure AlbertSemidirectProduct (R : Type*) where
  ideal : ImaginaryIdeal21 R
  symm : RealSymmetricMatrix3 R

/-! ### 4. Каноничен Изоморфизъм на Разцепването -/

/-- Разцепване на AlbertMatrix в полудиректната двойка. -/
def toSemidirect (M : AlbertMatrix R) : AlbertSemidirectProduct R :=
  { ideal := { off_im := fun i => (M.off i).im }
    symm := { diag := M.diag, off := fun i => (M.off i).re } }

/-- Реконструкция на пълната матрица. -/
def fromSemidirect (p : AlbertSemidirectProduct R) : AlbertMatrix R :=
  { diag := p.symm.diag
    off := fun i => { re := p.symm.off i, im := p.ideal.off_im i } }

/-- Изоморфизъм: Обратно действие отляво. -/
theorem toSemidirect_left_inv (M : AlbertMatrix R) :
    fromSemidirect (toSemidirect M) = M := by
  ext i <;> rfl

/-- Изоморфизъм: Обратно действие отдясно. -/
theorem toSemidirect_right_inv (p : AlbertSemidirectProduct R) :
    toSemidirect (fromSemidirect p) = p := by
  ext i <;> rfl

/-! ### 5. Оператор за Асоциативен Колапс (Фактор-Проекция) -/

def associativeCollapse (M : AlbertMatrix R) : RealSymmetricMatrix3 R :=
  (toSemidirect M).symm

def inCollapseKernel (M : AlbertMatrix R) : Prop :=
  associativeCollapse M = { diag := fun _ => 0, off := fun _ => 0 }

theorem collapse_kernel_is_pure_imaginary (M : AlbertMatrix R) :
    inCollapseKernel M ↔ (∀ i, M.diag i = 0) ∧ (∀ i, isPureImaginary (M.off i)) := by
  dsimp [inCollapseKernel, associativeCollapse, toSemidirect, isPureImaginary]
  constructor
  · intro h
    have h_diag : (fun i => M.diag i) = (fun _ => 0) := by
      have := congr_arg RealSymmetricMatrix3.diag h
      exact this
    have h_off : (fun i => (M.off i).re) = (fun _ => 0) := by
      have := congr_arg RealSymmetricMatrix3.off h
      exact this
    refine ⟨fun i => congr_fun h_diag i, fun i => congr_fun h_off i⟩
  · rintro ⟨h_diag, h_off⟩
    congr
    · funext i; exact h_diag i
    · funext i; exact h_off i

/-! ### 6. Зануляване на Асоциатора в Колабирания Образ -/

def toMatrix3 (S : RealSymmetricMatrix3 R) : Matrix (Fin 3) (Fin 3) R :=
  !![S.diag 0, S.off 0,  S.off 2;
     S.off 0,  S.diag 1, S.off 1;
     S.off 2,  S.off 1,  S.diag 2]

def matrixAssociator (A B C : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  (A * B) * C - A * (B * C)

theorem collapsed_associator_vanishes (A B C : RealSymmetricMatrix3 R) :
    matrixAssociator (toMatrix3 A) (toMatrix3 B) (toMatrix3 C) = 0 := by
  dsimp [matrixAssociator]
  rw [Matrix.mul_assoc, sub_self]

theorem collapse_annihilates_associator (M₁ M₂ M₃ : AlbertMatrix R) :
    let S₁ := associativeCollapse M₁
    let S₂ := associativeCollapse M₂
    let S₃ := associativeCollapse M₃
    matrixAssociator (toMatrix3 S₁) (toMatrix3 S₂) (toMatrix3 S₃) = 0 := by
  change matrixAssociator
    (toMatrix3 (associativeCollapse M₁))
    (toMatrix3 (associativeCollapse M₂))
    (toMatrix3 (associativeCollapse M₃)) = 0
  exact collapsed_associator_vanishes _ _ _

end InfoGeometry.AlbertSemidirectCollapse
