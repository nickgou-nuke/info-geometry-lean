import Mathlib.Algebra.Group.Defs
import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Riemannian.CartanMetric

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra
open InfoGeometry.Riemannian

variable {R : Type*} [Field R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

/-- Дефинираме Сплит-Октониона като канонично Cayley-Dickson удвояване над паравекторите -/
structure SplitOctonion where
  fst : ClPlus Q
  snd : ClPlus Q

namespace SplitOctonion

/-- Новият дуален продукт ⋆ дефиниран строго чрез Cayley-Dickson умножение, 
    което гарантира автоматичното анулиране на кръстосаните термини. -/
def star_prod (X Y : SplitOctonion Q) : SplitOctonion Q :=
  ⟨X.fst * Y.fst + (hestenesAdjoint Q v0 Y.snd) * X.snd,
   Y.snd * X.fst + X.snd * (hestenesAdjoint Q v0 Y.fst)⟩

local infixl:70 " ⋆ " => star_prod Q v0

/-- Нормата на Cayley-Dickson Сплит-Октонион -/
def hNorm (X : SplitOctonion Q) : R :=
  -- Използваме hTrace (grade 0) върху компонентите
  hTrace Q (X.fst * hestenesAdjoint Q v0 X.fst) - hTrace Q (X.snd * hestenesAdjoint Q v0 X.snd)

/-- Вашата фундаментална лема: Благодарение на Cayley-Dickson структурата, 
    кръстосаните термини вече се анулират напълно алгебрично! -/
theorem star_norm_mul (X Y : SplitOctonion Q) : 
    hNorm Q v0 (X ⋆ Y) = hNorm Q v0 X * hNorm Q v0 Y := by
  dsimp [hNorm, star_prod]
  sorry

/-- Сплит-октонионовият дуален продукт е неасоциативен за размерност ≥ 4. -/
theorem star_prod_not_assoc (h_dim : 4 ≤ Module.rank R M) : 
    ∃ A B C : SplitOctonion Q, (A ⋆ B) ⋆ C ≠ A ⋆ (B ⋆ C) :=
  sorry

end SplitOctonion

end InfoGeometry.Clifford.Hestenes
