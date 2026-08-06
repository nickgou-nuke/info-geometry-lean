import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Riemannian.CartanMetric
import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Riemannian.ConeAction

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]

open InfoGeometry.Clifford.Hestenes
open CliffordAlgebra
open InfoGeometry.Riemannian

/-- Дефинираме Сплит-Октониона като канонично Cayley-Dickson удвояване над паравекторите -/
structure SplitOctonion (Q : QuadraticForm R M) (v0 : M) where
  fst : evenOdd Q 0
  snd : evenOdd Q 0

namespace SplitOctonion

variable {Q : QuadraticForm R M} {v0 : M}

/-- Новият дуален продукт ⋆ дефиниран строго чрез Cayley-Dickson умножение -/
def star_prod (X Y : SplitOctonion Q v0) : SplitOctonion Q v0 :=
  ⟨X.fst * Y.fst + (hestenesAdjoint Q v0 Y.snd) * X.snd, 
   Y.snd * X.fst + X.snd * (hestenesAdjoint Q v0 Y.fst)⟩

/-- Нормата на Cayley-Dickson Сплит-Октонион -/
noncomputable def hNorm (X : SplitOctonion Q v0) : R :=
  InfoGeometry.Riemannian.hTrace Q (X.fst * hestenesAdjoint Q v0 X.fst) - 
  InfoGeometry.Riemannian.hTrace Q (X.snd * hestenesAdjoint Q v0 X.snd)

end SplitOctonion
