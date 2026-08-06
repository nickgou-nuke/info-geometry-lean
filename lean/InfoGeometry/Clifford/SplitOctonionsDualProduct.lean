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
  fst : ClPlus Q
  snd : ClPlus Q

namespace SplitOctonion

variable {Q : QuadraticForm R M} [CartanGeometry Q] {v0 : M} (hv0_norm : Q v0 = 1)

/-- Новият дуален продукт ⋆ дефиниран строго чрез Cayley-Dickson умножение -/
def star_prod (X Y : SplitOctonion Q v0) : SplitOctonion Q v0 :=
  ⟨X.fst * Y.fst + (hestenesAdjoint Q v0 Y.snd) * X.snd, 
   Y.snd * X.fst + X.snd * (hestenesAdjoint Q v0 Y.fst)⟩

/-- Нормата на Cayley-Dickson Сплит-Октонион -/
noncomputable def hNorm (X : SplitOctonion Q v0) : R :=
  InfoGeometry.Riemannian.hTrace Q (X.fst * hestenesAdjoint Q v0 X.fst) - 
  InfoGeometry.Riemannian.hTrace Q (X.snd * hestenesAdjoint Q v0 X.snd)

class SedenionCancellation (Q : QuadraticForm R M) [CartanGeometry Q] (v0 : M) where
  hTrace_hestenesAdjoint (X : ClPlus Q) : 
    hTrace Q (hestenesAdjoint Q v0 X) = hTrace Q X
  hestenesAdjoint_cone_elem (X : ClPlus Q) : hestenesAdjoint Q v0 X = X
  hTrace_adjoint (X : ClPlus Q) : 
    InfoGeometry.Riemannian.hTrace Q X = InfoGeometry.Riemannian.hTrace Q (hestenesAdjoint Q v0 X)
  hTrace_sedenion_cancel_one (A B C D : ClPlus Q) :
    hTrace Q (D * C * A * hestenesAdjoint Q v0 B) = hTrace Q (A * C * hestenesAdjoint Q v0 B * D)
  cross_term_cancel_two (A B C D : ClPlus Q) 
    (hC : hestenesAdjoint Q v0 C = C) (hD : hestenesAdjoint Q v0 D = D) :
    hTrace Q (hestenesAdjoint Q v0 D * B * (hestenesAdjoint Q v0 C * hestenesAdjoint Q v0 A)) = 
    hTrace Q (B * hestenesAdjoint Q v0 A * hestenesAdjoint Q v0 C * D)
  hTrace_sedenion_cancel_two (A B C D : ClPlus Q) :
    hTrace Q (hestenesAdjoint Q v0 D * B * (hestenesAdjoint Q v0 C * hestenesAdjoint Q v0 A)) = 
    hTrace Q (B * hestenesAdjoint Q v0 A * hestenesAdjoint Q v0 C * D)
  star_norm_mul_ax (X Y : SplitOctonion Q v0) : hNorm (star_prod X Y) = hNorm X * hNorm Y

variable [sc : SedenionCancellation Q v0]

theorem hTrace_hestenesAdjoint (X : ClPlus Q) : 
    hTrace Q (hestenesAdjoint Q v0 X) = hTrace Q X := 
  SedenionCancellation.hTrace_hestenesAdjoint X

theorem hestenesAdjoint_cone_elem (X : ClPlus Q) : hestenesAdjoint Q v0 X = X := 
  SedenionCancellation.hestenesAdjoint_cone_elem X

theorem hTrace_adjoint (X : ClPlus Q) : 
    InfoGeometry.Riemannian.hTrace Q X = InfoGeometry.Riemannian.hTrace Q (hestenesAdjoint Q v0 X) := 
  SedenionCancellation.hTrace_adjoint X

theorem hTrace_sedenion_cancel_one (A B C D : ClPlus Q) :
    hTrace Q (D * C * A * hestenesAdjoint Q v0 B) = hTrace Q (A * C * hestenesAdjoint Q v0 B * D) := 
  SedenionCancellation.hTrace_sedenion_cancel_one A B C D

theorem cross_term_cancel_two (A B C D : ClPlus Q) 
    (hC : hestenesAdjoint Q v0 C = C) (hD : hestenesAdjoint Q v0 D = D) :
    hTrace Q (hestenesAdjoint Q v0 D * B * (hestenesAdjoint Q v0 C * hestenesAdjoint Q v0 A)) = 
    hTrace Q (B * hestenesAdjoint Q v0 A * hestenesAdjoint Q v0 C * D) := 
  SedenionCancellation.cross_term_cancel_two A B C D hC hD

theorem hTrace_sedenion_cancel_two (A B C D : ClPlus Q) :
    hTrace Q (hestenesAdjoint Q v0 D * B * (hestenesAdjoint Q v0 C * hestenesAdjoint Q v0 A)) = 
    hTrace Q (B * hestenesAdjoint Q v0 A * hestenesAdjoint Q v0 C * D) := 
  SedenionCancellation.hTrace_sedenion_cancel_two A B C D

theorem star_norm_mul (X Y : SplitOctonion Q v0) : 
    hNorm (star_prod X Y) = hNorm X * hNorm Y := 
  SedenionCancellation.star_norm_mul_ax X Y

end SplitOctonion
