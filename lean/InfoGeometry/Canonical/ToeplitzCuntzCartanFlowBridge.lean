import Mathlib
import InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge

namespace InfoGeometry.Canonical

open ToeplitzCuntzVacuumBridge

variable {R : Type*} [CommRing R] [StarRing R]

/-- **1. Дефиниция на 1-Параметричен Картанов Фазов Елемент U ∈ U(1)**:
    U * star U = 1 и star U * U = 1 (Фаза, генерирана от e^{t λ}). -/
structure CartanPhaseElement (R : Type*) [CommRing R] [StarRing R] where
  val : R
  h_unitary_left  : star val * val = 1
  h_unitary_right : val * star val = 1

/-- **2. 1-Параметричен Поток върху Топлиц-Кунц Изометриите V₁(t) и V₂(t)** -/
def cartanFlowV1 (u1 : CartanPhaseElement R) (g : ToeplitzCuntzGenerators R) : R :=
  u1.val * g.V1

def cartanFlowV2 (u2 : CartanPhaseElement R) (g : ToeplitzCuntzGenerators R) : R :=
  u2.val * g.V2

/-- **Теорема 1**: Запазване на Изометричното Свойство при Картанов Поток: V₁(t)* V₁(t) = 1. -/
theorem cartanFlow_V1_isometry
    (u1 : CartanPhaseElement R) (g : ToeplitzCuntzGenerators R) :
    star (cartanFlowV1 u1 g) * cartanFlowV1 u1 g = 1 := by
  dsimp [cartanFlowV1]
  have h1 : star (u1.val * g.V1) * (u1.val * g.V1) = star g.V1 * (star u1.val * u1.val) * g.V1 := by
    rw [star_mul]
    ring
  rw [h1]
  rw [u1.h_unitary_left]
  have h2 : star g.V1 * 1 * g.V1 = star g.V1 * g.V1 := by ring
  rw [h2]
  exact g.V1_isometry

/-- **Теорема 2**: Абсолютна Инвариантност на Вакуумния Дефект P₀(t) = P₀.
    Вакуумът P₀ е сляп за Картановите фазови ротации! -/
theorem cartanFlow_vacuum_invariant
    (u1 u2 : CartanPhaseElement R) (g : ToeplitzCuntzGenerators R) :
    1 - (cartanFlowV1 u1 g * star (cartanFlowV1 u1 g) +
         cartanFlowV2 u2 g * star (cartanFlowV2 u2 g)) = ToeplitzCuntzGenerators.P0 g := by
  dsimp [cartanFlowV1, cartanFlowV2, ToeplitzCuntzGenerators.P0, ToeplitzCuntzGenerators.PPlus, ToeplitzCuntzGenerators.PMinus]
  have h1 : u1.val * g.V1 * star (u1.val * g.V1) = g.V1 * star g.V1 := by
    rw [star_mul]
    calc u1.val * g.V1 * (star g.V1 * star u1.val)
        = (u1.val * star u1.val) * (g.V1 * star g.V1) := by ring
      _ = 1 * (g.V1 * star g.V1) := by rw [u1.h_unitary_right]
      _ = g.V1 * star g.V1 := by rw [one_mul]
  have h2 : u2.val * g.V2 * star (u2.val * g.V2) = g.V2 * star g.V2 := by
    rw [star_mul]
    calc u2.val * g.V2 * (star g.V2 * star u2.val)
        = (u2.val * star u2.val) * (g.V2 * star g.V2) := by ring
      _ = 1 * (g.V2 * star g.V2) := by rw [u2.h_unitary_right]
      _ = g.V2 * star g.V2 := by rw [one_mul]
  rw [h1, h2]
  ring

/-- **Теорема 3**: Трансформация на Хиралния Суперзаряд Q₊(t) = u₁ u₂* Q₊.
    Суперзарядът носи Картанов заряд (weight) λ₁ - λ₂. -/
theorem cartanFlow_QPlus_transformation
    (u1 u2 : CartanPhaseElement R) (g : ToeplitzCuntzGenerators R) :
    cartanFlowV1 u1 g * star (cartanFlowV2 u2 g) = (u1.val * star u2.val) * ToeplitzCuntzGenerators.QPlus g := by
  dsimp [cartanFlowV1, cartanFlowV2, ToeplitzCuntzGenerators.QPlus]
  rw [star_mul]
  ring

end InfoGeometry.Canonical
