import InfoGeometry.Physics.TomitaTakesakiModularFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics

variable {A : Type*} [Ring A]

/-- A modular flow whose time slices preserve the ring operations. -/
structure ModularTimeEvolutionData (A : Type*) [Ring A]
    extends ModularFlowData A where
  sigma_zero_add : ∀ t, sigma t 0 = 0
  sigma_additive : ∀ t x y, sigma t (x + y) = sigma t x + sigma t y
  sigma_one : ∀ t, sigma t 1 = 1
  sigma_multiplicative : ∀ t x y, sigma t (x * y) = sigma t x * sigma t y

def modularTimeEvolutionRingHom
    (F : ModularTimeEvolutionData A) (t : ℝ) : A →+* A where
  toFun := F.sigma t
  map_one' := F.sigma_one t
  map_mul' := F.sigma_multiplicative t
  map_zero' := F.sigma_zero_add t
  map_add' := F.sigma_additive t

theorem modularTimeEvolutionRingHom_bijective
    (F : ModularTimeEvolutionData A) (t : ℝ) :
    Function.Bijective (modularTimeEvolutionRingHom F t) := by
  exact modular_flow_is_bijective A F.toModularFlowData t

/-- Each time slice is a genuine algebra automorphism, not merely a bijective
ring hom readout.  The inverse is supplied by the existing `(-t)` modular
flow law. -/
noncomputable def modularTimeEvolutionRingEquiv
    (F : ModularTimeEvolutionData A) (t : ℝ) : A ≃+* A :=
  RingEquiv.ofBijective (modularTimeEvolutionRingHom F t)
    (modularTimeEvolutionRingHom_bijective F t)

@[simp] theorem modularTimeEvolutionRingEquiv_apply
    (F : ModularTimeEvolutionData A) (t : ℝ) (x : A) :
    modularTimeEvolutionRingEquiv F t x = F.sigma t x :=
  rfl

theorem modularTimeEvolutionRingEquiv_inverse_apply
    (F : ModularTimeEvolutionData A) (t : ℝ) (x : A) :
    (modularTimeEvolutionRingEquiv F t).symm x = F.sigma (-t) x := by
  apply (modularTimeEvolutionRingEquiv F t).injective
  rw [RingEquiv.apply_symm_apply]
  simp only [modularTimeEvolutionRingEquiv_apply]
  exact (F.sigma_neg_right t x).symm

theorem modularTimeEvolution_group_law
    (F : ModularTimeEvolutionData A) (t s : ℝ) (x : A) :
    F.sigma (t + s) x =
      modularTimeEvolutionRingHom F t
        (modularTimeEvolutionRingHom F s x) := by
  exact F.sigma_add t s x

theorem modularTimeEvolution_inverse_law
    (F : ModularTimeEvolutionData A) (t : ℝ) (x : A) :
    modularTimeEvolutionRingHom F (-t)
        (modularTimeEvolutionRingHom F t x) = x := by
  exact F.sigma_neg_left t x

end InfoGeometry.Physics
