import InfoGeometry.Physics.TomitaTakesakiModularFlow

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

theorem modularTimeEvolutionRingHom_apply
    (F : ModularTimeEvolutionData A) (t : ℝ) (x : A) :
    modularTimeEvolutionRingHom F t x = F.sigma t x :=
  rfl

theorem modularTimeEvolutionRingHom_bijective
    (F : ModularTimeEvolutionData A) (t : ℝ) :
    Function.Bijective (modularTimeEvolutionRingHom F t) := by
  exact modular_flow_is_bijective A F.toModularFlowData t

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

theorem modular_time_evolution_automorphism_synthesis
    (F : ModularTimeEvolutionData A) (t s : ℝ) (x : A) :
    (Function.Bijective (modularTimeEvolutionRingHom F t)) ∧
    (F.sigma (t + s) x =
      modularTimeEvolutionRingHom F t
        (modularTimeEvolutionRingHom F s x)) ∧
    (modularTimeEvolutionRingHom F (-t)
        (modularTimeEvolutionRingHom F t x) = x) :=
  ⟨modularTimeEvolutionRingHom_bijective F t,
    modularTimeEvolution_group_law F t s x,
    modularTimeEvolution_inverse_law F t x⟩

end InfoGeometry.Physics
