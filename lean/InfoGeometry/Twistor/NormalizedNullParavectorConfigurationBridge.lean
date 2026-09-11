import InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
import InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration

/-!
# Normalized null paravectors and the existing celestial configuration owners

This file supplies only the finite adapter between the normalized `(1,3)`
paravector slice and the repository's existing celestial/configuration owners.
It does not identify incidence flags with twistor points and does not add a
new fundamental-group or braid framework.
-/

noncomputable section

namespace InfoGeometry.Twistor.NormalizedNullParavectorConfigurationBridge

open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.TwistorBoundaryParavectorIncidence
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge
open InfoGeometry.Twistor.ProjectiveNullConfiguration

abbrev NormalizedNullParavector :=
  {p : Minkowski13 // p.1 = 1 ∧ paravectorQuadratic p = 0}

def normalizedNullParavectorEquivCelestial :
    NormalizedNullParavector ≃ CelestialSphere where
  toFun p := ⟨p.1.2, by
    have h := p.2.2
    change p.1.1 ^ 2 - ∑ i : Fin 3, p.1.2 i ^ 2 = 0 at h
    change ∑ i : Fin 3, p.1.2 i ^ 2 = 1
    rw [p.2.1] at h
    norm_num at h
    exact (sub_eq_zero.mp h).symm⟩
  invFun x := ⟨(1, x.1), by
    constructor
    · rfl
    · simp [paravectorQuadratic, x.2]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact p.2.1.symm
    · rfl
  right_inv x := by
    apply Subtype.ext
    rfl

  @[simp] theorem normalizedNullParavectorEquivCelestial_apply
    (p : NormalizedNullParavector) :
    normalizedNullParavectorEquivCelestial p = ⟨p.1.2, by
      have h := p.2.2
      change p.1.1 ^ 2 - ∑ i : Fin 3, p.1.2 i ^ 2 = 0 at h
      change ∑ i : Fin 3, p.1.2 i ^ 2 = 1
      rw [p.2.1] at h
      norm_num at h
      exact (sub_eq_zero.mp h).symm⟩ := rfl

abbrev NormalizedParavectorOrderedConfiguration (n : ℕ) :=
  InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge.OrderedConfiguration
    NormalizedNullParavector n

def normalizedParavectorToCelestial (n : ℕ) :
    NormalizedParavectorOrderedConfiguration n →
      CelestialOrderedConfiguration n := by
  intro p
  refine ⟨fun i => normalizedNullParavectorEquivCelestial (p.1 i), ?_⟩
  intro i j hij heq
  exact p.2 i j hij (normalizedNullParavectorEquivCelestial.injective heq)

@[simp] theorem normalizedParavectorToCelestial_apply
    (n : ℕ) (p : NormalizedParavectorOrderedConfiguration n) (i : Fin n) :
    (normalizedParavectorToCelestial n p).1 i =
      normalizedNullParavectorEquivCelestial (p.1 i) := rfl

theorem normalizedParavectorToCelestial_injective (n : ℕ) :
    Function.Injective (normalizedParavectorToCelestial n) := by
  intro p q hpq
  apply Subtype.ext
  funext i
  apply normalizedNullParavectorEquivCelestial.injective
  exact congrFun (congrArg Subtype.val hpq) i

def normalizedParavectorToQ55Configuration (n : ℕ) :
    NormalizedParavectorOrderedConfiguration n →
      InfoGeometry.Twistor.ProjectiveNullConfiguration.NullOrderedConfiguration
        (K := ℝ) (V := V55) Q55 n :=
  celestialOrderedConfigurationMap n ∘ normalizedParavectorToCelestial n

@[simp] theorem normalizedParavectorToQ55Configuration_apply
    (n : ℕ) (p : NormalizedParavectorOrderedConfiguration n) (i : Fin n) :
    (normalizedParavectorToQ55Configuration n p).1 i =
      celestialNullPoint
        ((normalizedParavectorToCelestial n p).1 i) := rfl

theorem normalizedParavectorToQ55Configuration_injective (n : ℕ) :
    Function.Injective (normalizedParavectorToQ55Configuration n) := by
  intro p q hpq
  exact normalizedParavectorToCelestial_injective n
    (celestialOrderedConfigurationMap_injective n hpq)

end InfoGeometry.Twistor.NormalizedNullParavectorConfigurationBridge
