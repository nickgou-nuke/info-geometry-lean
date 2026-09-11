import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological
import InfoGeometry.Topology.CyclotomicLatentReflectionTopological

/-!
# Reflection of the cyclotomic Heisenberg/Sugawara product chart

The orientation-reversing action is defined on the latent quotient factor and
acts trivially on the dependent charged-Fock Sugawara packet.  This is an
explicit topological involution; no operator action on the Fock spaces is
assumed.
-/

namespace InfoGeometry.Topology.CyclotomicHeisenbergSugawaraReflectionTopological

open InfoGeometry.Topology.CyclotomicHeisenbergSugawaraProductTopological
open InfoGeometry.Topology.CyclotomicLatentReflectionTopological

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Reflection of the combined chart: latent reflection, Sugawara identity. -/
noncomputable def cyclotomicHeisenbergSugawaraReflection :
    CyclotomicHeisenbergSugawaraOutput 𝕜 ≃ₜ
      CyclotomicHeisenbergSugawaraOutput 𝕜 where
  toFun z := (cyclotomicLatentReflection z.1, z.2)
  invFun z := (cyclotomicLatentReflection z.1, z.2)
  left_inv z := by
    apply Prod.ext
    · exact cyclotomicLatentReflection_involutive z.1
    · rfl
  right_inv z := by
    apply Prod.ext
    · exact cyclotomicLatentReflection_involutive z.1
    · rfl
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

@[simp] theorem cyclotomicHeisenbergSugawaraReflection_latent
    (z : CyclotomicHeisenbergSugawaraOutput 𝕜) :
    (cyclotomicHeisenbergSugawaraReflection z).1 =
      cyclotomicLatentReflection z.1 := by
  rfl

@[simp] theorem cyclotomicHeisenbergSugawaraReflection_sugawara
    (z : CyclotomicHeisenbergSugawaraOutput 𝕜) :
    (cyclotomicHeisenbergSugawaraReflection z).2 = z.2 := by
  rfl

theorem cyclotomicHeisenbergSugawaraReflection_involutive
    (z : CyclotomicHeisenbergSugawaraOutput 𝕜) :
    cyclotomicHeisenbergSugawaraReflection
        (cyclotomicHeisenbergSugawaraReflection z) = z := by
  exact (cyclotomicHeisenbergSugawaraReflection (𝕜 := 𝕜)).left_inv z

theorem continuous_cyclotomicHeisenbergSugawaraReflection :
    Continuous (cyclotomicHeisenbergSugawaraReflection (𝕜 := 𝕜)) := by
  exact (cyclotomicHeisenbergSugawaraReflection (𝕜 := 𝕜)).continuous_toFun

end
end InfoGeometry.Topology.CyclotomicHeisenbergSugawaraReflectionTopological
