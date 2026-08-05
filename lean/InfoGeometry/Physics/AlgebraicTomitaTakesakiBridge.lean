import InfoGeometry.Physics.ThermodynamicAlgebraicCenter
import Mathlib.Data.Set.Basic

namespace InfoGeometry.Physics

variable {A : Type*} [Ring A]

/-- Algebraic anti-automorphism data for a Tomita-style conjugation. -/
structure AntiAutomorphism (A : Type*) [Ring A] where
  toFun : A → A
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_mul : ∀ x y, toFun (x * y) = toFun y * toFun x
  inv : ∀ x, toFun (toFun x) = x

/-- The algebraic content of the Tomita relation `J(S) = S'`. -/
def IsTomitaConjugation (J : AntiAutomorphism A) (S : Set A) : Prop :=
  ∀ a, a ∈ S ↔ J.toFun a ∈ Commutant A S

namespace AlgebraicTomitaTakesaki

variable (J : AntiAutomorphism A) (S : Set A)

theorem tomita_conjugation_maps_commutant_to_algebra
    (hJ : IsTomitaConjugation J S) (x : A) :
    x ∈ Commutant A S ↔ J.toFun x ∈ S := by
  have h_iff := (hJ (J.toFun x)).symm
  rw [J.inv x] at h_iff
  exact h_iff

def SubsystemCenter : Set A :=
  S ∩ Commutant A S

theorem macroscopic_center_is_tomita_invariant
    (hJ : IsTomitaConjugation J S) (z : A) :
    z ∈ SubsystemCenter S ↔ J.toFun z ∈ SubsystemCenter S := by
  dsimp [SubsystemCenter]
  constructor
  · rintro ⟨hzS, hzS'⟩
    have h1 : J.toFun z ∈ Commutant A S := (hJ z).mp hzS
    have h2 : J.toFun z ∈ S :=
      (tomita_conjugation_maps_commutant_to_algebra J S hJ z).mp hzS'
    exact ⟨h2, h1⟩
  · rintro ⟨hJzS, hJzS'⟩
    have h1 : J.toFun (J.toFun z) ∈ Commutant A S :=
      (hJ (J.toFun z)).mp hJzS
    have h2 : J.toFun (J.toFun z) ∈ S :=
      (tomita_conjugation_maps_commutant_to_algebra J S hJ
        (J.toFun z)).mp hJzS'
    rw [J.inv z] at h1 h2
    exact ⟨h2, h1⟩

theorem algebraic_tomita_takesaki_synthesis
    (hJ : IsTomitaConjugation J S) (z : A) :
    (z ∈ Commutant A S ↔ J.toFun z ∈ S) ∧
    (z ∈ SubsystemCenter S ↔ J.toFun z ∈ SubsystemCenter S) :=
  ⟨tomita_conjugation_maps_commutant_to_algebra J S hJ z,
    macroscopic_center_is_tomita_invariant J S hJ z⟩

end AlgebraicTomitaTakesaki

end InfoGeometry.Physics
