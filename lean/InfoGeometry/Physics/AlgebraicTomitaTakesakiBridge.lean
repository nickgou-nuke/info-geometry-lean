import InfoGeometry.Physics.ThermodynamicAlgebraicCenter
import InfoGeometry.OperatorAlgebra.TwoSheetedAlgebra
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Equiv

namespace InfoGeometry.Physics

variable {A : Type*} [Ring A]

/-- Algebraic anti-automorphism data for a Tomita-style conjugation. -/
structure AntiAutomorphism (A : Type*) [Ring A] where
  toFun : A → A
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_mul : ∀ x y, toFun (x * y) = toFun y * toFun x
  inv : ∀ x, toFun (toFun x) = x

open MulOpposite

/-! The anti-automorphism becomes an honest ring equivalence after passing to
the opposite ring.  This is the typed algebraic core of the right/opposite
frame; no commutant or Morita hypothesis is used here. -/
def antiOppositeRingEquiv
    {A : Type*} [Ring A]
    (J : AntiAutomorphism A) : Aᵐᵒᵖ ≃+* A where
  toFun := fun x => J.toFun (unop x)
  invFun := fun x => op (J.toFun x)
  left_inv := by
    intro x
    apply op_injective
    simp [J.inv]
  right_inv := by
    intro x
    simp [J.inv]
  map_add' := by
    intro x y
    simp [J.map_add]
  map_mul' := by
    intro x y
    simp [J.map_mul]

@[simp] theorem antiOppositeRingEquiv_apply
    {A : Type*} [Ring A]
    (J : AntiAutomorphism A) (x : Aᵐᵒᵖ) :
    antiOppositeRingEquiv J x = J.toFun (unop x) :=
  rfl

@[simp] theorem antiOppositeRingEquiv_symm_apply
    {A : Type*} [Ring A]
    (J : AntiAutomorphism A) (x : A) :
    (antiOppositeRingEquiv J).symm x = op (J.toFun x) :=
  rfl

/-! The existing two-sheet carrier can now be instantiated from the native
opposite-ring equivalence.  This is the algebraic Morita-side witness; an
analytic Hilbert-bimodule Morita theorem still requires its own module data. -/
def AntiAutomorphism.toTwoSheetedAlgebra
    {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (J : AntiAutomorphism A) :
    InfoGeometry.OperatorAlgebra.TwoSheetedAlgebra K where
  L := A
  R_alg := A
  commutant := (antiOppositeRingEquiv J).symm

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

end AlgebraicTomitaTakesaki

end InfoGeometry.Physics
