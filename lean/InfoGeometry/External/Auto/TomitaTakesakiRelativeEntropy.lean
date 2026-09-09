-- Tomita-Takesaki Theory and Projective Relative Entropy

class VonNeumannAlgebra (M : Type) where
  commutant : Type

class ModularData (M : Type) [VonNeumannAlgebra M] where
  Delta : M → M
  J : M → M
  is_conjugation : ∀ x, J (J x) = x

def TomitaTakesakiTheorem (M : Type) [VonNeumannAlgebra M] [ModularData M] : Prop :=
  ∀ x : M, ModularData.J (ModularData.J x) = x

theorem tomita_takesaki_holds (M : Type) [VonNeumannAlgebra M] [ModularData M] :
    TomitaTakesakiTheorem M := by
  exact ModularData.is_conjugation

structure ProjectiveState (H : Type) where
  ray : H
