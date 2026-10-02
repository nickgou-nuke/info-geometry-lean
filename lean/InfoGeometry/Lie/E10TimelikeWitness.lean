import InfoGeometry.Lie.E10HyperbolicSignature

/-!
# E₁₀ quadratic-form witness and scope

The affine E₉ null vector, perturbed in the extending direction, gives a
negative value for the E₁₀ Cartan quadratic form. Together with a positive
simple-coordinate direction, this proves indefiniteness. It does not by itself
prove Lorentzian signature or the strict hyperbolic-subdiagram criterion.
-/

namespace InfoGeometry.Lie.E10TimelikeWitness

open InfoGeometry.Lie.E10
open InfoGeometry.Lie.E10Hyperbolic

/-- Dependency nodes for the timelike-witness argument and its stronger
downstream classification goals. -/
inductive Archetype
  | e10CartanData
  | affineE9NullRoot
  | extendingNode
  | timelikePerturbation
  | negativeQuadraticValue
  | lorentzianSignature
  | strictHyperbolicity
  deriving DecidableEq, Repr

/-- Rank of a node in the causal dependency chain. -/
def Archetype.rank : Archetype → ℕ
  | .e10CartanData => 0
  | .affineE9NullRoot => 1
  | .extendingNode => 2
  | .timelikePerturbation => 3
  | .negativeQuadraticValue => 4
  | .lorentzianSignature => 5
  | .strictHyperbolicity => 6

/-- The causal poset is the order induced by dependency rank. -/
instance : PartialOrder Archetype where
  le a b := a.rank ≤ b.rank
  le_refl a := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [Archetype.rank]

/-- The extracted archetypes are linearly ordered by the proof dependencies. -/
theorem causal_archetype_chain :
    Archetype.e10CartanData ≤ .affineE9NullRoot ∧
    Archetype.affineE9NullRoot ≤ .extendingNode ∧
    Archetype.extendingNode ≤ .timelikePerturbation ∧
    Archetype.timelikePerturbation ≤ .negativeQuadraticValue ∧
    Archetype.negativeQuadraticValue ≤ .lorentzianSignature ∧
    Archetype.lorentzianSignature ≤ .strictHyperbolicity := by
  decide

/-- The proposed E₁₀ vector is a strict negative direction of the Cartan form. -/
theorem timelikeRoot_has_negative_quadratic_value :
    cartanQuadraticForm timelikeRoot < 0 := by
  rw [e10_is_hyperbolic]
  norm_num

/-- A simple-coordinate vector has positive Cartan quadratic value. -/
def positiveVector : Fin 10 → ℤ := fun i => if i = 0 then 1 else 0

theorem positiveVector_quadratic_value :
    cartanQuadraticForm positiveVector = 2 := by
  decide

/-- The E₁₀ Cartan quadratic form takes both positive and negative values. -/
theorem cartanQuadraticForm_has_both_signs :
    (∃ v : Fin 10 → ℤ, cartanQuadraticForm v < 0) ∧
    (∃ v : Fin 10 → ℤ, 0 < cartanQuadraticForm v) := by
  exact ⟨⟨timelikeRoot, timelikeRoot_has_negative_quadratic_value⟩,
    ⟨positiveVector, by rw [positiveVector_quadratic_value]; norm_num⟩⟩

end InfoGeometry.Lie.E10TimelikeWitness
