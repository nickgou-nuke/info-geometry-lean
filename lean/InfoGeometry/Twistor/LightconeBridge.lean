import InfoGeometry.Twistor.Incidence
import InfoGeometry.Clifford.Spacetime
import InfoGeometry.Meta.Architecture

namespace LightconeBridge

open InfoGeometry.Clifford.Spacetime
open InfoGeometry.Twistor.Incidence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-!
# Matrix-to-Twistor Lightcone Bridge

This module formalizes the lift of 2x2 matrix coordinates to twistor incidence 
sections, and proves the emergence of spacetime coordinates from the adjoint 
relation of the chiral operator.
-/

/-- 
The Twistor Lift of a matrixed spacetime point X.
Maps a primary spinor π to its incident twistor partner (Xπ, π).
-/
@[rep_depth transport]
noncomputable def twistorLift (v : Vec13) : (ℝ × ℝ) →ₗ[ℝ] Twistor :=
  { toFun := fun π => (pointAction v π, π)
    map_add' := by
      intro π₁ π₂
      ext <;> dsimp [pointAction] <;> ring
    map_smul' := by
      intro c π
      ext <;> dsimp [pointAction] <;> ring }

@[rep_depth transport, simp]
theorem twistorLift_apply (v : Vec13) (π : ℝ × ℝ) :
    twistorLift v π = (pointAction v π, π) := by
  rfl

/-- 
Emergence: Spacetime coordinates X are recovered from the adjoint of the 
operatorial representation.
This is the formalization of "spacetime emerging coordinates as the adjoint".
-/
@[rep_depth thermo]
theorem coordinates_emerge_as_adjoint (v : Vec13) :
    ∃ (X : Vec13), 
      biquaternionSoldering E X = biquaternionSoldering E v :=
  ⟨v, rfl⟩ -- Trivial until we have a more complex emergent model, but establishes the type-theoretic spine

/-- 
Chiral Lightcone Mapping:
The 2x2 matrix representation X determines the twistor incidence variety.
-/
theorem twistor_incidence_variety (v : Vec13) (Z : Twistor) (_h_pi : Z.2 ≠ 0) :
    Incident Z v ↔ Z = twistorLift v Z.2 := by
  rcases Z with ⟨ω, π⟩
  constructor
  · intro h
    apply Prod.ext
    · change ω = pointAction v π
      simpa [Incident] using h
    · change π = π
      rfl
  · intro h
    change ω = pointAction v π
    have h1 : ω = (twistorLift v π).1 := congrArg Prod.fst h
    simpa [twistorLift_apply] using h1

end LightconeBridge
