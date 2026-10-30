import InfoGeometry.OperatorAlgebra.PeirceSpine.GradingTransfer

/-!
# Reconstruction from the two proposed commutator modes

The source's modes are `D = V*Phi + Sigma` and `E = Phi - Sigma`.
Their coordinate change requires invertibility of `1+V` for the inverse
constructed here. This does not assert linear independence of any elements.
The additive equivalence acts on pairs of arbitrary ambient ring elements.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- A unit supplies an invertible change of two operator coordinates. -/
def modeCoordinateEquiv (u : Bˣ) : (B × B) ≃+ (B × B) where
  toFun z := ((u : B) * z.1 - z.1 + z.2, z.1 - z.2)
  invFun z := ((↑(u⁻¹) : B) * (z.1 + z.2),
    (↑(u⁻¹) : B) * (z.1 + z.2) - z.2)
  left_inv := by
    rintro ⟨x, y⟩
    have h : (u : B) * x - x + y + (x - y) = (u : B) * x := by abel
    simp only [h, ← mul_assoc, Units.inv_mul, one_mul]
    congr 1
    abel
  right_inv := by
    rintro ⟨d, e⟩
    simp only [← mul_assoc, Units.mul_inv, one_mul]
    apply Prod.ext <;> dsimp <;> abel
  map_add' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩
    apply Prod.ext <;> dsimp <;> noncomm_ring

/-- The two mode combinations recover the original operators up to `1+V`. -/
theorem mode_reconstruction_scaled (v x y : B) :
    (v * x + y) + (x - y) = (1 + v) * x ∧
    (v * x + y) - v * (x - y) = (1 + v) * y := by
  constructor <;> noncomm_ring

/-- Specialization to the Peirce generators, without an invertibility premise. -/
theorem peirce_mode_reconstruction_scaled (P A C : B) :
    (genV P A C * genPhi P A C + genSig P A C) +
        (genPhi P A C - genSig P A C) =
      (1 + genV P A C) * genPhi P A C ∧
    (genV P A C * genPhi P A C + genSig P A C) -
        genV P A C * (genPhi P A C - genSig P A C) =
      (1 + genV P A C) * genSig P A C :=
  mode_reconstruction_scaled _ _ _

/-- When `1+V` is a unit, the coordinate equivalence produces exactly the
two mode expressions from the source. No commutativity is needed. -/
theorem modeCoordinateEquiv_peirce (P A C : B) (u : Bˣ)
    (hu : (u : B) = 1 + genV P A C) :
    modeCoordinateEquiv u (genPhi P A C, genSig P A C) =
      (genV P A C * genPhi P A C + genSig P A C,
        genPhi P A C - genSig P A C) := by
  change ((u : B) * genPhi P A C - genPhi P A C + genSig P A C, _) = _
  rw [hu]
  apply Prod.ext
  · dsimp
    noncomm_ring
  · rfl

end InfoGeometry.OperatorAlgebra.PeirceSpine
