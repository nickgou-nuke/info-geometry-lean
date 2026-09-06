import proofs.A2InsideD5RootSubsystem
import proofs.HexagonalSixRootTiling

/-!
# Intertwining the six hexagonal labels with the `A₂` roots

The positive sheet is sent to the oriented triangle
`(0,1), (1,2), (2,0)` and the negative sheet to the reversed triangle
`(1,0), (2,1), (0,2)`.  Under this equivalence, colour rotation is the
coordinate cycle `(012)` and the Pin reflection is the Weyl reflection `(01)`.
-/

noncomputable section
namespace HexIndexA2RootIntertwiner

open HexagonalSixRootTiling A2InsideD5RootSubsystem

def colorFin (a : HexColor) : Fin 3 := ⟨a.val, a.val_lt⟩

def sheetColorRoot : HexSheet × HexColor → A2Root
  | (.positive, a) =>
      ⟨(colorFin a, next3 (colorFin a)), next3_ne (colorFin a)⟩
  | (.negative, a) =>
      ⟨(next3 (colorFin a), colorFin a), (next3_ne (colorFin a)).symm⟩

def hexToA2Root (n : HexIndex) : A2Root :=
  sheetColorRoot (sheetColorEquiv n)

theorem hexToA2Root_bijective : Function.Bijective hexToA2Root := by
  native_decide

/-- The six sheet--colour labels are exactly the six oriented `A₂` roots. -/
def hexA2Equiv : HexIndex ≃ A2Root :=
  Equiv.ofBijective hexToA2Root hexToA2Root_bijective

@[simp] theorem hexA2Equiv_apply (n : HexIndex) :
    hexA2Equiv n = hexToA2Root n := rfl

def prev3 : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 0
  | 2 => 1

def colorWeylCycle : Equiv.Perm (Fin 3) where
  toFun := next3
  invFun := prev3
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def colorWeylReflection : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1

/-- Colour rotation of the hexagon is the `A₂` Weyl three-cycle. -/
theorem hexA2Equiv_colorRotate (n : HexIndex) :
    hexA2Equiv (colorRotate n) =
      weylAction colorWeylCycle (hexA2Equiv n) := by
  simp only [hexA2Equiv_apply]
  fin_cases n <;> native_decide

/-- The Pin label reflection is the coordinate Weyl reflection `(01)`. -/
theorem hexA2Equiv_hexReflect (n : HexIndex) :
    hexA2Equiv (hexReflect n) =
      weylAction colorWeylReflection (hexA2Equiv n) := by
  simp only [hexA2Equiv_apply]
  fin_cases n <;> native_decide

theorem colorWeylReflection_cycle_relation :
    colorWeylReflection * colorWeylCycle * colorWeylReflection =
      colorWeylCycle⁻¹ := by
  ext i
  fin_cases i <;> rfl

/-- The `D₅` root assigned to a six-state label. -/
def hexD5Root (n : HexIndex) : D5Space :=
  a2RootVector (hexA2Equiv n)

theorem hexD5Root_isD5Root (n : HexIndex) : IsD5Root (hexD5Root n) :=
  a2RootVector_isD5Root (hexA2Equiv n)

theorem hexD5Root_injective : Function.Injective hexD5Root :=
  a2RootVector_injective.comp hexA2Equiv.injective

theorem hex_a2_intertwining_packet :
    Function.Bijective hexToA2Root ∧
    (∀ n, hexA2Equiv (colorRotate n) =
      weylAction colorWeylCycle (hexA2Equiv n)) ∧
    (∀ n, hexA2Equiv (hexReflect n) =
      weylAction colorWeylReflection (hexA2Equiv n)) ∧
    Function.Injective hexD5Root :=
  ⟨hexToA2Root_bijective, hexA2Equiv_colorRotate,
    hexA2Equiv_hexReflect, hexD5Root_injective⟩

end HexIndexA2RootIntertwiner
end noncomputable section
