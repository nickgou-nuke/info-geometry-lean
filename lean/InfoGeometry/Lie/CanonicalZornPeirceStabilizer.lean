import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

/-!
# Peirce stabilizer of the canonical split-Zorn derivation algebra

This module starts the intrinsic stabilizer construction on the native
canonical carrier.  It deliberately separates the derivation stabilizer from
any later `SL₃`, unitary, or phase identification.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornPeirceStabilizer

open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.CanonicalZornDerivation

abbrev CZ := CanonicalZornDerivation.CZ
abbrev EndCZ := CanonicalZornDerivation.EndCZ
abbrev Deriv := CanonicalZornDerivation.canonicalZornDerivations

/-- The two native diagonal Peirce idempotents on the canonical carrier. -/
def peircePlus : CZ :=
  { a := 1, b := 0, x := 0, y := 0 }

def peirceMinus : CZ :=
  { a := 0, b := 1, x := 0, y := 0 }

@[simp] theorem peircePlus_idempotent : peircePlus * peircePlus = peircePlus := by
  ext i <;> simp [peircePlus, InfoGeometry.Canonical.ZornMatrix.mul_def,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

@[simp] theorem peirceMinus_idempotent : peirceMinus * peirceMinus = peirceMinus := by
  ext i <;> simp [peirceMinus, InfoGeometry.Canonical.ZornMatrix.mul_def,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

@[simp] theorem peircePlus_mul_minus : peircePlus * peirceMinus = 0 := by
  ext i <;> simp [peircePlus, peirceMinus,
    InfoGeometry.Canonical.ZornMatrix.mul_def,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

@[simp] theorem peirceMinus_mul_plus : peirceMinus * peircePlus = 0 := by
  ext i <;> simp [peircePlus, peirceMinus,
    InfoGeometry.Canonical.ZornMatrix.mul_def,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

/-- The derivations fixing both diagonal Peirce idempotents. -/
noncomputable def peirceStabilizer : LieSubalgebra ℝ Deriv where
  carrier := {D | D.1 peircePlus = 0 ∧ D.1 peirceMinus = 0}
  zero_mem' := by simp
  add_mem' := by
    intro D E hD hE
    constructor <;> simp [hD.1, hD.2, hE.1, hE.2]
  smul_mem' := by
    intro r D hD
    constructor <;> simp [hD.1, hD.2]
  lie_mem' := by
    intro D E hD hE
    constructor
    · change D.1 (E.1 peircePlus) - E.1 (D.1 peircePlus) = 0
      simp [hD.1, hE.1]
    · change D.1 (E.1 peirceMinus) - E.1 (D.1 peirceMinus) = 0
      simp [hD.2, hE.2]

@[simp] theorem mem_peirceStabilizer (D : Deriv) :
    D ∈ peirceStabilizer ↔
      D.1 peircePlus = 0 ∧ D.1 peirceMinus = 0 :=
  Iff.rfl

/-- The diagonal Peirce corner maps. -/
def peircePlusCorner (X : CZ) : CZ :=
  (peircePlus * X) * peircePlus

def peirceMinusCorner (X : CZ) : CZ :=
  (peirceMinus * X) * peirceMinus

@[simp] theorem peircePlusCorner_apply (X : CZ) :
    peircePlusCorner X =
      { a := X.a, b := 0, x := 0, y := 0 } := by
  cases X
  ext i <;> simp [peircePlusCorner, peircePlus,
    InfoGeometry.Canonical.ZornMatrix.mul_def,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

@[simp] theorem peirceMinusCorner_apply (X : CZ) :
    peirceMinusCorner X =
      { a := 0, b := X.b, x := 0, y := 0 } := by
  cases X
  ext i <;> simp [peirceMinusCorner, peirceMinus,
    InfoGeometry.Canonical.ZornMatrix.mul_def,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals fin_cases i <;> rfl

/-- The off-diagonal Peirce carrier. -/
def offDiagonal : Submodule ℝ CZ where
  carrier := {X | X.a = 0 ∧ X.b = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    exact ⟨by simp [hX.1, hX.2, hY.1, hY.2],
      by simp [hX.1, hX.2, hY.1, hY.2]⟩
  smul_mem' := by
    intro r X hX
    exact ⟨by simp [hX.1], by simp [hX.2]⟩

/-- The off-diagonal carrier is the sum of the upper and lower vector slots. -/
abbrev offDiagonalCoordinates : Type :=
  (Fin 3 → ℝ) × (Fin 3 → ℝ)

noncomputable def offDiagonalLinearEquiv :
    offDiagonal ≃ₗ[ℝ] offDiagonalCoordinates where
  toFun X := (X.1.x, X.1.y)
  invFun v :=
    ⟨{ a := 0, b := 0, x := v.1, y := v.2 }, by
      change 0 = 0 ∧ 0 = 0
      exact ⟨rfl, rfl⟩⟩
  left_inv X := by
    apply Subtype.ext
    rcases X with ⟨⟨a, b, x, y⟩, hX⟩
    change a = 0 ∧ b = 0 at hX
    rcases hX with ⟨ha, hb⟩
    subst a
    subst b
    rfl
  right_inv v := by
    cases v
    rfl
  map_add' X Y := by
    rfl
  map_smul' r X := by
    rfl

/-- Fixing both Peirce idempotents forces a canonical derivation to preserve
both off-diagonal corners. -/
theorem peirceStabilizer_preserves_offDiagonal
    (D : peirceStabilizer) :
    ∀ X : offDiagonal, D.1.1 X.1 ∈ offDiagonal := by
  intro X
  have hPlusZero : peircePlusCorner X.1 = 0 := by
    rw [peircePlusCorner_apply]
    ext <;> simp [X.2.1]
  have hMinusZero : peirceMinusCorner X.1 = 0 := by
    rw [peirceMinusCorner_apply]
    ext <;> simp [X.2.2]
  have hPlusDeriv :
      D.1.1 (peircePlusCorner X.1) =
        peircePlusCorner (D.1.1 X.1) := by
    change D.1.1 ((peircePlus * X.1) * peircePlus) =
      (peircePlus * D.1.1 X.1) * peircePlus
    calc
      D.1.1 ((peircePlus * X.1) * peircePlus) =
          D.1.1 (peircePlus * X.1) * peircePlus +
            (peircePlus * X.1) * D.1.1 peircePlus :=
        D.1.2 _ _
      _ = (D.1.1 peircePlus * X.1 + peircePlus * D.1.1 X.1) *
            peircePlus + (peircePlus * X.1) * D.1.1 peircePlus := by
        rw [D.1.2]
      _ = (peircePlus * D.1.1 X.1) * peircePlus := by
        rw [D.2.1]
        simp only [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
          InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
          zero_add, add_zero]
  have hMinusDeriv :
      D.1.1 (peirceMinusCorner X.1) =
        peirceMinusCorner (D.1.1 X.1) := by
    change D.1.1 ((peirceMinus * X.1) * peirceMinus) =
      (peirceMinus * D.1.1 X.1) * peirceMinus
    calc
      D.1.1 ((peirceMinus * X.1) * peirceMinus) =
          D.1.1 (peirceMinus * X.1) * peirceMinus +
            (peirceMinus * X.1) * D.1.1 peirceMinus :=
        D.1.2 _ _
      _ = (D.1.1 peirceMinus * X.1 + peirceMinus * D.1.1 X.1) *
            peirceMinus + (peirceMinus * X.1) * D.1.1 peirceMinus := by
        rw [D.1.2]
      _ = (peirceMinus * D.1.1 X.1) * peirceMinus := by
        rw [D.2.2]
        simp only [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
          InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
          zero_add, add_zero]
  have hPlus : peircePlusCorner (D.1.1 X.1) = 0 := by
    rw [← hPlusDeriv, hPlusZero, map_zero]
  have hMinus : peirceMinusCorner (D.1.1 X.1) = 0 := by
    rw [← hMinusDeriv, hMinusZero, map_zero]
  rw [peircePlusCorner_apply] at hPlus
  rw [peirceMinusCorner_apply] at hMinus
  exact ⟨by simpa using congrArg (fun Z : CZ => Z.a) hPlus,
    by simpa using congrArg (fun Z : CZ => Z.b) hMinus⟩

/-- Restriction of a stabilizing derivation to the off-diagonal carrier. -/
noncomputable def restrictOffDiagonal
    (D : peirceStabilizer) :
    offDiagonal →ₗ[ℝ] offDiagonal where
  toFun X := ⟨D.1.1 X.1, peirceStabilizer_preserves_offDiagonal D X⟩
  map_add' X Y := by
    apply Subtype.ext
    change D.1.1 (X.1 + Y.1) = D.1.1 X.1 + D.1.1 Y.1
    exact D.1.1.map_add _ _
  map_smul' r X := by
    apply Subtype.ext
    simp

/-- The restriction is the canonical endomorphism induced by the derivation. -/
theorem restrictOffDiagonal_apply
    (D : peirceStabilizer) (X : offDiagonal) :
    (restrictOffDiagonal D X : CZ) = D.1.1 X.1 :=
  rfl

end InfoGeometry.Lie.CanonicalZornPeirceStabilizer

end
