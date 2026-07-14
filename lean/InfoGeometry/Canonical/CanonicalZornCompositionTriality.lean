import Mathlib
import InfoGeometry.Physics.SplitOctonionBraidSU3

/-!
# Composition-algebra triality on the canonical Zorn carrier

This file distinguishes three eight-dimensional carriers:

* the vector copy `8v`;
* the positive semispinor copy `8s`;
* the negative semispinor copy `8c`.

All three are typed wrappers around the canonical complex Zorn composition
algebra.  They are not definitionally interchangeable.  Zorn multiplication
and conjugation give the two chiral Clifford actions

`8v × 8s → 8c` and `8v × 8c → 8s`.

The main quadratic identities prove that composing the two actions is scalar
multiplication by the Zorn norm.  This is the composition-algebra form of the
split Clifford relation underlying Cartan triality.
-/

noncomputable section

namespace CanonicalZornCompositionTriality

open InfoGeometry.Physics.SplitOctonionBraidSU3

/-- Eight canonical complex coordinates of a Zorn element. -/
def zornCoordinates (X : Zorn) : Fin 8 → ℂ :=
  ![X.a, X.u 0, X.u 1, X.u 2, X.v 0, X.v 1, X.v 2, X.b]

theorem zornCoordinates_injective : Function.Injective zornCoordinates := by
  intro X Y h
  apply zorn_ext
  · exact congrFun h 0
  · funext i
    fin_cases i
    · exact congrFun h 1
    · exact congrFun h 2
    · exact congrFun h 3
  · funext i
    fin_cases i
    · exact congrFun h 4
    · exact congrFun h 5
    · exact congrFun h 6
  · exact congrFun h 7

/-! ## Canonical conjugation and quadratic action identities -/

/-- Standard conjugation of a Zorn matrix. -/
def zornConj (X : Zorn) : Zorn where
  a := X.b
  u := fun i => -X.u i
  v := fun i => -X.v i
  b := X.a

@[simp] theorem zornConj_conj (X : Zorn) : zornConj (zornConj X) = X := by
  apply zorn_ext
  · rfl
  · funext i
    simp [zornConj]
  · funext i
    simp [zornConj]
  · rfl

theorem zornNorm_conj (X : Zorn) : zornNorm (zornConj X) = zornNorm X := by
  simp [zornNorm, zornConj, dot3]
  ring

theorem zornConj_add (X Y : Zorn) :
    zornConj (zornAdd X Y) = zornAdd (zornConj X) (zornConj Y) := by
  apply zorn_ext
  · rfl
  · funext i
    simp [zornConj, zornAdd]
    ring
  · funext i
    simp [zornConj, zornAdd]
    ring
  · rfl

theorem zornConj_smul (c : ℂ) (X : Zorn) :
    zornConj (zornSmul c X) = zornSmul c (zornConj X) := by
  apply zorn_ext
  · rfl
  · funext i
    simp [zornConj, zornSmul]
  · funext i
    simp [zornConj, zornSmul]
  · rfl

theorem zornConj_mul_self (X : Zorn) :
    zornMul (zornConj X) X = zornSmul (zornNorm X) I_zorn := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, dot3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, cross3] <;> ring
  · simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, dot3]
    ring

theorem zornMul_conj_self (X : Zorn) :
    zornMul X (zornConj X) = zornSmul (zornNorm X) I_zorn := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, dot3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, cross3] <;> ring
  · simp [zornConj, zornMul, zornSmul, zornNorm, I_zorn, dot3]
    ring

/-- Left multiplication by `X`, followed by left multiplication by its
conjugate, is the norm scalar. -/
theorem zornConj_left_action (X Y : Zorn) :
    zornMul (zornConj X) (zornMul X Y) = zornSmul (zornNorm X) Y := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3] <;> ring
  · simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3]
    ring

/-- The opposite chiral composition has the same norm scalar. -/
theorem zorn_left_conj_action (X Y : Zorn) :
    zornMul X (zornMul (zornConj X) Y) = zornSmul (zornNorm X) Y := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3] <;> ring
  · simp [zornConj, zornMul, zornSmul, zornNorm, dot3, cross3]
    ring

/-- Polar form associated with the Zorn composition norm. -/
def zornPolar (X Y : Zorn) : ℂ :=
  zornNorm (zornAdd X Y) - zornNorm X - zornNorm Y

/-- Polarized Clifford relation on the positive chiral carrier. -/
theorem zorn_polarized_conj_left_action (X Y S : Zorn) :
    zornAdd
      (zornMul (zornConj X) (zornMul Y S))
      (zornMul (zornConj Y) (zornMul X S)) =
        zornSmul (zornPolar X Y) S := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
      dot3, cross3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
        dot3, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
        dot3, cross3] <;> ring
  · simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
      dot3, cross3]
    ring

/-- Polarized Clifford relation on the negative chiral carrier. -/
theorem zorn_polarized_left_conj_action (X Y S : Zorn) :
    zornAdd
      (zornMul X (zornMul (zornConj Y) S))
      (zornMul Y (zornMul (zornConj X) S)) =
        zornSmul (zornPolar X Y) S := by
  apply zorn_ext
  · simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
      dot3, cross3]
    ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
        dot3, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
        dot3, cross3] <;> ring
  · simp [zornConj, zornMul, zornAdd, zornSmul, zornPolar, zornNorm,
      dot3, cross3]
    ring

/-- Linear trace of a Zorn matrix. -/
def zornTrace (X : Zorn) : ℂ := X.a + X.b

/-- The scalar part of a triple Zorn product is cyclic. -/
theorem zornTripleTrace_cyclic (X Y Z : Zorn) :
    zornTrace (zornMul (zornMul X Y) Z) =
      zornTrace (zornMul (zornMul Y Z) X) := by
  simp [zornTrace, zornMul, dot3, cross3]
  ring

/-! ## Three distinct eight-dimensional carriers -/

inductive TrialitySector where
  | vector
  | spinorPlus
  | spinorMinus
  deriving DecidableEq, Fintype, Repr

/-- A tagged copy of the canonical Zorn carrier. -/
@[ext] structure ZornCopy (sector : TrialitySector) where
  val : Zorn

abbrev Vector8 := ZornCopy .vector
abbrev SpinorPlus8 := ZornCopy .spinorPlus
abbrev SpinorMinus8 := ZornCopy .spinorMinus

/-- Inverse to the canonical eight-coordinate map. -/
def coordinatesToZorn (v : Fin 8 → ℂ) : Zorn where
  a := v 0
  u := ![v 1, v 2, v 3]
  v := ![v 4, v 5, v 6]
  b := v 7

theorem coordinatesToZorn_zornCoordinates (X : Zorn) :
    coordinatesToZorn (zornCoordinates X) = X := by
  apply zorn_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem zornCoordinates_coordinatesToZorn (v : Fin 8 → ℂ) :
    zornCoordinates (coordinatesToZorn v) = v := by
  funext i
  fin_cases i <;> rfl

/-- Every triality carrier has canonical coordinates in `ℂ⁸`. -/
def copyEquivCoordinates (sector : TrialitySector) :
    ZornCopy sector ≃ (Fin 8 → ℂ) where
  toFun X := zornCoordinates X.val
  invFun v := ⟨coordinatesToZorn v⟩
  left_inv X := by
    ext
    exact coordinatesToZorn_zornCoordinates X.val
  right_inv := zornCoordinates_coordinatesToZorn

instance (sector : TrialitySector) : AddCommGroup (ZornCopy sector) :=
  (copyEquivCoordinates sector).addCommGroup

instance (sector : TrialitySector) : Module ℂ (ZornCopy sector) :=
  (copyEquivCoordinates sector).module ℂ

/-- The transported linear coordinate equivalence. -/
def copyLinearEquivCoordinates (sector : TrialitySector) :
    ZornCopy sector ≃ₗ[ℂ] (Fin 8 → ℂ) where
  toFun := copyEquivCoordinates sector
  invFun := (copyEquivCoordinates sector).symm
  left_inv := (copyEquivCoordinates sector).left_inv
  right_inv := (copyEquivCoordinates sector).right_inv
  map_add' X Y := by
    change zornCoordinates
      (coordinatesToZorn (zornCoordinates X.val + zornCoordinates Y.val)) =
        zornCoordinates X.val + zornCoordinates Y.val
    exact zornCoordinates_coordinatesToZorn _
  map_smul' c X := by
    change zornCoordinates
      (coordinatesToZorn (c • zornCoordinates X.val)) =
        c • zornCoordinates X.val
    exact zornCoordinates_coordinatesToZorn _

/-- Each typed triality copy is finite-dimensional because its coordinate
equivalence has the finite function space `Fin 8 → ℂ` as source. -/
noncomputable instance copyModuleFinite (sector : TrialitySector) :
    Module.Finite ℂ (ZornCopy sector) :=
  Module.Finite.equiv (copyLinearEquivCoordinates sector).symm

theorem copy_finrank_eight (sector : TrialitySector) :
    Module.finrank ℂ (ZornCopy sector) = 8 := by
  rw [(copyLinearEquivCoordinates sector).finrank_eq]
  exact Module.finrank_fin_fun ℂ

/-! ## Typed triality cycle and Clifford actions -/

def vectorToSpinorPlus : Vector8 ≃ₗ[ℂ] SpinorPlus8 :=
  (copyLinearEquivCoordinates .vector).trans
    (copyLinearEquivCoordinates .spinorPlus).symm

def spinorPlusToSpinorMinus : SpinorPlus8 ≃ₗ[ℂ] SpinorMinus8 :=
  (copyLinearEquivCoordinates .spinorPlus).trans
    (copyLinearEquivCoordinates .spinorMinus).symm

def spinorMinusToVector : SpinorMinus8 ≃ₗ[ℂ] Vector8 :=
  (copyLinearEquivCoordinates .spinorMinus).trans
    (copyLinearEquivCoordinates .vector).symm

theorem typed_triality_order_three (X : Vector8) :
    spinorMinusToVector
        (spinorPlusToSpinorMinus (vectorToSpinorPlus X)) = X := by
  ext
  exact coordinatesToZorn_zornCoordinates X.val

def vectorNorm (X : Vector8) : ℂ := zornNorm X.val
def spinorPlusNorm (S : SpinorPlus8) : ℂ := zornNorm S.val
def spinorMinusNorm (S : SpinorMinus8) : ℂ := zornNorm S.val

theorem vectorToSpinorPlus_norm (X : Vector8) :
    spinorPlusNorm (vectorToSpinorPlus X) = vectorNorm X := by
  change zornNorm (coordinatesToZorn (zornCoordinates X.val)) = zornNorm X.val
  rw [coordinatesToZorn_zornCoordinates]

theorem spinorPlusToSpinorMinus_norm (S : SpinorPlus8) :
    spinorMinusNorm (spinorPlusToSpinorMinus S) = spinorPlusNorm S := by
  change zornNorm (coordinatesToZorn (zornCoordinates S.val)) = zornNorm S.val
  rw [coordinatesToZorn_zornCoordinates]

theorem spinorMinusToVector_norm (S : SpinorMinus8) :
    vectorNorm (spinorMinusToVector S) = spinorMinusNorm S := by
  change zornNorm (coordinatesToZorn (zornCoordinates S.val)) = zornNorm S.val
  rw [coordinatesToZorn_zornCoordinates]

/-- Vector action from the positive to the negative semispinor carrier. -/
def cliffordPlus (X : Vector8) (S : SpinorPlus8) : SpinorMinus8 :=
  ⟨zornMul X.val S.val⟩

/-- Conjugate vector action from the negative to the positive semispinor carrier. -/
def cliffordMinus (X : Vector8) (S : SpinorMinus8) : SpinorPlus8 :=
  ⟨zornMul (zornConj X.val) S.val⟩

theorem cliffordMinus_plus (X : Vector8) (S : SpinorPlus8) :
    (cliffordMinus X (cliffordPlus X S)).val =
      zornSmul (vectorNorm X) S.val := by
  exact zornConj_left_action X.val S.val

theorem cliffordPlus_minus (X : Vector8) (S : SpinorMinus8) :
    (cliffordPlus X (cliffordMinus X S)).val =
      zornSmul (vectorNorm X) S.val := by
  exact zorn_left_conj_action X.val S.val

theorem clifford_polarized_plus (X Y : Vector8) (S : SpinorPlus8) :
    zornAdd
      (cliffordMinus X (cliffordPlus Y S)).val
      (cliffordMinus Y (cliffordPlus X S)).val =
        zornSmul (zornPolar X.val Y.val) S.val := by
  exact zorn_polarized_conj_left_action X.val Y.val S.val

theorem clifford_polarized_minus (X Y : Vector8) (S : SpinorMinus8) :
    zornAdd
      (cliffordPlus X (cliffordMinus Y S)).val
      (cliffordPlus Y (cliffordMinus X S)).val =
        zornSmul (zornPolar X.val Y.val) S.val := by
  exact zorn_polarized_left_conj_action X.val Y.val S.val

/-- Cartan's composition-algebra trilinear form on the three typed carriers. -/
def trialityForm (V : Vector8) (S : SpinorPlus8) (C : SpinorMinus8) : ℂ :=
  zornTrace (zornMul (zornMul V.val S.val) C.val)

/-- The typed triality cycle preserves the canonical trilinear form. -/
theorem trialityForm_cyclic (V : Vector8) (S : SpinorPlus8)
    (C : SpinorMinus8) :
    trialityForm V S C =
      trialityForm (spinorMinusToVector C)
        (vectorToSpinorPlus V) (spinorPlusToSpinorMinus S) := by
  change zornTrace (zornMul (zornMul V.val S.val) C.val) =
    zornTrace
      (zornMul
        (zornMul (coordinatesToZorn (zornCoordinates C.val))
          (coordinatesToZorn (zornCoordinates V.val)))
        (coordinatesToZorn (zornCoordinates S.val)))
  rw [coordinatesToZorn_zornCoordinates,
    coordinatesToZorn_zornCoordinates,
    coordinatesToZorn_zornCoordinates]
  exact (zornTripleTrace_cyclic C.val V.val S.val).symm

/-- The three typed eight-dimensional carriers and their two chiral Clifford
relations are simultaneously available. -/
theorem canonical_composition_triality_closure
    (X : Vector8) (Splus : SpinorPlus8) (Sminus : SpinorMinus8) :
    Module.finrank ℂ Vector8 = 8 ∧
    Module.finrank ℂ SpinorPlus8 = 8 ∧
    Module.finrank ℂ SpinorMinus8 = 8 ∧
    (cliffordMinus X (cliffordPlus X Splus)).val =
      zornSmul (vectorNorm X) Splus.val ∧
    (cliffordPlus X (cliffordMinus X Sminus)).val =
      zornSmul (vectorNorm X) Sminus.val ∧
    trialityForm X Splus Sminus =
      trialityForm (spinorMinusToVector Sminus)
        (vectorToSpinorPlus X) (spinorPlusToSpinorMinus Splus) := by
  exact ⟨copy_finrank_eight _, copy_finrank_eight _, copy_finrank_eight _,
    cliffordMinus_plus X Splus, cliffordPlus_minus X Sminus,
    trialityForm_cyclic X Splus Sminus⟩


end CanonicalZornCompositionTriality

end noncomputable section
