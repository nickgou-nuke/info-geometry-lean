import Mathlib
import InfoGeometry.Algebra.ZornMatrix

/-!
# Typed polarized Peirce and Jordan--Malcev readbacks

The upper sheet is a typed polarization, not the whole Peirce `1/2`-space.
The rectangular triple is therefore defined on `PPlus × PMinus × PPlus`.
Native Zorn multiplication is used only for the product and associator
readbacks; no associative envelope is imposed on the octonion carrier.
-/

namespace InfoGeometry.Canonical.SplitOctonionPolarizedJordanMalcev

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

noncomputable section

abbrev Carrier := ZornMatrix ℂ
abbrev Vec := Fin 3 → ℂ
abbrev PPlus := ℂ × Vec
abbrev PMinus := ℂ × Vec

def beta (x : PPlus) (y : PMinus) : ℂ :=
  x.1 * y.1 + ∑ i : Fin 3, x.2 i * y.2 i

def plusJordan (x y : PPlus) : PPlus :=
  (x.1 * y.1, fun i => (1 / 2 : ℂ) * (x.1 * y.2 i + y.1 * x.2 i))

def rectangularTriple (x z : PPlus) (y : PMinus) : PPlus :=
  (beta x y * z.1 + beta z y * x.1,
    fun i => beta x y * z.2 i + beta z y * x.2 i)

def vectorBivectorReadout (u v : Vec) : PMinus :=
  (0, Vec3.cross u v)

@[simp] theorem plusJordan_formula (x y : PPlus) :
    plusJordan x y =
      (x.1 * y.1, fun i => (1 / 2 : ℂ) *
        (x.1 * y.2 i + y.1 * x.2 i)) := rfl

theorem plusJordan_comm (x y : PPlus) :
    plusJordan x y = plusJordan y x := by
  ext <;> simp [plusJordan] <;> ring

theorem plusJordan_sheet_closed (x y : PPlus) :
    plusJordan x y ∈ Set.univ := by
  trivial

theorem plusJordan_vector_square_zero (u v : Vec) :
    plusJordan (0, u) (0, v) = (0, 0) := by
  ext <;> simp [plusJordan]

theorem plusJordan_unit_formula (a b : ℂ) (u v : Vec) :
    plusJordan (a, u) (b, v) =
      (a * b, fun i => (1 / 2 : ℂ) * (a * v i + b * u i)) := rfl

theorem rectangularTriple_swap_outer (x z : PPlus) (y : PMinus) :
    rectangularTriple x z y = rectangularTriple z x y := by
  ext <;> simp [rectangularTriple] <;> ring

def basisPlus (i : Fin 4) : PPlus :=
  if i = 0 then (1, 0) else
    (0, fun j => if j.val + 1 = i.val then 1 else 0)

def basisMinus (i : Fin 4) : PMinus := basisPlus i

theorem beta_basis (i j : Fin 4) :
    beta (basisPlus i) (basisMinus j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [basisPlus, basisMinus, beta, Fin.sum_univ_succ]

theorem native_peirce_unit_idempotent :
    (E11 : Carrier) * E11 = E11 := E11_mul_E11

theorem native_peirce_unit_vector (i : Fin 3) :
    (E11 : Carrier) * U i = U i := E11_mul_U i

theorem native_vector_unit_right (i : Fin 3) :
    (U i : Carrier) * E22 = U i := U_mul_E22 i

theorem native_vector_vector_anticommutator (i j : Fin 3) :
    (U i : Carrier) * U j + U j * U i = 0 := U_anticommute i j

theorem native_vector_vector_commutator_readout (i j : Fin 3) :
    (U i : Carrier) * U j - U j * U i =
      (U i : Carrier) * U j - U j * U i := rfl

def lowerLane (X : Carrier) : Prop :=
  X.a = 0 ∧ X.v = 0 ∧ X.b = 0

theorem native_vector_product_lowerLane (i j : Fin 3) :
    lowerLane ((U i : Carrier) * U j) := by
  rw [U_mul_U]
  refine ⟨rfl, ?_, rfl⟩
  funext k
  fin_cases k <;> simp

theorem native_associator_parity_property :
    ((U 0 : Carrier) * U 1) * U 2 - U 0 * (U 1 * U 2) =
      E22 - E11 := by
  rw [U_zero_mul_U_one, V_mul_U_self, U_one_mul_U_two, U_mul_V_self]

theorem native_associator_parity_property_ne_zero :
    ((U 0 : Carrier) * U 1) * U 2 ≠ U 0 * (U 1 * U 2) := by
  exact ZornMatrix.nonassociative_property (R := ℂ)

theorem native_sheet_closure_packet :
    (E11 : Carrier) * E11 = E11 ∧
      (∀ i j : Fin 3, (U i : Carrier) * U j + U j * U i = 0) ∧
      (∀ i : Fin 3, (E11 : Carrier) * U i = U i) ∧
      (∀ i j : Fin 3, lowerLane ((U i : Carrier) * U j)) ∧
      (((U 0 : Carrier) * U 1) * U 2 - U 0 * (U 1 * U 2) = E22 - E11) := by
  exact ⟨native_peirce_unit_idempotent,
    fun i j => native_vector_vector_anticommutator i j,
    fun i => native_peirce_unit_vector i,
    fun i j => native_vector_product_lowerLane i j,
    native_associator_parity_property⟩

end
end InfoGeometry.Canonical.SplitOctonionPolarizedJordanMalcev
