import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.SplitOctonionClassificationCore
import InfoGeometry.Canonical.SplitOctonionAutomorphism

noncomputable section

set_option linter.unusedSectionVars false

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionClassificationCore

namespace InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame

variable {R : Type} [CommRing R] [Invertible (2 : R)]

@[simp] theorem one_a : (1 : ZornMatrix R).a = 1 := rfl
@[simp] theorem one_b : (1 : ZornMatrix R).b = 1 := rfl
@[simp] theorem one_x : (1 : ZornMatrix R).x = 0 := rfl
@[simp] theorem one_y : (1 : ZornMatrix R).y = 0 := rfl

@[simp] theorem smul_a' (r : R) (z : ZornMatrix R) : (r • z).a = r * z.a := rfl
@[simp] theorem smul_b' (r : R) (z : ZornMatrix R) : (r • z).b = r * z.b := rfl
@[simp] theorem smul_x' (r : R) (z : ZornMatrix R) (i : Fin 3) : (r • z).x i = r * z.x i := rfl
@[simp] theorem smul_y' (r : R) (z : ZornMatrix R) (i : Fin 3) : (r • z).y i = r * z.y i := rfl

/-- The central diagonal Peirce idempotent e_+ = (1 + I) / 2. -/
def ePlus : ZornMatrix R := zornPlus

/-- The central diagonal Peirce idempotent e_- = (1 - I) / 2. -/
def eMinus : ZornMatrix R := zornMinus

/-- The principal chiral symmetry I = e_+ - e_-. -/
def chiralI : ZornMatrix R := ePlus - eMinus

/-- The upper chiral nilpotents g^+_i = (J_i + j_i) / 2. -/
def gPlus (i : Fin 3) : ZornMatrix R :=
  { a := 0, b := 0, x := fun j => if i = j then 1 else 0, y := 0 }

/-- The lower chiral nilpotents g^-_i = (J_i - j_i) / 2. -/
def gMinus (i : Fin 3) : ZornMatrix R :=
  { a := 0, b := 0, x := 0, y := fun j => if i = j then 1 else 0 }

-- 1. Structural algebraic claims

theorem ePlus_idempotent :
    ePlus (R := R) * ePlus (R := R) = ePlus :=
  zornPlus_idempotent

theorem eMinus_idempotent :
    eMinus (R := R) * eMinus (R := R) = eMinus :=
  zornMinus_idempotent

theorem ePlus_mul_eMinus :
    ePlus (R := R) * eMinus (R := R) = 0 :=
  zornPlus_mul_zornMinus

theorem eMinus_mul_ePlus :
    eMinus (R := R) * ePlus (R := R) = 0 :=
  zornMinus_mul_zornPlus

-- 2. Nilpotent behavior of the off-block pieces

theorem gPlus_square_zero (i : Fin 3) :
    gPlus (R := R) i * gPlus (R := R) i = 0 := by
  ext k
  · simp [mul_def, gPlus, mul, dot, cross]
  · simp [mul_def, gPlus, mul, dot, cross]
  · fin_cases k <;> simp [mul_def, gPlus, mul, dot, cross]
  · fin_cases k <;>
      simp [mul_def, gPlus, mul, dot, cross] <;>
      split_ifs <;> ring

theorem gMinus_square_zero (i : Fin 3) :
    gMinus (R := R) i * gMinus (R := R) i = 0 := by
  ext k
  · simp [mul_def, gMinus, mul, dot, cross]
  · simp [mul_def, gMinus, mul, dot, cross]
  · fin_cases k <;>
      simp [mul_def, gMinus, mul, dot, cross] <;>
      split_ifs <;> ring
  · fin_cases k <;> simp [mul_def, gMinus, mul, dot, cross]

-- 3. Automorphism/Derivation Transport

def transportedEPlus (U : SplitOctonionAutCandidate R) : ZornMatrix R := U (ePlus (R := R))
def transportedEMinus (U : SplitOctonionAutCandidate R) : ZornMatrix R := U (eMinus (R := R))
def transportedGPlus (U : SplitOctonionAutCandidate R) (i : Fin 3) : ZornMatrix R := U (gPlus (R := R) i)
def transportedGMinus (U : SplitOctonionAutCandidate R) (i : Fin 3) : ZornMatrix R := U (gMinus (R := R) i)

theorem transportedEPlus_idempotent (U : SplitOctonionAutCandidate R) (hU : IsSplitOctonionAut U) :
    transportedEPlus (R := R) U * transportedEPlus (R := R) U = transportedEPlus (R := R) U := by
  change U ePlus * U ePlus = U ePlus
  rw [← hU.2, ePlus_idempotent]

theorem transportedEMinus_idempotent (U : SplitOctonionAutCandidate R) (hU : IsSplitOctonionAut U) :
    transportedEMinus (R := R) U * transportedEMinus (R := R) U = transportedEMinus (R := R) U := by
  change U eMinus * U eMinus = U eMinus
  rw [← hU.2, eMinus_idempotent]

theorem transportedEPlus_mul_transportedEMinus (U : SplitOctonionAutCandidate R) (hU : IsSplitOctonionAut U) :
    transportedEPlus (R := R) U * transportedEMinus (R := R) U = 0 := by
  change U ePlus * U eMinus = 0
  rw [← hU.2, ePlus_mul_eMinus, map_zero]

theorem transportedEMinus_mul_transportedEPlus (U : SplitOctonionAutCandidate R) (hU : IsSplitOctonionAut U) :
    transportedEMinus (R := R) U * transportedEPlus (R := R) U = 0 := by
  change U eMinus * U ePlus = 0
  rw [← hU.2, eMinus_mul_ePlus, map_zero]

theorem transportedGPlus_square_zero (U : SplitOctonionAutCandidate R) (hU : IsSplitOctonionAut U) (i : Fin 3) :
    transportedGPlus (R := R) U i * transportedGPlus (R := R) U i = 0 := by
  change U (gPlus i) * U (gPlus i) = 0
  rw [← hU.2, gPlus_square_zero, map_zero]

theorem transportedGMinus_square_zero (U : SplitOctonionAutCandidate R) (hU : IsSplitOctonionAut U) (i : Fin 3) :
    transportedGMinus (R := R) U i * transportedGMinus (R := R) U i = 0 := by
  change U (gMinus i) * U (gMinus i) = 0
  rw [← hU.2, gMinus_square_zero, map_zero]

-- 4. Stabilizer property: If U(I) = I, the sheets are fixed.

theorem transportedEPlus_eq_of_U_chiralI_eq_chiralI
    (U : SplitOctonionAutCandidate R) (hU : IsSplitOctonionAut U)
    (hI : U chiralI = chiralI) :
    transportedEPlus (R := R) U = ePlus := by
  have h2 : (2 : R) • ePlus (R := R) = (1 : ZornMatrix R) + chiralI := by
    apply ZornMatrix.ext
    · change 2 * 1 = 1 + (1 - 0)
      ring
    · change 2 * 0 = 1 + (0 - 1)
      ring
    · ext j; simp [ePlus, chiralI, eMinus, zornPlus, zornMinus]
    · ext j; simp [ePlus, chiralI, eMinus, zornPlus, zornMinus]
  have h2_map : (2 : R) • transportedEPlus (R := R) U = (2 : R) • ePlus := by
    change (2 : R) • U ePlus = (2 : R) • ePlus
    rw [← map_smul, h2, map_add, hU.1, hI, ← h2]
  calc transportedEPlus (R := R) U
    _ = (⅟(2:R) * 2) • transportedEPlus (R := R) U := by rw [invOf_mul_self, one_smul]
    _ = ⅟(2:R) • ((2:R) • transportedEPlus (R := R) U) := by rw [mul_smul]
    _ = ⅟(2:R) • ((2:R) • ePlus) := by rw [h2_map]
    _ = (⅟(2:R) * 2) • ePlus := by rw [← mul_smul]
    _ = ePlus := by rw [invOf_mul_self, one_smul]

theorem transportedEMinus_eq_of_U_chiralI_eq_chiralI
    (U : SplitOctonionAutCandidate R) (hU : IsSplitOctonionAut U)
    (hI : U chiralI = chiralI) :
    transportedEMinus (R := R) U = eMinus := by
  have h2 : (2 : R) • eMinus (R := R) = (1 : ZornMatrix R) - chiralI := by
    apply ZornMatrix.ext
    · change 2 * 0 = 1 - (1 - 0)
      ring
    · change 2 * 1 = 1 - (0 - 1)
      ring
    · ext j; simp [ePlus, chiralI, eMinus, zornPlus, zornMinus]
    · ext j; simp [ePlus, chiralI, eMinus, zornPlus, zornMinus]
  have h2_map : (2 : R) • transportedEMinus (R := R) U = (2 : R) • eMinus := by
    change (2 : R) • U eMinus = (2 : R) • eMinus
    rw [← map_smul, h2, map_sub, hU.1, hI, ← h2]
  calc transportedEMinus (R := R) U
    _ = (⅟(2:R) * 2) • transportedEMinus (R := R) U := by rw [invOf_mul_self, one_smul]
    _ = ⅟(2:R) • ((2:R) • transportedEMinus (R := R) U) := by rw [mul_smul]
    _ = ⅟(2:R) • ((2:R) • eMinus) := by rw [h2_map]
    _ = (⅟(2:R) * 2) • eMinus := by rw [← mul_smul]
    _ = eMinus := by rw [invOf_mul_self, one_smul]

end InfoGeometry.Canonical.SplitOctonionPeirceChiralFrame
