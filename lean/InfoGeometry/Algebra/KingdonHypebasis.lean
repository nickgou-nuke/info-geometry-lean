import InfoGeometry.Algebra.KingdonSplitOctonion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ZornMatrixSU3.ZornSU3Properties

/-!
# Kingdon hypebasis for the real split octonion realization

This file records the concrete `1, i, j, k, l, li, lj, lk` basis surface on the
Zorn split-octonion target of `KingdonSplitOctonion.realization`.

The point is not a second algebra structure.  It is a readable basis packet:

* `i, j, k` are the realized inserted generators;
* `l` is the diagonal sector switch `p₊ - p₋`;
* `li, lj, lk` are the `l`-twisted off-diagonal companions.
-/

namespace InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion

open InfoGeometry.Algebra.Kingdon
open InfoGeometry.Physics.ZornMatrixSU3

/-- The unit basis element. -/
def hypeOne : ZornMatrix := 1

/-- The three realized Kingdon generators. -/
def hypeI : ZornMatrix := generator (basisVec 0)
def hypeJ : ZornMatrix := generator (basisVec 1)
def hypeK : ZornMatrix := generator (basisVec 2)

/-- The sector-switching diagonal basis element. -/
def hypeL : ZornMatrix := projector1 - projector2

/-- The `l`-twisted companions. -/
def hypeLi : ZornMatrix := hypeL * hypeI
def hypeLj : ZornMatrix := hypeL * hypeJ
def hypeLk : ZornMatrix := hypeL * hypeK

theorem hypeL_eq_sub :
    hypeL = projector1 - projector2 := rfl

/-- `l` acts as `+1` on the upper sector. -/
theorem hypeL_mul_projector1 : hypeL * projector1 = projector1 := by
  ext <;> simp [hypeL, projector1, projector2, mul, add, neg]

/-- `l` acts as `-1` on the lower sector. -/
theorem hypeL_mul_projector2 : hypeL * projector2 = -projector2 := by
  ext <;> simp [hypeL, projector1, projector2, mul, add, neg]

/-- Right multiplication by `l` gives the same sector action. -/
theorem projector1_mul_hypeL : projector1 * hypeL = projector1 := by
  ext <;> simp [hypeL, projector1, projector2, mul, add, neg]

theorem projector2_mul_hypeL : projector2 * hypeL = -projector2 := by
  ext <;> simp [hypeL, projector1, projector2, mul, add, neg]

@[simp] theorem realization_hypeI :
    realization (basisGenerator 0) = hypeI := by
  simp [hypeI, basisGenerator, realization_ι]

@[simp] theorem realization_hypeJ :
    realization (basisGenerator 1) = hypeJ := by
  simp [hypeJ, basisGenerator, realization_ι]

@[simp] theorem realization_hypeK :
    realization (basisGenerator 2) = hypeK := by
  simp [hypeK, basisGenerator, realization_ι]

@[simp] theorem realization_hypeL :
    realization (diagonalUpper - diagonalLower) = hypeL := by
  rw [hypeL, map_sub, realization_diagonalUpper, realization_diagonalLower]
  rfl

@[simp] theorem hypeI_sq : hypeI * hypeI = (1 : ZornMatrix) := by
  simpa [hypeI, basisGenerator, realization_ι] using
    congrArg realization (basisGenerator_sq (i := 0))

@[simp] theorem hypeJ_sq : hypeJ * hypeJ = (1 : ZornMatrix) := by
  simpa [hypeJ, basisGenerator, realization_ι] using
    congrArg realization (basisGenerator_sq (i := 1))

@[simp] theorem hypeK_sq : hypeK * hypeK = (1 : ZornMatrix) := by
  simpa [hypeK, basisGenerator, realization_ι] using
    congrArg realization (basisGenerator_sq (i := 2))

@[simp] theorem hypeL_sq : hypeL * hypeL = (1 : ZornMatrix) := by
  have horth := projector1_projector2_orthogonal
  rcases horth with ⟨h12, h21⟩
  rw [hypeL, sub_mul, mul_sub, mul_sub, projector1_sq, projector2_sq, h12, h21]
  simp [InfoGeometry.Physics.ZornMatrixSU3.add,
    InfoGeometry.Physics.ZornMatrixSU3.neg,
    InfoGeometry.Physics.ZornMatrixSU3.zero,
    projector1, projector2]
  rfl

@[simp] theorem hypeL_mul_hypeI :
    hypeL * hypeI = ⟨0, 0, basisVec 0, fun j => - basisVec 0 j⟩ := by
  rw [hypeL, sub_mul, mul_projector1, mul_projector2]
  simp [hypeI, generator, basisVec, add, neg]
  constructor
  · ext j <;> fin_cases j <;> simp
  · ext j <;> fin_cases j <;> simp [basisVec]

@[simp] theorem hypeI_mul_hypeL :
    hypeI * hypeL = ⟨0, 0, fun j => - basisVec 0 j, basisVec 0⟩ := by
  rw [hypeL, mul_sub, projector1_mul, projector2_mul]
  simp [hypeI, generator, basisVec, add, neg]
  constructor
  · ext j <;> fin_cases j <;> simp [basisVec]
  · ext j <;> fin_cases j <;> simp

@[simp] theorem hypeL_mul_hypeJ :
    hypeL * hypeJ = ⟨0, 0, basisVec 1, fun j => - basisVec 1 j⟩ := by
  rw [hypeL, sub_mul, mul_projector1, mul_projector2]
  simp [hypeJ, generator, basisVec, add, neg]
  constructor
  · ext j <;> fin_cases j <;> simp
  · ext j <;> fin_cases j <;> simp [basisVec]

@[simp] theorem hypeJ_mul_hypeL :
    hypeJ * hypeL = ⟨0, 0, fun j => - basisVec 1 j, basisVec 1⟩ := by
  rw [hypeL, mul_sub, projector1_mul, projector2_mul]
  simp [hypeJ, generator, basisVec, add, neg]
  constructor
  · ext j <;> fin_cases j <;> simp [basisVec]
  · ext j <;> fin_cases j <;> simp

@[simp] theorem hypeL_mul_hypeK :
    hypeL * hypeK = ⟨0, 0, basisVec 2, fun j => - basisVec 2 j⟩ := by
  rw [hypeL, sub_mul, mul_projector1, mul_projector2]
  simp [hypeK, generator, basisVec, add, neg]
  constructor
  · ext j <;> fin_cases j <;> simp
  · ext j <;> fin_cases j <;> simp [basisVec]

@[simp] theorem hypeK_mul_hypeL :
    hypeK * hypeL = ⟨0, 0, fun j => - basisVec 2 j, basisVec 2⟩ := by
  rw [hypeL, mul_sub, projector1_mul, projector2_mul]
  simp [hypeK, generator, basisVec, add, neg]
  constructor
  · ext j <;> fin_cases j <;> simp [basisVec]
  · ext j <;> fin_cases j <;> simp

@[simp] theorem hypeLi_eq :
    hypeLi = ⟨0, 0, basisVec 0, fun j => - basisVec 0 j⟩ := by
  simpa [hypeLi] using hypeL_mul_hypeI

@[simp] theorem hypeLj_eq :
    hypeLj = ⟨0, 0, basisVec 1, fun j => - basisVec 1 j⟩ := by
  simpa [hypeLj] using hypeL_mul_hypeJ

@[simp] theorem hypeLk_eq :
    hypeLk = ⟨0, 0, basisVec 2, fun j => - basisVec 2 j⟩ := by
  simpa [hypeLk] using hypeL_mul_hypeK

end InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion
