import Mathlib.Tactic
import InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics

/-!
# InfoGeometry.Arithmetic.HestenesKreinChiralProjectors

Native finite chiral projectors for the Hestenes--Krein split-complex plane.

This file stays on the algebraic side:

* the finite chiral idempotents `e₊` and `e₋`,
* their projector algebra,
* chiral reconstruction of split-complex numbers,
* split-temperature light-cone coordinates,
* pointwise projections of fields and kernels.

No bridge tags.
No socket imports.
No certificate carrier.
No Virasoro placeholder.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.HestenesKreinChiralProjectors

open InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics

/-! ## 1. Chiral idempotents -/

/-- Left/null idempotent `e₊ = (1+j)/2`. -/
def ePlus : SplitComplex :=
  ⟨(1 / 2 : ℝ), (1 / 2 : ℝ)⟩

/-- Right/null idempotent `e₋ = (1-j)/2`. -/
def eMinus : SplitComplex :=
  ⟨(1 / 2 : ℝ), -(1 / 2 : ℝ)⟩

/-- `e₊² = e₊`. -/
theorem ePlus_idempotent :
    SplitComplex.mul ePlus ePlus = ePlus := by
  ext <;> norm_num [ePlus, SplitComplex.mul]

/-- `e₋² = e₋`. -/
theorem eMinus_idempotent :
    SplitComplex.mul eMinus eMinus = eMinus := by
  ext <;> norm_num [eMinus, SplitComplex.mul]

/-- `e₊e₋ = 0`. -/
theorem ePlus_mul_eMinus :
    SplitComplex.mul ePlus eMinus = SplitComplex.zero := by
  ext <;> norm_num [ePlus, eMinus, SplitComplex.mul, SplitComplex.zero]

/-- `e₋e₊ = 0`. -/
theorem eMinus_mul_ePlus :
    SplitComplex.mul eMinus ePlus = SplitComplex.zero := by
  ext <;> norm_num [ePlus, eMinus, SplitComplex.mul, SplitComplex.zero]

/-- `e₊ + e₋ = 1`. -/
theorem ePlus_add_eMinus :
    SplitComplex.add ePlus eMinus = SplitComplex.one := by
  ext <;> norm_num [ePlus, eMinus, SplitComplex.add, SplitComplex.one]

/-- `e₊ - e₋ = j`, expressed through the primitive operations. -/
theorem ePlus_sub_eMinus_eq_j :
    SplitComplex.add ePlus (SplitComplex.neg eMinus) = SplitComplex.j := by
  ext <;> norm_num [ePlus, eMinus, SplitComplex.add,
    SplitComplex.neg, SplitComplex.j]


/-! ## 2. Chiral coefficients and projectors -/

/-- Left/light-cone coefficient of `z = x + j y`: `x+y`. -/
def plusCoeff (z : SplitComplex) : ℝ :=
  z.re + z.hyp

/-- Right/light-cone coefficient of `z = x + j y`: `x-y`. -/
def minusCoeff (z : SplitComplex) : ℝ :=
  z.re - z.hyp

/-- Reconstruct a split-complex number from chiral coefficients. -/
def chiralReconstruct (a b : ℝ) : SplitComplex :=
  SplitComplex.add (SplitComplex.smul a ePlus)
    (SplitComplex.smul b eMinus)

/-- Every split-complex number decomposes into its chiral idempotent sectors. -/
theorem chiralReconstruct_plus_minus (z : SplitComplex) :
    chiralReconstruct (plusCoeff z) (minusCoeff z) = z := by
  cases z
  ext <;> simp [chiralReconstruct, plusCoeff, minusCoeff,
    ePlus, eMinus, SplitComplex.add, SplitComplex.smul] <;> ring

/-- Projection onto the `e₊` sector. -/
def projectPlus (z : SplitComplex) : SplitComplex :=
  SplitComplex.mul ePlus z

/-- Projection onto the `e₋` sector. -/
def projectMinus (z : SplitComplex) : SplitComplex :=
  SplitComplex.mul eMinus z

/-- `P₊z = (x+y)e₊`. -/
theorem projectPlus_eq_smul_plusCoeff (z : SplitComplex) :
    projectPlus z = SplitComplex.smul (plusCoeff z) ePlus := by
  cases z
  ext <;> simp [projectPlus, plusCoeff, ePlus,
    SplitComplex.mul, SplitComplex.smul] <;> ring

/-- `P₋z = (x-y)e₋`. -/
theorem projectMinus_eq_smul_minusCoeff (z : SplitComplex) :
    projectMinus z = SplitComplex.smul (minusCoeff z) eMinus := by
  cases z
  ext <;> simp [projectMinus, minusCoeff, eMinus,
    SplitComplex.mul, SplitComplex.smul] <;> ring

/-- `P₊² = P₊`. -/
theorem projectPlus_idempotent (z : SplitComplex) :
    projectPlus (projectPlus z) = projectPlus z := by
  cases z
  ext <;> simp [projectPlus, ePlus, SplitComplex.mul] <;> ring

/-- `P₋² = P₋`. -/
theorem projectMinus_idempotent (z : SplitComplex) :
    projectMinus (projectMinus z) = projectMinus z := by
  cases z
  ext <;> simp [projectMinus, eMinus, SplitComplex.mul] <;> ring

/-- `P₊P₋ = 0`. -/
theorem projectPlus_projectMinus_zero (z : SplitComplex) :
    projectPlus (projectMinus z) = SplitComplex.zero := by
  cases z
  ext <;> simp [projectPlus, projectMinus, ePlus, eMinus,
    SplitComplex.mul, SplitComplex.zero] <;> ring

/-- `P₋P₊ = 0`. -/
theorem projectMinus_projectPlus_zero (z : SplitComplex) :
    projectMinus (projectPlus z) = SplitComplex.zero := by
  cases z
  ext <;> simp [projectPlus, projectMinus, ePlus, eMinus,
    SplitComplex.mul, SplitComplex.zero] <;> ring

/-- Chiral projections reconstruct the original split-complex number. -/
theorem projectPlus_add_projectMinus (z : SplitComplex) :
    SplitComplex.add (projectPlus z) (projectMinus z) = z := by
  rw [projectPlus_eq_smul_plusCoeff, projectMinus_eq_smul_minusCoeff]
  exact chiralReconstruct_plus_minus z


/-! ## 3. Light-cone coordinates for split Souriau temperatures -/

/-- `σ + j t = (σ+t)e₊ + (σ-t)e₋`. -/
theorem splitTemperature_chiral_decomposition
    (s : SplitSouriauTemperature) :
    chiralReconstruct (leftCone s) (rightCone s) =
      splitTemperatureAsNumber s := by
  cases s
  ext <;> simp [splitTemperatureAsNumber, leftCone, rightCone,
    chiralReconstruct, ePlus, eMinus, SplitComplex.add,
    SplitComplex.smul] <;> ring

/-- Antiunitary reflection sends `u` to `1-v`. -/
theorem antiunitaryReflection_leftCone
    (s : SplitSouriauTemperature) :
    leftCone (antiunitaryReflection s) =
      1 - rightCone s := by
  cases s
  simp [leftCone, rightCone, antiunitaryReflection, splitReflection]
  ring_nf

/-- Antiunitary reflection sends `v` to `1-u`. -/
theorem antiunitaryReflection_rightCone
    (s : SplitSouriauTemperature) :
    rightCone (antiunitaryReflection s) =
      1 - leftCone s := by
  cases s
  simp [leftCone, rightCone, antiunitaryReflection, splitReflection]
  ring_nf


/-! ## 4. Chiral split of normalized prime holonomies -/

/-- Left chiral coefficient of the normalized prime holonomy. -/
def normalizedHolonomyLeftCoeff
    (sigma t period : ℝ) : ℝ :=
  plusCoeff (normalizedPrimeHolonomySplit sigma t period)

/-- Right chiral coefficient of the normalized prime holonomy. -/
def normalizedHolonomyRightCoeff
    (sigma t period : ℝ) : ℝ :=
  minusCoeff (normalizedPrimeHolonomySplit sigma t period)

/-- The normalized prime holonomy decomposes into chiral idempotent sectors. -/
theorem normalizedPrimeHolonomy_chiral_decomposition
    (sigma t period : ℝ) :
    chiralReconstruct
        (normalizedHolonomyLeftCoeff sigma t period)
        (normalizedHolonomyRightCoeff sigma t period)
      =
    normalizedPrimeHolonomySplit sigma t period := by
  exact chiralReconstruct_plus_minus
    (normalizedPrimeHolonomySplit sigma t period)

/-- On the critical line, the chiral reconstruction has split norm one. -/
theorem critical_normalizedPrimeHolonomy_chiral_unit
    {sigma t period : ℝ}
    (hσ : sigma = (1 / 2 : ℝ)) :
    SplitComplex.norm
      (chiralReconstruct
        (normalizedHolonomyLeftCoeff sigma t period)
        (normalizedHolonomyRightCoeff sigma t period))
      =
    1 := by
  rw [normalizedPrimeHolonomy_chiral_decomposition]
  exact normalizedPrimeHolonomySplit_norm_eq_one_of_critical sigma t period hσ


/-! ## 5. Direct field and kernel projection theorems -/

/-- Split-complex-valued field over an arbitrary carrier. -/
abbrev SplitField (State : Type*) :=
  State → SplitComplex

/-- Split-complex-valued kernel over an arbitrary carrier. -/
abbrev SplitKernel (State : Type*) :=
  State → State → SplitComplex

/-- Pointwise left chiral projection of a field. -/
def fieldPlus {State : Type*} (F : SplitField State) :
    SplitField State :=
  fun x => projectPlus (F x)

/-- Pointwise right chiral projection of a field. -/
def fieldMinus {State : Type*} (F : SplitField State) :
    SplitField State :=
  fun x => projectMinus (F x)

/-- Fields decompose pointwise into left and right chiral sectors. -/
theorem field_chiral_decomposition
    {State : Type*} (F : SplitField State) :
    (fun x => SplitComplex.add (fieldPlus F x) (fieldMinus F x)) = F := by
  funext x
  exact projectPlus_add_projectMinus (F x)

/-- Pointwise left chiral projection of a kernel. -/
def kernelPlus {State : Type*} (K : SplitKernel State) :
    SplitKernel State :=
  fun x y => projectPlus (K x y)

/-- Pointwise right chiral projection of a kernel. -/
def kernelMinus {State : Type*} (K : SplitKernel State) :
    SplitKernel State :=
  fun x y => projectMinus (K x y)

/-- Kernels decompose pointwise into left and right chiral sectors. -/
theorem kernel_chiral_decomposition
    {State : Type*} (K : SplitKernel State) :
    (fun x y => SplitComplex.add (kernelPlus K x y) (kernelMinus K x y)) = K := by
  funext x y
  exact projectPlus_add_projectMinus (K x y)

/-- Left kernel projection is idempotent. -/
theorem kernelPlus_idempotent
    {State : Type*} (K : SplitKernel State) :
    kernelPlus (kernelPlus K) = kernelPlus K := by
  funext x y
  exact projectPlus_idempotent (K x y)

/-- Right kernel projection is idempotent. -/
theorem kernelMinus_idempotent
    {State : Type*} (K : SplitKernel State) :
    kernelMinus (kernelMinus K) = kernelMinus K := by
  funext x y
  exact projectMinus_idempotent (K x y)

/-- The left projection of the right kernel sector is zero. -/
theorem kernelPlus_kernelMinus_zero
    {State : Type*} (K : SplitKernel State) :
    kernelPlus (kernelMinus K) = fun _ _ => SplitComplex.zero := by
  funext x y
  exact projectPlus_projectMinus_zero (K x y)

/-- The right projection of the left kernel sector is zero. -/
theorem kernelMinus_kernelPlus_zero
    {State : Type*} (K : SplitKernel State) :
    kernelMinus (kernelPlus K) = fun _ _ => SplitComplex.zero := by
  funext x y
  exact projectMinus_projectPlus_zero (K x y)

end InfoGeometry.Arithmetic.HestenesKreinChiralProjectors
