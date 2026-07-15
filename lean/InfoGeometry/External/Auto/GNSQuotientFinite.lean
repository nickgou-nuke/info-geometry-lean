import Mathlib
import InfoGeometry.External.Auto.FiniteGNSConstruction

/-!
# Finite GNS quotient construction

A finite GNS construction for the vector state on `M₂(ℂ)`.
The GNS equivalence is the left-kernel relation: two matrices are equivalent
when they act identically on the cyclic vector `Ω=e₀`, equivalently when their
first columns agree.

This gives a quotient model of the finite GNS pre-Hilbert space, the
left-regular representation, and the expectation identity `ω(A)=<[1],π(A)[1]>`.
-/

noncomputable section

namespace GNSQuotientFinite

open Matrix
open scoped BigOperators

abbrev M2C := FiniteGNSConstruction.M2C
abbrev V2C := FiniteGNSConstruction.V2C

/-- The finite vector state `ω(A)=<Ω,AΩ>`. -/
def omega : M2C → ℂ := FiniteGNSConstruction.omegaState

/-- Raw finite GNS inner product `<[A],[B]> = ω(A†B)`. -/
def innerRaw (A B : M2C) : ℂ := omega (star A * B)

/-- GNS equivalence: two representatives have the same action on `Ω`, i.e. the
same first column. -/
def gnsRel (A B : M2C) : Prop := A 0 0 = B 0 0 ∧ A 1 0 = B 1 0

/-- The relation is reflexive. -/
theorem gnsRel_refl (A : M2C) : gnsRel A A := ⟨rfl, rfl⟩

/-- The relation is symmetric. -/
theorem gnsRel_symm {A B : M2C} (h : gnsRel A B) : gnsRel B A := ⟨h.1.symm, h.2.symm⟩

/-- The relation is transitive. -/
theorem gnsRel_trans {A B C : M2C} (hAB : gnsRel A B) (hBC : gnsRel B C) :
    gnsRel A C := ⟨hAB.1.trans hBC.1, hAB.2.trans hBC.2⟩

/-- The finite GNS setoid. -/
def gnsSetoid : Setoid M2C where
  r := gnsRel
  iseqv := ⟨gnsRel_refl, @gnsRel_symm, @gnsRel_trans⟩

/-- The finite GNS quotient space. -/
def GNSSpace : Type := Quotient gnsSetoid

/-- The class map `A ↦ [A]`. -/
def gnsClass (A : M2C) : GNSSpace := Quotient.mk gnsSetoid A

/-- The cyclic vector `[1]`. -/
def cyclic : GNSSpace := gnsClass (1 : M2C)

/-- The first-column equivalence agrees with equality of action on the cyclic
vector. -/
theorem gnsRel_iff_same_Omega (A B : M2C) :
    gnsRel A B ↔ FiniteGNSConstruction.pi A FiniteGNSConstruction.Omega =
      FiniteGNSConstruction.pi B FiniteGNSConstruction.Omega := by
  constructor
  · intro h
    funext i
    fin_cases i <;> simp [FiniteGNSConstruction.pi, FiniteGNSConstruction.matVec,
      FiniteGNSConstruction.Omega, Fin.sum_univ_two, h.1, h.2]
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [FiniteGNSConstruction.pi, FiniteGNSConstruction.matVec,
      FiniteGNSConstruction.Omega, Fin.sum_univ_two] at h0 h1
    constructor
    · simpa using h0
    · simpa using h1

/-- The raw inner product depends only on the first columns. -/
theorem innerRaw_eq_first_column (A B : M2C) :
    innerRaw A B = star (A 0 0) * B 0 0 + star (A 1 0) * B 1 0 := by
  simp [innerRaw, omega, FiniteGNSConstruction.omegaState_apply, Matrix.mul_apply,
    Matrix.star_apply, Fin.sum_univ_two]

/-- The raw GNS inner product is well-defined under the quotient relation. -/
theorem innerRaw_well_defined {A A' B B' : M2C}
    (hA : gnsRel A A') (hB : gnsRel B B') : innerRaw A B = innerRaw A' B' := by
  rw [innerRaw_eq_first_column A B, innerRaw_eq_first_column A' B']
  rw [hA.1, hA.2, hB.1, hB.2]

/-- Lifted inner product on the finite GNS quotient. -/
def inner (u v : GNSSpace) : ℂ :=
  Quotient.lift₂ innerRaw
    (by
      intro A B A' B' hA hB
      exact innerRaw_well_defined hA hB)
    u v

/-- Left multiplication is well-defined on the GNS quotient. -/
theorem leftMul_well_defined (A X Y : M2C) (h : gnsRel X Y) : gnsRel (A * X) (A * Y) := by
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2]

/-- The finite GNS representation `π(A)[X]=[AX]`. -/
def representation (A : M2C) : GNSSpace → GNSSpace :=
  Quotient.map (fun X : M2C => A * X) (leftMul_well_defined A)

/-- Representation preserves multiplication. -/
theorem representation_mul (A B : M2C) (u : GNSSpace) :
    representation (A * B) u = representation A (representation B u) := by
  refine Quotient.inductionOn u ?_
  intro X
  simp [representation]
  exact Quotient.sound (by
    constructor <;> simp [Matrix.mul_assoc])

/-- The GNS expectation identity: `ω(A)=<[1],π(A)[1]>`. -/
theorem gns_expectation_value (A : M2C) :
    inner cyclic (representation A cyclic) = omega A := by
  simp [inner, cyclic, gnsClass, representation, innerRaw, omega,
    FiniteGNSConstruction.omegaState_apply]

/-- The cyclic vector is cyclic: every quotient class has a representative `A[1]`. -/
theorem cyclic_is_cyclic (u : GNSSpace) : ∃ A : M2C, representation A cyclic = u := by
  refine Quotient.inductionOn u ?_
  intro X
  refine ⟨X, ?_⟩
  exact Quotient.sound (by
    constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

/-- Faithfulness fails for the vector state: nonzero matrices with zero first
column vanish in the GNS quotient. -/
def nullExample : M2C := !![(0 : ℂ), 1; 0, 0]

/-- The null example is equivalent to zero. -/
theorem nullExample_eq_zero_in_GNS : gnsClass nullExample = gnsClass 0 := by
  exact Quotient.sound (show gnsRel nullExample 0 by simp [gnsRel, nullExample])

/-- But the null example is not zero as an algebra element. -/
theorem nullExample_ne_zero : nullExample ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [nullExample] at h01

/-- Synthesis theorem for the finite quotient GNS construction. -/
theorem finite_gns_quotient_synthesis :
    (∀ A : M2C, inner cyclic (representation A cyclic) = omega A) ∧
    (∀ u : GNSSpace, ∃ A : M2C, representation A cyclic = u) ∧
    gnsClass nullExample = gnsClass 0 ∧
    nullExample ≠ 0 := by
  constructor
  · intro A
    exact gns_expectation_value A
  · constructor
    · intro u
      exact cyclic_is_cyclic u
    · constructor
      · exact nullExample_eq_zero_in_GNS
      · exact nullExample_ne_zero

end GNSQuotientFinite
