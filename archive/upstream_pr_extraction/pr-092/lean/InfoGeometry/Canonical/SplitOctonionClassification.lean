import Mathlib.Algebra.Ring.Associator
import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionClassificationCore

/-!
# Split-octonion classification

This file closes the concrete property layer on the explicit Zorn carrier.

The theorem surface is the existential one:

* a non-scalar element has a nonzero commutator property;
* a non-scalar element has a nonzero associator property.

The proofs are coordinate proofs on the explicit Zorn basis, not abstract
associative-ring arguments.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionClassification

open scoped BigOperators

variable {R : Type*} [CommRing R]

namespace ZornMatrix

open InfoGeometry.Canonical.SplitOctonionClassificationCore.ZornMatrix

/-- Scalar Zorn elements are scalar multiples of the identity. -/
def IsScalar (x : InfoGeometry.Canonical.ZornMatrix R) : Prop :=
  ∃ r : R, x = r • (1 : InfoGeometry.Canonical.ZornMatrix R)

@[simp] theorem a_sub (x y : InfoGeometry.Canonical.ZornMatrix R) :
    (x - y).a = x.a - y.a := by
  rfl

@[simp] theorem b_sub (x y : InfoGeometry.Canonical.ZornMatrix R) :
    (x - y).b = x.b - y.b := by
  rfl

@[simp] theorem x_sub (x y : InfoGeometry.Canonical.ZornMatrix R) :
    (x - y).x = x.x - y.x := by
  rfl

@[simp] theorem y_sub (x y : InfoGeometry.Canonical.ZornMatrix R) :
    (x - y).y = x.y - y.y := by
  rfl

@[simp] theorem vecHead_eq (v : Fin 3 → R) : Matrix.vecHead v = v 0 := by
  rfl

@[simp] theorem vecHead_tail_eq (v : Fin 3 → R) :
    Matrix.vecHead (Matrix.vecTail v) = v 1 := by
  rfl

@[simp] theorem vecHead_tail_tail_eq (v : Fin 3 → R) :
    Matrix.vecHead (Matrix.vecTail (Matrix.vecTail v)) = v 2 := by
  rfl

/-- Coordinate readout of the commutator with an upper basis vector. -/
theorem commutator_upper_a (x : InfoGeometry.Canonical.ZornMatrix R) (i : Fin 3) :
    (SplitOctonionClassificationCore.ZornMatrix.commutator (R := R) x (upper (basisVec i))).a =
      - x.y i := by
  fin_cases i <;> rcases x with ⟨a, b, u, v⟩ <;>
    simp [SplitOctonionClassificationCore.ZornMatrix.commutator,
      SplitOctonionClassificationCore.ZornMatrix.mulZ,
      upper, basisVec, e0, e1, e2,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]

/-- Coordinate readout of the commutator with a lower basis vector. -/
theorem commutator_lower_a (x : InfoGeometry.Canonical.ZornMatrix R) (i : Fin 3) :
    (SplitOctonionClassificationCore.ZornMatrix.commutator (R := R) x (lower (basisVec i))).a =
      x.x i := by
  fin_cases i <;> rcases x with ⟨a, b, u, v⟩ <;>
    simp [SplitOctonionClassificationCore.ZornMatrix.commutator,
      SplitOctonionClassificationCore.ZornMatrix.mulZ,
      lower, basisVec, e0, e1, e2,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]

/-- The lower `e₀` commutator detects the diagonal mismatch `b - a`. -/
theorem commutator_lower_e0_y0 (x : InfoGeometry.Canonical.ZornMatrix R) :
    (SplitOctonionClassificationCore.ZornMatrix.commutator (R := R) x (lower e0)).y 0 =
      x.b - x.a := by
  rcases x with ⟨a, b, u, v⟩
  simp [SplitOctonionClassificationCore.ZornMatrix.commutator,
    SplitOctonionClassificationCore.ZornMatrix.mulZ, lower, e0,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Canonical.ZornMatrix.cross]

/-- A non-scalar Zorn element has a nonzero commutator property. -/
theorem exists_nonzero_commutator_of_not_scalar
    {x : InfoGeometry.Canonical.ZornMatrix R}
    (hx : ¬ ∃ r : R, x = r • (1 : InfoGeometry.Canonical.ZornMatrix R)) :
    ∃ y : InfoGeometry.Canonical.ZornMatrix R,
      SplitOctonionClassificationCore.ZornMatrix.commutator (R := R) x y ≠ 0 := by
  rcases x with ⟨a, b, u, v⟩
  by_cases hAB : a = b
  · by_cases hu0 : u = 0
    · by_cases hv0 : v = 0
      · apply False.elim
        apply hx
        refine ⟨a, ?_⟩
        have h1a : (1 : InfoGeometry.Canonical.ZornMatrix R).a = 1 := by rfl
        have h1b : (1 : InfoGeometry.Canonical.ZornMatrix R).b = 1 := by rfl
        have h1x : (1 : InfoGeometry.Canonical.ZornMatrix R).x = 0 := by rfl
        have h1y : (1 : InfoGeometry.Canonical.ZornMatrix R).y = 0 := by rfl
        ext <;> simp [hAB, hu0, hv0, Equiv.smul_def, ZornMatrix.coordEquiv,
          h1a, h1b, h1x, h1y]
      · have hvnz : v ≠ 0 := hv0
        have hcoord : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
          by_contra h
          push_neg at h
          rcases h with ⟨h0, h1, h2⟩
          exact hvnz (by ext i <;> fin_cases i <;> simp [h0, h1, h2])
        rcases hcoord with hv0' | hv1' | hv2'
        · refine ⟨upper e0, ?_⟩
          intro hzero
          have hcoord' := congrArg (fun z : InfoGeometry.Canonical.ZornMatrix R => z.a) hzero
          have h0a : (0 : InfoGeometry.Canonical.ZornMatrix R).a = 0 := by rfl
          have hneg : -v 0 = (0 : R) := by
            simpa [SplitOctonionClassificationCore.ZornMatrix.commutator,
              SplitOctonionClassificationCore.ZornMatrix.mulZ, upper, e0,
              InfoGeometry.Canonical.ZornMatrix.dot,
              InfoGeometry.Canonical.ZornMatrix.cross, h0a] using hcoord'
          have hcoord'' : v 0 = 0 := by
            simpa using hneg
          exact hv0' hcoord''
        · refine ⟨upper e1, ?_⟩
          intro hzero
          have hcoord' := congrArg (fun z : InfoGeometry.Canonical.ZornMatrix R => z.a) hzero
          have h0a : (0 : InfoGeometry.Canonical.ZornMatrix R).a = 0 := by rfl
          have hneg : -v 1 = (0 : R) := by
            simpa [SplitOctonionClassificationCore.ZornMatrix.commutator,
              SplitOctonionClassificationCore.ZornMatrix.mulZ, upper, e1,
              InfoGeometry.Canonical.ZornMatrix.dot,
              InfoGeometry.Canonical.ZornMatrix.cross, h0a] using hcoord'
          have hcoord'' : v 1 = 0 := by
            simpa using hneg
          exact hv1' hcoord''
        · refine ⟨upper e2, ?_⟩
          intro hzero
          have hcoord' := congrArg (fun z : InfoGeometry.Canonical.ZornMatrix R => z.a) hzero
          have h0a : (0 : InfoGeometry.Canonical.ZornMatrix R).a = 0 := by rfl
          have hneg : -v 2 = (0 : R) := by
            simpa [SplitOctonionClassificationCore.ZornMatrix.commutator,
              SplitOctonionClassificationCore.ZornMatrix.mulZ, upper, e2,
              InfoGeometry.Canonical.ZornMatrix.dot,
              InfoGeometry.Canonical.ZornMatrix.cross, h0a] using hcoord'
          have hcoord'' : v 2 = 0 := by
            simpa using hneg
          exact hv2' hcoord''
    · have hunz : u ≠ 0 := hu0
      have hcoord : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
        by_contra h
        push_neg at h
        rcases h with ⟨h0, h1, h2⟩
        exact hunz (by ext i <;> fin_cases i <;> simp [h0, h1, h2])
      rcases hcoord with hu0' | hu1' | hu2'
      · refine ⟨lower e0, ?_⟩
        intro hzero
        have hcoord' := congrArg (fun z : InfoGeometry.Canonical.ZornMatrix R => z.a) hzero
        have h0a : (0 : InfoGeometry.Canonical.ZornMatrix R).a = 0 := by rfl
        have hcoord'' : u 0 = 0 := by
          simpa [SplitOctonionClassificationCore.ZornMatrix.commutator,
            SplitOctonionClassificationCore.ZornMatrix.mulZ, lower, e0,
            InfoGeometry.Canonical.ZornMatrix.dot,
            InfoGeometry.Canonical.ZornMatrix.cross, h0a] using hcoord'
        exact hu0' hcoord''
      · refine ⟨lower e1, ?_⟩
        intro hzero
        have hcoord' := congrArg (fun z : InfoGeometry.Canonical.ZornMatrix R => z.a) hzero
        have h0a : (0 : InfoGeometry.Canonical.ZornMatrix R).a = 0 := by rfl
        have hcoord'' : u 1 = 0 := by
          simpa [SplitOctonionClassificationCore.ZornMatrix.commutator,
            SplitOctonionClassificationCore.ZornMatrix.mulZ, lower, e1,
            InfoGeometry.Canonical.ZornMatrix.dot,
            InfoGeometry.Canonical.ZornMatrix.cross, h0a] using hcoord'
        exact hu1' hcoord''
      · refine ⟨lower e2, ?_⟩
        intro hzero
        have hcoord' := congrArg (fun z : InfoGeometry.Canonical.ZornMatrix R => z.a) hzero
        have h0a : (0 : InfoGeometry.Canonical.ZornMatrix R).a = 0 := by rfl
        have hcoord'' : u 2 = 0 := by
          simpa [SplitOctonionClassificationCore.ZornMatrix.commutator,
            SplitOctonionClassificationCore.ZornMatrix.mulZ, lower, e2,
            InfoGeometry.Canonical.ZornMatrix.dot,
            InfoGeometry.Canonical.ZornMatrix.cross, h0a] using hcoord'
        exact hu2' hcoord''
  · refine ⟨lower e0, ?_⟩
    intro hzero
    have hcoord' := congrArg (fun z : InfoGeometry.Canonical.ZornMatrix R => z.y 0) hzero
    have hcoord'' : b - a = 0 := by
      simpa [SplitOctonionClassificationCore.ZornMatrix.commutator,
        SplitOctonionClassificationCore.ZornMatrix.mulZ, lower, e0,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross] using hcoord'
    exact hAB (sub_eq_zero.mp hcoord'').symm

/-- A non-scalar Zorn element has a nonzero associator property. -/
theorem exists_nonzero_associator_of_not_scalar
    {x : InfoGeometry.Canonical.ZornMatrix R}
    (hx : ¬ ∃ r : R, x = r • (1 : InfoGeometry.Canonical.ZornMatrix R)) :
    ∃ y z : InfoGeometry.Canonical.ZornMatrix R,
      SplitOctonionClassificationCore.ZornMatrix.associator (R := R) x y z ≠ 0 := by
  exact SplitOctonionClassificationCore.ZornMatrix.nonzero_associator_of_not_scalar
    (R := R) x hx

/-- The commutant of the explicit Zorn carrier collapses to scalars. -/
theorem commutant_eq_scalars
    (x : InfoGeometry.Canonical.ZornMatrix R)
    (hcomm : ∀ y : InfoGeometry.Canonical.ZornMatrix R,
      SplitOctonionClassificationCore.ZornMatrix.commutator (R := R) x y = 0) :
    IsScalar (R := R) x := by
  by_contra hx
  rcases exists_nonzero_commutator_of_not_scalar (R := R) (x := x) hx with
    ⟨y, hy⟩
  exact hy (hcomm y)

/-- The left nucleus of the explicit Zorn carrier collapses to scalars. -/
theorem left_nucleus_eq_scalars
    (x : InfoGeometry.Canonical.ZornMatrix R)
    (hnuc : ∀ y z : InfoGeometry.Canonical.ZornMatrix R,
      SplitOctonionClassificationCore.ZornMatrix.associator (R := R) x y z = 0) :
    IsScalar (R := R) x := by
  by_contra hx
  rcases exists_nonzero_associator_of_not_scalar (R := R) (x := x) hx with
    ⟨y, z, hyz⟩
  exact hyz (hnuc y z)

end ZornMatrix

end InfoGeometry.Canonical.SplitOctonionClassification
