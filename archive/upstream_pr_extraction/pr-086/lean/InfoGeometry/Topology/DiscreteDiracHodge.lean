import Mathlib.Tactic
import InfoGeometry.Topology.EckmannDiscreteHodge

/-!
# Discrete Dirac--Hodge Calculus

Finite matrix theorem layer for a three-term cochain complex

```text
  C⁰ --d₀--> C¹ --d₁--> C².
```

The executable DAG matrices remain owned by `DAG.GraphHodge`; this file supplies
reusable proof-grade identities for finite matrices:

* exterior differential and codifferential are nilpotent under the explicit
  complex/adjoint-complex hypotheses;
* the Dirac--Hodge operator `D = d + d*` anticommutes with degree chirality;
* `D²` equals the Hodge Laplacian `d d* + d* d`;
* even forms are sent to odd forms and odd forms are sent to even forms.

No analytic Hodge decomposition theorem, continuum limit, spectral theorem, or
physical zero-mode theorem is asserted here.
-/

open Matrix

namespace InfoGeometry.Topology.DiscreteDiracHodge

noncomputable section

/-- Total finite form space `C⁰ ⊕ C¹ ⊕ C²`. -/
structure TotalForm (n0 n1 n2 : ℕ) where
  zero : Fin n0 → ℝ
  one : Fin n1 → ℝ
  two : Fin n2 → ℝ

@[ext]
theorem TotalForm.ext
    {n0 n1 n2 : ℕ}
    {x y : TotalForm n0 n1 n2}
    (h0 : x.zero = y.zero)
    (h1 : x.one = y.one)
    (h2 : x.two = y.two) :
    x = y := by
  cases x
  cases y
  simp_all

namespace TotalForm

variable {n0 n1 n2 : ℕ}

instance : Zero (TotalForm n0 n1 n2) where
  zero := ⟨0, 0, 0⟩

instance : Add (TotalForm n0 n1 n2) where
  add x y := ⟨x.zero + y.zero, x.one + y.one, x.two + y.two⟩

instance : Neg (TotalForm n0 n1 n2) where
  neg x := ⟨-x.zero, -x.one, -x.two⟩

instance : Sub (TotalForm n0 n1 n2) where
  sub x y := ⟨x.zero - y.zero, x.one - y.one, x.two - y.two⟩

@[simp] theorem zero_zero : (0 : TotalForm n0 n1 n2).zero = 0 := rfl
@[simp] theorem zero_one : (0 : TotalForm n0 n1 n2).one = 0 := rfl
@[simp] theorem zero_two : (0 : TotalForm n0 n1 n2).two = 0 := rfl

@[simp] theorem add_zero_component (x y : TotalForm n0 n1 n2) :
    (x + y).zero = x.zero + y.zero := rfl
@[simp] theorem add_one_component (x y : TotalForm n0 n1 n2) :
    (x + y).one = x.one + y.one := rfl
@[simp] theorem add_two_component (x y : TotalForm n0 n1 n2) :
    (x + y).two = x.two + y.two := rfl

@[simp] theorem neg_zero_component (x : TotalForm n0 n1 n2) :
    (-x).zero = -x.zero := rfl
@[simp] theorem neg_one_component (x : TotalForm n0 n1 n2) :
    (-x).one = -x.one := rfl
@[simp] theorem neg_two_component (x : TotalForm n0 n1 n2) :
    (-x).two = -x.two := rfl

@[simp] theorem sub_zero_component (x y : TotalForm n0 n1 n2) :
    (x - y).zero = x.zero - y.zero := rfl
@[simp] theorem sub_one_component (x y : TotalForm n0 n1 n2) :
    (x - y).one = x.one - y.one := rfl
@[simp] theorem sub_two_component (x y : TotalForm n0 n1 n2) :
    (x - y).two = x.two - y.two := rfl

end TotalForm

variable {n0 n1 n2 : ℕ}

/-- Exterior differential `d : C⁰ ⊕ C¹ ⊕ C² → C⁰ ⊕ C¹ ⊕ C²`. -/
def exteriorDerivative
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : TotalForm n0 n1 n2) : TotalForm n0 n1 n2 :=
  ⟨0, d0.mulVec x.zero, d1.mulVec x.one⟩

/-- Codifferential `d*`, represented by transposed incidence matrices. -/
def codifferential
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : TotalForm n0 n1 n2) : TotalForm n0 n1 n2 :=
  ⟨d0.transpose.mulVec x.one, d1.transpose.mulVec x.two, 0⟩

/-- Dirac--Hodge operator `D = d + d*`. -/
def diracHodge
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : TotalForm n0 n1 n2) : TotalForm n0 n1 n2 :=
  exteriorDerivative d0 d1 x + codifferential d0 d1 x

/-- Hodge Laplacian `L = d d* + d* d`. -/
def hodgeLaplacian
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : TotalForm n0 n1 n2) : TotalForm n0 n1 n2 :=
  exteriorDerivative d0 d1 (codifferential d0 d1 x) +
    codifferential d0 d1 (exteriorDerivative d0 d1 x)

/-- Degree chirality: even forms have sign `+1`, odd forms sign `-1`. -/
def chirality (x : TotalForm n0 n1 n2) : TotalForm n0 n1 n2 :=
  ⟨x.zero, -x.one, x.two⟩

/-- The cochain-complex condition `d₁ d₀ = 0`. -/
def IsCochainComplex
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ) : Prop :=
  d1 * d0 = 0

/-- The adjoint complex condition `(d₀ᵀ)(d₁ᵀ) = 0`. -/
def IsAdjointCochainComplex
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ) : Prop :=
  d0.transpose * d1.transpose = 0

@[simp]
lemma mulVec_neg_apply {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) (i : Fin m) :
    (A.mulVec (-v)) i = -(A.mulVec v) i := by
  rw [Matrix.mulVec_neg]
  rfl

@[simp]
lemma mulVec_add_apply {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (v w : Fin n → ℝ) (i : Fin m) :
    (A.mulVec (v + w)) i = (A.mulVec v) i + (A.mulVec w) i := by
  rw [Matrix.mulVec_add]
  rfl

theorem exteriorDerivative_sq_zero
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hComplex : IsCochainComplex d0 d1)
    (x : TotalForm n0 n1 n2) :
    exteriorDerivative d0 d1 (exteriorDerivative d0 d1 x) = 0 := by
  ext i <;> simp [exteriorDerivative]
  have hmat : (d1 * d0).mulVec x.zero = 0 := by
    rw [hComplex]
    simp
  exact congrFun (by simpa [Matrix.mulVec_mulVec] using hmat) i

theorem codifferential_sq_zero
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hAdjoint : IsAdjointCochainComplex d0 d1)
    (x : TotalForm n0 n1 n2) :
    codifferential d0 d1 (codifferential d0 d1 x) = 0 := by
  ext i <;> simp [codifferential]
  have hmat : (d0.transpose * d1.transpose).mulVec x.two = 0 := by
    rw [hAdjoint]
    simp
  exact congrFun (by simpa [Matrix.mulVec_mulVec] using hmat) i

theorem chirality_sq (x : TotalForm n0 n1 n2) :
    chirality (chirality x) = x := by
  ext i <;> simp [chirality]

theorem exteriorDerivative_anticommutes_chirality
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : TotalForm n0 n1 n2) :
    exteriorDerivative d0 d1 (chirality x) +
        chirality (exteriorDerivative d0 d1 x) = 0 := by
  ext i <;> simp [exteriorDerivative, chirality]

theorem codifferential_anticommutes_chirality
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : TotalForm n0 n1 n2) :
    codifferential d0 d1 (chirality x) +
        chirality (codifferential d0 d1 x) = 0 := by
  ext i <;> simp [codifferential, chirality]

theorem diracHodge_anticommutes_chirality
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : TotalForm n0 n1 n2) :
    diracHodge d0 d1 (chirality x) +
        chirality (diracHodge d0 d1 x) = 0 := by
  ext i
  · simp [diracHodge, exteriorDerivative, codifferential, chirality]
  · simp [diracHodge, exteriorDerivative, codifferential, chirality]
    ring
  · simp [diracHodge, exteriorDerivative, codifferential, chirality]

theorem diracHodge_sq_eq_hodgeLaplacian
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hComplex : IsCochainComplex d0 d1)
    (hAdjoint : IsAdjointCochainComplex d0 d1)
    (x : TotalForm n0 n1 n2) :
    diracHodge d0 d1 (diracHodge d0 d1 x) =
      hodgeLaplacian d0 d1 x := by
  ext i
  · have hcross : ((d0.transpose * d1.transpose).mulVec x.two) i = 0 := by
      have hmat : (d0.transpose * d1.transpose).mulVec x.two = 0 := by
        rw [hAdjoint]
        simp
      exact congrFun hmat i
    simp [diracHodge, hodgeLaplacian, exteriorDerivative, codifferential,
      Matrix.mulVec_add, Matrix.mulVec_mulVec, hcross]
  · simp [diracHodge, hodgeLaplacian, exteriorDerivative, codifferential,
      Matrix.mulVec_add, Matrix.mulVec_mulVec, add_comm]
  · have hcross : ((d1 * d0).mulVec x.zero) i = 0 := by
      have hmat : (d1 * d0).mulVec x.zero = 0 := by
        rw [hComplex]
        simp
      exact congrFun hmat i
    simp [diracHodge, hodgeLaplacian, exteriorDerivative, codifferential,
      Matrix.mulVec_add, Matrix.mulVec_mulVec, hcross]

/-- An even form has no one-form component. -/
def IsEvenForm (x : TotalForm n0 n1 n2) : Prop :=
  x.one = 0

/-- An odd form has no zero- or two-form component. -/
def IsOddForm (x : TotalForm n0 n1 n2) : Prop :=
  x.zero = 0 ∧ x.two = 0

theorem diracHodge_maps_even_to_odd
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {x : TotalForm n0 n1 n2}
    (hx : IsEvenForm x) :
    IsOddForm (diracHodge d0 d1 x) := by
  constructor
  · simp [diracHodge, exteriorDerivative, codifferential]
    rw [hx]
    simp
  · simp [diracHodge, exteriorDerivative, codifferential]
    rw [hx]
    simp

theorem diracHodge_maps_odd_to_even
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {x : TotalForm n0 n1 n2}
    (hx : IsOddForm x) :
    IsEvenForm (diracHodge d0 d1 x) := by
  rcases hx with ⟨h0, h2⟩
  simp [IsEvenForm, diracHodge, exteriorDerivative, codifferential]
  rw [h0, h2]
  simp

/-- A finite one-form is harmonic when it is closed and coclosed. -/
def HarmonicOneForm
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) : Prop :=
  d1.mulVec x = 0 ∧ d0.transpose.mulVec x = 0

/-- Readback to the Eckmann owner predicate for harmonic one-forms. -/
theorem harmonicOneForm_iff_eckmannHarmonic1
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) :
    HarmonicOneForm d0 d1 x ↔
      EckmannDiscreteHodge.eckmannHarmonic1 d0 d1 x := by
  rfl

end

end InfoGeometry.Topology.DiscreteDiracHodge
