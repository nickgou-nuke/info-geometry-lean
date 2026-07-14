import Mathlib.Tactic

/-!
# Split Jordan--spinor boundary layer

This file records a theorem-safe abstraction of the split-algebraic
Jordan/spinor triad highlighted in Fioresi--Latini--Marrani,
"Klein and Conformal Superspaces, Split Algebras and Spinor Orbits"
(arXiv:1603.09063v2).

It formalizes the finite structural layer only:

* split composition algebra parameters with `q ∈ {2,4,8}`;
* the Hermitian `2 × 2` Jordan carrier `J₂(A_s)` as coordinates
  `(α, β, Z)`;
* its quadratic determinant `αβ - N(Z)`;
* the spinor carrier `A_s²` and raw `2 × 2` action;
* orbit-representative/stabilizer predicates for the Klein-spinor
  stratification discussion.

Boundary: this file does **not** prove the global isomorphism
`Str₀(J₂(A_s)) ≃ Spin(q/2+1,q/2+1)`, the double-cover theorems, or the
full orbit classification of Section 5.1.  Those are represented as explicit
interfaces/sockets to be filled only by later kernel-checked constructions.
-/

namespace SplitJordanSpinor

/-- The three split composition dimensions used in the paper: `q = 2,4,8`. -/
inductive SplitCriticalDimension where
  | splitComplex
  | splitQuaternion
  | splitOctonion
  deriving DecidableEq, Repr

namespace SplitCriticalDimension

/-- Real dimension of the split composition algebra. -/
def q : SplitCriticalDimension → ℕ
  | splitComplex => 2
  | splitQuaternion => 4
  | splitOctonion => 8

/-- Ambient split-signature dimension `D = q + 2`, namely `4,6,10`. -/
def D (d : SplitCriticalDimension) : ℕ :=
  q d + 2

/-- The only allowed split composition dimensions are `2,4,8`. -/
theorem q_val (d : SplitCriticalDimension) : q d = 2 ∨ q d = 4 ∨ q d = 8 := by
  cases d <;> simp [q]

@[simp] theorem D_splitComplex : D splitComplex = 4 := by rfl
@[simp] theorem D_splitQuaternion : D splitQuaternion = 6 := by rfl
@[simp] theorem D_splitOctonion : D splitOctonion = 10 := by rfl

end SplitCriticalDimension

/--
Abstract split composition algebra interface.

We deliberately use `NonAssocSemiring`, not `Ring`/`Algebra`, so that the
split-octonionic case is not accidentally forced to be associative.  The only
multiplicative law required here is the norm-composition identity.
-/
class SplitCompositionAlgebra (K A : Type*) [CommRing K] [NonAssocSemiring A] [SMul K A] where
  /-- Real coordinate dimension `q`; in applications this is `2`, `4`, or `8`. -/
  q : ℕ
  /-- Critical-dimension restriction from the split composition algebra list. -/
  q_val : q = 2 ∨ q = 4 ∨ q = 8
  /-- Conjugation on the split composition algebra. -/
  conjugate : A → A
  /-- Quadratic norm. -/
  norm : A → K
  /-- The norm of zero is zero. -/
  norm_zero_eq : norm 0 = 0
  /-- Norm composition identity. -/
  norm_map_mul : ∀ x y : A, norm (x * y) = norm x * norm y
  /-- Coordinate form of `x x̄ = N(x) · 1`. -/
  conj_self : ∀ x : A, x * conjugate x = (norm x) • (1 : A)
  /-- Norm of one is one. -/
  norm_one : norm (1 : A) = 1

namespace SplitCompositionAlgebraLemmas

variable {K A : Type*} [CommRing K] [NonAssocSemiring A] [SMul K A]
variable [SplitCompositionAlgebra K A]

/-- Local notation-free accessor for conjugation. -/
def conj (x : A) : A :=
  SplitCompositionAlgebra.conjugate (K := K) (A := A) x

/-- Local notation-free accessor for the split norm. -/
def splitNorm (x : A) : K :=
  SplitCompositionAlgebra.norm (K := K) (A := A) x

@[simp]
theorem splitNorm_zero :
    splitNorm (K := K) (A := A) (0 : A) = 0 :=
  SplitCompositionAlgebra.norm_zero_eq (K := K) (A := A)

/-- Restatement of the norm-composition law. -/
theorem splitNorm_mul (x y : A) :
    splitNorm (K := K) (A := A) (x * y) =
      splitNorm (K := K) (A := A) x * splitNorm (K := K) (A := A) y :=
  SplitCompositionAlgebra.norm_map_mul (K := K) (A := A) x y

/-- Restatement of the conjugate/norm law. -/
theorem mul_conj_eq_norm_smul_one (x : A) :
    x * conj (K := K) (A := A) x = splitNorm (K := K) (A := A) x • (1 : A) :=
  SplitCompositionAlgebra.conj_self (K := K) (A := A) x

end SplitCompositionAlgebraLemmas

/--
Equation (3.4): coordinate carrier for the Hermitian Jordan algebra `J₂(A_s)`.
The intended matrix is `[[α, Z], [conj Z, β]]`.
-/
structure JordanMatrix2 (K A : Type*) where
  α : K
  β : K
  Z : A
  deriving Repr

namespace JordanMatrix2

variable {K A : Type*} [CommRing K] [NonAssocSemiring A] [SMul K A]
variable [SplitCompositionAlgebra K A]

/-- Equation (3.5): determinant/quadratic norm `αβ - N(Z)`. -/
def determinant (J : JordanMatrix2 K A) : K :=
  J.α * J.β - SplitCompositionAlgebraLemmas.splitNorm (K := K) (A := A) J.Z

/-- Diagonal Jordan element with zero off-diagonal coordinate. -/
def diagonal (α β : K) : JordanMatrix2 K A :=
  ⟨α, β, 0⟩

@[simp]
theorem determinant_diagonal (α β : K) :
    determinant (A := A) (diagonal (A := A) α β) = α * β := by
  simp [determinant, diagonal, SplitCompositionAlgebraLemmas.splitNorm,
    SplitCompositionAlgebra.norm_zero_eq]

end JordanMatrix2

/-- Equations (4.11), (4.15), (4.19): the spinor carrier `A_s²`. -/
structure Spinor2 (A : Type*) where
  ψ_pos : A
  ψ_neg : A
  deriving DecidableEq, Repr

namespace Spinor2

variable {A : Type*} [NonAssocSemiring A]

/-- Zero spinor. -/
def zero : Spinor2 A :=
  ⟨0, 0⟩

/-- Generic representative `(1,0)^t` used in the Section 5.1 orbit discussion. -/
def genericRepresentative : Spinor2 A :=
  ⟨1, 0⟩

/-- Null/zero-divisor representative `(ε,0)^t`, for e.g. `ε = E = 1+j` in `C_s`. -/
def nullRepresentative (ε : A) : Spinor2 A :=
  ⟨ε, 0⟩

/-- Paper-equivalent null representative `(ε,ε)^t`. -/
def diagonalNullRepresentative (ε : A) : Spinor2 A :=
  ⟨ε, ε⟩

@[ext]
theorem ext {ψ φ : Spinor2 A}
    (hpos : ψ.ψ_pos = φ.ψ_pos) (hneg : ψ.ψ_neg = φ.ψ_neg) : ψ = φ := by
  rcases ψ with ⟨ψp, ψn⟩
  rcases φ with ⟨φp, φn⟩
  dsimp at hpos hneg
  cases hpos
  cases hneg
  rfl

end Spinor2

/-- Raw `2 × 2` split-algebra matrix coordinates. -/
structure SplitMatrix2 (A : Type*) where
  aa : A
  ab : A
  ba : A
  bb : A
  deriving Repr

namespace SplitMatrix2

variable {A : Type*} [NonAssocSemiring A]

/-- Identity matrix. -/
def identity : SplitMatrix2 A :=
  ⟨1, 0, 0, 1⟩

/-- Raw matrix action on the spinor carrier `A_s²`. -/
def spinorAction (M : SplitMatrix2 A) (ψ : Spinor2 A) : Spinor2 A where
  ψ_pos := M.aa * ψ.ψ_pos + M.ab * ψ.ψ_neg
  ψ_neg := M.ba * ψ.ψ_pos + M.bb * ψ.ψ_neg

@[simp]
theorem identity_spinorAction (ψ : Spinor2 A) :
    spinorAction (A := A) identity ψ = ψ := by
  ext <;> simp [spinorAction, identity]

/-- Predicate that a raw `2 × 2` matrix stabilizes a spinor. -/
def Stabilizes (M : SplitMatrix2 A) (ψ : Spinor2 A) : Prop :=
  spinorAction M ψ = ψ

@[simp]
theorem identity_stabilizes (ψ : Spinor2 A) :
    Stabilizes (A := A) identity ψ := by
  simp [Stabilizes]

@[simp]
theorem identity_stabilizes_generic :
    Stabilizes (A := A) identity (Spinor2.genericRepresentative (A := A)) := by
  simp

@[simp]
theorem identity_stabilizes_null (ε : A) :
    Stabilizes (A := A) identity (Spinor2.nullRepresentative (A := A) ε) := by
  simp

@[simp]
theorem identity_stabilizes_diagonalNull (ε : A) :
    Stabilizes (A := A) identity (Spinor2.diagonalNullRepresentative (A := A) ε) := by
  simp

end SplitMatrix2

/--
Boundary object for the paper's reduced-structure/spin isomorphism target.
Supplying this structure records the two group-like carriers and the desired
comparison proposition; it does not itself prove the comparison.
-/
structure ReducedStructureSpinBoundary where
  q : ℕ
  q_val : q = 2 ∨ q = 4 ∨ q = 8
  reducedStructureGroup : Type*
  spinGroup : Type*
  expectedIsomorphism : Prop

/--
Boundary object for a future proof of the Section 5.1 Klein spinor orbit
stratification.  The fields are propositions so callers must provide genuine
proofs before claiming classification.
-/
structure KleinSpinorOrbitStratification (A : Type*) [NonAssocSemiring A] where
  epsilon : A
  epsilon_square_two_smul : epsilon * epsilon = (2 : ℕ) • epsilon
  generic_representative_complete : Prop
  null_representative_complete : Prop
  generic_stabilizer_description : Prop
  null_stabilizer_description : Prop

end SplitJordanSpinor
