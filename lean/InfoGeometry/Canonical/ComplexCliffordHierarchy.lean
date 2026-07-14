import Mathlib

/-!
Finite, source-checkable invariants for the complex Clifford hierarchy.

This file deliberately proves only the shape and dimension layer:

* even stages are represented by one matrix block;
* odd stages are represented by the two-block complex split;
* adding two Clifford generators multiplies the complex dimension by four;
* the Jordan anticommutator recovers the Clifford polar form.

It does not claim an abstract algebra equivalence `Cl(n,C) ~= ...`; that stronger
classification theorem belongs in an owner file once the repo-native Clifford
surface is selected.

#### BUCKET 1: CLOSED FINITE THEOREMS
The finite shape recursion, block-rank recursion, dimension recursion, and
Jordan-product polar readout.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
No abstract algebra equivalence for the complex Clifford classification is
claimed here.
-/

namespace ComplexCliffordHierarchy

/-- Matrix-block shape of the complex Clifford classification. -/
inductive ComplexCliffordShape where
  | matrix : Nat -> ComplexCliffordShape
  | doubled : Nat -> ComplexCliffordShape
deriving DecidableEq, Repr

namespace ComplexCliffordShape

/-- Tensoring with `M_2(C)` doubles each matrix-block rank. -/
def tensorM2 : ComplexCliffordShape -> ComplexCliffordShape
  | matrix m => matrix (2 * m)
  | doubled m => doubled (2 * m)

/-- Complex vector-space dimension of the classified finite algebra shape. -/
def complexDim : ComplexCliffordShape -> Nat
  | matrix m => m * m
  | doubled m => 2 * (m * m)

/-- Matrix block size inside the shape. -/
def blockRank : ComplexCliffordShape -> Nat
  | matrix m => m
  | doubled m => m

theorem tensorM2_complexDim (S : ComplexCliffordShape) :
    complexDim (tensorM2 S) = 4 * complexDim S := by
  cases S <;> simp [tensorM2, complexDim] <;> ring

theorem tensorM2_blockRank (S : ComplexCliffordShape) :
    blockRank (tensorM2 S) = 2 * blockRank S := by
  cases S <;> simp [tensorM2, blockRank]

end ComplexCliffordShape

/-- The finite complex Clifford shape sequence. -/
def complexCliffordShape : Nat -> ComplexCliffordShape
  | 0 => .matrix 1
  | 1 => .doubled 1
  | n + 2 => (complexCliffordShape n).tensorM2

theorem shape_add_two (n : Nat) :
    complexCliffordShape (n + 2) =
      ComplexCliffordShape.tensorM2 (complexCliffordShape n) := by
  rfl

theorem shape_zero : complexCliffordShape 0 = .matrix 1 := rfl
theorem shape_one : complexCliffordShape 1 = .doubled 1 := rfl
theorem shape_two : complexCliffordShape 2 = .matrix 2 := rfl
theorem shape_three : complexCliffordShape 3 = .doubled 2 := rfl
theorem shape_four : complexCliffordShape 4 = .matrix 4 := rfl
theorem shape_five : complexCliffordShape 5 = .doubled 4 := rfl
theorem shape_six : complexCliffordShape 6 = .matrix 8 := rfl
theorem shape_seven : complexCliffordShape 7 = .doubled 8 := rfl
theorem shape_eight : complexCliffordShape 8 = .matrix 16 := rfl

theorem complexDim_shape : forall n : Nat,
    ComplexCliffordShape.complexDim (complexCliffordShape n) = 2 ^ n
  | 0 => by simp [complexCliffordShape, ComplexCliffordShape.complexDim]
  | 1 => by simp [complexCliffordShape, ComplexCliffordShape.complexDim]
  | n + 2 => by
      calc
        ComplexCliffordShape.complexDim (complexCliffordShape (n + 2))
            = ComplexCliffordShape.complexDim
                (ComplexCliffordShape.tensorM2 (complexCliffordShape n)) := rfl
        _ = 4 * ComplexCliffordShape.complexDim (complexCliffordShape n) :=
            ComplexCliffordShape.tensorM2_complexDim (complexCliffordShape n)
        _ = 4 * 2 ^ n := by rw [complexDim_shape n]
        _ = 2 ^ 2 * 2 ^ n := by norm_num
        _ = 2 ^ (2 + n) := by rw [pow_add]
        _ = 2 ^ (n + 2) := by rw [Nat.add_comm]

theorem complexDim_add_two (n : Nat) :
    ComplexCliffordShape.complexDim (complexCliffordShape (n + 2)) =
      4 * ComplexCliffordShape.complexDim (complexCliffordShape n) := by
  rw [shape_add_two, ComplexCliffordShape.tensorM2_complexDim]

/-- Algebraic Jordan product used for the Clifford metric readout. -/
def jordanProduct {A : Type*} [Ring A] (u v : A) : A :=
  u * v + v * u

/-- In a Clifford algebra, the Jordan product of generators recovers the polar form. -/
theorem jordan_recovers_polar {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (u v : M) :
    jordanProduct (CliffordAlgebra.ι Q u) (CliffordAlgebra.ι Q v) =
      algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q u v) := by
  exact CliffordAlgebra.ι_mul_ι_add_swap u v

end ComplexCliffordHierarchy
