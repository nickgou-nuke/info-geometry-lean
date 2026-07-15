import InfoGeometry.Canonical.AssociativeSuperBracket
import InfoGeometry.Algebra.TensorAlgebraCanonical
import InfoGeometry.Clifford.Tower
import InfoGeometry.Clifford.BottPeriodicity

/-!
# InfoGeometry.Clifford.Cl11SupergradedTensorBridge

Supergraded bracket transport along the recursive split `Cl(1,1)` tensor string.

This file does not invent a new superalgebra theory. It reuses:

* the associative superbracket on any `ℝ`-algebra;
* the recursive split Clifford tower `Cl(n+1,n+1) ≃ Cl(1,1) ᵍ⊗ Cl(n,n)`;
* the graded `evenOdd` structure already provided by Mathlib.

The point is simply: superbrackets transport through the owned tower step.
-/

open scoped TensorProduct

namespace InfoGeometry.Clifford.Cl11SupergradedTensorBridge

open InfoGeometry.Canonical.AssociativeSuperBracket
open InfoGeometry.Canonical.SuperAnomaly
open InfoGeometry.CliffordTower

section QuadraticTensorAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

@[rep_depth krein, simp]
theorem tensorAlgebra_toClifford_ι (x : M) :
    TensorAlgebra.toClifford (Q := Q) (TensorAlgebra.ι ℝ x) =
      CliffordAlgebra.ι Q x := by
  exact TensorAlgebra.toClifford_ι (Q := Q) x

@[rep_depth krein, simp]
theorem tensorAlgebra_toClifford_square_relation (x : M) :
    TensorAlgebra.toClifford (Q := Q)
        (TensorAlgebra.ι ℝ x * TensorAlgebra.ι ℝ x) =
      algebraMap ℝ (CliffordAlgebra Q) (Q x) := by
  rw [map_mul]
  simp

@[rep_depth krein]
theorem tensorAlgebra_toClifford_polar_relation (x y : M) :
    TensorAlgebra.toClifford (Q := Q)
        (TensorAlgebra.ι ℝ x * TensorAlgebra.ι ℝ y +
          TensorAlgebra.ι ℝ y * TensorAlgebra.ι ℝ x) =
      algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q x y) := by
  rw [map_add, map_mul, map_mul]
  simpa using (CliffordAlgebra.ι_mul_ι_add_swap (Q := Q) x y)

@[rep_depth krein, simp]
theorem clifford_ι_sq_eq_quadratic (x : M) :
    CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q x =
      algebraMap ℝ (CliffordAlgebra Q) (Q x) := by
  exact CliffordAlgebra.ι_sq_scalar Q x

@[rep_depth krein]
theorem clifford_oddOdd_superBracket_ι_eq_polar (x y : M) :
    superBracket SuperParity.odd SuperParity.odd
        (CliffordAlgebra.ι Q x) (CliffordAlgebra.ι Q y) =
      algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q x y) := by
  rw [superBracket_odd_odd]
  exact CliffordAlgebra.ι_mul_ι_add_swap (Q := Q) x y

@[rep_depth krein]
theorem clifford_ι_mem_odd (x : M) :
    CliffordAlgebra.ι Q x ∈ CliffordAlgebra.evenOdd Q 1 := by
  exact CliffordAlgebra.ι_mem_evenOdd_one (Q := Q) x

@[rep_depth krein]
theorem clifford_ι_mul_ι_mem_even (x y : M) :
    CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q y ∈ CliffordAlgebra.evenOdd Q 0 := by
  exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero (Q := Q) x y

end QuadraticTensorAlgebra

/-- The recursive split `Cl(1,1)` tensor string. -/
@[rep_depth krein]
abbrev Cl11String (n : ℕ) := Clsplit n

/-- The owner equivalence for the next split `Cl(1,1)` tensor step. -/
@[rep_depth krein]
noncomputable def cl11StringStepEquiv (n : ℕ) :
    Cl11String (n + 1)
      ≃ₐ[ℝ]
        (CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ]
          CliffordAlgebra.evenOdd (Qsplit n)) :=
  clsplit_succ_equiv n

/-- The split `Cl(1,1)` tensor step is an algebra equivalence. -/
@[rep_depth krein]
theorem cl11StringStepEquiv_eq_owner (n : ℕ) :
    cl11StringStepEquiv n = clsplit_succ_equiv n :=
  rfl

/-- Algebra homomorphisms preserve the graded superbracket along the split tower step. -/
@[rep_depth krein]
theorem cl11StringStep_superBracket_map
    (n : ℕ) (p q : SuperParity) (a b : Cl11String (n + 1)) :
    cl11StringStepEquiv n (superBracket p q a b) =
      superBracket p q (cl11StringStepEquiv n a) (cl11StringStepEquiv n b) := by
  change (clsplit_succ_equiv n : Cl11String (n + 1) →ₐ[ℝ]
      CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n))
      (superBracket p q a b) =
    superBracket p q
      ((clsplit_succ_equiv n : Cl11String (n + 1) →ₐ[ℝ]
          CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) a)
      ((clsplit_succ_equiv n : Cl11String (n + 1) →ₐ[ℝ]
          CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) b)
  exact map_superBracket
    (f := (clsplit_succ_equiv n : Cl11String (n + 1) →ₐ[ℝ]
      CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)))
    p q a b

/-- The odd-odd channel is transported unchanged through the split tower step. -/
@[rep_depth krein, simp]
theorem cl11StringStep_oddOdd_superBracket
    (n : ℕ) (a b : Cl11String (n + 1)) :
    cl11StringStepEquiv n (superBracket SuperParity.odd SuperParity.odd a b) =
      superBracket SuperParity.odd SuperParity.odd
        (cl11StringStepEquiv n a) (cl11StringStepEquiv n b) := by
  exact cl11StringStep_superBracket_map (n := n) (p := SuperParity.odd)
    (q := SuperParity.odd) a b

/-- The even-even channel is transported unchanged through the split tower step. -/
@[rep_depth krein, simp]
theorem cl11StringStep_evenEven_superBracket
    (n : ℕ) (a b : Cl11String (n + 1)) :
    cl11StringStepEquiv n (superBracket SuperParity.even SuperParity.even a b) =
      superBracket SuperParity.even SuperParity.even
        (cl11StringStepEquiv n a) (cl11StringStepEquiv n b) := by
  exact cl11StringStep_superBracket_map (n := n) (p := SuperParity.even)
    (q := SuperParity.even) a b

/-- The canonical `Cl(1,1)` generators are odd in the `evenOdd` grading. -/
@[rep_depth krein]
theorem cl11_generator_odd (n : ℕ) (x : SplitSpace (n + 1)) :
    CliffordAlgebra.ι (Qsplit (n + 1)) x ∈ CliffordAlgebra.evenOdd (Qsplit (n + 1)) 1 := by
  exact CliffordAlgebra.ι_mem_evenOdd_one (Q := Qsplit (n + 1)) x

@[rep_depth krein, simp]
theorem cl11String_generator_square_eq_quadratic
    (n : ℕ) (x : SplitSpace (n + 1)) :
    CliffordAlgebra.ι (Qsplit (n + 1)) x * CliffordAlgebra.ι (Qsplit (n + 1)) x =
      algebraMap ℝ (CliffordAlgebra (Qsplit (n + 1))) (Qsplit (n + 1) x) := by
  exact clifford_ι_sq_eq_quadratic (Q := Qsplit (n + 1)) x

@[rep_depth krein]
theorem cl11String_tensorAlgebra_toClifford_square_relation
    (n : ℕ) (x : SplitSpace (n + 1)) :
    TensorAlgebra.toClifford (Q := Qsplit (n + 1))
        (TensorAlgebra.ι ℝ x * TensorAlgebra.ι ℝ x) =
      algebraMap ℝ (CliffordAlgebra (Qsplit (n + 1))) (Qsplit (n + 1) x) := by
  exact tensorAlgebra_toClifford_square_relation (Q := Qsplit (n + 1)) x

@[rep_depth krein]
theorem cl11String_oddOdd_superBracket_eq_polar
    (n : ℕ) (x y : SplitSpace (n + 1)) :
    superBracket SuperParity.odd SuperParity.odd
        (CliffordAlgebra.ι (Qsplit (n + 1)) x)
        (CliffordAlgebra.ι (Qsplit (n + 1)) y) =
      algebraMap ℝ (CliffordAlgebra (Qsplit (n + 1)))
        (QuadraticMap.polar (Qsplit (n + 1)) x y) := by
  exact clifford_oddOdd_superBracket_ι_eq_polar (Q := Qsplit (n + 1)) x y

@[rep_depth krein]
theorem cl11String_generator_product_even
    (n : ℕ) (x y : SplitSpace (n + 1)) :
    CliffordAlgebra.ι (Qsplit (n + 1)) x *
        CliffordAlgebra.ι (Qsplit (n + 1)) y ∈
      CliffordAlgebra.evenOdd (Qsplit (n + 1)) 0 := by
  exact clifford_ι_mul_ι_mem_even (Q := Qsplit (n + 1)) x y

/-- The split tower step packages the recursive `Cl(1,1)` string as a supergraded algebra. -/
@[rep_depth krein]
theorem cl11String_supergraded_tower_step
    (n : ℕ) (x y : SplitSpace (n + 1)) :
    superBracket SuperParity.odd SuperParity.odd
      (CliffordAlgebra.ι (Qsplit (n + 1)) x)
      (CliffordAlgebra.ι (Qsplit (n + 1)) y)
      = CliffordAlgebra.ι (Qsplit (n + 1)) x * CliffordAlgebra.ι (Qsplit (n + 1)) y
        + CliffordAlgebra.ι (Qsplit (n + 1)) y * CliffordAlgebra.ι (Qsplit (n + 1)) x := by
  rw [superBracket_odd_odd]

end InfoGeometry.Clifford.Cl11SupergradedTensorBridge
