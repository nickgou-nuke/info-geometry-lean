import InfoGeometry.Canonical.AssociativeSuperBracket
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
  simpa using cl11StringStep_superBracket_map (n := n) (p := SuperParity.odd)
    (q := SuperParity.odd) a b

/-- The even-even channel is transported unchanged through the split tower step. -/
@[rep_depth krein, simp]
theorem cl11StringStep_evenEven_superBracket
    (n : ℕ) (a b : Cl11String (n + 1)) :
    cl11StringStepEquiv n (superBracket SuperParity.even SuperParity.even a b) =
      superBracket SuperParity.even SuperParity.even
        (cl11StringStepEquiv n a) (cl11StringStepEquiv n b) := by
  simpa using cl11StringStep_superBracket_map (n := n) (p := SuperParity.even)
    (q := SuperParity.even) a b

/-- The canonical `Cl(1,1)` generators are odd in the `evenOdd` grading. -/
@[rep_depth krein]
theorem cl11_generator_odd (n : ℕ) (x : SplitSpace (n + 1)) :
    CliffordAlgebra.ι (Qsplit (n + 1)) x ∈ CliffordAlgebra.evenOdd (Qsplit (n + 1)) 1 := by
  exact CliffordAlgebra.ι_mem_evenOdd_one (Q := Qsplit (n + 1)) x

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
