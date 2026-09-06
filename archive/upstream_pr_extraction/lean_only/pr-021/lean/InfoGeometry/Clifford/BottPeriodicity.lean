import InfoGeometry.Clifford.ClNN
import InfoGeometry.Meta.Architecture

open scoped TensorProduct

/-!
# InfoGeometry.Clifford.BottPeriodicity

Search-facing split Bott periodicity façade for the repo's recursive
`Cl(n,n)` tower.

The theorem-bearing owner is `InfoGeometry.Clifford.Tower.clsplit_succ_equiv`:

`Cl(n+1,n+1) ≃ Cl(1,1) ᵍ⊗ Cl(n,n)`.

This file gives that owner theorem the expected Bott-periodicity names.  It
does not assert the full real eightfold classification, nor the unproved matrix
classification `Cl(n,n) ≃ M(2^n, ℝ)` for all `n`.
-/

namespace InfoGeometry.Clifford.BottPeriodicity

open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower

/-- Split `Cl(n,n)` carrier, re-exported under Bott-periodicity naming. -/
@[rep_depth krein]
abbrev SplitBottCarrier (n : ℕ) := Carrier n

/-- Split `Cl(n,n)` quadratic form, re-exported under Bott-periodicity naming. -/
@[rep_depth krein]
noncomputable abbrev SplitBottQuad (n : ℕ) := Quad n

/-- Split `Cl(n,n)` algebra, re-exported under Bott-periodicity naming. -/
@[rep_depth krein]
abbrev SplitBottClifford (n : ℕ) := Alg n

/--
One-step split Bott periodicity for the recursive `Cl(n,n)` tower.

This is the source-supported form of Bott periodicity in the repository:
adjoining one split `Cl(1,1)` factor moves from `Cl(n,n)` to
`Cl(n+1,n+1)`.
-/
@[rep_depth krein]
noncomputable def splitBottStep (n : ℕ) :
    SplitBottClifford (n + 1)
      ≃ₐ[ℝ]
        (CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ]
          CliffordAlgebra.evenOdd (SplitBottQuad n)) :=
  clsplit_succ_equiv n

/-- Owner-equality form of the split Bott step. -/
@[rep_depth krein]
theorem splitBottStep_eq_clsplit_succ_equiv (n : ℕ) :
    splitBottStep n = clsplit_succ_equiv n :=
  rfl

/-- The `Cl(4,4)` object in the repo's split Bott tower. -/
@[rep_depth krein]
abbrev Cl44 := SplitBottClifford 4

/-- The split `Cl(4,4)` carrier in the repo's tower. -/
@[rep_depth krein]
abbrev Carrier44 := SplitBottCarrier 4

/-- The split `Cl(4,4)` quadratic form in the repo's tower. -/
@[rep_depth krein]
noncomputable abbrev Quad44 := SplitBottQuad 4

/--
`Cl(4,4)` is one split Bott step over `Cl(3,3)` in the current tower.
-/
@[rep_depth krein]
noncomputable def cl44_as_splitBottStep :
    Cl44
      ≃ₐ[ℝ]
        (CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ]
          CliffordAlgebra.evenOdd (SplitBottQuad 3)) :=
  splitBottStep 3

@[rep_depth krein]
theorem cl44_as_splitBottStep_eq_owner :
    cl44_as_splitBottStep = clsplit_succ_equiv 3 :=
  rfl

end InfoGeometry.Clifford.BottPeriodicity
