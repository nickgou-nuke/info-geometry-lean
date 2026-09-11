import InfoGeometry.Canonical.CuntzCantorBoundaryShift
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Cantor branching

The finite prefix tower has an explicit binary decomposition.  This is the
finite carrier counterpart of the two Cuntz branches; it is kept separate
from the topological boundary and from any mapping-cone construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzCantorBoundaryShift

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

def branchTail {n : ℕ} (w : BitWord (n + 1)) : BitWord n :=
  fun i => w ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

@[simp]
theorem branchTail_branchPrefix (n : ℕ) (b : Bool) (w : BitWord n) :
    branchTail (branchPrefix n b w) = w := by
  funext i
  simp [branchTail]

@[simp]
theorem branchPrefix_head_branchTail (n : ℕ) (w : BitWord (n + 1)) :
    branchPrefix n (w ⟨0, Nat.succ_pos n⟩) (branchTail w) = w := by
  funext i
  by_cases h : i.1 = 0
  · have hi : i = ⟨0, Nat.succ_pos n⟩ := Fin.ext h
    subst i
    rfl
  · simp [branchPrefix, branchTail, h]
    apply congrArg w
    apply Fin.ext
    exact Nat.sub_add_cancel (by omega : 1 ≤ i.1)

/-- Every finite word is uniquely a head bit together with its tail. -/
noncomputable def bitWordSuccEquiv (n : ℕ) :
    BitWord (n + 1) ≃ Bool × BitWord n where
  toFun w := (w ⟨0, Nat.succ_pos n⟩, branchTail w)
  invFun p := branchPrefix n p.1 p.2
  left_inv w := branchPrefix_head_branchTail n w
  right_inv p := by
    apply Prod.ext
    · exact branchPrefix_zero n p.1 p.2
    · simp

@[simp]
theorem bitWordSuccEquiv_apply (n : ℕ) (w : BitWord (n + 1)) :
    bitWordSuccEquiv n w =
      (w ⟨0, Nat.succ_pos n⟩, branchTail w) :=
  rfl

@[simp]
theorem bitWordSuccEquiv_symm_apply
    (n : ℕ) (b : Bool) (w : BitWord n) :
    (bitWordSuccEquiv n).symm (b, w) = branchPrefix n b w :=
  rfl

end InfoGeometry.Canonical.CuntzCantorBoundaryShift
