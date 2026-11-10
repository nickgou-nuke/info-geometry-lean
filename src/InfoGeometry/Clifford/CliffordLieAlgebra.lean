/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Clifford.ClNN
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Clifford

open CliffordAlgebra

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Associative Lie commutator Jacobi identity in any non-commutative ring `[Ring B]`. -/
theorem ring_lie_jacobi {B : Type*} [Ring B] (x y z : B) :
    ((x * y - y * x) * z - z * (x * y - y * x)) +
    ((y * z - z * y) * x - x * (y * z - z * y)) +
    ((z * x - x * z) * y - y * (z * x - x * z)) = 0 := by
  noncomm_ring

attribute [local instance 100] LieRing.ofAssociativeRing

/-- 
The Lie algebra of bivectors in a Clifford algebra Cl(Q).
These span a Lie subalgebra isomorphic to so(Q).
-/
def soLieAlgebra {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) : 
    LieSubalgebra R (CliffordAlgebra Q) :=
  LieSubalgebra.lieSpan R (CliffordAlgebra Q) (Set.range (fun p : M × M => ⁅ι Q p.1, ι Q p.2⁆))

/-- The Lie algebra so(n,n) realized inside Clsplit n. -/
def soNN (n : ℕ) : LieSubalgebra ℝ (InfoGeometry.CliffordTower.Clsplit n) :=
  soLieAlgebra (InfoGeometry.CliffordTower.Qsplit n)

namespace soNN

variable {n : ℕ}

/-- A bivector generator [e_i, e_j] in so(n,n). -/
def bivector (m1 m2 : InfoGeometry.CliffordTower.SplitSpace n) : soNN n :=
  ⟨⁅ι (InfoGeometry.CliffordTower.Qsplit n) m1, ι (InfoGeometry.CliffordTower.Qsplit n) m2⁆, 
   LieSubalgebra.subset_lieSpan (Set.mem_range_self (m1, m2))⟩

end soNN

end InfoGeometry.Clifford
