/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The square-zero domain of the Peirce graded derivation

The total graded derivation squares to the inner derivation by V. Its
centralizer is invariant and carries a square-zero restriction. This states
the precise domain condition behind the transcript's cochain-complex claim.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

section CentralizerMultiplication

variable {B : Type*} [Ring B]

/-- The centralizer of any element in an associative ring is closed under
multiplication. -/
lemma genV_centralizer_mul {P A C : B}
    (X Y : {X : B // genV P A C * X = X * genV P A C}) :
    genV P A C * (X.val * Y.val) = (X.val * Y.val) * genV P A C := by
  calc genV P A C * (X.val * Y.val)
      = (genV P A C * X.val) * Y.val := by rw [mul_assoc]
    _ = (X.val * genV P A C) * Y.val := by rw [X.property]
    _ = X.val * (genV P A C * Y.val) := by rw [mul_assoc]
    _ = X.val * (Y.val * genV P A C) := by rw [Y.property]
    _ = (X.val * Y.val) * genV P A C := by rw [mul_assoc]

end CentralizerMultiplication

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)
include hP

theorem superDerivPhi_square (A C X : B) :
    superDerivPhi P A C (superDerivPhi P A C X) = connV P A C X := by
  simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj, connV]
  peirce_nf hP

theorem superDerivPhi_square_zero_iff (A C X : B) :
    superDerivPhi P A C (superDerivPhi P A C X) = 0 ↔
      genV P A C * X = X * genV P A C := by
  rw [superDerivPhi_square hP, connV, comm, sub_eq_zero]

/-- The graded derivation preserves the kernel of its square. -/
theorem superDerivPhi_connV (A C X : B) :
    superDerivPhi P A C (connV P A C X) =
      connV P A C (superDerivPhi P A C X) := by
  rw [← superDerivPhi_square hP A C X,
    superDerivPhi_square hP A C (superDerivPhi P A C X)]

theorem superDerivPhi_preserves_centralizer (A C X : B)
    (hX : genV P A C * X = X * genV P A C) :
    genV P A C * superDerivPhi P A C X =
      superDerivPhi P A C X * genV P A C := by
  have hz : connV P A C X = 0 := by simp [connV, comm, hX]
  have h := superDerivPhi_connV hP A C X
  rw [hz] at h
  have hd : superDerivPhi P A C (0 : B) = 0 := by
    simp [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
  rw [hd] at h
  exact sub_eq_zero.mp h.symm

/-- The Peirce superderivation obeys the twisted Leibniz rule.  The twist is
the actual grading automorphism `parityConj`; this is the algebraic
compatibility needed before treating its square-zero restriction as a
graded differential. -/
theorem superDerivPhi_twisted_leibniz (A C X Y : B) :
    superDerivPhi P A C (X * Y) =
      superDerivPhi P A C X * Y + parityConj P X * superDerivPhi P A C Y := by
  have hS : invS P * invS P = 1 := by
    simp only [invS]
    noncomm_ring [hP]
  have htwist : parityConj P (X * Y) = parityConj P X * parityConj P Y :=
    (parityConj_involutive_ring_action hP X Y).2.1
  simp only [superDerivPhi, superDerivPlus, superDerivMinus]
  rw [htwist]
  noncomm_ring [hS]

/-- Parity conjugation preserves the centralizer of the even curvature term
`genV`, so it restricts to the same carrier on which `superDerivPhi` squares
to zero. -/
theorem parityConj_preserves_genV_centralizer (A C X : B)
    (hX : genV P A C * X = X * genV P A C) :
    genV P A C * parityConj P X = parityConj P X * genV P A C := by
  rcases archetype_A27_grading_parities hP A C with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hV, _, _, _⟩
  have hparity_mul (U V : B) :
      parityConj P (U * V) = parityConj P U * parityConj P V :=
    (parityConj_involutive_ring_action hP U V).2.1
  calc genV P A C * parityConj P X
      = parityConj P (genV P A C) * parityConj P X := by rw [hV]
    _ = parityConj P (genV P A C * X) := (hparity_mul _ _).symm
    _ = parityConj P (X * genV P A C) := congrArg (parityConj P) hX
    _ = parityConj P X * parityConj P (genV P A C) := hparity_mul _ _
    _ = parityConj P X * genV P A C := by rw [hV]

/-- Restriction to the invariant centralizer, with no assumption that V is
central in the ambient ring. -/
def centralizerDifferential (A C : B)
    (X : {X : B // genV P A C * X = X * genV P A C}) :
    {X : B // genV P A C * X = X * genV P A C} :=
  ⟨superDerivPhi P A C X.val,
    superDerivPhi_preserves_centralizer hP A C X.val X.property⟩

/-- On the `genV` centralizer, the square-zero Peirce differential is odd for
the restricted parity involution. -/
theorem centralizerDifferential_parity_odd (A C : B)
    (X : {X : B // genV P A C * X = X * genV P A C}) :
    parityConj P (centralizerDifferential hP A C X).val =
      -(centralizerDifferential hP A C ⟨parityConj P X.val,
        parityConj_preserves_genV_centralizer hP A C X.val X.property⟩).val := by
  have h := InfoGeometry.OperatorAlgebra.PeirceGradedSuperderivations.differentialPhi_parity_odd
    (P := P) A C X.val hP
  change parityConj P (superDerivPhi P A C X.val) =
    -superDerivPhi P A C (parityConj P X.val) at h
  exact h

theorem centralizerDifferential_square_val (A C : B)
    (X : {X : B // genV P A C * X = X * genV P A C}) :
    (centralizerDifferential hP A C (centralizerDifferential hP A C X)).val = 0 :=
  (superDerivPhi_square_zero_iff hP A C X.val).2 X.property

/-- The restricted differential obeys the graded Leibniz rule on the
centralizer carrier, with parity acting on the left factor.  Together with
`centralizerDifferentialHom_comp_self`, this is the concrete Z/2 differential
algebra law available before any geometric form representation is chosen. -/
theorem centralizerDifferential_mul (A C : B)
    (X Y : {X : B // genV P A C * X = X * genV P A C}) :
    (centralizerDifferential hP A C
      ⟨X.val * Y.val, genV_centralizer_mul X Y⟩).val =
        (centralizerDifferential hP A C X).val * Y.val +
          parityConj P X.val * (centralizerDifferential hP A C Y).val := by
  change superDerivPhi P A C (X.val * Y.val) = _
  exact superDerivPhi_twisted_leibniz hP A C X.val Y.val

/-- The unital subring of operators centralizing `genV`. -/
def metricCentralizer (P A C : B) : Subring B where
  carrier := {X | genV P A C * X = X * genV P A C}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    change genV P A C * X = X * genV P A C at hX
    change genV P A C * Y = Y * genV P A C at hY
    change genV P A C * (X + Y) = (X + Y) * genV P A C
    simp only [mul_add, add_mul, hX, hY]
  neg_mem' := by
    intro X hX
    change genV P A C * X = X * genV P A C at hX
    change genV P A C * (-X) = (-X) * genV P A C
    simp only [mul_neg, neg_mul, hX]
  mul_mem' := by
    intro X Y hX hY
    exact genV_centralizer_mul ⟨X, hX⟩ ⟨Y, hY⟩

/-- The total graded derivation as an additive endomorphism on its invariant
centralizer. -/
def centralizerDifferentialHom (A C : B) :
    (metricCentralizer P A C).toAddSubgroup →+
      (metricCentralizer P A C).toAddSubgroup where
  toFun X := ⟨superDerivPhi P A C X.val,
    superDerivPhi_preserves_centralizer hP A C X.val X.property⟩
  map_zero' := by
    apply Subtype.ext
    change superDerivPhi P A C 0 = 0
    simp [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
  map_add' := by
    intro X Y
    apply Subtype.ext
    change superDerivPhi P A C (X.val + Y.val) =
      superDerivPhi P A C X.val + superDerivPhi P A C Y.val
    simp only [superDerivPhi, superDerivPlus, superDerivMinus, parityConj]
    noncomm_ring

/-- Composition of the centralizer differential with itself is the zero
additive homomorphism. -/
theorem centralizerDifferentialHom_comp_self (A C : B) :
    (centralizerDifferentialHom hP A C).comp (centralizerDifferentialHom hP A C) = 0 := by
  ext X
  change superDerivPhi P A C (superDerivPhi P A C X.val) = 0
  exact (superDerivPhi_square_zero_iff hP A C X.val).2 X.property

end InfoGeometry.OperatorAlgebra.PeirceSpine
