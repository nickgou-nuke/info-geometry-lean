import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# The square-zero domain of the Peirce graded derivation

The total graded derivation squares to the inner derivation by V. Its
centralizer is invariant and carries a square-zero restriction. This states
the precise domain condition behind the transcript's cochain-complex claim.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

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

/-- Restriction to the invariant centralizer, with no assumption that V is
central in the ambient ring. -/
def centralizerDifferential (A C : B)
    (X : {X : B // genV P A C * X = X * genV P A C}) :
    {X : B // genV P A C * X = X * genV P A C} :=
  ⟨superDerivPhi P A C X.val,
    superDerivPhi_preserves_centralizer hP A C X.val X.property⟩

theorem centralizerDifferential_square_val (A C : B)
    (X : {X : B // genV P A C * X = X * genV P A C}) :
    (centralizerDifferential hP A C (centralizerDifferential hP A C X)).val = 0 :=
  (superDerivPhi_square_zero_iff hP A C X.val).2 X.property

/-- The additive group of operators centralizing V. -/
def metricCentralizer (P A C : B) : AddSubgroup B where
  carrier := {X | genV P A C * X = X * genV P A C}
  zero_mem' := by simp
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

/-- The total graded derivation as an additive endomorphism on its invariant
centralizer. -/
def centralizerDifferentialHom (A C : B) :
    metricCentralizer P A C →+ metricCentralizer P A C where
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
