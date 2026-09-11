import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.Cl11MoritaUnimodularPairs

abbrev Matrix2R := Matrix (Fin 2) (Fin 2) ℝ

/-!
# Unimodular pairs for the Morita projective-line construction

This is only the definition-level layer.  It does not yet quotient pairs or
claim the projective-line/Grassmannian equivalence.
-/

structure UnimodularPair where
  a : Matrix2R
  b : Matrix2R
  leftWitnessA : Matrix2R
  leftWitnessB : Matrix2R
  left_unimodular :
    leftWitnessA * a + leftWitnessB * b = 1

abbrev MatrixTwoByTwo := Matrix (Fin 2) (Fin 2) Matrix2R

def pairVector (p : UnimodularPair) : Fin 2 → Matrix2R :=
  ![p.a, p.b]

def witnessVector (p : UnimodularPair) : Fin 2 → Matrix2R :=
  ![p.leftWitnessA, p.leftWitnessB]

def matrixPairAction (g : MatrixTwoByTwo) (p : UnimodularPair) :
    Fin 2 → Matrix2R :=
  Matrix.mulVec g (pairVector p)

@[simp] theorem matrixPairAction_one (p : UnimodularPair) :
    matrixPairAction (1 : MatrixTwoByTwo) p = pairVector p := by
  simp [matrixPairAction]

theorem matrixPairAction_mul
    (g h : MatrixTwoByTwo) (p : UnimodularPair) :
    matrixPairAction (g * h) p =
      Matrix.mulVec g (matrixPairAction h p) := by
  simp only [matrixPairAction]
  rw [Matrix.mulVec_mulVec]

def unitPairAction (u : MatrixTwoByTwoˣ) (p : UnimodularPair) :
    Fin 2 → Matrix2R :=
  Matrix.mulVec (u : MatrixTwoByTwo) (pairVector p)

def unitWitnessAction (u : MatrixTwoByTwoˣ) (p : UnimodularPair) :
    Fin 2 → Matrix2R :=
  Matrix.vecMul (witnessVector p) (↑(u⁻¹) : MatrixTwoByTwo)

theorem unitWitnessAction_pairing (u : MatrixTwoByTwoˣ)
    (p : UnimodularPair) :
    dotProduct (unitWitnessAction u p) (unitPairAction u p) = 1 := by
  simp only [unitWitnessAction, unitPairAction]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  rw [show (↑(u⁻¹) : MatrixTwoByTwo) * (u : MatrixTwoByTwo) = 1 by
    exact Units.inv_mul u]
  simpa [witnessVector, pairVector] using p.left_unimodular

def unitTransformedPair (u : MatrixTwoByTwoˣ) (p : UnimodularPair) :
    UnimodularPair where
  a := unitPairAction u p 0
  b := unitPairAction u p 1
  leftWitnessA := unitWitnessAction u p 0
  leftWitnessB := unitWitnessAction u p 1
  left_unimodular := by
    change (unitWitnessAction u p 0) * (unitPairAction u p 0) +
      (unitWitnessAction u p 1) * (unitPairAction u p 1) = 1
    simpa only [dotProduct, Fin.sum_univ_two] using
      unitWitnessAction_pairing u p

@[simp] theorem unitTransformedPair_a (u : MatrixTwoByTwoˣ)
    (p : UnimodularPair) :
    (unitTransformedPair u p).a = unitPairAction u p 0 := rfl

@[simp] theorem unitTransformedPair_b (u : MatrixTwoByTwoˣ)
    (p : UnimodularPair) :
    (unitTransformedPair u p).b = unitPairAction u p 1 := rfl

theorem unimodularPair_ext {p q : UnimodularPair}
    (ha : p.a = q.a) (hb : p.b = q.b)
    (hwa : p.leftWitnessA = q.leftWitnessA)
    (hwb : p.leftWitnessB = q.leftWitnessB) :
    p = q := by
  cases p
  cases q
  simp_all

theorem unitPairAction_mul (u v : MatrixTwoByTwoˣ)
    (p : UnimodularPair) :
    unitPairAction (u * v) p =
      Matrix.mulVec (u : MatrixTwoByTwo) (unitPairAction v p) := by
  unfold unitPairAction
  change Matrix.mulVec ((u : MatrixTwoByTwo) * (v : MatrixTwoByTwo))
      (pairVector p) = _
  rw [Matrix.mulVec_mulVec]

theorem unitWitnessAction_mul (u v : MatrixTwoByTwoˣ)
    (p : UnimodularPair) :
    unitWitnessAction (u * v) p =
      Matrix.vecMul (unitWitnessAction v p)
        (↑(u⁻¹) : MatrixTwoByTwo) := by
  unfold unitWitnessAction
  rw [Matrix.vecMul_vecMul]
  rw [mul_inv_rev]
  rfl

theorem pairVector_unitTransformedPair (u : MatrixTwoByTwoˣ)
    (p : UnimodularPair) :
    pairVector (unitTransformedPair u p) = unitPairAction u p := by
  funext i
  fin_cases i <;> rfl

theorem witnessVector_unitTransformedPair (u : MatrixTwoByTwoˣ)
    (p : UnimodularPair) :
    witnessVector (unitTransformedPair u p) = unitWitnessAction u p := by
  funext i
  fin_cases i <;> rfl

theorem unitTransformedPair_mul (u v : MatrixTwoByTwoˣ)
    (p : UnimodularPair) :
    unitTransformedPair (u * v) p =
      unitTransformedPair u (unitTransformedPair v p) := by
  apply unimodularPair_ext
  · change unitPairAction (u * v) p 0 =
      unitPairAction u (unitTransformedPair v p) 0
    simp only [unitPairAction]
    rw [pairVector_unitTransformedPair v p]
    exact congrFun (unitPairAction_mul u v p) 0
  · change unitPairAction (u * v) p 1 =
      unitPairAction u (unitTransformedPair v p) 1
    simp only [unitPairAction]
    rw [pairVector_unitTransformedPair v p]
    exact congrFun (unitPairAction_mul u v p) 1
  · change unitWitnessAction (u * v) p 0 =
      unitWitnessAction u (unitTransformedPair v p) 0
    simp only [unitWitnessAction]
    rw [witnessVector_unitTransformedPair v p]
    exact congrFun (unitWitnessAction_mul u v p) 0
  · change unitWitnessAction (u * v) p 1 =
      unitWitnessAction u (unitTransformedPair v p) 1
    simp only [unitWitnessAction]
    rw [witnessVector_unitTransformedPair v p]
    exact congrFun (unitWitnessAction_mul u v p) 1

theorem unitTransformedPair_one (p : UnimodularPair) :
    unitTransformedPair (1 : MatrixTwoByTwoˣ) p = p := by
  apply unimodularPair_ext <;>
  simp [unitTransformedPair, unitPairAction, unitWitnessAction,
    pairVector, witnessVector]

theorem unitTransformedPair_inv (u : MatrixTwoByTwoˣ)
    (p : UnimodularPair) :
    unitTransformedPair u⁻¹ (unitTransformedPair u p) = p := by
  have h := unitTransformedPair_mul (u⁻¹) u p
  have h' : unitTransformedPair (1 : MatrixTwoByTwoˣ) p =
      unitTransformedPair u⁻¹ (unitTransformedPair u p) := by
    simpa only [inv_mul_cancel] using h
  exact h'.symm.trans (unitTransformedPair_one p)

noncomputable def rightScalarAction (s : Matrix2Rˣ) (p : UnimodularPair) :
    UnimodularPair where
  a := p.a * (s : Matrix2R)
  b := p.b * (s : Matrix2R)
  leftWitnessA := (↑(s⁻¹) : Matrix2R) * p.leftWitnessA
  leftWitnessB := (↑(s⁻¹) : Matrix2R) * p.leftWitnessB
  left_unimodular := by
    calc
      ((↑(s⁻¹) : Matrix2R) * p.leftWitnessA) * (p.a * (s : Matrix2R)) +
          ((↑(s⁻¹) : Matrix2R) * p.leftWitnessB) * (p.b * (s : Matrix2R)) =
        (↑(s⁻¹) : Matrix2R) * (p.leftWitnessA * p.a +
          p.leftWitnessB * p.b) * (s : Matrix2R) := by
            simp only [mul_add, add_mul, mul_assoc]
      _ = 1 := by
        rw [p.left_unimodular, mul_one]
        exact Units.inv_mul s

theorem rightScalarAction_preserves_pairing (s : Matrix2Rˣ)
    (p : UnimodularPair) :
    ((↑(s⁻¹) : Matrix2R) * p.leftWitnessA) * (p.a * (s : Matrix2R)) +
        ((↑(s⁻¹) : Matrix2R) * p.leftWitnessB) * (p.b * (s : Matrix2R)) =
      1 := by
  calc
    ((↑(s⁻¹) : Matrix2R) * p.leftWitnessA) * (p.a * (s : Matrix2R)) +
        ((↑(s⁻¹) : Matrix2R) * p.leftWitnessB) * (p.b * (s : Matrix2R)) =
      (↑(s⁻¹) : Matrix2R) * (p.leftWitnessA * p.a +
        p.leftWitnessB * p.b) * (s : Matrix2R) := by
          simp only [mul_add, add_mul, mul_assoc]
    _ = 1 := by
      rw [p.left_unimodular, mul_one]
      exact Units.inv_mul s

def RightAssociated (p q : UnimodularPair) : Prop :=
  ∃ s : Matrix2Rˣ, rightScalarAction s p = q

theorem rightScalarAction_one (p : UnimodularPair) :
    rightScalarAction (1 : Matrix2Rˣ) p = p := by
  apply unimodularPair_ext <;>
  simp [rightScalarAction]

theorem rightAssociated_refl (p : UnimodularPair) :
    RightAssociated p p := by
  exact ⟨1, rightScalarAction_one p⟩

theorem rightScalarAction_mul (s t : Matrix2Rˣ)
    (p : UnimodularPair) :
    rightScalarAction (s * t) p =
      rightScalarAction t (rightScalarAction s p) := by
  apply unimodularPair_ext <;>
  simp [rightScalarAction, mul_assoc, mul_inv_rev]

theorem rightAssociated_symm {p q : UnimodularPair}
    (h : RightAssociated p q) :
    RightAssociated q p := by
  rcases h with ⟨s, hs⟩
  refine ⟨s⁻¹, ?_⟩
  rw [← hs]
  have hcomp := rightScalarAction_mul s s⁻¹ p
  have hone : rightScalarAction (s * s⁻¹) p = p := by
    rw [mul_inv_cancel, rightScalarAction_one]
  exact hcomp.symm.trans hone

theorem rightAssociated_trans {p q r : UnimodularPair}
    (hpq : RightAssociated p q)
    (hqr : RightAssociated q r) :
    RightAssociated p r := by
  rcases hpq with ⟨s, hs⟩
  rcases hqr with ⟨t, ht⟩
  refine ⟨s * t, ?_⟩
  calc
    rightScalarAction (s * t) p =
        rightScalarAction t (rightScalarAction s p) :=
      rightScalarAction_mul s t p
    _ = rightScalarAction t q := by rw [hs]
    _ = r := ht

instance rightAssociatedSetoid : Setoid UnimodularPair where
  r := RightAssociated
  iseqv := {
    refl := rightAssociated_refl
    symm := rightAssociated_symm
    trans := rightAssociated_trans
  }

abbrev ProjectiveRepresentative := Quotient rightAssociatedSetoid

def projectiveRepresentativeMk (p : UnimodularPair) :
    ProjectiveRepresentative :=
  Quotient.mk' p

@[simp] theorem pairVector_rightScalarAction_zero
    (s : Matrix2Rˣ) (p : UnimodularPair) :
    pairVector (rightScalarAction s p) 0 =
      pairVector p 0 * (s : Matrix2R) := rfl

@[simp] theorem pairVector_rightScalarAction_one
    (s : Matrix2Rˣ) (p : UnimodularPair) :
    pairVector (rightScalarAction s p) 1 =
      pairVector p 1 * (s : Matrix2R) := rfl

@[simp] theorem witnessVector_rightScalarAction_zero
    (s : Matrix2Rˣ) (p : UnimodularPair) :
    witnessVector (rightScalarAction s p) 0 =
      (↑(s⁻¹) : Matrix2R) * witnessVector p 0 := rfl

@[simp] theorem witnessVector_rightScalarAction_one
    (s : Matrix2Rˣ) (p : UnimodularPair) :
    witnessVector (rightScalarAction s p) 1 =
      (↑(s⁻¹) : Matrix2R) * witnessVector p 1 := rfl

def rightScalarVector (s : Matrix2Rˣ) (v : Fin 2 → Matrix2R) :
    Fin 2 → Matrix2R := fun i => v i * (s : Matrix2R)

theorem unitPairAction_rightScalarVector
    (u : MatrixTwoByTwoˣ) (s : Matrix2Rˣ) (p : UnimodularPair) :
    unitPairAction u (rightScalarAction s p) =
      rightScalarVector s (unitPairAction u p) := by
  funext i
  fin_cases i <;>
    simp [unitPairAction, rightScalarAction, rightScalarVector,
      pairVector, Matrix.mulVec, Fin.sum_univ_two, mul_add, add_mul,
      mul_assoc]

theorem leftScalarVec_vecMul (c : Matrix2R)
    (v : Fin 2 → Matrix2R) (M : MatrixTwoByTwo) :
    Matrix.vecMul (fun i => c * v i) M =
      fun j => c * Matrix.vecMul v M j := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  rw [mul_add, ← mul_assoc, ← mul_assoc]

def leftScalarVector (s : Matrix2Rˣ) (v : Fin 2 → Matrix2R) :
    Fin 2 → Matrix2R := fun i => (↑(s⁻¹) : Matrix2R) * v i

theorem witnessVector_rightScalarAction
    (s : Matrix2Rˣ) (p : UnimodularPair) :
    witnessVector (rightScalarAction s p) =
      leftScalarVector s (witnessVector p) := by
  funext i
  fin_cases i <;> rfl

theorem unitWitnessAction_rightScalarVector
    (u : MatrixTwoByTwoˣ) (s : Matrix2Rˣ) (p : UnimodularPair) :
    unitWitnessAction u (rightScalarAction s p) =
      leftScalarVector s (unitWitnessAction u p) := by
  unfold unitWitnessAction
  rw [witnessVector_rightScalarAction]
  exact leftScalarVec_vecMul (↑(s⁻¹) : Matrix2R)
    (witnessVector p) (↑(u⁻¹) : MatrixTwoByTwo)

theorem unitTransformedPair_rightScalar_commute
    (u : MatrixTwoByTwoˣ) (s : Matrix2Rˣ) (p : UnimodularPair) :
    unitTransformedPair u (rightScalarAction s p) =
      rightScalarAction s (unitTransformedPair u p) := by
  apply unimodularPair_ext
  · change unitPairAction u (rightScalarAction s p) 0 =
      rightScalarVector s (unitPairAction u p) 0
    exact congrFun (unitPairAction_rightScalarVector u s p) 0
  · change unitPairAction u (rightScalarAction s p) 1 =
      rightScalarVector s (unitPairAction u p) 1
    exact congrFun (unitPairAction_rightScalarVector u s p) 1
  · change unitWitnessAction u (rightScalarAction s p) 0 =
      leftScalarVector s (unitWitnessAction u p) 0
    exact congrFun (unitWitnessAction_rightScalarVector u s p) 0
  · change unitWitnessAction u (rightScalarAction s p) 1 =
      leftScalarVector s (unitWitnessAction u p) 1
    exact congrFun (unitWitnessAction_rightScalarVector u s p) 1

noncomputable def projectiveUnitAction (u : MatrixTwoByTwoˣ) :
    ProjectiveRepresentative → ProjectiveRepresentative :=
  Quotient.map (unitTransformedPair u) (by
    intro p q hpq
    rcases hpq with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    calc
      rightScalarAction s (unitTransformedPair u p) =
          unitTransformedPair u (rightScalarAction s p) :=
        (unitTransformedPair_rightScalar_commute u s p).symm
      _ = unitTransformedPair u q := by rw [hs])

@[simp] theorem projectiveUnitAction_mk
    (u : MatrixTwoByTwoˣ) (p : UnimodularPair) :
    projectiveUnitAction u (projectiveRepresentativeMk p) =
      projectiveRepresentativeMk (unitTransformedPair u p) := rfl

theorem projectiveUnitAction_one (q : ProjectiveRepresentative) :
    projectiveUnitAction (1 : MatrixTwoByTwoˣ) q = q := by
  refine Quotient.inductionOn q ?_
  intro p
  change projectiveUnitAction (1 : MatrixTwoByTwoˣ)
      (projectiveRepresentativeMk p) = projectiveRepresentativeMk p
  rw [projectiveUnitAction_mk, unitTransformedPair_one]

theorem projectiveUnitAction_mul (u v : MatrixTwoByTwoˣ)
    (q : ProjectiveRepresentative) :
    projectiveUnitAction (u * v) q =
      projectiveUnitAction u (projectiveUnitAction v q) := by
  refine Quotient.inductionOn q ?_
  intro p
  change projectiveUnitAction (u * v) (projectiveRepresentativeMk p) =
      projectiveUnitAction u
        (projectiveUnitAction v (projectiveRepresentativeMk p))
  rw [projectiveUnitAction_mk, projectiveUnitAction_mk,
    projectiveUnitAction_mk,
    unitTransformedPair_mul]

@[simp] theorem pairVector_zero (p : UnimodularPair) :
    pairVector p 0 = p.a := by
  simp [pairVector]

@[simp] theorem pairVector_one (p : UnimodularPair) :
    pairVector p 1 = p.b := by
  simp [pairVector]

theorem witnessVector_pairing (p : UnimodularPair) :
    (witnessVector p 0) * (pairVector p 0) +
        (witnessVector p 1) * (pairVector p 1) = 1 := by
  simpa [witnessVector, pairVector] using p.left_unimodular

noncomputable def standardPair : UnimodularPair where
  a := 1
  b := 0
  leftWitnessA := 1
  leftWitnessB := 0
  left_unimodular := by simp

@[simp] theorem standardPair_a :
    standardPair.a = (1 : Matrix2R) := rfl

@[simp] theorem standardPair_b :
    standardPair.b = (0 : Matrix2R) := rfl

end InfoGeometry.Canonical.Cl11MoritaUnimodularPairs
