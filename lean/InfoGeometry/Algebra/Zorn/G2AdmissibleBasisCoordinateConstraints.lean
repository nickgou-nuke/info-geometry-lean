import InfoGeometry.Algebra.Zorn.G2AdmissibleBasisPrefix

/-!
# Algebraic constraints on admissible-basis coordinates

The admissibility predicate already contains the algebra-homomorphism laws.
This owner exposes those laws at the extracted-coordinate level, without
assuming a geometric interpretation or a cardinality classification.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem mul_add (X Y Z : SplitOctF2) : mul X (add Y Z) = add (mul X Y) (mul X Z) := by
  rcases X with ⟨Xa, Xb, Xx0, Xx1, Xx2, Xy0, Xy1, Xy2⟩
  rcases Y with ⟨Ya, Yb, Yx0, Yx1, Yx2, Yy0, Yy1, Yy2⟩
  rcases Z with ⟨Za, Zb, Zx0, Zx1, Zx2, Zy0, Zy1, Zy2⟩
  apply SplitOctF2.ext
  all_goals dsimp only [mul, add]
  · revert Xa Xx0 Xx1 Xx2 Ya Yy0 Yy1 Yy2 Za Zy0 Zy1 Zy2; decide
  · revert Xb Xy0 Xy1 Xy2 Yb Yx0 Yx1 Yx2 Zb Zx0 Zx1 Zx2; decide
  · revert Xa Xx0 Xy1 Xy2 Yb Yx0 Yy1 Yy2 Zb Zx0 Zy1 Zy2; decide
  · revert Xa Xx1 Xy0 Xy2 Yb Yx1 Yy0 Yy2 Zb Zx1 Zy0 Zy2; decide
  · revert Xa Xx2 Xy0 Xy1 Yb Yx2 Yy0 Yy1 Zb Zx2 Zy0 Zy1; decide
  · revert Xb Xy0 Xx1 Xx2 Ya Yy0 Yx1 Yx2 Za Zy0 Zx1 Zx2; decide
  · revert Xb Xy1 Xx0 Xx2 Ya Yy1 Yx0 Yx2 Za Zy1 Zx0 Zx2; decide
  · revert Xb Xy2 Xx0 Xx1 Ya Yy2 Yx0 Yx1 Za Zy2 Zx0 Zx1; decide

theorem add_mul (X Y Z : SplitOctF2) : mul (add X Y) Z = add (mul X Z) (mul Y Z) := by
  rcases X with ⟨Xa, Xb, Xx0, Xx1, Xx2, Xy0, Xy1, Xy2⟩
  rcases Y with ⟨Ya, Yb, Yx0, Yx1, Yx2, Yy0, Yy1, Yy2⟩
  rcases Z with ⟨Za, Zb, Zx0, Zx1, Zx2, Zy0, Zy1, Zy2⟩
  apply SplitOctF2.ext
  all_goals dsimp only [mul, add]
  · revert Xa Ya Za Xx0 Yx0 Xx1 Yx1 Xx2 Yx2 Zy0 Zy1 Zy2; decide
  · revert Xb Yb Zb Xy0 Yy0 Xy1 Yy1 Xy2 Yy2 Zx0 Zx1 Zx2; decide
  · revert Xa Ya Zx0 Zb Xx0 Yx0 Xy1 Yy1 Xy2 Yy2 Zy1 Zy2; decide
  · revert Xa Ya Zx1 Zb Xx1 Yx1 Xy0 Yy0 Xy2 Yy2 Zy0 Zy2; decide
  · revert Xa Ya Zx2 Zb Xx2 Yx2 Xy0 Yy0 Xy1 Yy1 Zy0 Zy1; decide
  · revert Xb Yb Zy0 Za Xy0 Yy0 Xx1 Yx1 Xx2 Yx2 Zx1 Zx2; decide
  · revert Xb Yb Zy1 Za Xy1 Yy1 Xx0 Yx0 Xx2 Yx2 Zx0 Zx2; decide
  · revert Xb Yb Zy2 Za Xy2 Yy2 Xx0 Yx0 Xx1 Yx1 Zx0 Zx1; decide

@[simp] theorem one_mul (X : SplitOctF2) : mul one X = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  cases a <;> cases b <;> cases x0 <;> cases x1 <;> cases x2 <;> cases y0 <;> cases y1 <;> cases y2 <;> rfl

@[simp] theorem mul_one (X : SplitOctF2) : mul X one = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  cases a <;> cases b <;> cases x0 <;> cases x1 <;> cases x2 <;> cases y0 <;> cases y1 <;> cases y2 <;> rfl

abbrev NontrivialIdempotent :=
  {p : SplitOctF2 // mul p p = p ∧ p ≠ zero ∧ p ≠ one}

/-- The Peirce complement expression attached to an idempotent coordinate. -/
def peirceComplement (p : SplitOctF2) : SplitOctF2 :=
  add one p

@[simp] theorem peirceComplement_apply (p : SplitOctF2) :
    peirceComplement p = add one p :=
  rfl

def nontrivialIdempotentComplement
    (p : NontrivialIdempotent) : NontrivialIdempotent := by
  refine ⟨peirceComplement p.1, ?_, ?_, ?_⟩
  · change mul (add one p.1) (add one p.1) = add one p.1
    simp only [add_mul, mul_add, one_mul, mul_one, p.2.1, add_self,
      add_zero]
  · intro h
    apply p.2.2.2
    have h' := congrArg (fun x => add x one) h
    have hc : add (add one p.1) one = p.1 := by
      rw [add_assoc, add_comm p.1 one, ← add_assoc, add_self, zero_add]
    change add (add one p.1) one = add zero one at h'
    rw [hc] at h'
    simpa using h'
  · intro h
    apply p.2.2.1
    have h' := congrArg (fun x => add x one) h
    have hc : add (add one p.1) one = p.1 := by
      rw [add_assoc, add_comm p.1 one, ← add_assoc, add_self, zero_add]
    change add (add one p.1) one = add one one at h'
    rw [hc, add_self] at h'
    exact h'

theorem nontrivialIdempotentComplement_sum
    (p : NontrivialIdempotent) :
    add p.1 (nontrivialIdempotentComplement p).1 = one := by
  change add p.1 (add one p.1) = one
  rw [← add_assoc, add_comm p.1 one, add_assoc, add_self, add_zero]

theorem nontrivialIdempotentComplement_left_orthogonal
    (p : NontrivialIdempotent) :
    mul p.1 (nontrivialIdempotentComplement p).1 = zero := by
  change mul p.1 (add one p.1) = zero
  rw [mul_add, mul_one, p.2.1, add_self]

theorem nontrivialIdempotentComplement_right_orthogonal
    (p : NontrivialIdempotent) :
    mul (nontrivialIdempotentComplement p).1 p.1 = zero := by
  change mul (add one p.1) p.1 = zero
  rw [add_mul, one_mul, p.2.1, add_self]

def NontrivialIdempotentNeighbours (u : NontrivialIdempotent) :=
  {v : NontrivialIdempotent // mul u.1 v.1 = zero}

def RightNontrivialIdempotentNeighbours (u : NontrivialIdempotent) :=
  {v : NontrivialIdempotent // mul v.1 u.1 = zero}

def nontrivialIdempotentAction
    (f : SplitOctF2Aut) (p : NontrivialIdempotent) :
    NontrivialIdempotent := by
  refine ⟨f⁻¹.1 p.1, ?_, ?_, ?_⟩
  · have h := f⁻¹.2.2.2 p.1 p.1
    rw [p.2.1] at h
    exact h.symm
  · intro h
    apply p.2.2.1
    apply f⁻¹.1.injective
    simp [h, map_zero]
  · intro h
    apply p.2.2.2
    apply f⁻¹.1.injective
    simp [h, f⁻¹.2.1]

instance : MulAction SplitOctF2Aut NontrivialIdempotent where
  smul := nontrivialIdempotentAction
  one_smul p := by
    change nontrivialIdempotentAction 1 p = p
    apply Subtype.ext
    rfl
  mul_smul f g p := by
    change nontrivialIdempotentAction (f * g) p =
      nontrivialIdempotentAction f (nontrivialIdempotentAction g p)
    apply Subtype.ext
    rfl

theorem nontrivialIdempotentAction_preserve_orthogonality
    (f : SplitOctF2Aut) (p₁ p₂ : NontrivialIdempotent)
    (h_orth : mul p₁.1 p₂.1 = zero) :
    mul (f • p₁).1 (f • p₂).1 = zero := by
  change mul (f⁻¹.1 p₁.1) (f⁻¹.1 p₂.1) = zero
  have h := f⁻¹.2.2.2 p₁.1 p₂.1
  rw [h_orth] at h
  simpa [map_zero] using h.symm

theorem nontrivialIdempotentAction_preserve_orthogonality_iff
    (f : SplitOctF2Aut) (p₁ p₂ : NontrivialIdempotent) :
    mul (f • p₁).1 (f • p₂).1 = zero ↔ mul p₁.1 p₂.1 = zero := by
  constructor
  · intro h
    have h' := nontrivialIdempotentAction_preserve_orthogonality
      f⁻¹ (f • p₁) (f • p₂) h
    simpa using h'
  · exact nontrivialIdempotentAction_preserve_orthogonality f p₁ p₂

theorem nontrivialIdempotentAction_preserve_right_neighbour_relation
    (f : SplitOctF2Aut) (p₁ p₂ : NontrivialIdempotent)
    (h_orth : mul p₂.1 p₁.1 = zero) :
    mul (f • p₂).1 (f • p₁).1 = zero := by
  change mul (f⁻¹.1 p₂.1) (f⁻¹.1 p₁.1) = zero
  have h := f⁻¹.2.2.2 p₂.1 p₁.1
  rw [h_orth] at h
  simpa [map_zero] using h.symm

theorem nontrivialIdempotentAction_preserve_right_orthogonality_iff
    (f : SplitOctF2Aut) (p₁ p₂ : NontrivialIdempotent) :
    mul (f • p₂).1 (f • p₁).1 = zero ↔ mul p₂.1 p₁.1 = zero := by
  constructor
  · intro h
    have h' := nontrivialIdempotentAction_preserve_right_neighbour_relation
      f⁻¹ (f • p₁) (f • p₂) h
    simpa using h'
  · exact nontrivialIdempotentAction_preserve_right_neighbour_relation f p₁ p₂

def rightNontrivialIdempotentNeighboursEquiv
    (f : SplitOctF2Aut) (u : NontrivialIdempotent) :
    RightNontrivialIdempotentNeighbours u ≃
      RightNontrivialIdempotentNeighbours (f • u) where
  toFun v := ⟨f • v.1, by
    exact nontrivialIdempotentAction_preserve_right_neighbour_relation f u v.1 v.2⟩
  invFun v := ⟨f⁻¹ • v.1, by
    have h := nontrivialIdempotentAction_preserve_right_neighbour_relation
      f⁻¹ (f • u) v.1 v.2
    simpa using h⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp

theorem rightNontrivialIdempotentNeighbours_card_invariant
    (f : SplitOctF2Aut) (u : NontrivialIdempotent)
    [Fintype (RightNontrivialIdempotentNeighbours u)]
    [Fintype (RightNontrivialIdempotentNeighbours (f • u))] :
    Fintype.card (RightNontrivialIdempotentNeighbours u) =
      Fintype.card (RightNontrivialIdempotentNeighbours (f • u)) :=
  Fintype.card_congr (rightNontrivialIdempotentNeighboursEquiv f u)

def nontrivialIdempotentNeighboursEquiv
    (f : SplitOctF2Aut) (u : NontrivialIdempotent) :
    NontrivialIdempotentNeighbours u ≃
      NontrivialIdempotentNeighbours (f • u) where
  toFun v := ⟨f • v.1, by
    exact nontrivialIdempotentAction_preserve_orthogonality f u v.1 v.2⟩
  invFun v := ⟨f⁻¹ • v.1, by
    have h := nontrivialIdempotentAction_preserve_orthogonality
      f⁻¹ (f • u) v.1 v.2
    simpa using h⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp

theorem nontrivialIdempotentNeighbours_card_invariant
    (f : SplitOctF2Aut) (u : NontrivialIdempotent)
    [Fintype (NontrivialIdempotentNeighbours u)]
    [Fintype (NontrivialIdempotentNeighbours (f • u))] :
    Fintype.card (NontrivialIdempotentNeighbours u) =
      Fintype.card (NontrivialIdempotentNeighbours (f • u)) :=
  Fintype.card_congr (nontrivialIdempotentNeighboursEquiv f u)

/- The complementary idempotent acts as the identity on the zero-product
   fibre.  This is the genuine Peirce eigenspace statement for the existing
   neighbour carrier; it does not identify square-zero frame coordinates
   with idempotents. -/
theorem nontrivialIdempotentNeighbours_complement_mul
    (u : NontrivialIdempotent)
    (v : NontrivialIdempotentNeighbours u) :
    mul (peirceComplement u.1) v.1.1 = v.1.1 := by
  change mul (add one u.1) v.1.1 = v.1.1
  rw [add_mul, one_mul, v.2, add_zero]

theorem nontrivialIdempotentAction_preserve_completeness
    (f : SplitOctF2Aut) (p₁ p₂ : NontrivialIdempotent)
    (h_comp : add p₁.1 p₂.1 = one) :
    add (f • p₁).1 (f • p₂).1 = one := by
  change add (f⁻¹.1 p₁.1) (f⁻¹.1 p₂.1) = one
  have h := f⁻¹.2.2.1 p₁.1 p₂.1
  rw [h_comp, f⁻¹.2.1] at h
  exact h.symm

theorem nontrivialIdempotentAction_preserve_completeness_iff
    (f : SplitOctF2Aut) (p₁ p₂ : NontrivialIdempotent) :
    add (f • p₁).1 (f • p₂).1 = one ↔ add p₁.1 p₂.1 = one := by
  constructor
  · intro h
    have h' := nontrivialIdempotentAction_preserve_completeness
      f⁻¹ (f • p₁) (f • p₂) h
    simpa using h'
  · exact nontrivialIdempotentAction_preserve_completeness f p₁ p₂

theorem admissibleBasis7_prefix_map_one
    (v : AdmissibleBasis7Carrier) :
    extendBasisMap (basis8From7 (basisCoordinates v)) one = one := by
  exact v.2.2.1

theorem admissibleBasis7_prefix_map_add
    (v : AdmissibleBasis7Carrier) (X Y : SplitOctF2) :
    extendBasisMap (basis8From7 (basisCoordinates v)) (add X Y) =
      add (extendBasisMap (basis8From7 (basisCoordinates v)) X)
        (extendBasisMap (basis8From7 (basisCoordinates v)) Y) := by
  exact v.2.2.2.1 X Y

theorem admissibleBasis7_prefix_map_mul
    (v : AdmissibleBasis7Carrier) (X Y : SplitOctF2) :
    extendBasisMap (basis8From7 (basisCoordinates v)) (mul X Y) =
      mul (extendBasisMap (basis8From7 (basisCoordinates v)) X)
        (extendBasisMap (basis8From7 (basisCoordinates v)) Y) := by
  exact v.2.2.2.2 X Y

theorem admissibleBasis7_prefix_map_zero
    (v : AdmissibleBasis7Carrier) :
    extendBasisMap (basis8From7 (basisCoordinates v)) zero = zero := by
  have h := admissibleBasis7_prefix_map_add v zero zero
  rw [add_self] at h
  exact h

theorem admissibleBasis7_prefix_map_injective
    (v : AdmissibleBasis7Carrier) :
    Function.Injective (extendBasisMap (basis8From7 (basisCoordinates v))) := by
  exact v.2.1

/- The first extracted coordinate is the image of the split idempotent
   `ePlus`; this is the first algebraic constraint needed by any subsequent
   finite prefix classification. -/
theorem admissibleBasis7_first_prefix_idempotent
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix1 v) (basisPrefix1 v) = basisPrefix1 v := by
  have h := admissibleBasis7_prefix_map_mul v ePlus ePlus
  have he : mul ePlus ePlus = ePlus := by
    rfl
  rw [he] at h
  have hv :
      extendBasisMap (basis8From7 (basisCoordinates v)) ePlus =
        basisPrefix1 v := by
    simpa [basisPrefix1, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  rw [hv] at h
  exact h.symm

theorem admissibleBasis7_first_prefix_ne_zero
    (v : AdmissibleBasis7Carrier) :
    basisPrefix1 v ≠ zero := by
  intro hzero
  have hv :
      extendBasisMap (basis8From7 (basisCoordinates v)) ePlus =
        basisPrefix1 v := by
    simpa [basisPrefix1, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  have hz := admissibleBasis7_prefix_map_zero v
  have hinj := admissibleBasis7_prefix_map_injective v
  have heq :
      extendBasisMap (basis8From7 (basisCoordinates v)) ePlus =
        extendBasisMap (basis8From7 (basisCoordinates v)) zero := by
    rw [hv, hzero, hz]
  exact (by decide : ePlus ≠ zero) (hinj heq)

theorem admissibleBasis7_first_prefix_ne_one
    (v : AdmissibleBasis7Carrier) :
    basisPrefix1 v ≠ one := by
  intro hone
  have hv :
      extendBasisMap (basis8From7 (basisCoordinates v)) ePlus =
        basisPrefix1 v := by
    simpa [basisPrefix1, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  have h₁ := admissibleBasis7_prefix_map_one v
  have hinj := admissibleBasis7_prefix_map_injective v
  have heq :
      extendBasisMap (basis8From7 (basisCoordinates v)) ePlus =
        extendBasisMap (basis8From7 (basisCoordinates v)) one := by
    rw [hv, hone, h₁]
  exact (by decide : ePlus ≠ one) (hinj heq)

def admissibleBasis7_first_prefix_code
    (v : AdmissibleBasis7Carrier) : NontrivialIdempotent :=
  ⟨basisPrefix1 v,
    admissibleBasis7_first_prefix_idempotent v,
    admissibleBasis7_first_prefix_ne_zero v,
    admissibleBasis7_first_prefix_ne_one v⟩

def admissibleBasis7FirstFiber (p : NontrivialIdempotent) : Type :=
  {v : AdmissibleBasis7Carrier // admissibleBasis7_first_prefix_code v = p}

noncomputable def admissibleBasis7CarrierSigmaEquiv :
    AdmissibleBasis7Carrier ≃
      Σ p : NontrivialIdempotent, admissibleBasis7FirstFiber p where
  toFun v := ⟨admissibleBasis7_first_prefix_code v, ⟨v, rfl⟩⟩
  invFun q := q.2.1
  left_inv v := by rfl
  right_inv q := by
    rcases q with ⟨p, v, hv⟩
    cases hv
    rfl

@[simp] theorem admissibleBasis7_first_prefix_code_value
    (v : AdmissibleBasis7Carrier) :
    (admissibleBasis7_first_prefix_code v : SplitOctF2) = basisPrefix1 v :=
  rfl

theorem admissibleBasis7_eMinus_image_from_first_prefix
    (v : AdmissibleBasis7Carrier) :
    extendBasisMap (basis8From7 (basisCoordinates v)) eMinus =
      peirceComplement (basisPrefix1 v) := by
  have he : eMinus = add one ePlus := by
    rfl
  rw [he, admissibleBasis7_prefix_map_add,
    admissibleBasis7_prefix_map_one]
  have hv :
      extendBasisMap (basis8From7 (basisCoordinates v)) ePlus =
        basisPrefix1 v := by
    simpa [basisPrefix1, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  rw [hv]
  rfl

theorem admissibleBasis7_complement_prefix_idempotent
    (v : AdmissibleBasis7Carrier) :
    mul (peirceComplement (basisPrefix1 v)) (peirceComplement (basisPrefix1 v)) =
      peirceComplement (basisPrefix1 v) := by
  have h := admissibleBasis7_prefix_map_mul v eMinus eMinus
  have he : mul eMinus eMinus = eMinus := by rfl
  rw [he] at h
  have hv := admissibleBasis7_eMinus_image_from_first_prefix v
  rw [hv] at h
  exact h.symm

theorem admissibleBasis7_first_prefix_orthogonal_complement
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix1 v) (peirceComplement (basisPrefix1 v)) = zero := by
  have h := admissibleBasis7_prefix_map_mul v ePlus eMinus
  have he : mul ePlus eMinus = zero := by rfl
  rw [he] at h
  have hp :
      extendBasisMap (basis8From7 (basisCoordinates v)) ePlus =
        basisPrefix1 v := by
    simpa [basisPrefix1, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  have hcomp := admissibleBasis7_eMinus_image_from_first_prefix v
  rw [hp, hcomp, admissibleBasis7_prefix_map_zero v] at h
  exact h.symm

theorem admissibleBasis7_complement_orthogonal_first_prefix
    (v : AdmissibleBasis7Carrier) :
    mul (peirceComplement (basisPrefix1 v)) (basisPrefix1 v) = zero := by
  have h := admissibleBasis7_prefix_map_mul v eMinus ePlus
  have he : mul eMinus ePlus = zero := by rfl
  rw [he] at h
  have hp :
      extendBasisMap (basis8From7 (basisCoordinates v)) ePlus =
        basisPrefix1 v := by
    simpa [basisPrefix1, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  have hcomp := admissibleBasis7_eMinus_image_from_first_prefix v
  rw [hcomp, hp, admissibleBasis7_prefix_map_zero v] at h
  exact h.symm

theorem admissibleBasis7_complement_prefix_ne_zero
    (v : AdmissibleBasis7Carrier) :
    peirceComplement (basisPrefix1 v) ≠ zero := by
  intro hzero
  have hcomp := admissibleBasis7_eMinus_image_from_first_prefix v
  have hz := admissibleBasis7_prefix_map_zero v
  have hinj := admissibleBasis7_prefix_map_injective v
  have heq :
      extendBasisMap (basis8From7 (basisCoordinates v)) eMinus =
        extendBasisMap (basis8From7 (basisCoordinates v)) zero := by
    rw [hcomp, hzero, hz]
  exact (by decide : eMinus ≠ zero) (hinj heq)

theorem admissibleBasis7_complement_prefix_ne_one
    (v : AdmissibleBasis7Carrier) :
    peirceComplement (basisPrefix1 v) ≠ one := by
  intro hone
  have hcomp := admissibleBasis7_eMinus_image_from_first_prefix v
  have h₁ := admissibleBasis7_prefix_map_one v
  have hinj := admissibleBasis7_prefix_map_injective v
  have heq :
      extendBasisMap (basis8From7 (basisCoordinates v)) eMinus =
        extendBasisMap (basis8From7 (basisCoordinates v)) one := by
    rw [hcomp, hone, h₁]
  exact (by decide : eMinus ≠ one) (hinj heq)

def admissibleBasis7_complement_prefix_code
    (v : AdmissibleBasis7Carrier) : NontrivialIdempotent :=
  ⟨peirceComplement (basisPrefix1 v),
    admissibleBasis7_complement_prefix_idempotent v,
    admissibleBasis7_complement_prefix_ne_zero v,
    admissibleBasis7_complement_prefix_ne_one v⟩

@[simp] theorem admissibleBasis7_complement_prefix_code_value
    (v : AdmissibleBasis7Carrier) :
    (admissibleBasis7_complement_prefix_code v : SplitOctF2) =
      peirceComplement (basisPrefix1 v) :=
  rfl

def admissibleBasis7_first_peirce_pair
    (v : AdmissibleBasis7Carrier) :
    NontrivialIdempotent × NontrivialIdempotent :=
  (admissibleBasis7_first_prefix_code v,
    admissibleBasis7_complement_prefix_code v)

@[simp] theorem admissibleBasis7_first_peirce_pair_values
    (v : AdmissibleBasis7Carrier) :
    (((admissibleBasis7_first_peirce_pair v).1 : SplitOctF2),
      ((admissibleBasis7_first_peirce_pair v).2 : SplitOctF2)) =
      (basisPrefix1 v, peirceComplement (basisPrefix1 v)) := by
  rfl

theorem admissibleBasis7_first_prefix_complement_sum
    (v : AdmissibleBasis7Carrier) :
    add (basisPrefix1 v) (peirceComplement (basisPrefix1 v)) = one := by
  have h := admissibleBasis7_prefix_map_add v ePlus eMinus
  have he : add ePlus eMinus = one := by rfl
  rw [he] at h
  have hp :
      extendBasisMap (basis8From7 (basisCoordinates v)) ePlus =
        basisPrefix1 v := by
    simpa [basisPrefix1, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  have hcomp := admissibleBasis7_eMinus_image_from_first_prefix v
  have h₁ := admissibleBasis7_prefix_map_one v
  rw [h₁, hp, hcomp] at h
  exact h.symm

def admissibleBasis7_first_peirce_pair_neighbour
    (v : AdmissibleBasis7Carrier) :
    NontrivialIdempotentNeighbours
      (admissibleBasis7_first_peirce_pair v).1 := by
  refine ⟨(admissibleBasis7_first_peirce_pair v).2, ?_⟩
  exact admissibleBasis7_first_prefix_orthogonal_complement v

theorem admissibleBasis7_complement_first_prefix_sum
    (v : AdmissibleBasis7Carrier) :
    add (peirceComplement (basisPrefix1 v)) (basisPrefix1 v) = one := by
  rw [add_comm]
  exact admissibleBasis7_first_prefix_complement_sum v

theorem admissibleBasis7_second_fifth_product_eq_first
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix2 v) (basisPrefix5 v) = basisPrefix1 v := by
  have h := admissibleBasis7_prefix_map_mul v up0 down0
  have he : mul up0 down0 = ePlus := by
    rfl
  rw [he] at h
  have h₂ :
      extendBasisMap (basis8From7 (basisCoordinates v)) up0 =
        basisPrefix2 v := by
    simpa [basisPrefix2, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 2)
  have h₅ :
      extendBasisMap (basis8From7 (basisCoordinates v)) down0 =
        basisPrefix5 v := by
    simpa [basisPrefix5, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 5)
  have h₁ :
      extendBasisMap (basis8From7 (basisCoordinates v)) ePlus =
        basisPrefix1 v := by
    simpa [basisPrefix1, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  rw [h₂, h₅, h₁] at h
  exact h.symm

theorem admissibleBasis7_fifth_second_product_eq_complement
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix5 v) (basisPrefix2 v) =
      peirceComplement (basisPrefix1 v) := by
  have h := admissibleBasis7_prefix_map_mul v down0 up0
  have he : mul down0 up0 = eMinus := by
    rfl
  rw [he] at h
  have h₅ :
      extendBasisMap (basis8From7 (basisCoordinates v)) down0 =
        basisPrefix5 v := by
    simpa [basisPrefix5, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 5)
  have h₂ :
      extendBasisMap (basis8From7 (basisCoordinates v)) up0 =
        basisPrefix2 v := by
    simpa [basisPrefix2, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 2)
  have hcomp := admissibleBasis7_eMinus_image_from_first_prefix v
  rw [h₅, h₂, hcomp] at h
  exact h.symm

theorem admissibleBasis7_second_sixth_product_eq_zero
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix2 v) (basisPrefix6 v) = zero := by
  have h := admissibleBasis7_prefix_map_mul v up0 down1
  have he : mul up0 down1 = zero := by rfl
  rw [he] at h
  have h₂ :
      extendBasisMap (basis8From7 (basisCoordinates v)) up0 =
        basisPrefix2 v := by
    simpa [basisPrefix2, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 2)
  have h₆ :
      extendBasisMap (basis8From7 (basisCoordinates v)) down1 =
        basisPrefix6 v := by
    simpa [basisPrefix6, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 6)
  have hz := admissibleBasis7_prefix_map_zero v
  rw [h₂, h₆, hz] at h
  exact h.symm

theorem admissibleBasis7_second_prefix_square_zero
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix2 v) (basisPrefix2 v) = zero := by
  have h := admissibleBasis7_prefix_map_mul v up0 up0
  have he : mul up0 up0 = zero := by
    rfl
  rw [he] at h
  have hv :
      extendBasisMap (basis8From7 (basisCoordinates v)) up0 =
        basisPrefix2 v := by
    simpa [basisPrefix2, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 2)
  have hz := admissibleBasis7_prefix_map_zero v
  rw [hv, hz] at h
  exact h.symm

def NonzeroSquareZero :=
  {x : SplitOctF2 // mul x x = zero ∧ x ≠ zero}

theorem admissibleBasis7_second_prefix_ne_zero
    (v : AdmissibleBasis7Carrier) :
    basisPrefix2 v ≠ zero := by
  intro hzero
  have hv :
      extendBasisMap (basis8From7 (basisCoordinates v)) up0 =
        basisPrefix2 v := by
    simpa [basisPrefix2, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 2)
  have hz := admissibleBasis7_prefix_map_zero v
  have hinj := admissibleBasis7_prefix_map_injective v
  have heq :
      extendBasisMap (basis8From7 (basisCoordinates v)) up0 =
        extendBasisMap (basis8From7 (basisCoordinates v)) zero := by
    rw [hv, hzero, hz]
  exact (by decide : up0 ≠ zero) (hinj heq)

def admissibleBasis7_second_prefix_code
    (v : AdmissibleBasis7Carrier) : NonzeroSquareZero :=
  ⟨basisPrefix2 v,
    admissibleBasis7_second_prefix_square_zero v,
    admissibleBasis7_second_prefix_ne_zero v⟩

/- The second prefix is a square-zero Peirce-root coordinate.  Its correct
   relation with the first idempotent is the eigenvalue-one relation, not the
   zero-product neighbour relation. -/
theorem admissibleBasis7_first_prefix_mul_second_prefix
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix1 v) (basisPrefix2 v) = basisPrefix2 v := by
  have h := admissibleBasis7_prefix_map_mul v ePlus up0
  have he : mul ePlus up0 = up0 := by
    rfl
  rw [he] at h
  have h₁ :
      extendBasisMap (basis8From7 (basisCoordinates v)) ePlus =
        basisPrefix1 v := by
    simpa [basisPrefix1, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 0)
  have h₂ :
      extendBasisMap (basis8From7 (basisCoordinates v)) up0 =
        basisPrefix2 v := by
    simpa [basisPrefix2, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 2)
  rw [h₁, h₂] at h
  exact h.symm

def PeircePlusFiber (p : NontrivialIdempotent) : Type :=
  {x : NonzeroSquareZero // mul p.1 x.1 = x.1}

def admissibleBasis7Second
    (v : AdmissibleBasis7Carrier) :
    PeircePlusFiber (admissibleBasis7_first_prefix_code v) :=
  ⟨admissibleBasis7_second_prefix_code v, by
    simpa [PeircePlusFiber, admissibleBasis7_first_prefix_code,
      admissibleBasis7_second_prefix_code] using
      admissibleBasis7_first_prefix_mul_second_prefix v⟩

theorem admissibleBasis7_third_prefix_square_zero
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix3 v) (basisPrefix3 v) = zero := by
  have h := admissibleBasis7_prefix_map_mul v up1 up1
  have he : mul up1 up1 = zero := by
    rfl
  rw [he] at h
  have hv :
      extendBasisMap (basis8From7 (basisCoordinates v)) up1 =
        basisPrefix3 v := by
    simpa [basisPrefix3, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 3)
  have hz := admissibleBasis7_prefix_map_zero v
  rw [hv, hz] at h
  exact h.symm

theorem admissibleBasis7_fourth_prefix_square_zero
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix4 v) (basisPrefix4 v) = zero := by
  have h := admissibleBasis7_prefix_map_mul v up2 up2
  have he : mul up2 up2 = zero := by rfl
  rw [he] at h
  have hv :
      extendBasisMap (basis8From7 (basisCoordinates v)) up2 =
        basisPrefix4 v := by
    simpa [basisPrefix4, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 4)
  have hz := admissibleBasis7_prefix_map_zero v
  rw [hv, hz] at h
  exact h.symm

theorem admissibleBasis7_fifth_prefix_square_zero
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix5 v) (basisPrefix5 v) = zero := by
  have h := admissibleBasis7_prefix_map_mul v down0 down0
  have he : mul down0 down0 = zero := by rfl
  rw [he] at h
  have hv :
      extendBasisMap (basis8From7 (basisCoordinates v)) down0 =
        basisPrefix5 v := by
    simpa [basisPrefix5, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 5)
  have hz := admissibleBasis7_prefix_map_zero v
  rw [hv, hz] at h
  exact h.symm

theorem admissibleBasis7_sixth_prefix_square_zero
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix6 v) (basisPrefix6 v) = zero := by
  have h := admissibleBasis7_prefix_map_mul v down1 down1
  have he : mul down1 down1 = zero := by rfl
  rw [he] at h
  have hv :
      extendBasisMap (basis8From7 (basisCoordinates v)) down1 =
        basisPrefix6 v := by
    simpa [basisPrefix6, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 6)
  have hz := admissibleBasis7_prefix_map_zero v
  rw [hv, hz] at h
  exact h.symm

theorem admissibleBasis7_seventh_prefix_square_zero
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix7 v) (basisPrefix7 v) = zero := by
  have h := admissibleBasis7_prefix_map_mul v down2 down2
  have he : mul down2 down2 = zero := by rfl
  rw [he] at h
  have hv :
      extendBasisMap (basis8From7 (basisCoordinates v)) down2 =
        basisPrefix7 v := by
    simpa [basisPrefix7, basisCoordinates, basis8] using
      (extendBasisMap_basis (basis8From7 (basisCoordinates v)) 7)
  have hz := admissibleBasis7_prefix_map_zero v
  rw [hv, hz] at h
  exact h.symm

theorem admissibleBasis7_to_aut_basis7
    (v : AdmissibleBasis7Carrier) (i : Fin 7) :
    (admissibleBasis7_to_aut v.1 v.2).1 (basis7 i) = basisCoordinates v i := by
  rw [admissibleBasis7_to_aut_apply]
  fin_cases i <;>
    simp [basis8From7, basis7, basisCoordinates, extendBasisMap,
      add, zero, ePlus, up0, up1, up2, down0, down1, down2]

theorem admissibleBasis7_all_prefixes_square_zero
    (v : AdmissibleBasis7Carrier) :
    mul (basisPrefix2 v) (basisPrefix2 v) = zero ∧
    mul (basisPrefix3 v) (basisPrefix3 v) = zero ∧
    mul (basisPrefix4 v) (basisPrefix4 v) = zero ∧
    mul (basisPrefix5 v) (basisPrefix5 v) = zero ∧
    mul (basisPrefix6 v) (basisPrefix6 v) = zero ∧
    mul (basisPrefix7 v) (basisPrefix7 v) = zero := by
  exact ⟨admissibleBasis7_second_prefix_square_zero v,
    admissibleBasis7_third_prefix_square_zero v,
    admissibleBasis7_fourth_prefix_square_zero v,
    admissibleBasis7_fifth_prefix_square_zero v,
    admissibleBasis7_sixth_prefix_square_zero v,
    admissibleBasis7_seventh_prefix_square_zero v⟩

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
