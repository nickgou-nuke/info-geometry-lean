import InfoGeometry.Exceptional.FreudenthalAction
import InfoGeometry.Exceptional.STUFreudenthalIdentity
import InfoGeometry.Exceptional.STUFreudenthalQuarticScaling

/-!
# Scaling invariance of the STU Freudenthal boundary

The concrete STU quartic is homogeneous of degree four.  Together with the
fact that a nonzero scalar cannot annihilate a charge, this gives the exact
boundary invariant needed by later projective/colimit constructions.
-/

noncomputable section

namespace InfoGeometry.Exceptional.STUDatum

open InfoGeometry.Exceptional.Freudenthal

@[simp] theorem stuHeisenberg_zero_eq_additive_zero :
    (HeisenbergElement.zero : HeisenbergElement STUCarrier) = 0 := by
  apply HeisenbergElement.ext
  · apply FreudenthalCharge.ext <;> rfl
  · rfl

theorem stuDatum_adjoint_identity (x : STUCarrier) :
    STU_Datum.adjointQuad (STU_Datum.adjointQuad x) =
      STU_Datum.normCubic x • x := by
  simpa [STU_Datum] using stuAdjointQuad_adjointQuad x

theorem stuHeisenbergBracket_add_left
    (X Y Z : HeisenbergElement STUCarrier) :
    HeisenbergElement.bracket STU_Datum (X + Y) Z =
      HeisenbergElement.bracket STU_Datum X Z +
        HeisenbergElement.bracket STU_Datum Y Z := by
  apply HeisenbergElement.ext
  · ext <;> simp [HeisenbergElement.bracket, HeisenbergElement.zeroCharge]
  · simp [HeisenbergElement.bracket, symplecticForm_add_left]

theorem stuHeisenbergBracket_add_right
    (X Y Z : HeisenbergElement STUCarrier) :
    HeisenbergElement.bracket STU_Datum X (Y + Z) =
      HeisenbergElement.bracket STU_Datum X Y +
        HeisenbergElement.bracket STU_Datum X Z := by
  apply HeisenbergElement.ext
  · ext <;> simp [HeisenbergElement.bracket, HeisenbergElement.zeroCharge]
  · simp [HeisenbergElement.bracket, symplecticForm_add_right]

theorem stuHeisenbergBracket_smul_left
    (r : ℝ) (X Y : HeisenbergElement STUCarrier) :
    HeisenbergElement.bracket STU_Datum (r • X) Y =
      r • HeisenbergElement.bracket STU_Datum X Y := by
  apply HeisenbergElement.ext
  · change (0 : FreudenthalCharge STUCarrier) = r • 0
    simp
  · change FreudenthalCharge.symplecticForm STU_Datum (r • X.charge) Y.charge =
      r * FreudenthalCharge.symplecticForm STU_Datum X.charge Y.charge
    exact symplecticForm_smul_left STU_Datum r X.charge Y.charge

theorem stuHeisenbergBracket_smul_right
    (r : ℝ) (X Y : HeisenbergElement STUCarrier) :
    HeisenbergElement.bracket STU_Datum X (r • Y) =
      r • HeisenbergElement.bracket STU_Datum X Y := by
  apply HeisenbergElement.ext
  · change (0 : FreudenthalCharge STUCarrier) = r • 0
    simp
  · change FreudenthalCharge.symplecticForm STU_Datum X.charge (r • Y.charge) =
      r * FreudenthalCharge.symplecticForm STU_Datum X.charge Y.charge
    exact symplecticForm_smul_right STU_Datum r X.charge Y.charge

theorem stuHeisenbergBracket_neg_left
    (X Y : HeisenbergElement STUCarrier) :
    HeisenbergElement.bracket STU_Datum (-X) Y =
      -HeisenbergElement.bracket STU_Datum X Y := by
  simpa only [neg_one_smul] using
    stuHeisenbergBracket_smul_left (-1 : ℝ) X Y

theorem stuHeisenbergBracket_neg_right
    (X Y : HeisenbergElement STUCarrier) :
    HeisenbergElement.bracket STU_Datum X (-Y) =
      -HeisenbergElement.bracket STU_Datum X Y := by
  simpa only [neg_one_smul] using
    stuHeisenbergBracket_smul_right (-1 : ℝ) X Y

theorem stuHeisenbergBracket_jacobi
    (X Y Z : HeisenbergElement STUCarrier) :
    HeisenbergElement.bracket STU_Datum X
        (HeisenbergElement.bracket STU_Datum Y Z) +
      HeisenbergElement.bracket STU_Datum Y
        (HeisenbergElement.bracket STU_Datum Z X) +
      HeisenbergElement.bracket STU_Datum Z
        (HeisenbergElement.bracket STU_Datum X Y) = 0 := by
  rw [HeisenbergElement.bracket_bracket_right,
    HeisenbergElement.bracket_bracket_right,
    HeisenbergElement.bracket_bracket_right]
  simp only [stuHeisenberg_zero_eq_additive_zero, add_zero]

/-- The coordinate polynomial represented by the STU Freudenthal quartic. -/
def stuQuarticPolynomial (Q : FreudenthalCharge STUCarrier) : ℝ :=
  (Q.alpha * Q.beta -
      (Q.x 0 * Q.y 0 + Q.x 1 * Q.y 1 + Q.x 2 * Q.y 2)) ^ 2 -
    4 * (Q.alpha * (Q.x 0 * Q.x 1 * Q.x 2) +
      Q.beta * (Q.y 0 * Q.y 1 * Q.y 2) -
      ((Q.x 1 * Q.x 2) * (Q.y 1 * Q.y 2) +
        (Q.x 0 * Q.x 2) * (Q.y 0 * Q.y 2) +
        (Q.x 0 * Q.x 1) * (Q.y 0 * Q.y 1)))

@[simp] theorem stuQuarticInvariant_eq_polynomial
    (Q : FreudenthalCharge STUCarrier) :
    FreudenthalCharge.quarticInvariant STU_Datum Q = stuQuarticPolynomial Q := by
  simpa [stuQuarticPolynomial] using stuQuarticInvariant_expanded Q

theorem stuTraceBilin_nondegenerate :
    ∀ x : STUCarrier, (∀ y : STUCarrier, stuTraceBilin x y = 0) → x = 0 := by
  intro x hx
  funext i
  fin_cases i
  · have h := hx (Pi.single 0 1)
    simpa [stuTraceBilin] using h
  · have h := hx (Pi.single 1 1)
    simpa [stuTraceBilin] using h
  · have h := hx (Pi.single 2 1)
    simpa [stuTraceBilin] using h

theorem stuFreudenthalSymplectic_nondegenerate :
    ∀ Q : FreudenthalCharge STUCarrier,
      (∀ P : FreudenthalCharge STUCarrier,
        FreudenthalCharge.symplecticForm STU_Datum Q P = 0) → Q = 0 := by
  exact symplecticForm_nondegenerate_of_traceBilin_nondegenerate STU_Datum
    stuTraceBilin_nondegenerate

theorem stuFreudenthalRegular_iff_polynomial_ne_zero
    (Q : FreudenthalCharge STUCarrier) :
    FreudenthalRegular STU_Datum Q ↔ stuQuarticPolynomial Q ≠ 0 := by
  simp [FreudenthalRegular]

theorem stuFreudenthalBoundary_iff_polynomial
    (Q : FreudenthalCharge STUCarrier) :
    FreudenthalBoundary STU_Datum Q ↔
      stuQuarticPolynomial Q = 0 ∧ Q ≠ zeroCharge STUCarrier := by
  simp [FreudenthalBoundary]

theorem stuFreudenthalBoundary_iff_coordinates
    (Q : FreudenthalCharge STUCarrier) :
    FreudenthalBoundary STU_Datum Q ↔
      stuQuarticPolynomial Q = 0 ∧
        (Q.alpha ≠ 0 ∨ Q.beta ≠ 0 ∨ Q.x ≠ 0 ∨ Q.y ≠ 0) := by
  rw [stuFreudenthalBoundary_iff_polynomial]
  constructor
  · rintro ⟨hq, hn⟩
    refine ⟨hq, ?_⟩
    by_contra hnot
    push_neg at hnot
    exact hn ((HeisenbergElement.zeroCharge_eq_iff Q).2
      ⟨hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2⟩)
  · rintro ⟨hq, hn⟩
    refine ⟨hq, ?_⟩
    intro hzero
    rcases hn with ha | hb | hx | hy
    · exact ha ((HeisenbergElement.zeroCharge_eq_iff Q).1 hzero).1
    · exact hb ((HeisenbergElement.zeroCharge_eq_iff Q).1 hzero).2.1
    · exact hx ((HeisenbergElement.zeroCharge_eq_iff Q).1 hzero).2.2.1
    · exact hy ((HeisenbergElement.zeroCharge_eq_iff Q).1 hzero).2.2.2

theorem stuFreudenthalBoundary_smul_iff
    (r : ℝ) (hr : r ≠ 0) (Q : FreudenthalCharge STUCarrier) :
    FreudenthalBoundary STU_Datum (r • Q) ↔
      FreudenthalBoundary STU_Datum Q := by
  constructor
  · rintro ⟨hquartic, hzero⟩
    constructor
    · rw [stuQuarticInvariant_smul] at hquartic
      exact (mul_eq_zero.mp hquartic).resolve_left (pow_ne_zero 4 hr)
    · intro hQ
      apply hzero
      rw [hQ]
      ext <;> simp [zeroCharge]
  · rintro ⟨hquartic, hzero⟩
    constructor
    · rw [stuQuarticInvariant_smul]
      rw [hquartic, mul_zero]
    · intro hQ
      apply hzero
      apply (smul_right_injective _ hr)
      have hz : r • zeroCharge STUCarrier = zeroCharge STUCarrier := by
        ext <;> simp [zeroCharge]
      exact hQ.trans hz.symm

theorem stuFreudenthalBoundary_neg_iff
    (Q : FreudenthalCharge STUCarrier) :
    FreudenthalBoundary STU_Datum (-Q) ↔
      FreudenthalBoundary STU_Datum Q := by
  simpa only [neg_one_smul] using
    stuFreudenthalBoundary_smul_iff (-1 : ℝ) (by norm_num) Q

theorem stuFreudenthalRegular_neg_iff
    (Q : FreudenthalCharge STUCarrier) :
    FreudenthalRegular STU_Datum (-Q) ↔
      FreudenthalRegular STU_Datum Q := by
  simp only [FreudenthalRegular, stuQuarticInvariant_neg]

end InfoGeometry.Exceptional.STUDatum
