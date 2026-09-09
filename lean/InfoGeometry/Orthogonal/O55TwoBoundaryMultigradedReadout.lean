import InfoGeometry.Orthogonal.O55ContactFiveGrading
import InfoGeometry.Streaming.MultigradedTwoBoundarySelection

/-!
# Two-boundary readouts of the `O(5,5)` multigrading

The Witt-matrix representation acts on the ten-coordinate complex carrier.
A regular pair of projective boundary vectors then supplies normalized matrix
coefficients.  The five Cartan weights impose an exact selection rule: a
nonzero root readout can occur only when its `D₅` multidegree equals the
left/right boundary-weight difference.

The Witt-sheet exchange is constructed explicitly.  It reverses all five
Cartan operators and hence reverses every multidegree, while simultaneous
exchange of the two boundary vectors and conjugation of the probe leaves the
normalized coefficient unchanged.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55TwoBoundary

open scoped Matrix BigOperators
open InfoGeometry.Orthogonal.O55D5
open InfoGeometry.Orthogonal.O55Witt
open InfoGeometry.Orthogonal.O55Contact
open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
open InfoGeometry.Streaming.MultigradedTwoBoundarySelection

abbrev O55State :=
  InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional.State Index
abbrev O55Operator :=
  InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional.Operator Index
abbrev O55BoundaryPair :=
  InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional.RegularBoundaryPair Index

/-- Matrix action on the ten-coordinate Witt carrier. -/
def matrixAction (A : Mat10) : O55Operator where
  toFun x := fun p => ∑ q, A p q * x q
  map_add' x y := by
    ext p
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext p
    change (∑ q, A p q * (c * x q)) = c * (∑ q, A p q * x q)
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring

@[simp] theorem matrixAction_apply (A : Mat10) (x : O55State) (p : Index) :
    matrixAction A x p = ∑ q, A p q * x q := rfl

@[simp] theorem matrixAction_zero :
    matrixAction (0 : Mat10) = 0 := by
  apply LinearMap.ext
  intro x
  ext p
  simp [matrixAction]

@[simp] theorem matrixAction_add (A B : Mat10) :
    matrixAction (A + B) = matrixAction A + matrixAction B := by
  apply LinearMap.ext
  intro x
  ext p
  simp [matrixAction, Finset.sum_add_distrib, add_mul]

@[simp] theorem matrixAction_sub (A B : Mat10) :
    matrixAction (A - B) = matrixAction A - matrixAction B := by
  apply LinearMap.ext
  intro x
  ext p
  simp [matrixAction, Finset.sum_sub_distrib, sub_mul]

@[simp] theorem matrixAction_smul (c : ℂ) (A : Mat10) :
    matrixAction (c • A) = c • matrixAction A := by
  apply LinearMap.ext
  intro x
  ext p
  simp [matrixAction, Finset.mul_sum, mul_assoc]

/-- Matrix multiplication agrees with endomorphism composition. -/
@[simp] theorem matrixAction_mul (A B : Mat10) :
    matrixAction (A * B) = matrixAction A * matrixAction B := by
  classical
  apply LinearMap.ext
  intro x
  ext p
  simp only [matrixAction_apply, Matrix.mul_apply, Module.End.mul_apply]
  calc
    ∑ q, (∑ r, A p r * B r q) * x q =
        ∑ q, ∑ r, A p r * (B r q * x q) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = ∑ r, ∑ q, A p r * (B r q * x q) := by
          rw [Finset.sum_comm]
    _ = ∑ r, A p r * ∑ q, B r q * x q := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
    _ = _ := rfl

/-- The five Cartan endomorphisms. -/
def gradingOperator (a : Axis) : O55Operator :=
  matrixAction (axisCartanMatrix a)

/-- Root endomorphism in the Witt representation. -/
def rootOperator (r : Root) : O55Operator :=
  matrixAction (rootMatrix r)

/-- The root operators have their full `D₅` multidegrees. -/
theorem rootOperator_multiweight (r : Root) :
    IsOperatorMultiweight gradingOperator
      (fun a => (r.multiDegree a : ℂ)) (rootOperator r) := by
  intro a
  rw [gradingOperator, rootOperator, ← matrixAction_mul,
    ← matrixAction_mul, ← matrixAction_sub,
    axisCartan_rootMatrix, matrixAction_smul]

/-- Collapsed contact grading operator. -/
def contactGradingOperator : O55Operator :=
  matrixAction contactGradingMatrix

/-- Root operators have the expected collapsed contact degree. -/
theorem rootOperator_contact_weight (r : Root) :
    contactGradingOperator * rootOperator r -
        rootOperator r * contactGradingOperator =
      (r.contactDegree : ℂ) • rootOperator r := by
  rw [contactGradingOperator, rootOperator, ← matrixAction_mul,
    ← matrixAction_mul, ← matrixAction_sub,
    contactGrading_rootMatrix, matrixAction_smul]

/-- Normalized two-boundary coefficient of one root operator. -/
def rootReadout (B : O55BoundaryPair) (r : Root) : ℂ :=
  weakValue B (rootOperator r)

/-- A nonzero root coefficient selects exactly the boundary weight
difference in all five Cartan coordinates. -/
theorem rootReadout_ne_zero_implies_multidegree
    (B : O55BoundaryPair) (α β : Axis → ℂ)
    (hpre : IsRightWeight gradingOperator α B.pre)
    (hpost : IsLeftWeight gradingOperator β B.post)
    (r : Root) (hread : rootReadout B r ≠ 0) :
    (fun a => (r.multiDegree a : ℂ)) =
      boundaryWeightDifference α β := by
  exact weakValue_ne_zero_implies_weight_match
    B gradingOperator α β (fun a => (r.multiDegree a : ℂ))
      (rootOperator r) hpre hpost (rootOperator_multiweight r) hread

/-- Mismatch in one `D₅` coordinate forces the root readout to vanish. -/
theorem rootReadout_eq_zero_of_coordinate_mismatch
    (B : O55BoundaryPair) (α β : Axis → ℂ)
    (hpre : IsRightWeight gradingOperator α B.pre)
    (hpost : IsLeftWeight gradingOperator β B.post)
    (r : Root) (a : Axis)
    (hmismatch : β a - α a - (r.multiDegree a : ℂ) ≠ 0) :
    rootReadout B r = 0 := by
  exact weakValue_eq_zero_of_weight_mismatch
    B gradingOperator α β (fun b => (r.multiDegree b : ℂ))
      (rootOperator r) hpre hpost (rootOperator_multiweight r)
      a hmismatch

/-- A nonzero multigraded readout also obeys the collapsed five-grade
selection rule. -/
theorem rootReadout_contact_degree_selection
    (B : O55BoundaryPair) (α β : Axis → ℂ)
    (hpre : IsRightWeight gradingOperator α B.pre)
    (hpost : IsLeftWeight gradingOperator β B.post)
    (r : Root) (hread : rootReadout B r ≠ 0) :
    (r.contactDegree : ℂ) =
      (β 0 - α 0) + (β 1 - α 1) := by
  have hμ := rootReadout_ne_zero_implies_multidegree
    B α β hpre hpost r hread
  have h0 := congrFun hμ 0
  have h1 := congrFun hμ 1
  dsimp [boundaryWeightDifference] at h0 h1
  change ((r.multiDegree 0 + r.multiDegree 1 : ℤ) : ℂ) = _
  norm_cast
  push_cast
  rw [h0, h1]

/-! ## Witt-sheet exchange -/

/-- Exchange the two isotropic Witt sheets. -/
def sheetExchange : O55Operator where
  toFun x := fun p => x (flipIndex p)
  map_add' x y := by
    ext p
    rfl
  map_smul' c x := by
    ext p
    rfl

@[simp] theorem sheetExchange_apply (x : O55State) (p : Index) :
    sheetExchange x p = x (flipIndex p) := rfl

@[simp] theorem sheetExchange_sq :
    sheetExchange * sheetExchange = 1 := by
  apply LinearMap.ext
  intro x
  ext p
  simp [Module.End.mul_apply, sheetExchange]

/-- A Cartan matrix acts diagonally on the Witt carrier. -/
theorem cartanAction_apply (h : Axis → ℂ) (x : O55State) (p : Index) :
    matrixAction (cartanMatrix h) x p = indexWeight h p * x p := by
  classical
  simp [matrixAction, cartanMatrix]

/-- Sheet exchange reverses every diagonal Cartan direction. -/
theorem sheetExchange_cartan_conjugation (h : Axis → ℂ) :
    sheetExchange * matrixAction (cartanMatrix h) * sheetExchange =
      -matrixAction (cartanMatrix h) := by
  apply LinearMap.ext
  intro x
  ext p
  simp only [Module.End.mul_apply, sheetExchange_apply]
  simp [matrixAction, cartanMatrix, indexWeight_flip]

/-- In particular all five grading operators change sign. -/
theorem sheetExchange_gradingOperator (a : Axis) :
    sheetExchange * gradingOperator a * sheetExchange =
      -gradingOperator a := by
  exact sheetExchange_cartan_conjugation (axisCartanCoefficient a)

/-- Direct anticommutation form of the sheet/grading relation. -/
theorem gradingOperator_sheetExchange (a : Axis) :
    gradingOperator a * sheetExchange =
      -(sheetExchange * gradingOperator a) := by
  have h := sheetExchange_gradingOperator a
  calc
    gradingOperator a * sheetExchange =
        (sheetExchange * sheetExchange) *
          gradingOperator a * sheetExchange := by rw [sheetExchange_sq]; simp
    _ = sheetExchange *
        (sheetExchange * gradingOperator a * sheetExchange) := by
          noncomm_ring
    _ = sheetExchange * (-gradingOperator a) := by rw [h]
    _ = -(sheetExchange * gradingOperator a) := by
      ext x
      simp [Module.End.mul_apply]

/-- Conjugation of a probe by the sheet exchange. -/
def sheetConjugate (A : O55Operator) : O55Operator :=
  sheetExchange * A * sheetExchange

/-- Sheet conjugation reverses every operator multidegree. -/
theorem sheetConjugate_multiweight
    (μ : Axis → ℂ) (A : O55Operator)
    (hA : IsOperatorMultiweight gradingOperator μ A) :
    IsOperatorMultiweight gradingOperator (fun a => -μ a)
      (sheetConjugate A) := by
  intro a
  have hg := gradingOperator_sheetExchange a
  have hA' := hA a
  unfold sheetConjugate
  calc
    gradingOperator a * (sheetExchange * A * sheetExchange) -
        (sheetExchange * A * sheetExchange) * gradingOperator a =
      -sheetExchange *
        (gradingOperator a * A - A * gradingOperator a) *
          sheetExchange := by
            have hg' : sheetExchange * gradingOperator a =
                -(gradingOperator a * sheetExchange) := by
              have := congrArg Neg.neg hg
              simpa using this.symm
            calc
              gradingOperator a * (sheetExchange * (A * sheetExchange)) -
                  sheetExchange * (A * (sheetExchange * gradingOperator a)) =
                  (gradingOperator a * sheetExchange) * (A * sheetExchange) -
                    sheetExchange * (A * (sheetExchange * gradingOperator a)) := by
                      rw [mul_assoc]
              _ = -(sheetExchange * gradingOperator a) * (A * sheetExchange) -
                    sheetExchange * (A * (sheetExchange * gradingOperator a)) := by
                      rw [hg]
              _ = -sheetExchange *
                    ((gradingOperator a * A - A * gradingOperator a) * sheetExchange) := by
                      nth_rewrite 2 [hg']
                      apply LinearMap.ext
                      intro x
                      apply funext
                      intro p
                      simp [Module.End.mul_apply]
                      ring
    _ = -sheetExchange * (μ a • A) * sheetExchange := by rw [hA']
    _ = (-μ a) • (sheetExchange * A * sheetExchange) := by
      ext x
      simp [Module.End.mul_apply]

/-- The standard pairing is invariant under simultaneous sheet exchange. -/
theorem pairing_sheetExchange (post pre : O55State) :
    pairing (sheetExchange post) (sheetExchange pre) =
      pairing post pre := by
  classical
  unfold pairing
  simpa [sheetExchange] using
    (Equiv.sum_comp flipIndexEquiv
      (fun p => star (post p) * pre p))

/-- Exchange both boundary vectors. -/
def exchangeBoundary (B : O55BoundaryPair) : O55BoundaryPair where
  pre := sheetExchange B.pre
  post := sheetExchange B.post
  overlap_ne := by
    rw [pairing_sheetExchange]
    exact B.overlap_ne

/-- Conjugating the probe and exchanging both boundaries leaves the normalized
matrix coefficient invariant. -/
theorem weakValue_exchangeBoundary
    (B : O55BoundaryPair) (A : O55Operator) :
    weakValue (exchangeBoundary B) (sheetConjugate A) =
      weakValue B A := by
  unfold weakValue numerator overlap exchangeBoundary sheetConjugate
  have hact :
      (sheetExchange * A * sheetExchange) (sheetExchange B.pre) =
        sheetExchange (A B.pre) := by
    change sheetExchange (A (sheetExchange (sheetExchange B.pre))) =
      sheetExchange (A B.pre)
    have hs : sheetExchange (sheetExchange B.pre) = B.pre := by
      ext p
      simp [sheetExchange_apply, flipIndex]
    rw [hs]
  rw [hact, pairing_sheetExchange, pairing_sheetExchange]

/-- The complete two-boundary `O(5,5)` multigrading packet. -/
theorem o55_two_boundary_multigraded_packet
    (B : O55BoundaryPair) (α β : Axis → ℂ)
    (hpre : IsRightWeight gradingOperator α B.pre)
    (hpost : IsLeftWeight gradingOperator β B.post)
    (r : Root) :
    IsOperatorMultiweight gradingOperator
        (fun a => (r.multiDegree a : ℂ)) (rootOperator r) ∧
      (rootReadout B r ≠ 0 →
        (fun a => (r.multiDegree a : ℂ)) =
          boundaryWeightDifference α β) ∧
      weakValue (exchangeBoundary B)
          (sheetConjugate (rootOperator r)) = rootReadout B r := by
  exact ⟨rootOperator_multiweight r,
    fun h => rootReadout_ne_zero_implies_multidegree
      B α β hpre hpost r h,
    weakValue_exchangeBoundary B (rootOperator r)⟩

end InfoGeometry.Orthogonal.O55TwoBoundary

end noncomputable section
