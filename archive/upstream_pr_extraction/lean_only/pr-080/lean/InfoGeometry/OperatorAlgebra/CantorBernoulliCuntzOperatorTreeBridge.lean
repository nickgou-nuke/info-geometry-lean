import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge

open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization

abbrev BoundedL2Operator :=
  InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.BoundedL2Operator

def branchOperator (b : Bool) : BoundedL2Operator :=
  match b with
  | false => vLeft
  | true => vRight

def operatorWord : List Bool → BoundedL2Operator
  | [] => ContinuousLinearMap.id ℂ L2Boundary
  | b :: w => (branchOperator b).comp (operatorWord w)

def operatorWordDag : List Bool → BoundedL2Operator
  | [] => ContinuousLinearMap.id ℂ L2Boundary
  | b :: w => (operatorWordDag w).comp (star (branchOperator b))

def operatorCylinderProjection (w : List Bool) : BoundedL2Operator :=
  (operatorWord w).comp (operatorWordDag w)

/-! The projection tree has a direct recursive operator-level description.
This is the algebraic precursor of the cylinder-multiplication theorem: a
child projection is obtained by restricting the parent projection to the
corresponding branch.  No measure-theoretic identification is used here. -/

theorem operatorCylinderProjection_cons (b : Bool) (w : List Bool) :
    operatorCylinderProjection (b :: w) =
      (branchOperator b).comp
        ((operatorCylinderProjection w).comp (star (branchOperator b))) := by
  simp [operatorCylinderProjection, operatorWord, operatorWordDag,
    ContinuousLinearMap.comp_assoc]

@[simp] theorem operatorWord_nil :
    operatorWord ([] : List Bool) = ContinuousLinearMap.id ℂ L2Boundary := by
  simp [operatorWord]

@[simp] theorem operatorWordDag_nil :
    operatorWordDag ([] : List Bool) = ContinuousLinearMap.id ℂ L2Boundary := by
  simp [operatorWordDag]

theorem operatorWord_append (u v : List Bool) :
    operatorWord (u ++ v) = (operatorWord u).comp (operatorWord v) := by
  induction u with
  | nil => simp [operatorWord]
  | cons b u ih =>
      simp only [List.cons_append, operatorWord]
      rw [ih]
      ext x
      rfl

theorem operatorWordDag_append (u v : List Bool) :
    operatorWordDag (u ++ v) =
      (operatorWordDag v).comp (operatorWordDag u) := by
  induction u with
  | nil => simp [operatorWordDag]
  | cons b u ih =>
      simp only [List.cons_append, operatorWordDag]
      rw [ih]
      ext x
      rfl

theorem operatorCylinderProjection_append (u v : List Bool) :
    operatorCylinderProjection (u ++ v) =
      (operatorWord u).comp
        ((operatorCylinderProjection v).comp (operatorWordDag u)) := by
  simp [operatorCylinderProjection, operatorWord_append,
    operatorWordDag_append, ContinuousLinearMap.comp_assoc]

@[simp] theorem star_operatorWord (w : List Bool) :
    star (operatorWord w) = operatorWordDag w := by
  induction w with
  | nil => simp [operatorWord, operatorWordDag, ContinuousLinearMap.star_eq_adjoint]
  | cons b w ih =>
      change
        star ((branchOperator b).comp (operatorWord w)) =
          (operatorWordDag w).comp (star (branchOperator b))
      rw [ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_comp]
      simpa [ContinuousLinearMap.star_eq_adjoint] using
        congrArg
          (fun T : BoundedL2Operator =>
            T.comp (star (branchOperator b))) ih

theorem operatorWordDag_eq_star (w : List Bool) :
    operatorWordDag w = star (operatorWord w) := by
  exact (star_operatorWord w).symm

theorem operatorWordDag_comp_operatorWord (w : List Bool) :
    (operatorWordDag w).comp (operatorWord w) =
      ContinuousLinearMap.id ℂ L2Boundary := by
  induction w with
  | nil => simp [operatorWord, operatorWordDag]
  | cons b w ih =>
      apply ContinuousLinearMap.ext
      intro f
      cases b with
      | false =>
          change operatorWordDag w
            (normalizedPrependBitLpAdjoint false
              (normalizedPrependBitLpContinuousLinearMap false
                (operatorWord w f))) = f
          have hself := ContinuousLinearMap.ext_iff.mp
            (normalizedPrependBitLpAdjoint_comp_self false)
            (operatorWord w f)
          have hi := ContinuousLinearMap.ext_iff.mp ih f
          have hself' :
              normalizedPrependBitLpAdjoint false
                  (normalizedPrependBitLpContinuousLinearMap false
                    (operatorWord w f)) = operatorWord w f := by
            simpa using hself
          have hi' : operatorWordDag w (operatorWord w f) = f := by
            simpa using hi
          rw [hself']
          exact hi'
      | true =>
          change operatorWordDag w
            (normalizedPrependBitLpAdjoint true
              (normalizedPrependBitLpContinuousLinearMap true
                (operatorWord w f))) = f
          have hself := ContinuousLinearMap.ext_iff.mp
            (normalizedPrependBitLpAdjoint_comp_self true)
            (operatorWord w f)
          have hi := ContinuousLinearMap.ext_iff.mp ih f
          have hself' :
              normalizedPrependBitLpAdjoint true
                  (normalizedPrependBitLpContinuousLinearMap true
                    (operatorWord w f)) = operatorWord w f := by
            simpa using hself
          have hi' : operatorWordDag w (operatorWord w f) = f := by
            simpa using hi
          rw [hself']
          exact hi'

theorem operatorWordDag_comp_operatorWord_of_length_eq
    {u v : List Bool} (hlen : u.length = v.length) :
    u ≠ v →
      (operatorWordDag u).comp (operatorWord v) = 0 := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => simp
      | cons c v =>
          intro _
          simp at hlen
  | cons b u ih =>
      cases v with
      | nil =>
          intro _
          simp at hlen
      | cons c v =>
          simp only [List.length_cons] at hlen
          have htail : u.length = v.length := by omega
          by_cases hbc : b = c
          · subst c
            intro hne
            have htail_ne : u ≠ v := by
              intro huv
              apply hne
              simp [huv]
            apply ContinuousLinearMap.ext
            intro f
            change operatorWordDag u
              (star (branchOperator b)
                (branchOperator b (operatorWord v f))) = 0
            cases b with
            | false =>
                rw [show star (branchOperator false) =
                    normalizedPrependBitLpAdjoint false by rfl]
                change operatorWordDag u
                  (normalizedPrependBitLpAdjoint false
                    (normalizedPrependBitLpContinuousLinearMap false
                      (operatorWord v f))) = 0
                rw [show normalizedPrependBitLpAdjoint false
                    (normalizedPrependBitLpContinuousLinearMap false
                      (operatorWord v f)) = operatorWord v f by
                  exact ContinuousLinearMap.ext_iff.mp
                    (normalizedPrependBitLpAdjoint_comp_self false)
                    (operatorWord v f)]
                exact ContinuousLinearMap.ext_iff.mp (ih htail htail_ne) f
            | true =>
                rw [show star (branchOperator true) =
                    normalizedPrependBitLpAdjoint true by rfl]
                change operatorWordDag u
                  (normalizedPrependBitLpAdjoint true
                    (normalizedPrependBitLpContinuousLinearMap true
                      (operatorWord v f))) = 0
                rw [show normalizedPrependBitLpAdjoint true
                    (normalizedPrependBitLpContinuousLinearMap true
                      (operatorWord v f)) = operatorWord v f by
                  exact ContinuousLinearMap.ext_iff.mp
                    (normalizedPrependBitLpAdjoint_comp_self true)
                    (operatorWord v f)]
                exact ContinuousLinearMap.ext_iff.mp (ih htail htail_ne) f
          · intro _
            apply ContinuousLinearMap.ext
            intro f
            change operatorWordDag u
              (star (branchOperator b)
                (branchOperator c (operatorWord v f))) = 0
            cases b <;> cases c
            · contradiction
            · change operatorWordDag u
                (normalizedPrependBitLpAdjoint false
                  (normalizedPrependBitLpContinuousLinearMap true
                    (operatorWord v f))) = 0
              have hzero := normalizedPrependBitLpAdjoint_comp_cross_eq_zero
                (b := false) (c := true) (by decide)
              have hzero' :
                  normalizedPrependBitLpAdjoint false
                    (normalizedPrependBitLpContinuousLinearMap true
                      (operatorWord v f)) = 0 := by
                simpa using ContinuousLinearMap.ext_iff.mp hzero (operatorWord v f)
              rw [hzero']
              simp
            · change operatorWordDag u
                (normalizedPrependBitLpAdjoint true
                  (normalizedPrependBitLpContinuousLinearMap false
                    (operatorWord v f))) = 0
              have hzero := normalizedPrependBitLpAdjoint_comp_cross_eq_zero
                (b := true) (c := false) (by decide)
              have hzero' :
                  normalizedPrependBitLpAdjoint true
                    (normalizedPrependBitLpContinuousLinearMap false
                      (operatorWord v f)) = 0 := by
                simpa using ContinuousLinearMap.ext_iff.mp hzero (operatorWord v f)
              rw [hzero']
              simp
            · contradiction

theorem operatorCylinderProjection_comp_of_equal_length_ne
    {u v : List Bool} (hlen : u.length = v.length) (hne : u ≠ v) :
    (operatorCylinderProjection u).comp (operatorCylinderProjection v) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  change operatorWord u
    (operatorWordDag u
      (operatorWord v (operatorWordDag v f))) = 0
  have horth := operatorWordDag_comp_operatorWord_of_length_eq hlen hne
  have horth' : operatorWordDag u (operatorWord v (operatorWordDag v f)) = 0 := by
    simpa using ContinuousLinearMap.ext_iff.mp horth (operatorWordDag v f)
  rw [horth']
  simp

theorem operatorCylinderProjection_idempotent (w : List Bool) :
    (operatorCylinderProjection w).comp (operatorCylinderProjection w) =
      operatorCylinderProjection w := by
  apply ContinuousLinearMap.ext
  intro f
  change
    operatorWord w
        (operatorWordDag w
          (operatorWord w (operatorWordDag w f))) =
      operatorWord w (operatorWordDag w f)
  have h := ContinuousLinearMap.ext_iff.mp
    (operatorWordDag_comp_operatorWord w) (operatorWordDag w f)
  have h' : operatorWordDag w
      (operatorWord w (operatorWordDag w f)) = operatorWordDag w f := by
    simpa using h
  rw [h']

theorem operatorCylinderProjection_selfAdjoint (w : List Bool) :
    star (operatorCylinderProjection w) = operatorCylinderProjection w := by
  unfold operatorCylinderProjection
  change star ((operatorWord w) * (operatorWordDag w)) = (operatorWord w) * (operatorWordDag w)
  rw [star_mul]
  rw [operatorWordDag_eq_star, star_star, star_operatorWord]

theorem operatorCylinderProjection_children_sum (w : List Bool) :
    operatorCylinderProjection (w ++ [false]) +
        operatorCylinderProjection (w ++ [true]) =
      operatorCylinderProjection w := by
  unfold operatorCylinderProjection
  rw [operatorWord_append, operatorWord_append,
    operatorWordDag_append, operatorWordDag_append]
  dsimp [operatorWord, operatorWordDag]
  have hpart := cantorL2CuntzFamily.partition
  rw [Fintype.sum_bool] at hpart
  have hpart' :
      (branchOperator false).comp (star (branchOperator false)) +
        (branchOperator true).comp (star (branchOperator true)) =
      ContinuousLinearMap.id ℂ L2Boundary := by
    change
      (InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily.S
          cantorL2CuntzFamily false) *
          (InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily.S
            cantorL2CuntzFamily false)† +
        (InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily.S
          cantorL2CuntzFamily true) *
          (InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily.S
            cantorL2CuntzFamily true)† = 1
    rw [add_comm]
    exact hpart
  calc
    (operatorWord w).comp ((branchOperator false).comp
      ((star (branchOperator false)).comp (operatorWordDag w))) +
    (operatorWord w).comp ((branchOperator true).comp
      ((star (branchOperator true)).comp (operatorWordDag w)))
      = (operatorWord w).comp
          (((branchOperator false).comp (star (branchOperator false)) +
            (branchOperator true).comp (star (branchOperator true))).comp
            (operatorWordDag w)) := by
        simp only [ContinuousLinearMap.comp_assoc,
          ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    _ = (operatorWord w).comp ((ContinuousLinearMap.id ℂ L2Boundary).comp (operatorWordDag w)) := by
        rw [hpart']
    _ = (operatorWord w).comp (operatorWordDag w) := by
        simp

@[simp] theorem operatorCylinderProjection_singleton (b : Bool) :
    operatorCylinderProjection [b] =
      (normalizedPrependBitLpContinuousLinearMap b).comp
        (normalizedPrependBitLpAdjoint b) := by
  cases b <;> rfl

/-! Fixed-depth matrix-unit packet.  The finite indexing by `BitWord n` is
kept downstream; these relations are valid for arbitrary list words of a
common length and are the exact algebraic input for that packaging. -/

def operatorMatrixUnit (u v : List Bool) : BoundedL2Operator :=
  (operatorWord u).comp (operatorWordDag v)

theorem operatorMatrixUnit_star (u v : List Bool) :
    star (operatorMatrixUnit u v) = operatorMatrixUnit v u := by
  simp [operatorMatrixUnit, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_comp, operatorWordDag_eq_star]

theorem operatorMatrixUnit_diag_eq_projection (u : List Bool) :
    operatorMatrixUnit u u = operatorCylinderProjection u :=
  rfl

theorem operatorMatrixUnit_mul
    {u v x y : List Bool}
    (hlen : v.length = x.length) :
    (operatorMatrixUnit u v).comp (operatorMatrixUnit x y) =
      if v = x then operatorMatrixUnit u y else 0 := by
  apply ContinuousLinearMap.ext
  intro f
  unfold operatorMatrixUnit
  change operatorWord u
      (operatorWordDag v (operatorWord x (operatorWordDag y f))) = _
  by_cases hvx : v = x
  · subst x
    have hself := ContinuousLinearMap.ext_iff.mp
      (operatorWordDag_comp_operatorWord v) (operatorWordDag y f)
    have hself' :
        operatorWordDag v (operatorWord v (operatorWordDag y f)) =
          operatorWordDag y f := by
      simpa using hself
    rw [hself']
    simp
  · have hzero := operatorWordDag_comp_operatorWord_of_length_eq hlen hvx
    have hzero' := ContinuousLinearMap.ext_iff.mp hzero (operatorWordDag y f)
    have hzero'' :
        operatorWordDag v (operatorWord x (operatorWordDag y f)) = 0 := by
      simpa using hzero'
    rw [hzero'']
    simp [hvx]

end InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
