import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.CantorKMSState
import InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

/-!
# Fixed-depth matrix units for the Bernoulli Cuntz tree

The recursive word calculus uses `List Bool`.  Finite UHF stages use the
canonical carrier `BitWord n := Fin n → Bool`.  This bridge packages the
already-proved list-word matrix-unit relations on that finite carrier.  It
does not yet assert an algebra isomorphism with `Matrix (BitWord n) ...`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorKMSState
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCylinderMultiplicationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

def bitWordUnit (n : ℕ) (u v : BitWord n) :
    InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.BoundedL2Operator :=
  operatorMatrixUnit (List.ofFn u) (List.ofFn v)

/-! The finite matrix carrier indexed by the same `BitWord n` type as the
operator units.  This is deliberately a finite algebraic trace packet; it
does not assert a norm completion or an infinite UHF state. -/

abbrev BitWordMatrixStage (n : ℕ) :=
  Matrix (BitWord n) (BitWord n) ℂ

def bitWordMatrixTraceFunctional (n : ℕ) :
    BitWordMatrixStage n →ₗ[ℂ] ℂ :=
  (1 / (Fintype.card (BitWord n) : ℂ)) •
    Matrix.traceLinearMap (BitWord n) ℂ ℂ

@[simp] theorem bitWordMatrixTraceFunctional_apply
    (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordMatrixTraceFunctional n A =
      (1 / (Fintype.card (BitWord n) : ℂ)) * Matrix.trace A :=
  rfl

theorem bitWordMatrixTraceFunctional_single
    (n : ℕ) (u v : BitWord n) :
    bitWordMatrixTraceFunctional n (Matrix.single u v 1) =
      if u = v then (1 / (Fintype.card (BitWord n) : ℂ)) else 0 := by
  rw [bitWordMatrixTraceFunctional_apply]
  by_cases huv : u = v
  · subst v
    simp [Matrix.trace, Matrix.single]
  · simp [Matrix.trace, Matrix.single, huv, Ne.symm huv]

theorem bitWordMatrixTraceFunctional_single_eq_gaugeState
    (n : ℕ) (u v : BitWord n) :
    bitWordMatrixTraceFunctional n (Matrix.single u v 1) =
      canonicalGaugeState (List.ofFn u) (List.ofFn v) := by
  rw [bitWordMatrixTraceFunctional_single]
  rw [canonicalGaugeState_word]
  by_cases huv : u = v
  · subst v
    have hcard : Fintype.card (BitWord n) = 2 ^ n := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    simp [hcard, List.length_ofFn]
  · have hlist : List.ofFn u ≠ List.ofFn v := by
      intro h
      exact huv (List.ofFn_injective h)
    simp [huv, hlist]

theorem bitWordUnit_star (n : ℕ) (u v : BitWord n) :
    star (bitWordUnit n u v) = bitWordUnit n v u := by
  exact operatorMatrixUnit_star (List.ofFn u) (List.ofFn v)

theorem bitWordUnit_mul (n : ℕ) (u v x y : BitWord n) :
    (bitWordUnit n u v).comp (bitWordUnit n x y) =
      if v = x then bitWordUnit n u y else 0 := by
  by_cases hvx : v = x
  · subst x
    simpa [bitWordUnit] using
      (operatorMatrixUnit_mul
        (u := List.ofFn u) (v := List.ofFn v)
        (x := List.ofFn v) (y := List.ofFn y)
        (by simp only [List.length_ofFn]))
  · have hlist : List.ofFn v ≠ List.ofFn x := by
      intro h
      apply hvx
      exact List.ofFn_injective h
    simpa [bitWordUnit, hvx, hlist] using
      (operatorMatrixUnit_mul
        (u := List.ofFn u) (v := List.ofFn v)
        (x := List.ofFn x) (y := List.ofFn y)
        (by simp only [List.length_ofFn]))

theorem bitWordUnit_diag_eq_projection (n : ℕ) (u : BitWord n) :
    bitWordUnit n u u = operatorCylinderProjection (List.ofFn u) :=
  operatorMatrixUnit_diag_eq_projection (List.ofFn u)

theorem operatorMatrixUnit_refinement (u v : List Bool) :
    operatorMatrixUnit (u ++ [false]) (v ++ [false]) +
        operatorMatrixUnit (u ++ [true]) (v ++ [true]) =
      operatorMatrixUnit u v := by
  unfold operatorMatrixUnit
  rw [operatorWord_append, operatorWord_append,
    operatorWordDag_append, operatorWordDag_append]
  dsimp [operatorWord, operatorWordDag]
  have hpart :=
    InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.cantorL2CuntzFamily.partition
  rw [Fintype.sum_bool] at hpart
  have hpart' :
      (branchOperator false).comp (star (branchOperator false)) +
        (branchOperator true).comp (star (branchOperator true)) =
      ContinuousLinearMap.id ℂ L2Boundary := by
    change
      (InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily.S
          InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.cantorL2CuntzFamily false) *
          (InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily.S
            InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.cantorL2CuntzFamily false)† +
        (InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily.S
          InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.cantorL2CuntzFamily true) *
          (InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily.S
            InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.cantorL2CuntzFamily true)† = 1
    rw [add_comm]
    exact hpart
  calc
    (operatorWord u).comp ((branchOperator false).comp
      ((star (branchOperator false)).comp (operatorWordDag v))) +
    (operatorWord u).comp ((branchOperator true).comp
      ((star (branchOperator true)).comp (operatorWordDag v)))
        = (operatorWord u).comp
            (((branchOperator false).comp (star (branchOperator false)) +
              (branchOperator true).comp (star (branchOperator true))).comp
              (operatorWordDag v)) := by
          simp only [ContinuousLinearMap.comp_assoc,
            ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    _ = (operatorWord u).comp
          ((ContinuousLinearMap.id ℂ L2Boundary).comp (operatorWordDag v)) := by
          rw [hpart']
    _ = (operatorWord u).comp (operatorWordDag v) := by
          simp

/--
The diagonal fixed-depth matrix unit has the same finite trace readout as
the corresponding Bernoulli cylinder.  This is only a finite/core identity:
it does not extend `DiagTrace` to the completed concrete C*-algebra.
-/
theorem bitWordUnit_diag_eq_diagTrace_cylinder (n : ℕ) (u : BitWord n) :
    canonicalGaugeState (List.ofFn u) (List.ofFn u) =
      DiagTrace n (cylinderIndicator n u) := by
  rw [canonicalGaugeState_proj, DiagTrace_cylinderIndicator]
  simp [List.length_ofFn, inv_pow]

theorem bitWord_card (n : ℕ) :
    Fintype.card (BitWord n) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-! The gauge word kernel is normalized on the same finite level. -/

theorem bitWordUnit_level_gauge_sum_one (n : ℕ) :
    ∑ w : BitWord n,
      canonicalGaugeState (List.ofFn w) (List.ofFn w) = 1 := by
  classical
  simp_rw [canonicalGaugeState_proj, List.length_ofFn]
  simp [Finset.sum_const]

private theorem list_ofFn_extendBitWord (n : ℕ) (w : BitWord n) (b : Bool) :
    List.ofFn (extendBitWord n w b) = List.ofFn w ++ [b] := by
  have hb : [b] = List.ofFn (fun _ : Fin 1 => b) := by simp
  rw [hb, ← List.ofFn_fin_append w (fun _ : Fin 1 => b)]
  apply congrArg List.ofFn
  funext i
  by_cases hi : i.1 < n
  · let j : Fin n := ⟨i.1, hi⟩
    have hij : i = Fin.castLE (by omega : n ≤ n + 1) j := by
      ext
      rfl
    have hleft : extendBitWord n w b i = w j := by
      simp [extendBitWord, bitWordEquiv, hi, j]
    have hright : Fin.append w (fun _ : Fin 1 => b) i = w j := by
      rw [hij]
      exact Fin.append_left' w (fun _ : Fin 1 => b) j
    exact hleft.trans hright.symm
  · have hiN : i.1 = n := by omega
    have hij : i = Fin.natAdd n (0 : Fin 1) := by
      ext
      exact hiN
    have hleft : extendBitWord n w b i = b := by
      simp [extendBitWord, bitWordEquiv, hiN]
    have hright : Fin.append w (fun _ : Fin 1 => b) i = b := by
      rw [hij]
      simp only [Fin.append_right]
    exact hleft.trans hright.symm

theorem bitWordUnit_refinement (n : ℕ) (u v : BitWord n) :
    bitWordUnit n u v =
      bitWordUnit (n + 1) (extendBitWord n u false) (extendBitWord n v false) +
      bitWordUnit (n + 1) (extendBitWord n u true) (extendBitWord n v true) := by
  unfold bitWordUnit
  rw [list_ofFn_extendBitWord n u false,
    list_ofFn_extendBitWord n v false,
    list_ofFn_extendBitWord n u true,
    list_ofFn_extendBitWord n v true]
  exact (operatorMatrixUnit_refinement (List.ofFn u) (List.ofFn v)).symm

theorem bitWord_level_projection_sum (n : ℕ) :
    (∑ w : BitWord n,
      operatorCylinderProjection (List.ofFn w)) =
      ContinuousLinearMap.id ℂ L2Boundary := by
  induction n with
  | zero =>
      classical
      have h_univ : (Finset.univ : Finset (BitWord 0)) = {fun _ => false} := by
        ext x
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        ext i
        exact i.elim0
      rw [h_univ, Finset.sum_singleton]
      dsimp [operatorCylinderProjection, List.ofFn, operatorWord, operatorWordDag]
      rfl
  | succ n ih =>
      classical
      have h_equiv := (bitWordEquiv n).symm.sum_comp
        (fun w : BitWord (n + 1) =>
          operatorCylinderProjection (List.ofFn w))
      rw [← h_equiv]
      rw [← Finset.univ_product_univ]
      rw [Finset.sum_product]
      have h_inner : ∀ w : BitWord n,
          (∑ b : Bool, operatorCylinderProjection (List.ofFn ((bitWordEquiv n).symm (w, b)))) =
            operatorCylinderProjection (List.ofFn w) := by
        intro w
        rw [Fintype.sum_bool]
        change operatorCylinderProjection (List.ofFn (extendBitWord n w true)) +
            operatorCylinderProjection (List.ofFn (extendBitWord n w false)) =
          operatorCylinderProjection (List.ofFn w)
        rw [list_ofFn_extendBitWord n w true, list_ofFn_extendBitWord n w false, add_comm]
        exact operatorCylinderProjection_children_sum (List.ofFn w)
      simp_rw [h_inner]
      exact ih

/-! The diagonal matrix units resolve the identity at every finite level. -/

theorem bitWordUnit_level_sum_one (n : ℕ) :
    (∑ w : BitWord n, bitWordUnit n w w) =
      ContinuousLinearMap.id ℂ L2Boundary := by
  calc
    (∑ w : BitWord n, bitWordUnit n w w) =
        ∑ w : BitWord n, operatorCylinderProjection (List.ofFn w) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact bitWordUnit_diag_eq_projection n w
    _ = ContinuousLinearMap.id ℂ L2Boundary := bitWord_level_projection_sum n

end InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
