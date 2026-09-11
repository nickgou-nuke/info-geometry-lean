import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

/-!
# Finite matrix-unit representation on the Bernoulli boundary

This owner packages the fixed-depth matrix coefficients as a linear readout
into the concrete bounded operators.  It proves the matrix-unit and identity
readouts without claiming an infinite C*-completion.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge

open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open MeasureTheory

def bitWordMatrixRepresentationFun (n : ℕ) (A : BitWordMatrixStage n) :
    BoundedL2Operator :=
  ∑ u : BitWord n, ∑ v : BitWord n,
    A u v • bitWordUnit n u v

def bitWordMatrixLinearRepresentation (n : ℕ) :
    BitWordMatrixStage n →ₗ[ℂ] BoundedL2Operator where
  toFun := bitWordMatrixRepresentationFun n
  map_add' A B := by
    classical
    simp [bitWordMatrixRepresentationFun, add_smul,
      Finset.sum_add_distrib]
  map_smul' c A := by
    classical
    simp [bitWordMatrixRepresentationFun, mul_smul, Finset.smul_sum]

@[simp] theorem bitWordMatrixLinearRepresentation_single
    (n : ℕ) (u v : BitWord n) :
    bitWordMatrixLinearRepresentation n (Matrix.single u v 1) =
      bitWordUnit n u v := by
  classical
  change bitWordMatrixRepresentationFun n (Matrix.single u v 1) = bitWordUnit n u v
  unfold bitWordMatrixRepresentationFun
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single v]
    · rw [Matrix.single_apply]
      simp
    · intro j _ hjv
      have : (Matrix.single u v (1 : ℂ)) u j = 0 := by
        rw [Matrix.single_apply]
        have h_cond : ¬(u = u ∧ v = j) := by
          intro ⟨_, hvj⟩
          exact hjv hvj.symm
        rw [if_neg h_cond]
      rw [this, zero_smul]
    · simp
  · intro i _ hiu
    have : (∑ j : BitWord n, (Matrix.single u v (1 : ℂ)) i j • bitWordUnit n i j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hzero : (Matrix.single u v (1 : ℂ)) i j = 0 := by
        rw [Matrix.single_apply]
        have h_cond : ¬(u = i ∧ v = j) := by
          intro ⟨hui, _⟩
          exact hiu hui.symm
        rw [if_neg h_cond]
      rw [hzero, zero_smul]
    exact this
  · simp

@[simp] theorem bitWordMatrixLinearRepresentation_single_smul
    (n : ℕ) (u v : BitWord n) (c : ℂ) :
    bitWordMatrixLinearRepresentation n (Matrix.single u v c) =
      c • bitWordUnit n u v := by
  classical
  change bitWordMatrixRepresentationFun n (Matrix.single u v c) =
    c • bitWordUnit n u v
  unfold bitWordMatrixRepresentationFun
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single v]
    · rw [Matrix.single_apply]
      simp
    · intro j _ hjv
      have : (Matrix.single u v c) u j = 0 := by
        rw [Matrix.single_apply]
        have h_cond : ¬(u = u ∧ v = j) := by
          intro ⟨_, hvj⟩
          exact hjv hvj.symm
        rw [if_neg h_cond]
      rw [this, zero_smul]
    · simp
  · intro i _ hiu
    have : (∑ j : BitWord n, (Matrix.single u v c) i j • bitWordUnit n i j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hzero : (Matrix.single u v c) i j = 0 := by
        rw [Matrix.single_apply]
        have h_cond : ¬(u = i ∧ v = j) := by
          intro ⟨hui, _⟩
          exact hiu hui.symm
        rw [if_neg h_cond]
      rw [hzero, zero_smul]
    exact this
  · simp

theorem bitWordMatrixLinearRepresentation_diagonal_sum
    (n : ℕ) :
    bitWordMatrixLinearRepresentation n (1 : BitWordMatrixStage n) =
      ContinuousLinearMap.id ℂ L2Boundary := by
  classical
  change bitWordMatrixRepresentationFun n (1 : BitWordMatrixStage n) =
    ContinuousLinearMap.id ℂ L2Boundary
  unfold bitWordMatrixRepresentationFun
  have h_diag : (∑ u : BitWord n, ∑ v : BitWord n, (1 : BitWordMatrixStage n) u v • bitWordUnit n u v) =
      ∑ u : BitWord n, bitWordUnit n u u := by
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_eq_single u]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro v _ hvu
      rw [Matrix.one_apply_ne (Ne.symm hvu), zero_smul]
    · simp
  rw [h_diag]
  exact bitWordUnit_level_sum_one n

theorem bitWordMatrixLinearRepresentation_star_single
    (n : ℕ) (u v : BitWord n) :
    star (bitWordMatrixLinearRepresentation n (Matrix.single u v 1)) =
      bitWordMatrixLinearRepresentation n (Matrix.single v u 1) := by
  rw [bitWordMatrixLinearRepresentation_single,
    bitWordMatrixLinearRepresentation_single]
  exact bitWordUnit_star n u v

/-! The finite commuting square readout.  This is a matrix-stage statement:
it identifies the normalized matrix trace with the diagonal gauge weights of
the represented matrix units, without asserting a state on the completed
infinite C*-algebra. -/

def bitWordMatrixGaugeReadout (n : ℕ) (A : BitWordMatrixStage n) : ℂ :=
  ∑ u : BitWord n,
    A u u * canonicalGaugeState (List.ofFn u) (List.ofFn u)

theorem bitWordMatrixGaugeReadout_eq_trace
    (n : ℕ) (A : BitWordMatrixStage n) :
    bitWordMatrixGaugeReadout n A =
      bitWordMatrixTraceFunctional n A := by
  classical
  unfold bitWordMatrixGaugeReadout
  rw [bitWordMatrixTraceFunctional_apply]
  simp_rw [canonicalGaugeState_proj, List.length_ofFn]
  rw [bitWord_card]
  have hpow : (1 / 2 : ℂ) ^ n = 1 / (2 ^ n : ℂ) := by
    simpa only [one_div] using (inv_pow (2 : ℂ) n)
  rw [← Finset.sum_mul, hpow]
  simp only [Matrix.trace, Matrix.diag]
  push_cast
  ring

theorem bitWordMatrixGaugeReadout_single
    (n : ℕ) (u v : BitWord n) :
    bitWordMatrixGaugeReadout n (Matrix.single u v 1) =
      canonicalGaugeState (List.ofFn u) (List.ofFn v) := by
  rw [bitWordMatrixGaugeReadout_eq_trace]
  exact bitWordMatrixTraceFunctional_single_eq_gaugeState n u v

/-! The finite UHF readout is cyclic because it is the normalized matrix
trace. This is the concrete equal-depth KMS/trace compatibility theorem; it
does not assert an infinite C*-state or an unrestricted word-level modular
action. -/
theorem bitWordMatrixGaugeReadout_mul_comm
    (n : ℕ) (A B : BitWordMatrixStage n) :
    bitWordMatrixGaugeReadout n (A * B) =
      bitWordMatrixGaugeReadout n (B * A) := by
  rw [bitWordMatrixGaugeReadout_eq_trace,
    bitWordMatrixGaugeReadout_eq_trace]
  change (1 / (Fintype.card (BitWord n) : ℂ)) * Matrix.trace (A * B) =
    (1 / (Fintype.card (BitWord n) : ℂ)) * Matrix.trace (B * A)
  congr 1
  exact Matrix.trace_mul_comm A B

theorem bitWordMatrixGaugeReadout_unit
    (n : ℕ) :
    bitWordMatrixGaugeReadout n (1 : BitWordMatrixStage n) = 1 := by
  rw [bitWordMatrixGaugeReadout_eq_trace]
  simp [bitWordMatrixTraceFunctional_apply]

end InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
