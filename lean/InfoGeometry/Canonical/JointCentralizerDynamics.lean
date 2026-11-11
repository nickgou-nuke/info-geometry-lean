/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedCentralizer
import InfoGeometry.Lie.ConcreteSplitCartan
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# The actual Cartan exponential and its common commutant

The existing `splitCartanHom` is evaluated for the partially supported Cartan
element of a dual-seed pair. Its adjoint action scales the two seeds, fixes
their common commutant pointwise, and preserves the constructed centralizer
projection. All actions remain in the full ambient real Banach algebra.

The residual idempotent is retained: the seed equations do not imply `H²=1`.
These are real exponential similarities, with no assertion of Hilbert-star
preservation, modular time, a chosen state, or an Apollonian realization.
-/

noncomputable section

namespace InfoGeometry.Canonical.JointCentralizerDynamics

open InfoGeometry.Core.DualSeedPeirce InfoGeometry.Core.PeirceRotor
open InfoGeometry.Core.PeirceBilateralAction InfoGeometry.Lie.ConcreteSplitCartan

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
variable {d b : A}

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

/-- The native exponential includes the identity on the residual corner. -/
theorem exp_phasePolarization (h : IsDualSeedPair d b) (t : ℝ) :
    NormedSpace.exp (t • phasePolarization d b) =
      completedBlock d b (Real.exp t) 0 0 (Real.exp (-t)) := by
  have hp : phasePolarization d b * polePlus d b = polePlus d b := by
    change (polePlus d b - poleMinus d b) * polePlus d b = _
    rw [sub_mul, h.pp, h.qp, sub_zero]
  have hq : phasePolarization d b * poleMinus d b = -poleMinus d b := by
    change (polePlus d b - poleMinus d b) * poleMinus d b = _
    rw [sub_mul, h.pq, h.qq, zero_sub]
  have hr : phasePolarization d b * zeroModeSupport d b = 0 := by
    change (polePlus d b - poleMinus d b) * (1 - polePlus d b - poleMinus d b) = 0
    simp only [mul_sub, sub_mul, mul_one, h.pp, h.pq, h.qp, h.qq]
    abel
  have exp_scalar (s : ℝ) :
      NormedSpace.exp (s • (1 : A)) = Real.exp s • (1 : A) := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) s).symm
  have hep : NormedSpace.exp (t • phasePolarization d b) * polePlus d b =
      Real.exp t • polePlus d b := by
    have hs : SemiconjBy (polePlus d b) (t • (1 : A)) (t • phasePolarization d b) := by
      change polePlus d b * (t • (1 : A)) = (t • phasePolarization d b) * polePlus d b
      rw [mul_smul_comm, smul_mul_assoc, mul_one, hp]
    simpa only [SemiconjBy, exp_scalar, mul_smul_comm, mul_one] using hs.exp_right.symm
  have heq : NormedSpace.exp (t • phasePolarization d b) * poleMinus d b =
      Real.exp (-t) • poleMinus d b := by
    have hs : SemiconjBy (poleMinus d b) ((-t) • (1 : A)) (t • phasePolarization d b) := by
      change poleMinus d b * ((-t) • (1 : A)) = (t • phasePolarization d b) * poleMinus d b
      rw [mul_smul_comm, smul_mul_assoc, mul_one, hq, neg_smul, smul_neg]
    simpa only [SemiconjBy, exp_scalar, mul_smul_comm, mul_one] using hs.exp_right.symm
  have her : NormedSpace.exp (t • phasePolarization d b) * zeroModeSupport d b =
      zeroModeSupport d b := by
    have hs : SemiconjBy (zeroModeSupport d b) (0 : A) (t • phasePolarization d b) := by
      change zeroModeSupport d b * 0 = (t • phasePolarization d b) * zeroModeSupport d b
      rw [mul_zero, smul_mul_assoc, hr, smul_zero]
    simpa only [SemiconjBy, NormedSpace.exp_zero, mul_one] using hs.exp_right.symm
  have hsum : polePlus d b + poleMinus d b + zeroModeSupport d b = 1 := by
    change polePlus d b + poleMinus d b + (1 - polePlus d b - poleMinus d b) = 1
    abel
  calc
    _ = NormedSpace.exp (t • phasePolarization d b) *
        (polePlus d b + poleMinus d b + zeroModeSupport d b) := by rw [hsum, mul_one]
    _ = _ := by
      rw [mul_add, mul_add, hep, heq, her]
      simp only [completedBlock, peirceBlock, zero_smul, add_zero]
      abel

/-- The analytic group unit is the existing algebraically constructed diagonal unit. -/
theorem splitCartanHom_eq_diagonalUnit (h : IsDualSeedPair d b) (t : ℝ) :
    splitCartanHom (phasePolarization d b) (Multiplicative.ofAdd t) =
      diagonalUnit h (l := Real.exp t) (m := Real.exp (-t))
        (by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]) := by
  apply Units.ext
  exact exp_phasePolarization h t

/-- Exact source scaling by the actual exponential, on arbitrary partial support. -/
theorem splitCartan_conjugates_seed (h : IsDualSeedPair d b) (t : ℝ) :
    let u := splitCartanHom (phasePolarization d b) (Multiplicative.ofAdd t)
    (u : A) * d * (↑(u⁻¹) : A) = Real.exp (2 * t) • d := by
  have hr := harmonic_block (R := ℝ) h 0 1 0 0
  simp only [peirceBlock, zero_smul, one_smul, zero_add, add_zero] at hr
  dsimp only
  rw [splitCartanHom_eq_diagonalUnit h t]
  change completedBlock d b (Real.exp t) 0 0 (Real.exp (-t)) * d *
    completedBlock d b (Real.exp (-t)) 0 0 (Real.exp t) = _
  simp only [completedBlock, peirceBlock, zero_smul, add_zero, add_mul,
    smul_mul_assoc, h.pd, h.qd, hr.1, smul_zero, zero_add,
    mul_add, mul_smul_comm, hr.2, h.dp, h.dq, smul_smul]
  rw [← Real.exp_add, ← two_mul]

/-- The partner carries the opposite exponential weight. -/
theorem splitCartan_conjugates_partner (h : IsDualSeedPair d b) (t : ℝ) :
    let u := splitCartanHom (phasePolarization d b) (Multiplicative.ofAdd t)
    (u : A) * b * (↑(u⁻¹) : A) = Real.exp (-(2 * t)) • b := by
  have hr := harmonic_block (R := ℝ) h 0 0 1 0
  simp only [peirceBlock, zero_smul, one_smul, zero_add, add_zero] at hr
  dsimp only
  rw [splitCartanHom_eq_diagonalUnit h t]
  change completedBlock d b (Real.exp t) 0 0 (Real.exp (-t)) * b *
    completedBlock d b (Real.exp (-t)) 0 0 (Real.exp t) = _
  simp only [completedBlock, peirceBlock, zero_smul, add_zero, add_mul,
    smul_mul_assoc, h.pb, h.qb, hr.1, smul_zero, zero_add,
    mul_add, mul_smul_comm, hr.2, h.bp, h.bq, smul_smul]
  rw [← Real.exp_add, ← neg_add, ← two_mul]

/-- Every common-commutant element is fixed pointwise; seed equations are unnecessary. -/
theorem splitCartan_fixes_jointCentralizer (d b a : A)
    (ha : a ∈ Subalgebra.centralizer ℝ ({d, b} : Set A)) (t : ℝ) :
    let u := splitCartanHom (phasePolarization d b) (Multiplicative.ofAdd t)
    (u : A) * a * (↑(u⁻¹) : A) = a := by
  have hc := (Subalgebra.mem_centralizer_iff ℝ).mp ha
  have hH := commute_phasePolarization_of_commute
    (hc d (Set.mem_insert d {b})).symm
    (hc b (Set.mem_insert_of_mem d (Set.mem_singleton b))).symm
  apply Units.commute_iff_mul_inv_cancel.mp
  exact ((hH.smul_right t).exp_right).symm

/-- The constructed projection is invariant under the Cartan similarity.
Naturality is essential: the Cartan unit does not itself centralize the seeds. -/
theorem centralizerProjection_splitCartan (h : IsDualSeedPair d b) (a : A) (t : ℝ) :
    let u := splitCartanHom (phasePolarization d b) (Multiplicative.ofAdd t)
    centralizerProjection ℝ d b ((u : A) * a * (↑(u⁻¹) : A)) =
      centralizerProjection ℝ d b a := by
  let u := splitCartanHom (phasePolarization d b) (Multiplicative.ofAdd t)
  let f := MulSemiringAction.toAlgEquiv ℝ A (ConjAct.toConjAct u)
  have hf (x : A) : f x = (u : A) * x * (↑(u⁻¹) : A) := by
    exact ConjAct.units_smul_def _ _
  have hd : f d = Real.exp (2 * t) • d := by
    rw [hf]
    exact splitCartan_conjugates_seed h t
  have hb : f b = Real.exp (-(2 * t)) • b := by
    rw [hf]
    exact splitCartan_conjugates_partner h t
  have hn := centralizerProjection_map f.toAlgHom d b a
  change f (centralizerProjection ℝ d b a) =
    centralizerProjection ℝ (f d) (f b) (f a) at hn
  rw [hd, hb, centralizerProjection_rescale d b (f a)
    (Real.exp (2 * t)) (Real.exp (-(2 * t)))
      (by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero])] at hn
  rw [hf, splitCartan_fixes_jointCentralizer d b _ (h.centralizerProjection_mem a) t] at hn
  exact (congrArg (centralizerProjection ℝ d b) (hf a)).symm.trans hn.symm

end InfoGeometry.Canonical.JointCentralizerDynamics
