import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Real doubled Krein mirror

This owner records the real-linear part of a doubled Hestenes--Krein or
Nambu--Gorkov carrier.  The mirror is a linear involution; no conjugation or
antilinearity is built into the data.  Krein involution, mirror conjugation,
and order-reversing Clifford operations are deliberately separate notions.
-/

namespace InfoGeometry.Canonical

structure DoubledHestenesKreinData (V : Type*)
    [AddCommGroup V] [Module ℝ V] where
  eta : V →ₗ[ℝ] V
  mirror : V ≃ₗ[ℝ] V
  clock : V →ₗ[ℝ] V
  eta_sq : eta.comp eta = LinearMap.id
  mirror_sq : mirror.toLinearMap.comp mirror.toLinearMap = LinearMap.id
  mirror_clock :
    mirror.toLinearMap.comp (clock.comp mirror.symm.toLinearMap) = (-clock)

namespace DoubledHestenesKreinData

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (K : DoubledHestenesKreinData V)

abbrev Operator (W : Type*) [AddCommGroup W] [Module ℝ W] :=
  W →ₗ[ℝ] W

/-! Conjugation by the real-linear mirror is an automorphism of the operator
envelope. -/

def mirrorConjugate (T : Operator V) : Operator V :=
  K.mirror.toLinearMap.comp (T.comp K.mirror.symm.toLinearMap)

def operatorCommutator (T U : Operator V) : Operator V :=
  T.comp U - U.comp T

def HasGrade (clock : Operator V) (k : ℤ) (T : Operator V) : Prop :=
  operatorCommutator clock T = (k : ℝ) • T

theorem mirrorConjugate_apply (T : Operator V) (v : V) :
    mirrorConjugate K T v = K.mirror (T (K.mirror.symm v)) := by
  rfl

theorem mirrorConjugate_mul (T U : Operator V) :
    mirrorConjugate K (T.comp U) =
      (mirrorConjugate K T).comp (mirrorConjugate K U) := by
  ext v
  simp [mirrorConjugate, LinearMap.comp_apply]

theorem mirrorConjugate_id :
    mirrorConjugate K (LinearMap.id) = LinearMap.id := by
  ext v
  simp [mirrorConjugate, LinearMap.comp_apply]

theorem mirrorConjugate_sub (T U : Operator V) :
    mirrorConjugate K (T - U) =
      mirrorConjugate K T - mirrorConjugate K U := by
  ext v
  simp [mirrorConjugate, LinearMap.comp_apply]

theorem mirrorConjugate_add (T U : Operator V) :
    mirrorConjugate K (T + U) =
      mirrorConjugate K T + mirrorConjugate K U := by
  ext v
  simp [mirrorConjugate, LinearMap.comp_apply]

theorem mirrorConjugate_smul (a : ℝ) (T : Operator V) :
    mirrorConjugate K (a • T) = a • mirrorConjugate K T := by
  ext v
  simp [mirrorConjugate, LinearMap.comp_apply]

theorem mirrorConjugate_clock :
    mirrorConjugate K K.clock = -K.clock := by
  exact K.mirror_clock

theorem mirrorConjugate_commutator (T U : Operator V) :
    mirrorConjugate K (operatorCommutator T U) =
      operatorCommutator (mirrorConjugate K T) (mirrorConjugate K U) := by
  simp only [operatorCommutator, mirrorConjugate_sub, mirrorConjugate_mul]

theorem mirrorConjugate_anticommutator (T U : Operator V) :
    mirrorConjugate K (T.comp U + U.comp T) =
      (mirrorConjugate K T).comp (mirrorConjugate K U) +
        (mirrorConjugate K U).comp (mirrorConjugate K T) := by
  simp only [mirrorConjugate_add, mirrorConjugate_mul]

theorem mirror_reverses_operator_grade
    {k : ℤ} {T : Operator V}
    (hT : HasGrade K.clock k T) :
    HasGrade K.clock (-k) (mirrorConjugate K T) := by
  have htransport := congrArg (mirrorConjugate K) hT
  rw [mirrorConjugate_commutator, mirrorConjugate_clock,
    mirrorConjugate_smul] at htransport
  change operatorCommutator (-K.clock) (mirrorConjugate K T) =
    (k : ℝ) • mirrorConjugate K T at htransport
  change operatorCommutator K.clock (mirrorConjugate K T) =
    ((-k : ℤ) : ℝ) • mirrorConjugate K T
  calc
    operatorCommutator K.clock (mirrorConjugate K T) =
        -operatorCommutator (-K.clock) (mirrorConjugate K T) := by
          ext v
          simp [operatorCommutator]
          abel
    _ = -((k : ℝ) • mirrorConjugate K T) := by rw [htransport]
    _ = ((-k : ℤ) : ℝ) • mirrorConjugate K T := by simp

theorem mirror_sq_apply (v : V) :
    K.mirror (K.mirror v) = v := by
  have h := congrArg (fun f : Operator V => f v) K.mirror_sq
  simpa [LinearMap.comp_apply] using h

theorem eta_sq_apply (v : V) :
    K.eta (K.eta v) = v := by
  have h := congrArg (fun f : Operator V => f v) K.eta_sq
  simpa [LinearMap.comp_apply] using h

end DoubledHestenesKreinData

end InfoGeometry.Canonical
