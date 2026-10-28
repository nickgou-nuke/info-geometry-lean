/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.Examples
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.Crossover
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.TraceAdjoint
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.DoubleCommutator

/-!
# Crossover and trace defects in the inherited full matrix example

The existing nondiagonal projection, charge, Gram matrix, and matrix-unit
probe live in the full algebra `Matrix (Fin 4) (Fin 4) ℂ`. Their corner
identifications specialize the crossover laws, and explicit defects
separate bilinear trace symmetry, star compatibility, and graded Hodge
kernel statements.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators.Examples

open Matrix InfoGeometry.Core
open scoped ComplexOrder
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

attribute [local instance] LieRing.ofAssociativeRing

local instance : NormedAddCommGroup (Matrix (Fin 4) (Fin 4) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance : InnerProductSpace ℂ (Matrix (Fin 4) (Fin 4) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local notation "adM" => LieAlgebra.ad ℂ (Matrix (Fin 4) (Fin 4) ℂ)
local notation "J" => jordanLeft (R := ℂ)
local notation "E" => Module.End ℂ (Matrix (Fin 4) (Fin 4) ℂ)
local notation "S" => PeirceGrading.reflection projection
local notation "Δ" => (-(adM charge * adM chargeᴴ + adM chargeᴴ * adM charge) : E)
local notation "F" => (adM charge * J chargeᴴ - adM chargeᴴ * J charge : E)
local notation "G" => (adM gram - (adM charge * adM chargeᴴ + adM chargeᴴ * adM charge) : E)
local notation "B" =>
  LinearMap.compr₂ (LinearMap.mul ℂ (Matrix (Fin 4) (Fin 4) ℂ))
    (Matrix.traceLinearMap (Fin 4) ℂ ℂ)
local notation "θ" =>
  parityEquiv (R := ℂ) projection projection_isStarProjection.isIdempotentElem

/-- The inherited charge is its actual forward Peirce component. -/
theorem charge_component10 : component10 projection charge = charge := by
  change projection * charge * (1 - projection) = charge
  rw [projection_mul_charge, mul_sub, mul_one, charge_mul_projection, sub_zero]

/-- Its conjugate transpose is the opposite directed component. -/
theorem charge_adjoint_component01 : component01 projection chargeᴴ = chargeᴴ := by
  have hp : projectionᴴ = projection := projection_isStarProjection.isSelfAdjoint
  have hright : chargeᴴ * projection = chargeᴴ := by
    simpa only [conjTranspose_mul, hp] using
      congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => Mᴴ) projection_mul_charge
  have hleft : projection * chargeᴴ = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_zero, hp] using
      congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => Mᴴ) charge_mul_projection
  change (1 - projection) * chargeᴴ * projection = chargeᴴ
  rw [sub_mul, one_mul, hleft, sub_zero, hright]

/-- The paired double inner action annihilates the identity. -/
theorem double_charge_one : Δ (1 : Matrix (Fin 4) (Fin 4) ℂ) = 0 :=
  double_lie_one charge chargeᴴ

/-- The mixed action sends the identity to four times the coefficient commutator. -/
theorem mixed_charge_one :
    F (1 : Matrix (Fin 4) (Fin 4) ℂ) = 4 • ⁅charge, chargeᴴ⁆ :=
  mixed_difference_one charge chargeᴴ

/-- The double action has the opposite crossover value on the actual reflection. -/
theorem double_charge_reflection : Δ S = -(4 • ⁅charge, chargeᴴ⁆) := by
  simpa only [charge_component10, charge_adjoint_component01] using
    double_lie_reflection (R := ℂ) projection_isStarProjection.isIdempotentElem charge chargeᴴ

/-- The mixed action annihilates that same reflection. -/
theorem mixed_charge_reflection : F S = 0 := by
  simpa only [charge_component10, charge_adjoint_component01] using
    mixed_difference_reflection (R := ℂ) projection_isStarProjection.isIdempotentElem
      charge chargeᴴ

/-- Native bilinear trace-skewness fails by the already established noncommutation. -/
theorem mixed_charge_not_traceSkewAdjoint : ¬ LinearMap.IsSkewAdjoint B F := by
  intro h
  exact charge_adjoint_noncommute
    ((trace_mixed_isSkewAdjoint_iff_commute charge chargeᴴ).mp h).eq

/-- The trace-skewness defect on the reflection and identity is exactly nonzero. -/
theorem mixed_charge_trace_skew_defect :
    trace ((F S) * (1 : Matrix (Fin 4) (Fin 4) ℂ)) +
      trace (S * (F (1 : Matrix (Fin 4) (Fin 4) ℂ))) = 448 := by
  rw [mixed_charge_reflection, mixed_charge_one, zero_mul, trace_zero, zero_add]
  norm_num [PeirceGrading.reflection, projection, charge, Ring.lie_def,
    Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, conjTranspose_apply,
    map_ofNat, Fin.sum_univ_succ]

/-- The raw Gram-commutator perturbation fails bilinear trace symmetry on two matrix units. -/
theorem raw_commutator_trace_symmetry_defect :
    trace ((G probe) * probeᴴ) - trace (probe * (G probeᴴ)) = -64 := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LieAlgebra.ad_apply, Ring.lie_def]
  norm_num [gram, charge, probe, Matrix.single, Matrix.trace, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, conjTranspose_apply, map_ofNat, Fin.sum_univ_succ]

/-- The raw perturbation fails star compatibility on `probe + probeᴴ`, with explicit orientation. -/
theorem raw_commutator_star_defect :
    (G ((probe + probeᴴ)ᴴ) - (G (probe + probeᴴ))ᴴ) 0 2 = -64 := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LieAlgebra.ad_apply, Ring.lie_def]
  norm_num [gram, charge, probe, Matrix.single, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, conjTranspose_apply, map_ofNat, Fin.sum_univ_succ]

/-- The charge centralizes its Gram matrix but is absent from the joint-commutant kernel. -/
theorem charge_not_doubleCommutator_kernel : charge ∉ Δ.ker := by
  intro h
  have hpair := (doubleCommutator_apply_eq_zero_iff charge charge).mp
    (LinearMap.mem_ker.mp h)
  exact charge_adjoint_noncommute (sub_eq_zero.mp hpair.2).symm

/-- The identity remains in the ordinary paired double-commutator kernel. -/
theorem identity_doubleCommutator_kernel :
    (1 : Matrix (Fin 4) (Fin 4) ℂ) ∈ Δ.ker :=
  LinearMap.mem_ker.mpr double_charge_one

/-- The ordinary paired kernel differs from the actual graded Hodge kernel. -/
theorem doubleCommutator_kernel_ne_gradedHodge_kernel :
    Δ.ker ≠
      (gradedAdjoint θ charge * (gradedAdjoint θ charge).adjoint +
        (gradedAdjoint θ charge).adjoint * gradedAdjoint θ charge).ker := by
  intro h
  have hI := identity_doubleCommutator_kernel
  rw [h] at hI
  exact identity_not_hodge_kernel hI

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators.Examples
