import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-!
# Direct CAR readout on the unscaled neutral Clifford algebra

The semantic carrier and both quadratic normalizations belong to
`NeutralPhaseSpaceCore`.  This file only exposes the direct-evaluation
Clifford convention, whose mixed anticommutator is `α u`.
-/

namespace InfoGeometry.Canonical.NeutralDualPair

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {U : Type*} [AddCommGroup U] [Module ℝ U]

abbrev Cl (U : Type*) [AddCommGroup U] [Module ℝ U] :=
  CliffordAlgebra (canonicalNeutralFormUnscaled (E := U))

noncomputable def generator : PhaseSpaceCarrier U →ₗ[ℝ] Cl U :=
  CliffordAlgebra.ι (canonicalNeutralFormUnscaled (E := U))

@[simp] theorem generator_apply (x : PhaseSpaceCarrier U) :
    generator x = CliffordAlgebra.ι
      (canonicalNeutralFormUnscaled (E := U)) x := rfl

theorem generator_sq (x : PhaseSpaceCarrier U) :
    generator x * generator x =
      algebraMap ℝ (Cl U) (canonicalNeutralFormUnscaled x) := by
  exact CliffordAlgebra.ι_sq_scalar
    (canonicalNeutralFormUnscaled (E := U)) x

theorem generator_mul_add_swap (x y : PhaseSpaceCarrier U) :
    generator x * generator y + generator y * generator x =
      algebraMap ℝ (Cl U)
        (QuadraticMap.polar
          (canonicalNeutralFormUnscaled (E := U)) x y) := by
  exact CliffordAlgebra.ι_mul_ι_add_swap
    (Q := canonicalNeutralFormUnscaled (E := U)) x y

noncomputable def vectorGenerator (u : U) : Cl U :=
  generator (u, 0)

noncomputable def covectorGenerator (α : Module.Dual ℝ U) : Cl U :=
  generator (0, α)

theorem vectorGenerator_sq_zero (u : U) :
    vectorGenerator u * vectorGenerator u = 0 := by
  rw [vectorGenerator, generator_sq]
  simp [canonicalNeutralFormUnscaled_snd_zero]

theorem covectorGenerator_sq_zero (α : Module.Dual ℝ U) :
    covectorGenerator α * covectorGenerator α = 0 := by
  rw [covectorGenerator, generator_sq]
  simp [canonicalNeutralFormUnscaled_fst_zero]

theorem vector_covector_CAR (u : U) (α : Module.Dual ℝ U) :
    vectorGenerator u * covectorGenerator α +
        covectorGenerator α * vectorGenerator u =
      algebraMap ℝ (Cl U) (α u) := by
  simpa [vectorGenerator, covectorGenerator,
    canonicalNeutralFormUnscaled_polar,
    canonicalNeutralBilin_apply] using
    (CliffordAlgebra.ι_mul_ι_add_swap
      (Q := canonicalNeutralFormUnscaled (E := U))
      ((u, 0) : PhaseSpaceCarrier U) ((0, α) : PhaseSpaceCarrier U))

theorem covector_vector_CAR (α : Module.Dual ℝ U) (u : U) :
    covectorGenerator α * vectorGenerator u +
        vectorGenerator u * covectorGenerator α =
      algebraMap ℝ (Cl U) (α u) := by
  rw [add_comm]
  exact vector_covector_CAR u α

end InfoGeometry.Canonical.NeutralDualPair
