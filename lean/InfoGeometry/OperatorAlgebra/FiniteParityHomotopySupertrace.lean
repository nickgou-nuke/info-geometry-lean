import InfoGeometry.OperatorAlgebra.FiniteParityContractible
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Trace

noncomputable section

namespace InfoGeometry.OperatorAlgebra.FiniteParityComplex

namespace TwoPeriodicComplex

variable {Vplus Vminus : Type*}
variable [AddCommGroup Vplus] [Module ℝ Vplus]
variable [AddCommGroup Vminus] [Module ℝ Vminus]

namespace Hom

variable {C : TwoPeriodicComplex Vplus Vminus}

def carrierSupertrace (f : Hom C C) : ℝ :=
  LinearMap.trace ℝ Vplus f.positive -
    LinearMap.trace ℝ Vminus f.negative

def cohomologySupertrace (f : Hom C C) : ℝ :=
  LinearMap.trace ℝ C.PositiveCohomology f.positiveCohomologyMap -
    LinearMap.trace ℝ C.NegativeCohomology f.negativeCohomologyMap

@[simp]
theorem id_carrierSupertrace
    (C : TwoPeriodicComplex Vplus Vminus)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    (id C).carrierSupertrace =
      (Module.finrank ℝ Vplus : ℝ) -
        Module.finrank ℝ Vminus := by
  simp [carrierSupertrace, id, LinearMap.trace_id]

@[simp]
theorem id_cohomologySupertrace
    (C : TwoPeriodicComplex Vplus Vminus)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    (id C).cohomologySupertrace =
      (Module.finrank ℝ C.PositiveCohomology : ℝ) -
        Module.finrank ℝ C.NegativeCohomology := by
  letI : Module.Finite ℝ C.PositiveCohomology :=
    Module.Finite.quotient ℝ C.positiveBoundaries
  letI : Module.Finite ℝ C.NegativeCohomology :=
    Module.Finite.quotient ℝ C.negativeBoundaries
  rw [cohomologySupertrace, positiveCohomologyMap_id,
    negativeCohomologyMap_id, LinearMap.trace_id, LinearMap.trace_id]

end Hom

namespace Homotopy

variable {C : TwoPeriodicComplex Vplus Vminus}
variable {f g : Hom C C}

theorem carrierSupertrace_eq
    (H : Homotopy f g)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    f.carrierSupertrace = g.carrierSupertrace := by
  have hPositive :=
    congrArg (fun T : Module.End ℝ Vplus => LinearMap.trace ℝ Vplus T)
      H.positive_identity
  have hNegative :=
    congrArg (fun T : Module.End ℝ Vminus => LinearMap.trace ℝ Vminus T)
      H.negative_identity
  simp only [map_sub, map_add] at hPositive hNegative
  have hCyclePlus :
      LinearMap.trace ℝ Vplus (C.dMinus.comp H.hPlus) =
        LinearMap.trace ℝ Vminus (H.hPlus.comp C.dMinus) := by
    exact LinearMap.congr_fun
      (LinearMap.congr_fun
        (LinearMap.trace_comp_comm ℝ Vplus Vminus)
        C.dMinus)
      H.hPlus
  have hCycleMinus :
      LinearMap.trace ℝ Vplus (H.hMinus.comp C.dPlus) =
        LinearMap.trace ℝ Vminus (C.dPlus.comp H.hMinus) := by
    exact LinearMap.congr_fun
      (LinearMap.congr_fun
        (LinearMap.trace_comp_comm ℝ Vplus Vminus)
        H.hMinus)
      C.dPlus
  unfold Hom.carrierSupertrace
  linarith

end Homotopy

theorem identity_hopfTrace
    (C : TwoPeriodicComplex Vplus Vminus)
    [FiniteDimensional ℝ Vplus]
    [FiniteDimensional ℝ Vminus] :
    (Hom.id C).carrierSupertrace =
      (Hom.id C).cohomologySupertrace := by
  rw [Hom.id_carrierSupertrace, Hom.id_cohomologySupertrace]
  exact_mod_cast C.eulerCharacteristic_eq

end TwoPeriodicComplex

end InfoGeometry.OperatorAlgebra.FiniteParityComplex
