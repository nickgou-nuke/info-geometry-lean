import Mathlib.Tactic
import Omega.CircleDimension.CechCyclotomicQuantization

namespace Omega.TypedAddressBiaxialCompletion

/-- Typed-address wrapper around the chapter-local Čech--cyclotomic quantization package.
    thm:typed-address-biaxial-completion-cech-cyclotomic -/
theorem paper_typed_address_biaxial_completion_cech_cyclotomic
    {obstructionGivesPrimitiveRootOrbit primitiveRootOrbitForcesNull : Prop}
    (hObstruction : obstructionGivesPrimitiveRootOrbit)
    (hPrimitiveRoot : primitiveRootOrbitForcesNull) :
    obstructionGivesPrimitiveRootOrbit ∧ primitiveRootOrbitForcesNull :=
  Omega.CircleDimension.paper_cdim_cech_cyclotomic_quantization hObstruction hPrimitiveRoot

end Omega.TypedAddressBiaxialCompletion
