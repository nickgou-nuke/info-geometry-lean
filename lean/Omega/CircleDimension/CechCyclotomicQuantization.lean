import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper-facing wrapper for the `\v{C}ech`--cyclotomic quantization package.
    thm:cdim-cech-cyclotomic-quantization -/
theorem paper_cdim_cech_cyclotomic_quantization
    {obstructionGivesPrimitiveRootOrbit primitiveRootOrbitForcesNull : Prop}
    (hObstruction : obstructionGivesPrimitiveRootOrbit)
    (hPrimitiveRoot : primitiveRootOrbitForcesNull) :
    obstructionGivesPrimitiveRootOrbit /\ primitiveRootOrbitForcesNull :=
  ⟨hObstruction, hPrimitiveRoot⟩

end Omega.CircleDimension
