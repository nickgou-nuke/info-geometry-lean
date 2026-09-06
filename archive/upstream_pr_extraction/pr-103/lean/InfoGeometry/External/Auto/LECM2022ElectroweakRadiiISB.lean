import Mathlib.Data.Rat.Defs

/-!
The numerical input used by the LECM 2022 isospin-breaking lane.

This is an explicit literature datum, not a derived theorem: the downstream
algebraic file is responsible for proving consequences of the value it uses.
-/
namespace LECM2022ElectroweakRadiiISB

def deltaCMax_permyriad : ℚ := 100

theorem deltaCMax_permyriad_value :
    deltaCMax_permyriad = 100 := rfl

end LECM2022ElectroweakRadiiISB
