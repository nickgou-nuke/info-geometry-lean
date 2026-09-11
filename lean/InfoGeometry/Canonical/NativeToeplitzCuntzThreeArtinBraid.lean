import InfoGeometry.Canonical.CuntzTensorToeplitzThreeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge

/-!
# Native Artin braid generators in the three-generator Toeplitz--Cuntz quotient

This is the native consumer API for the three-generator braid shadow.  Its
carrier is `CuntzToeplitzAlg 3`; the old generator-record interface is used
only to transport the already proved noncommutative identities.
-/

noncomputable section

namespace InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Canonical.NativeToeplitzCuntzThree
open InfoGeometry.Canonical.CuntzTensorToeplitzThreeBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge

abbrev Carrier := CuntzToeplitzAlg 3

def braidGenerator1 : Carrier :=
  generator (0 : Fin 3) * star (generator (1 : Fin 3)) +
    generator (1 : Fin 3) * star (generator (0 : Fin 3)) +
    rangeProjection (2 : Fin 3) + vacuumDefect

def braidGenerator2 : Carrier :=
  generator (1 : Fin 3) * star (generator (2 : Fin 3)) +
    generator (2 : Fin 3) * star (generator (1 : Fin 3)) +
    rangeProjection (0 : Fin 3) + vacuumDefect

def coxeterElement : Carrier := braidGenerator2 * braidGenerator1

theorem braidGenerator1_sq : braidGenerator1 * braidGenerator1 = 1 := by
  simpa [braidGenerator1,
    ToeplitzCuntzThreeArtinBraidBridge.braidGenerator1,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P0,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P1,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P2,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P3,
    Fin.ext_iff,
    NativeToeplitzCuntzThree.generator,
    NativeToeplitzCuntzThree.rangeProjection,
    NativeToeplitzCuntzThree.vacuumDefect, sub_eq_add_neg, star_toeplitzS] using
    (ToeplitzCuntzThreeArtinBraidBridge.braidGenerator1_sq
      nativeToeplitzThreeGenerators)

theorem braidGenerator2_sq : braidGenerator2 * braidGenerator2 = 1 := by
  simpa [braidGenerator2,
    ToeplitzCuntzThreeArtinBraidBridge.braidGenerator2,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P0,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P1,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P2,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P3,
    Fin.ext_iff,
    NativeToeplitzCuntzThree.generator,
    NativeToeplitzCuntzThree.rangeProjection,
    NativeToeplitzCuntzThree.vacuumDefect, sub_eq_add_neg, star_toeplitzS] using
    (ToeplitzCuntzThreeArtinBraidBridge.braidGenerator2_sq
      nativeToeplitzThreeGenerators)

theorem artin_braid_relation :
    braidGenerator1 * braidGenerator2 * braidGenerator1 =
      braidGenerator2 * braidGenerator1 * braidGenerator2 := by
  simpa [braidGenerator1, braidGenerator2,
    ToeplitzCuntzThreeArtinBraidBridge.braidGenerator1,
    ToeplitzCuntzThreeArtinBraidBridge.braidGenerator2,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P0,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P1,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P2,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P3,
    Fin.ext_iff,
    NativeToeplitzCuntzThree.generator,
    NativeToeplitzCuntzThree.rangeProjection,
    NativeToeplitzCuntzThree.vacuumDefect, sub_eq_add_neg, star_toeplitzS] using
    (ToeplitzCuntzThreeArtinBraidBridge.artin_braid_relation
      nativeToeplitzThreeGenerators)

theorem coxeterElement_eq_cyclicSupercharge_add_defect :
    coxeterElement =
      (generator (0 : Fin 3) * star (generator (1 : Fin 3)) +
        generator (1 : Fin 3) * star (generator (2 : Fin 3)) +
        generator (2 : Fin 3) * star (generator (0 : Fin 3))) + vacuumDefect := by
  simpa [coxeterElement, braidGenerator1, braidGenerator2,
    ToeplitzCuntzThreeArtinBraidBridge.coxeterElement,
    ToeplitzCuntzThreeArtinBraidBridge.braidGenerator1,
    ToeplitzCuntzThreeArtinBraidBridge.braidGenerator2,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P0,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P1,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P2,
    ToeplitzCuntzThreeVacuumBridge.ToeplitzCuntzThreeGenerators.P3,
    Fin.ext_iff,
    ToeplitzCuntzThreeCyclicSuperchargeBridge.cyclicSupercharge,
    NativeToeplitzCuntzThree.generator,
    NativeToeplitzCuntzThree.rangeProjection,
    NativeToeplitzCuntzThree.vacuumDefect, sub_eq_add_neg, star_toeplitzS] using
    (ToeplitzCuntzThreeArtinBraidBridge.coxeterElement_eq_cyclicSupercharge_add_defect
      nativeToeplitzThreeGenerators)

end InfoGeometry.Canonical.NativeToeplitzCuntzThreeArtinBraid
