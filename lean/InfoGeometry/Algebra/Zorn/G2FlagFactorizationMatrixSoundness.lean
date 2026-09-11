import InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

/-!
# Matrix readback for conditional flag factorizations

This file owns only the faithful readback from an automorphism-matrix equality
to equality in `SplitOctF2Aut`.  Its `factorizationMatrixValid_of_sound` lemma
is conditional on `CellFactorizationCertificate.sound`; it does not validate
CAS data or construct a global certificate.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagFactorizationMatrixSoundness

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def factorizationMatrixValid (C : CellFactorizationCertificate)
    (k : Fin 12) (i : Fin 189) : Prop :=
  autMatrix (flagRepresentative i) =
      autMatrix
      (collect (C.normalizedLeftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (C.normalizedRightFactorWord k i))

theorem factorizationMatrixValid_of_sound
    (C : CellFactorizationCertificate) (k : Fin 12) (i : Fin 189)
    (hi : i ∈ orbitCells k) :
    factorizationMatrixValid C k i := by
  unfold factorizationMatrixValid
  rw [C.sound k i hi]

theorem factorizationCertificate_sound
    (C : CellFactorizationCertificate) (k : Fin 12) (i : Fin 189)
    (h : factorizationMatrixValid C k i) :
    flagRepresentative i =
      collect (C.normalizedLeftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (C.normalizedRightFactorWord k i) := by
  exact autMatrix_injective h

end InfoGeometry.Algebra.Zorn.G2FlagFactorizationMatrixSoundness
