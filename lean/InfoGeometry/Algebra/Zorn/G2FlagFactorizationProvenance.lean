import InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate

/-!
# Provenance boundary for G₂ flag factorization

The CAS words are data.  Their alignment with the native representatives is a
separate proposition.  This file exposes that distinction without claiming a
global certificate.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagFactorizationProvenance

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate

/-- The exported factor words, without any soundness field. -/
structure CellFactorizationData where
  left : Fin 12 → Fin 189 → FactorWord
  right : Fin 12 → Fin 189 → FactorWord

/-- The exact native statement that a data payload would have to prove. -/
def CellFactorizationSound (D : CellFactorizationData) : Prop :=
  ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
    flagRepresentative i =
      collect (D.left k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (D.right k i)

/-- Project the words from the legacy proof-contract carrier to data. -/
def certificateData
    (C : CellFactorizationCertificate) : CellFactorizationData where
  left := C.normalizedLeftFactorWord
  right := C.normalizedRightFactorWord

/-- A certificate contract supplies precisely the corresponding soundness
proposition for its data projection. -/
theorem CellFactorizationCertificate.data_sound
    (C : CellFactorizationCertificate) :
    CellFactorizationSound (certificateData C) := by
  intro k i hi
  exact C.sound k i hi

theorem CellFactorizationSound.factorization
    (D : CellFactorizationData) (hD : CellFactorizationSound D)
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i =
      collect (D.left k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (D.right k i) :=
  hD k i hi

end InfoGeometry.Algebra.Zorn.G2FlagFactorizationProvenance
