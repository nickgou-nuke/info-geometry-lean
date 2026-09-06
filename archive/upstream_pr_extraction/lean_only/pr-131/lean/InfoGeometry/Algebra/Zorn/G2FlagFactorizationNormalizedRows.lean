import InfoGeometry.Algebra.Zorn.G2FlagFactorizationRows

/-!
# Proven normalized flag-factorization rows

This owner records only rows for which the repository already contains a
factorization proof.  In particular, the exported row `(4,18)` is stored with
its verified reversed orientation.  It deliberately does not promote the
partial CAS table to a global certificate.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagFactorizationNormalizedRows

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagFactorizationRows
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

structure NormalizedFactorizationRow where
  left : FactorWord
  right : FactorWord

def row_0_0_data : NormalizedFactorizationRow :=
  ⟨leftFactorWord 0 0, rightFactorWord 0 0⟩

def row_1_24_data : NormalizedFactorizationRow :=
  ⟨leftFactorWord 1 24, rightFactorWord 1 24⟩

def row_4_6_data : NormalizedFactorizationRow :=
  ⟨leftFactorWord 4 6, rightFactorWord 4 6⟩

def row_1_45_data : NormalizedFactorizationRow :=
  ⟨leftFactorWord 1 45, rightFactorWord 1 45⟩

/-- The exporter row `(4,18)` is normalized by swapping the two raw factors. -/
def row_4_18_data : NormalizedFactorizationRow :=
  ⟨rightFactorWord 4 18, leftFactorWord 4 18⟩

theorem row_0_0_data_sound :
    flagRepresentative 0 =
      collect row_0_0_data.left *
        weylNF (orbitWeyl 0).1 (orbitWeyl 0).2 *
          collect row_0_0_data.right := by
  exact row_0_0

theorem row_1_24_data_sound :
    flagRepresentative 24 =
      collect row_1_24_data.left *
        weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 *
          collect row_1_24_data.right := by
  exact row_1_24

theorem row_4_6_data_sound :
    flagRepresentative 6 =
      collect row_4_6_data.left *
        weylNF (orbitWeyl 4).1 (orbitWeyl 4).2 *
          collect row_4_6_data.right := by
  exact row_4_6

theorem row_1_45_data_sound :
    flagRepresentative 45 =
      collect row_1_45_data.left *
        weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 *
          collect row_1_45_data.right := by
  exact row_1_45

theorem row_4_18_data_sound :
    flagRepresentative 18 =
      collect row_4_18_data.left *
        weylNF (orbitWeyl 4).1 (orbitWeyl 4).2 *
          collect row_4_18_data.right := by
  exact row_4_18

end InfoGeometry.Algebra.Zorn.G2FlagFactorizationNormalizedRows
