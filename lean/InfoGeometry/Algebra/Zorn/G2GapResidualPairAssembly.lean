import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity

namespace InfoGeometry.Algebra.Zorn.G2GapResidualPairAssembly

open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative

abbrev GapResidualPair :=
  InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent ×
    InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.PCExponent

def gapResidualPair (k : Fin 12) (i : Fin 189) : GapResidualPair :=
  (factorWordExponent (gapLeftWitness k i),
    factorWordExponent (gapRightWitness k i))

theorem gapResidualPair_left_eq_of_eq
    (k : Fin 12) (i j : Fin 189)
    (h : gapResidualPair k i = gapResidualPair k j) :
    factorWordExponent (gapLeftWitness k i) =
      factorWordExponent (gapLeftWitness k j) := by
  exact congrArg Prod.fst h

theorem gapResidualPair_right_eq_of_eq
    (k : Fin 12) (i j : Fin 189)
    (h : gapResidualPair k i = gapResidualPair k j) :
    factorWordExponent (gapRightWitness k i) =
      factorWordExponent (gapRightWitness k j) := by
  exact congrArg Prod.snd h

theorem gapResidualPair_eq_iff
    (k : Fin 12) (i j : Fin 189) :
    gapResidualPair k i = gapResidualPair k j ↔
      factorWordExponent (gapLeftWitness k i) =
        factorWordExponent (gapLeftWitness k j) ∧
      factorWordExponent (gapRightWitness k i) =
        factorWordExponent (gapRightWitness k j) := by
  constructor
  · intro h
    exact ⟨gapResidualPair_left_eq_of_eq k i j h,
      gapResidualPair_right_eq_of_eq k i j h⟩
  · rintro ⟨hleft, hright⟩
    exact Prod.ext hleft hright

theorem quotientRepresentative_injective_of_gapResidualPair_alignment
    (hcell : ∀ (k : Fin 12) (i j : Fin 189),
      i ∈ orbitCells k → j ∈ orbitCells k →
      gapResidualPair k i = gapResidualPair k j → i = j)
    (halign : ∀ (i j : Fin 189),
      quotientRepresentative i = quotientRepresentative j →
        ∃ k : Fin 12,
          i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
            gapResidualPair k i = gapResidualPair k j) :
    Function.Injective quotientRepresentative := by
  intro i j hij
  obtain ⟨k, hik, hjk, hpair⟩ := halign i j hij
  exact hcell k i j hik hjk hpair

end InfoGeometry.Algebra.Zorn.G2GapResidualPairAssembly
