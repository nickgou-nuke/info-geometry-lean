import InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2FlagRepresentativeBase
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval
import InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
import InfoGeometry.Algebra.Zorn.G2Fin189OrbitMembership

/-!
# Orientation-normalized flag factorization certificates

The GAP witness carrier contains rows in both factor orders.  This file does
not claim that a raw table is a factorization for every pair `(k,i)`.
Instead it packages the finite orientation bit together with the two words,
so a sound row certificate has one uniform downstream shape.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagFactorizationOrientation

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2Fin189OrbitMembership
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def normalizedLeftFactorWord (k : Fin 12) (i : Fin 189) (reversed : Bool) : FactorWord :=
  if reversed then rightFactorWord k i else leftFactorWord k i

noncomputable def normalizedRightFactorWord (k : Fin 12) (i : Fin 189) (reversed : Bool) : FactorWord :=
  if reversed then leftFactorWord k i else rightFactorWord k i

noncomputable def normalizedFactorization (k : Fin 12) (i : Fin 189) (reversed : Bool) : SplitOctF2Aut :=
  collect (normalizedLeftFactorWord k i reversed) *
    weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
      collect (normalizedRightFactorWord k i reversed)

theorem normalizedFactorization_of_forward_certificate
    (k : Fin 12) (i : Fin 189)
    (h : flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (rightFactorWord k i)) :
    flagRepresentative i = normalizedFactorization k i false := by
  simpa [normalizedFactorization, normalizedLeftFactorWord,
    normalizedRightFactorWord] using h

theorem normalizedFactorization_of_reversed_certificate
    (k : Fin 12) (i : Fin 189)
    (h : flagRepresentative i =
      collect (rightFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (leftFactorWord k i)) :
    flagRepresentative i = normalizedFactorization k i true := by
  simpa [normalizedFactorization, normalizedLeftFactorWord,
    normalizedRightFactorWord] using h

theorem normalizedFactorization_of_orientation_certificate
    (k : Fin 12) (i : Fin 189) (reversed : Bool)
    (h : flagRepresentative i =
      if reversed then
        collect (rightFactorWord k i) *
          weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
            collect (leftFactorWord k i)
      else
        collect (leftFactorWord k i) *
          weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
            collect (rightFactorWord k i)) :
    flagRepresentative i = normalizedFactorization k i reversed := by
  cases reversed <;> simp [normalizedFactorization, normalizedLeftFactorWord,
    normalizedRightFactorWord] at h ⊢
  · exact h
  · exact h

theorem normalizedLeftFactorWord_mem_unipotentSubgroup
    (k : Fin 12) (i : Fin 189) (reversed : Bool) :
    collect (normalizedLeftFactorWord k i reversed) ∈
      unipotentSubgroup := by
  cases reversed
  · exact leftFactorWord_mem_unipotentSubgroup k i
  · exact rightFactorWord_mem_unipotentSubgroup k i

theorem normalizedRightFactorWord_mem_unipotentSubgroup
    (k : Fin 12) (i : Fin 189) (reversed : Bool) :
    collect (normalizedRightFactorWord k i reversed) ∈
      unipotentSubgroup := by
  cases reversed
  · exact rightFactorWord_mem_unipotentSubgroup k i
  · exact leftFactorWord_mem_unipotentSubgroup k i

noncomputable def orientationCellFactorizationCertificate
    (reversed : Fin 12 → Fin 189 → Bool)
    (hsound : ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      flagRepresentative i =
        if reversed k i then
          collect (rightFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (leftFactorWord k i)
        else
          collect (leftFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (rightFactorWord k i)) :
    CellFactorizationCertificate where
  normalizedLeftFactorWord := fun k i =>
    normalizedLeftFactorWord k i (reversed k i)
  normalizedRightFactorWord := fun k i =>
    normalizedRightFactorWord k i (reversed k i)
  sound := by
    intro k i hi
    exact normalizedFactorization_of_orientation_certificate k i
      (reversed k i) (hsound k i hi)

theorem representative_mem_concreteBruhatCell_of_orientation_certificate
    (reversed : Fin 12 → Fin 189 → Bool)
    (hsound : ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      flagRepresentative i =
        if reversed k i then
          collect (rightFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (leftFactorWord k i)
        else
          collect (leftFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (rightFactorWord k i))
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i ∈
      concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2) := by
  exact G2CellFactorizationCertificate.representative_mem_concreteBruhatCell
    (orientationCellFactorizationCertificate reversed hsound) k i hi

theorem orbit_membership_of_orientation_certificate
    (reversed : Fin 12 → Fin 189 → Bool)
    (hsound : ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      flagRepresentative i =
        if reversed k i then
          collect (rightFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (leftFactorWord k i)
        else
          collect (leftFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (rightFactorWord k i))
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i =
          b • (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
              InfoGeometry.Algebra.Zorn.G2ConcreteBruhatOrbitCertificate.CarrierQuotient) := by
  exact fin189_orbit_membership
    (orientationCellFactorizationCertificate reversed hsound) k i hi

end InfoGeometry.Algebra.Zorn.G2FlagFactorizationOrientation
