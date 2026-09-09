import InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeInjectivity

/-!
# Selected-row factorization/alignment interface for the 189 flag carrier

This owner packages the two independent obligations: recursive factorization of
concrete representatives and residual-word alignment in a common quotient
cell. The package is deliberately explicit; it does not manufacture either
obligation from the finite index type.
-/

namespace InfoGeometry.Algebra.Zorn.G2FactorizationAlignmentCertificate

open InfoGeometry.Algebra.Zorn.G2FlagFactorizationRecursion
open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeInjectivity
open InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
open InfoGeometry.Algebra.Zorn.G2QuotientOrbitSeparation
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative

structure FactorizationAlignmentSystem where
  base : ∀ k i, (∀ j : Fin 189, ¬ j.val < i.val) →
    flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (rightFactorWord k i)
  step : ∀ k i, (∃ j : Fin 189, j.val < i.val) →
    FactorizationStep g2FlagFactorizationTarget k i
      (fun j i => j.val < i.val)
  separation : ∀ {k l : Fin 12}, k ≠ l →
    ∀ a c d : PCWordExp,
      pcWord c * orbitWeylRepresentative l =
        pcWord a * orbitWeylRepresentative k * pcWord d → False
  residual_alignment : ∀ (k : Fin 12) (i j : Fin 189),
    i ∈ orbitCells k → j ∈ orbitCells k →
    quotientRepresentative i = quotientRepresentative j →
    residualWord k i = residualWord k j
  residual_injective : ∀ (k : Fin 12) (i j : Fin 189),
    i ∈ orbitCells k → j ∈ orbitCells k →
    residualWord k i = residualWord k j → i = j

/-- The concrete version of the factorization system.  In contrast to
the generic predecessor field above, this records that the predecessor and
the current representative really belong to the same orbit cell and that
the step is induced by one of the native flag generators. -/
structure ConcreteFactorizationAlignmentSystem where
  base : ∀ k i, (∀ j : Fin 189, ¬ j.val < i.val) →
    flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (rightFactorWord k i)
  step : ∀ k i, (∃ j : Fin 189, j.val < i.val) →
    G2OrbitFactorizationStep k i
  separation : ∀ {k l : Fin 12}, k ≠ l →
    ∀ a c d : PCWordExp,
      pcWord c * orbitWeylRepresentative l =
        pcWord a * orbitWeylRepresentative k * pcWord d → False
  residual_alignment : ∀ (k : Fin 12) (i j : Fin 189),
    i ∈ orbitCells k → j ∈ orbitCells k →
    quotientRepresentative i = quotientRepresentative j →
    residualWord k i = residualWord k j
  residual_injective : ∀ (k : Fin 12) (i j : Fin 189),
    i ∈ orbitCells k → j ∈ orbitCells k →
    residualWord k i = residualWord k j → i = j

noncomputable def ConcreteFactorizationAlignmentSystem.toGeneric
    (C : ConcreteFactorizationAlignmentSystem) :
    FactorizationAlignmentSystem where
  base := C.base
  step k i hi := (C.step k i hi).toGeneric
  separation := C.separation
  residual_alignment := C.residual_alignment
  residual_injective := C.residual_injective

theorem generic_factorization
    (C : FactorizationAlignmentSystem) :
    ∀ k i, flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (rightFactorWord k i) :=
  flagRepresentative_factorization_of_predecessor_certificate C.base C.step

theorem concrete_factorization
    (C : ConcreteFactorizationAlignmentSystem) :
    ∀ k i, flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (rightFactorWord k i) :=
  generic_factorization C.toGeneric

theorem generic_alignment
    (C : FactorizationAlignmentSystem) :
    ∀ i j, quotientRepresentative i = quotientRepresentative j →
      ∃ k : Fin 12, i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
        residualWord k i = residualWord k j :=
  quotient_alignment_of_predecessor_certificate C.base C.step
    C.separation C.residual_alignment

theorem concrete_alignment
    (C : ConcreteFactorizationAlignmentSystem) :
    ∀ i j, quotientRepresentative i = quotientRepresentative j →
      ∃ k : Fin 12, i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
        residualWord k i = residualWord k j :=
  generic_alignment C.toGeneric

theorem concrete_quotientRepresentative_injective
    (C : ConcreteFactorizationAlignmentSystem) :
    Function.Injective quotientRepresentative := by
  exact quotientRepresentative_injective_of_residual_alignment
    C.residual_injective (concrete_alignment C)

noncomputable def concrete_quotientRepresentativeEquiv
    (C : ConcreteFactorizationAlignmentSystem)
    (hsurj : Function.Surjective quotientRepresentative) :
    Fin 189 ≃
      InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative.CarrierQuotient :=
  InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeInjectivity.quotientRepresentativeEquiv
    C.residual_injective (concrete_alignment C) hsurj

theorem concrete_factorization_alignment
    (C : ConcreteFactorizationAlignmentSystem)
    (hsurj : Function.Surjective quotientRepresentative) :
    (∀ k i, flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (rightFactorWord k i)) ∧
    (∀ i j, quotientRepresentative i = quotientRepresentative j →
      ∃ k : Fin 12, i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
        residualWord k i = residualWord k j) ∧
    Function.Injective quotientRepresentative ∧
    Nonempty (Fin 189 ≃
      InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative.CarrierQuotient) := by
  exact ⟨concrete_factorization C, concrete_alignment C,
    concrete_quotientRepresentative_injective C,
    ⟨concrete_quotientRepresentativeEquiv C hsurj⟩⟩

theorem quotientRepresentative_injective
    (C : FactorizationAlignmentSystem) :
    Function.Injective quotientRepresentative := by
  exact quotientRepresentative_injective_of_residual_alignment
    C.residual_injective (generic_alignment C)

noncomputable def quotientRepresentativeEquiv
    (C : FactorizationAlignmentSystem)
    (hsurj : Function.Surjective quotientRepresentative) :
    Fin 189 ≃
      InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative.CarrierQuotient :=
  InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeInjectivity.quotientRepresentativeEquiv
    C.residual_injective (generic_alignment C) hsurj

end InfoGeometry.Algebra.Zorn.G2FactorizationAlignmentCertificate

