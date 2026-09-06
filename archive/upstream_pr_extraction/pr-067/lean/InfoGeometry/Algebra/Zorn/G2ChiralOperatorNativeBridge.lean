import InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionStandardDerivation

/-!
# Native readout of the chiral operator labels

The free associative `ChiralOperatorEnvelope` is not identified with the
non-associative Zorn algebra.  This owner only supplies the honest linear
readout of its eight generator labels into the existing circular Peirce basis.
The active rotation generators remain the separate fourteen-dimensional native
derivation carrier.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2ChiralOperatorNativeBridge

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

def chiralGeneratorIndex : ChiralGenerator → Fin 8
  | .pPlus => 0
  | .sPlus 0 => 1
  | .sPlus 1 => 2
  | .sPlus 2 => 3
  | .pMinus => 4
  | .sMinus 0 => 5
  | .sMinus 1 => 6
  | .sMinus 2 => 7

def chiralOperatorNativeReadout (g : ChiralGenerator) : CartesianCoordinates :=
  circularBasis (chiralGeneratorIndex g)

theorem chiralOperatorNativeReadout_eq_circularBasis (g : ChiralGenerator) :
    chiralOperatorNativeReadout g = circularBasis (chiralGeneratorIndex g) := rfl

theorem chiralOperatorNativeReadout_ne_zero (g : ChiralGenerator) :
    chiralOperatorNativeReadout g ≠ 0 := by
  exact circularBasis.ne_zero (chiralGeneratorIndex g)

theorem chiralGeneratorIndex_injective : Function.Injective chiralGeneratorIndex := by
  native_decide

theorem chiralOperatorNativeReadout_injective :
    Function.Injective chiralOperatorNativeReadout := by
  intro g h eq
  apply chiralGeneratorIndex_injective
  apply circularBasis.linearIndependent.injective
  simpa [chiralOperatorNativeReadout] using eq

theorem chiralOperatorNativeReadout_is_not_derivation_basis :
    ¬ Nonempty
      (CartesianCoordinates ≃ₗ[ℝ]
        InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)) := by
  rintro ⟨e⟩
  have h := e.finrank_eq
  rw [cartesianCoordinates_finrank,
    InfoGeometry.Lie.CanonicalZornDerivationDimension.finrank_vectorDerivations] at h
  norm_num at h

/-- The free associative envelope has an exact operatorial readout on the
canonical Zorn carrier.  No associativity of the Zorn product is used here:
the source is free, so `FreeAlgebra.lift` supplies the algebra hom. -/
noncomputable def chiralEnvelopeRepresentation :
    ChiralOperatorEnvelope ℝ →ₐ[ℝ] Module.End ℝ CanonicalZorn :=
  FreeAlgebra.lift ℝ (fun g =>
    L (circularPeirceBasis (chiralGeneratorIndex g)))

noncomputable def chiralEnvelopeRightRepresentation :
    ChiralOperatorEnvelope ℝ →ₐ[ℝ] Module.End ℝ CanonicalZorn :=
  FreeAlgebra.lift ℝ (fun g =>
    R (circularPeirceBasis (chiralGeneratorIndex g)))

@[simp] theorem chiralEnvelopeRepresentation_on_generator
    (g : ChiralGenerator) :
    chiralEnvelopeRepresentation (ChiralOperatorEnvelope.ofGenerator g) =
      L (circularPeirceBasis (chiralGeneratorIndex g)) := by
  exact FreeAlgebra.lift_ι_apply _ _

theorem chiralEnvelopeRepresentation_on_generator_apply
    (g : ChiralGenerator) (x : CanonicalZorn) :
    chiralEnvelopeRepresentation (ChiralOperatorEnvelope.ofGenerator g) x =
      circularPeirceBasis (chiralGeneratorIndex g) * x := by
  rw [chiralEnvelopeRepresentation_on_generator]
  rfl

@[simp] theorem chiralEnvelopeRightRepresentation_on_generator
    (g : ChiralGenerator) :
    chiralEnvelopeRightRepresentation (ChiralOperatorEnvelope.ofGenerator g) =
      R (circularPeirceBasis (chiralGeneratorIndex g)) := by
  exact FreeAlgebra.lift_ι_apply _ _

theorem chiralEnvelopeRightRepresentation_on_generator_apply
    (g : ChiralGenerator) (x : CanonicalZorn) :
    chiralEnvelopeRightRepresentation (ChiralOperatorEnvelope.ofGenerator g) x =
      x * circularPeirceBasis (chiralGeneratorIndex g) := by
  rw [chiralEnvelopeRightRepresentation_on_generator]
  rfl

noncomputable def chiralStanOperator
    (g h : ChiralGenerator) : Module.End ℝ CanonicalZorn :=
    (chiralEnvelopeRepresentation (ChiralOperatorEnvelope.ofGenerator g)).comp
        (chiralEnvelopeRepresentation (ChiralOperatorEnvelope.ofGenerator h)) -
      (chiralEnvelopeRepresentation (ChiralOperatorEnvelope.ofGenerator h)).comp
        (chiralEnvelopeRepresentation (ChiralOperatorEnvelope.ofGenerator g)) +
      ((chiralEnvelopeRepresentation (ChiralOperatorEnvelope.ofGenerator g)).comp
          (chiralEnvelopeRightRepresentation
            (ChiralOperatorEnvelope.ofGenerator h)) -
        (chiralEnvelopeRightRepresentation
            (ChiralOperatorEnvelope.ofGenerator h)).comp
          (chiralEnvelopeRepresentation (ChiralOperatorEnvelope.ofGenerator g))) +
      ((chiralEnvelopeRightRepresentation (ChiralOperatorEnvelope.ofGenerator g)).comp
          (chiralEnvelopeRightRepresentation
            (ChiralOperatorEnvelope.ofGenerator h)) -
        (chiralEnvelopeRightRepresentation
            (ChiralOperatorEnvelope.ofGenerator h)).comp
          (chiralEnvelopeRightRepresentation
            (ChiralOperatorEnvelope.ofGenerator g)))

theorem chiralStanOperator_apply (g h : ChiralGenerator) (x : CanonicalZorn) :
    chiralStanOperator g h x =
      (circularPeirceBasis (chiralGeneratorIndex g) *
          (circularPeirceBasis (chiralGeneratorIndex h) * x) -
        circularPeirceBasis (chiralGeneratorIndex h) *
          (circularPeirceBasis (chiralGeneratorIndex g) * x)) +
      (circularPeirceBasis (chiralGeneratorIndex g) *
          (x * circularPeirceBasis (chiralGeneratorIndex h)) -
        (circularPeirceBasis (chiralGeneratorIndex g) * x) *
          circularPeirceBasis (chiralGeneratorIndex h)) +
      ((x * circularPeirceBasis (chiralGeneratorIndex h)) *
          circularPeirceBasis (chiralGeneratorIndex g) -
        (x * circularPeirceBasis (chiralGeneratorIndex g)) *
          circularPeirceBasis (chiralGeneratorIndex h)) := by
  simp [chiralStanOperator, chiralEnvelopeRepresentation_on_generator,
    chiralEnvelopeRightRepresentation_on_generator, Function.comp_apply]

theorem chiralStanOperator_eq_directCanonicalStanDerMap
    (g h : ChiralGenerator) :
    chiralStanOperator g h =
      directCanonicalStanDerMap
        (circularPeirceBasis (chiralGeneratorIndex g))
        (circularPeirceBasis (chiralGeneratorIndex h)) := by
  apply LinearMap.ext
  intro x
  rw [chiralStanOperator_apply, directCanonicalStanDerMap_apply]

theorem chiralStanOperator_is_derivation
    (g h : ChiralGenerator) :
    InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation
      (chiralStanOperator g h) := by
  rw [chiralStanOperator_eq_directCanonicalStanDerMap]
  exact (canonicalStandardDerivationOfCanonical
    (circularPeirceBasis (chiralGeneratorIndex g))
    (circularPeirceBasis (chiralGeneratorIndex h))).property

noncomputable def chiralStanDerivation
    (g h : ChiralGenerator) :
    InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  canonicalStandardDerivationOfCanonical
    (circularPeirceBasis (chiralGeneratorIndex g))
    (circularPeirceBasis (chiralGeneratorIndex h))

theorem chiralStanDerivation_val (g h : ChiralGenerator) :
    (chiralStanDerivation g h).1 = chiralStanOperator g h := by
  rw [chiralStanDerivation, chiralStanOperator_eq_directCanonicalStanDerMap]
  rfl

theorem chiralStanDerivation_apply_normal_form
    (g h : ChiralGenerator) (x : CanonicalZorn) :
    (chiralStanDerivation g h).1 x =
      ((circularPeirceBasis (chiralGeneratorIndex g) *
          circularPeirceBasis (chiralGeneratorIndex h) -
        circularPeirceBasis (chiralGeneratorIndex h) *
          circularPeirceBasis (chiralGeneratorIndex g)) * x -
        x * (circularPeirceBasis (chiralGeneratorIndex g) *
          circularPeirceBasis (chiralGeneratorIndex h) -
        circularPeirceBasis (chiralGeneratorIndex h) *
          circularPeirceBasis (chiralGeneratorIndex g))) -
      3 • ((circularPeirceBasis (chiralGeneratorIndex g) *
          circularPeirceBasis (chiralGeneratorIndex h)) * x -
        circularPeirceBasis (chiralGeneratorIndex g) *
          (circularPeirceBasis (chiralGeneratorIndex h) * x)) := by
  rw [chiralStanDerivation]
  change directCanonicalStanDerMap
      (circularPeirceBasis (chiralGeneratorIndex g))
      (circularPeirceBasis (chiralGeneratorIndex h)) x = _
  exact directCanonicalStanDerMap_apply_normal_form
    (circularPeirceBasis (chiralGeneratorIndex g))
    (circularPeirceBasis (chiralGeneratorIndex h)) x

theorem chiralEnvelopeRepresentation_word_append
    (u v : List ChiralGenerator) :
    chiralEnvelopeRepresentation
        (ChiralOperatorEnvelope.word (R := ℝ) (u ++ v)) =
      chiralEnvelopeRepresentation (ChiralOperatorEnvelope.word (R := ℝ) u) *
        chiralEnvelopeRepresentation (ChiralOperatorEnvelope.word (R := ℝ) v) := by
  rw [ChiralOperatorEnvelope.word_append]
  exact (chiralEnvelopeRepresentation).map_mul _ _

theorem chiralEnvelopeRepresentation_commutator
    (X Y : ChiralOperatorEnvelope ℝ) :
    chiralEnvelopeRepresentation
        (ChiralOperatorEnvelope.commutator X Y) =
      chiralEnvelopeRepresentation X * chiralEnvelopeRepresentation Y -
        chiralEnvelopeRepresentation Y * chiralEnvelopeRepresentation X := by
  simp [ChiralOperatorEnvelope.commutator]

@[simp] theorem chiralEnvelopeRepresentation_on_PPlus :
    chiralEnvelopeRepresentation (ChiralOperatorEnvelope.PPlus (R := ℝ)) =
      L (circularPeirceBasis 0) := by
  exact chiralEnvelopeRepresentation_on_generator .pPlus

@[simp] theorem chiralEnvelopeRepresentation_on_PMinus :
    chiralEnvelopeRepresentation (ChiralOperatorEnvelope.PMinus (R := ℝ)) =
      L (circularPeirceBasis 4) := by
  exact chiralEnvelopeRepresentation_on_generator .pMinus

@[simp] theorem chiralEnvelopeRepresentation_on_SPlus (i : Fin 3) :
    chiralEnvelopeRepresentation (ChiralOperatorEnvelope.SPlus (R := ℝ) i) =
      L (circularPeirceBasis (chiralGeneratorIndex (.sPlus i))) := by
  exact chiralEnvelopeRepresentation_on_generator (.sPlus i)

@[simp] theorem chiralEnvelopeRepresentation_on_SMinus (i : Fin 3) :
    chiralEnvelopeRepresentation (ChiralOperatorEnvelope.SMinus (R := ℝ) i) =
      L (circularPeirceBasis (chiralGeneratorIndex (.sMinus i))) := by
  exact chiralEnvelopeRepresentation_on_generator (.sMinus i)

end InfoGeometry.Algebra.Zorn.G2ChiralOperatorNativeBridge
