import InfoGeometry.Tessellation.CantorDiracSeaWalk
import InfoGeometry.Tessellation.CantorDiracSeaCharge
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
import InfoGeometry.Canonical.ProjectorEquivariance
import InfoGeometry.Canonical.Cl11PolarizedBasis
import InfoGeometry.Clifford.RealDoubledHestenesAnchor
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.Tessellation

open scoped InnerProductSpace

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
open InfoGeometry.Canonical.ProjectorEquivariance
open InfoGeometry.Canonical.Cl11PolarizedBasis
open InfoGeometry.Clifford.RealDoubledHestenesAnchor
open InfoGeometry.CondensedMatter.CliffordAtomsZ2n

/--
Operator-geometry owner packet for the Cantor/binary Dirac-sea picture.

This packet is the compact synthesis requested by user-level geometry:
binary boundary + symmetric constrained hopping + supercharges +
Bogoliubov/doubled-real carrier + idempotent/nilpotent/null micro-operators.
-/
@[owner_target_tag]
def CantorDiracSeaOperatorGeometryOwnerTarget : Prop :=
  (∀ ξ : InfiniteBinaryWordSpace,
      ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ)) ∧
  (∀ {Op : Type*} [Ring Op] (W : CantorDiracSeaWalkDatum Op (Z2Charge Bool))
      (w : FiniteBinaryWord),
      (W.sector w).P * (W.sector w).P = (W.sector w).P) ∧
  (∀ {Op : Type*} [Ring Op] (W : CantorDiracSeaWalkDatum Op (Z2Charge Bool))
      (w : FiniteBinaryWord),
      (W.sector w).P * (W.sector (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child w false)).P = 0 ∧
      (W.sector w).P * (W.sector (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child w true)).P = 0) ∧
  (∀ {Op : Type*} [Ring Op],
      ∀ (W : CantorDiracSeaWalkDatum Op (Z2Charge Bool)),
      ∀ w : FiniteBinaryWord,
      (W.leftHop w).N * (W.leftHop w).N = 0 ∧
      (W.rightHop w).N * (W.rightHop w).N = 0) ∧
  (∀ {Op : Type*} [Ring Op],
      ∀ (D : CantorDiracSeaChargeDatum Op),
      ∀ w : FiniteBinaryWord,
      D.walk.charge
          (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child w false) false =
            !D.walk.charge w false ∧
      D.walk.charge
          (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child w false) true =
            D.walk.charge w true ∧
      D.walk.charge
          (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child w true) true =
            !D.walk.charge w true ∧
      D.walk.charge
          (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child w true) false =
            D.walk.charge w false) ∧
  (∀ {Op : Type*} [Ring Op],
      ∀ (P : BinaryWordTiltReadout Op),
      P.bitOperator false * P.bitOperator false = 1 ∧
      P.bitOperator true * P.bitOperator true = 1 ∧
      P.bitOperator false * P.bitOperator true + P.bitOperator true * P.bitOperator false = 0) ∧
  (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ((InfoGeometry.Krein.spectral_epsilon (E := E) :
          InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) *
        (InfoGeometry.Krein.spectral_epsilon (E := E) :
          InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) =
        (1 : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E)) ∧
      InfoGeometry.Canonical.ProjectorEquivariance.plusProjectorAfterPhaseFlip (E := E) =
        InfoGeometry.Canonical.ProjectorEquivariance.minusProjector (E := E) ∧
      InfoGeometry.Canonical.ProjectorEquivariance.minusProjectorAfterPhaseFlip (E := E) =
        InfoGeometry.Canonical.ProjectorEquivariance.plusProjector (E := E) ∧
      InfoGeometry.Canonical.ProjectorEquivariance.plusProjectorAfterPhaseFlip (E := E) +
        InfoGeometry.Canonical.ProjectorEquivariance.minusProjectorAfterPhaseFlip (E := E) =
        ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) ∧
  (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ∀ A B : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E,
      doubledUPlus (E := E) A * doubledUPlus (E := E) B = 0 ∧
      doubledUMinus (E := E) A * doubledUMinus (E := E) B = 0) ∧
  (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ∀ θ : ℝ,
      (InfoGeometry.Clifford.Rotor.modularFlow
          (E := E) doubledIBivector θ).exp.comp
            (InfoGeometry.Clifford.Rotor.modularFlow
                (E := E) doubledIBivector θ).reverse =
          ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) ∧
      (InfoGeometry.Clifford.Rotor.modularFlow
          (E := E) doubledIBivector θ).reverse.comp
            (InfoGeometry.Clifford.Rotor.modularFlow
                (E := E) doubledIBivector θ).exp =
          ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E))

/-- The packet is fully discharged by existing theorem-safe lemmas. -/
theorem cantorDiracSeaOperatorGeometryOwnerTarget :
    CantorDiracSeaOperatorGeometryOwnerTarget := by
  constructor
  · intro ξ
    exact boundary_recursive_decomposition ξ
  · constructor
    · intro Op _ W w
      exact W.sector w |>.idem
    · constructor
      · intro Op _ W w
        refine ⟨?_, ?_⟩
        · exact W.leftOrthogonal w
        · exact W.rightOrthogonal w
      · constructor
        · intro Op _ W w
          refine ⟨?_, ?_⟩
          · exact W.leftHop_square_zero w
          · exact W.rightHop_square_zero w
        · constructor
          · intro Op _ D w
            refine ⟨?_, ?_, ?_, ?_⟩
            · exact D.leftHop_flips_false_bit w
            · exact D.leftHop_preserves_true_bit w
            · exact D.rightHop_flips_true_bit w
            · exact D.rightHop_preserves_false_bit w
          · constructor
            · intro Op _ P
              refine ⟨?_, ?_, ?_⟩
              · exact P.bitOperator_false_sq
              · exact P.bitOperator_true_sq
              · exact P.bitOperator_anticomm
            · constructor
              · intro E _ _ _
                refine ⟨?_, ?_, ?_, ?_⟩
                · exact chiralBoost_generator_sq_one (E := E)
                · exact plusProjectorAfterPhaseFlip_eq_minusProjector (E := E)
                · exact minusProjectorAfterPhaseFlip_eq_plusProjector (E := E)
                · exact phaseFlip_projectorResolution (E := E)
              · constructor
                · intro E _ _ _ A B
                  refine ⟨?_, ?_⟩
                  · exact doubledUPlus_mul_doubledUPlus_eq_zero (E := E) A B
                  · exact doubledUMinus_mul_doubledUMinus_eq_zero (E := E) A B
                · intro E _ _ _ θ
                  refine ⟨?_, ?_⟩
                  · exact doubledI_rotor_exp_reverse (E := E) θ
                  · exact doubledI_rotor_reverse_comp_exp (E := E) θ

/-- Concise downstream name for the geometry/symmetry-hopping package on supergraded doubled operators. -/
theorem geometry_eq_symmetry_constrained_hopping_on_supergraded_doubled_operator_space :
    CantorDiracSeaOperatorGeometryOwnerTarget :=
  cantorDiracSeaOperatorGeometryOwnerTarget

/-- Short form for downstream references. -/
theorem geometry_eq_symmetry_constrained_hopping :
    CantorDiracSeaOperatorGeometryOwnerTarget :=
  geometry_eq_symmetry_constrained_hopping_on_supergraded_doubled_operator_space
