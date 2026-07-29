import InfoGeometry.OperatorAlgebra.FullO55MatrixLaws
import InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws
import InfoGeometry.OperatorAlgebra.PO55ConformalClosure
import InfoGeometry.Clifford.ConformalProjectiveEmbedding55

/-!
# Explicit O(5,5) conformal evidence bridge

This packet joins the repository's independently maintained finite matrix,
Clifford, and projective-conformal owners at their common null-pair data.
The diagonal and hyperbolic matrix presentations remain explicit: the finite
Pin owner supplies the off-diagonal Buscher swap, while the full matrix owner
supplies the diagonal split Lie algebra and null-coordinate packet.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.O55ConformalEvidenceBridge

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Clifford

/-- The concrete finite matrix and Clifford null-pair packet. -/
theorem finite_matrix_clifford_packet :
    FullO55MatrixLaws.eta * FullO55MatrixLaws.eta = 1 ∧
      (∀ i j : Fin 5,
        FullO55MatrixLaws.IsSO55Lie (FullO55MatrixLaws.boost i j)) ∧
      (∀ i : Fin 5,
        FullO55MatrixLaws.etaPair
          (FullO55MatrixLaws.lightlikePlus i)
          (FullO55MatrixLaws.lightlikePlus i) = 0) ∧
      FullPin55MatrixLaws.IsO55Off FullPin55MatrixLaws.buscherSwapFirst ∧
      FullPin55MatrixLaws.buscherSwapFirst *
          FullPin55MatrixLaws.buscherSwapFirst = 1 ∧
      ∃ P : Clifford.ConformalLift55.ConformalNullPair,
        Clifford.ConformalProjectiveEmbedding55.S P *
            Clifford.ConformalProjectiveEmbedding55.S P = 1 := by
  refine ⟨FullO55MatrixLaws.eta_sq,
    FullO55MatrixLaws.boost_all_so55,
    FullO55MatrixLaws.lightlikePlus_null,
    FullPin55MatrixLaws.buscherSwapFirst_o55Off,
    FullPin55MatrixLaws.buscherSwapFirst_involutive, ?_⟩
  rcases Clifford.ConformalLift55.conformalNullPair_exists with ⟨P⟩
  exact ⟨P, Clifford.ConformalProjectiveEmbedding55.S_sq P⟩

/-- The explicit Clifford null-pair inversion readback. -/
theorem conformal_null_pair_inversion_packet
    (P : Clifford.ConformalLift55.ConformalNullPair) :
    Clifford.ConformalProjectiveEmbedding55.S P *
        Clifford.ConformalProjectiveEmbedding55.S P = 1 ∧
      Clifford.ConformalProjectiveEmbedding55.S P * P.u *
          Clifford.ConformalProjectiveEmbedding55.S P = P.v ∧
      Clifford.ConformalProjectiveEmbedding55.S P * P.v *
          Clifford.ConformalProjectiveEmbedding55.S P = P.u := by
  exact ⟨Clifford.ConformalProjectiveEmbedding55.S_sq P,
    Clifford.ConformalProjectiveEmbedding55.S_u_S P,
    Clifford.ConformalProjectiveEmbedding55.S_v_S P⟩

/-- Every installed projective `PO(5,5)` closure exposes its null-state packet. -/
theorem projective_owner_packet
    {V W PinConf : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [Monoid PinConf]
    (C : PO55ConformalClosure V W PinConf) :
    (∀ v : V,
      (C.affineState v).1.IsAmbientNullRay C.mobius.ambientQ) ∧
      C.inversionPO55.rep = C.inversion.swap ∧
      SplitQuadratic55.SameRay
        (C.inversion.swap.toLinearEquiv C.nullPair.eMinus)
        C.nullPair.ePlus ∧
      SplitQuadratic55.SameRay
        (C.inversion.swap.toLinearEquiv C.nullPair.ePlus)
        C.nullPair.eMinus := by
  refine ⟨C.affineState_is_null, C.inversionPO55_is_nullSwap,
    C.inversion.maps_minus_to_plus_projectively,
    C.inversion.maps_plus_to_minus_projectively⟩

/--
The cross-owner laws, expressed directly as a conjunction of native
propositions.  This replaces the former proposition-valued evidence record:
each conjunct remains on its original matrix or Clifford carrier, so no
additional carrier identification or marker field is introduced.
-/
def O55CliffordConformalBridgePacket : Prop :=
  FullO55MatrixLaws.eta * FullO55MatrixLaws.eta = 1 ∧
    (∀ i j : Fin 5,
      FullO55MatrixLaws.IsSO55Lie (FullO55MatrixLaws.boost i j)) ∧
    (∀ i : Fin 5,
      FullO55MatrixLaws.etaPair
        (FullO55MatrixLaws.lightlikePlus i)
        (FullO55MatrixLaws.lightlikePlus i) = 0) ∧
    FullPin55MatrixLaws.IsO55Off FullPin55MatrixLaws.buscherSwapFirst ∧
    FullPin55MatrixLaws.buscherSwapFirst *
        FullPin55MatrixLaws.buscherSwapFirst = 1 ∧
    (FullPin55MatrixLaws.buscherSwapFirst.mulVec
          (FullPin55MatrixLaws.basisVec 0) =
        FullPin55MatrixLaws.basisVec 5 ∧
      FullPin55MatrixLaws.buscherSwapFirst.mulVec
          (FullPin55MatrixLaws.basisVec 5) =
        FullPin55MatrixLaws.basisVec 0) ∧
    (∀ P : Clifford.ConformalLift55.ConformalNullPair,
      Clifford.ConformalProjectiveEmbedding55.S P *
          Clifford.ConformalProjectiveEmbedding55.S P = 1 ∧
      Clifford.ConformalProjectiveEmbedding55.S P * P.u *
          Clifford.ConformalProjectiveEmbedding55.S P = P.v ∧
      Clifford.ConformalProjectiveEmbedding55.S P * P.v *
          Clifford.ConformalProjectiveEmbedding55.S P = P.u) ∧
    (∀ (P : Clifford.ConformalLift55.ConformalNullPair)
      (x : Clifford.ConformalLift55.Cl55) (q : ℝ),
      (x * P.u = - P.u * x) →
      (x * P.v = - P.v * x) →
      x * x = q • (1 : Clifford.ConformalLift55.Cl55) →
      Clifford.ConformalProjectiveEmbedding55.F P x q *
          Clifford.ConformalProjectiveEmbedding55.F P x q = 0) ∧
    (∀ (P : Clifford.ConformalLift55.ConformalNullPair)
      (x : Clifford.ConformalLift55.Cl55) (q : ℝ),
      (x * P.u = - P.u * x) →
      (x * P.v = - P.v * x) →
      x * x = q • (1 : Clifford.ConformalLift55.Cl55) →
      q ≠ 0 →
      - (Clifford.ConformalProjectiveEmbedding55.S P *
          Clifford.ConformalProjectiveEmbedding55.F P x q *
          Clifford.ConformalProjectiveEmbedding55.S P) =
        q • Clifford.ConformalProjectiveEmbedding55.F P
          (Clifford.ConformalProjectiveEmbedding55.geoInv x q) (1 / q))

namespace O55CliffordConformalBridgePacket

variable (h : O55CliffordConformalBridgePacket)
include h

theorem diagonal_metric : FullO55MatrixLaws.eta * FullO55MatrixLaws.eta = 1 := h.1
theorem diagonal_boosts :
    ∀ i j : Fin 5, FullO55MatrixLaws.IsSO55Lie (FullO55MatrixLaws.boost i j) := h.2.1
theorem diagonal_nulls :
    ∀ i : Fin 5,
      FullO55MatrixLaws.etaPair (FullO55MatrixLaws.lightlikePlus i)
        (FullO55MatrixLaws.lightlikePlus i) = 0 := h.2.2.1
theorem hyperbolic_swap_isometric :
    FullPin55MatrixLaws.IsO55Off FullPin55MatrixLaws.buscherSwapFirst := h.2.2.2.1
theorem hyperbolic_swap_involutive :
    FullPin55MatrixLaws.buscherSwapFirst * FullPin55MatrixLaws.buscherSwapFirst = 1 :=
  h.2.2.2.2.1
theorem hyperbolic_swap_first_pair :
    FullPin55MatrixLaws.buscherSwapFirst.mulVec (FullPin55MatrixLaws.basisVec 0) =
        FullPin55MatrixLaws.basisVec 5 ∧
      FullPin55MatrixLaws.buscherSwapFirst.mulVec (FullPin55MatrixLaws.basisVec 5) =
        FullPin55MatrixLaws.basisVec 0 := h.2.2.2.2.2.1
theorem clifford_null_swap :
    ∀ P : Clifford.ConformalLift55.ConformalNullPair,
      Clifford.ConformalProjectiveEmbedding55.S P *
          Clifford.ConformalProjectiveEmbedding55.S P = 1 ∧
      Clifford.ConformalProjectiveEmbedding55.S P * P.u *
          Clifford.ConformalProjectiveEmbedding55.S P = P.v ∧
      Clifford.ConformalProjectiveEmbedding55.S P * P.v *
          Clifford.ConformalProjectiveEmbedding55.S P = P.u := h.2.2.2.2.2.2.1
theorem clifford_affine_nullity :
    ∀ (P : Clifford.ConformalLift55.ConformalNullPair)
      (x : Clifford.ConformalLift55.Cl55) (q : ℝ),
      (x * P.u = - P.u * x) → (x * P.v = - P.v * x) →
      x * x = q • (1 : Clifford.ConformalLift55.Cl55) →
      Clifford.ConformalProjectiveEmbedding55.F P x q *
          Clifford.ConformalProjectiveEmbedding55.F P x q = 0 := h.2.2.2.2.2.2.2.1
theorem clifford_inversion_chart :
    ∀ (P : Clifford.ConformalLift55.ConformalNullPair)
      (x : Clifford.ConformalLift55.Cl55) (q : ℝ),
      (x * P.u = - P.u * x) → (x * P.v = - P.v * x) →
      x * x = q • (1 : Clifford.ConformalLift55.Cl55) → q ≠ 0 →
      - (Clifford.ConformalProjectiveEmbedding55.S P *
          Clifford.ConformalProjectiveEmbedding55.F P x q *
          Clifford.ConformalProjectiveEmbedding55.S P) =
        q • Clifford.ConformalProjectiveEmbedding55.F P
          (Clifford.ConformalProjectiveEmbedding55.geoInv x q) (1 / q) :=
  h.2.2.2.2.2.2.2.2

end O55CliffordConformalBridgePacket

theorem installed_bridge_packet : O55CliffordConformalBridgePacket := by
  refine ⟨FullO55MatrixLaws.eta_sq,
    FullO55MatrixLaws.boost_all_so55,
    FullO55MatrixLaws.lightlikePlus_null,
    FullPin55MatrixLaws.buscherSwapFirst_o55Off,
    FullPin55MatrixLaws.buscherSwapFirst_involutive, ?_, ?_, ?_, ?_⟩
  · exact ⟨FullPin55MatrixLaws.buscherSwapFirst_basis_zero,
      FullPin55MatrixLaws.buscherSwapFirst_basis_five⟩
  · intro P
    exact conformal_null_pair_inversion_packet P
  · intro P x q hxu hxv hsq
    exact Clifford.ConformalProjectiveEmbedding55.F_sq_zero P x q hxu hxv hsq
  · intro P x q hxu hxv hsq hq
    exact Clifford.ConformalProjectiveEmbedding55.conformal_inversion_maps_to_geoInv
      P x q hxu hxv hsq hq

end InfoGeometry.OperatorAlgebra.O55ConformalEvidenceBridge
