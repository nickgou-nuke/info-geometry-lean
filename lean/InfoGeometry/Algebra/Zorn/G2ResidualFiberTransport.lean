import InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints

namespace InfoGeometry.Algebra.Zorn.G2ResidualFiberTransport

open _root_.InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2PeirceFibration
open InfoGeometry.Algebra.Zorn.G2FixedPrefixResidualConstraints

noncomputable def transportAutomorphism
    (v : AdmissibleBasis7Carrier) : SplitOctF2Aut :=
  admissibleBasis7Equiv.symm v

@[simp] theorem transportAutomorphism_inv_maps_firstPrefix
    (v : AdmissibleBasis7Carrier) :
    (transportAutomorphism v)⁻¹.1
        (admissibleBasis7_first_prefix_code v).1 = ePlus := by
  rw [admissibleBasis7_first_prefix_code_value v]
  rw [← admissibleBasis7Equiv_symm_maps_ePlus v]
  exact (transportAutomorphism v).1.left_inv ePlus

@[simp] theorem transportAutomorphism_inv_maps_secondPrefix
    (v : AdmissibleBasis7Carrier) :
    (transportAutomorphism v)⁻¹.1
        (admissibleBasis7Second v).1.1 = up0 := by
  change (transportAutomorphism v)⁻¹.1 (basisPrefix2 v) = up0
  rw [← admissibleBasis7Equiv_symm_maps_up0 v]
  exact (transportAutomorphism v).1.left_inv up0

noncomputable def occurringResidualFiberEquivCanonical
    (v : AdmissibleBasis7Carrier) :
    ResidualFiber
        (admissibleBasis7_first_prefix_code v)
        (admissibleBasis7Second v) ≃
      ResidualFiber canonicalP canonicalX where
  toFun w := by
    let w' := admissibleBasis7ActionCarrier (transportAutomorphism v)⁻¹ w.1
    refine ⟨w', ?_⟩
    constructor
    · apply Subtype.ext
      change basisPrefix1 w' = ePlus
      change basisPrefix1
        (admissibleBasis7ActionCarrier (transportAutomorphism v)⁻¹ w.1) = ePlus
      rw [admissibleBasis7ActionCarrier_firstPrefix]
      have hw : basisPrefix1 w.1 = basisPrefix1 v := by
        simpa [admissibleBasis7_first_prefix_code_value] using
          congrArg Subtype.val w.2.1
      rw [hw]
      rw [← admissibleBasis7Equiv_symm_maps_ePlus v]
      exact (transportAutomorphism v).1.left_inv _
    · apply Subtype.ext
      change basisPrefix2 w' = canonicalX.1.1
      change basisPrefix2
        (admissibleBasis7ActionCarrier (transportAutomorphism v)⁻¹ w.1) = canonicalX.1.1
      rw [admissibleBasis7ActionCarrier_secondPrefix]
      have hw : basisPrefix2 w.1 = basisPrefix2 v := by
        simpa [admissibleBasis7_second_prefix_code] using congrArg Subtype.val w.2.2
      rw [hw]
      rw [← admissibleBasis7Equiv_symm_maps_up0 v]
      exact (transportAutomorphism v).1.left_inv _
  invFun w := by
    let w' := admissibleBasis7ActionCarrier (transportAutomorphism v) w.1
    refine ⟨w', ?_⟩
    constructor
    · apply Subtype.ext
      change basisPrefix1 w' =
        (admissibleBasis7_first_prefix_code v).1
      change basisPrefix1
        (admissibleBasis7ActionCarrier (transportAutomorphism v) w.1) =
          (admissibleBasis7_first_prefix_code v).1
      rw [admissibleBasis7ActionCarrier_firstPrefix]
      change (transportAutomorphism v).1 (basisPrefix1 w.1) = basisPrefix1 v
      have hw : basisPrefix1 w.1 = ePlus := by
        have h := congrArg Subtype.val w.2.1
        simpa [canonicalP] using h
      rw [hw]
      change (admissibleBasis7Equiv.symm v).1 ePlus = basisPrefix1 v
      rw [admissibleBasis7Equiv_symm_maps_ePlus v]
    · apply Subtype.ext
      change basisPrefix2 w' =
        (admissibleBasis7Second v).1.1
      change basisPrefix2
        (admissibleBasis7ActionCarrier (transportAutomorphism v) w.1) =
          (admissibleBasis7Second v).1.1
      rw [admissibleBasis7ActionCarrier_secondPrefix]
      change (transportAutomorphism v).1 (basisPrefix2 w.1) = basisPrefix2 v
      have hw : basisPrefix2 w.1 = up0 := by
        have h := congrArg Subtype.val w.2.2
        simpa [canonicalX, canonicalP, admissibleBasis7_second_prefix_code] using h
      rw [hw]
      change (admissibleBasis7Equiv.symm v).1 up0 = basisPrefix2 v
      rw [admissibleBasis7Equiv_symm_maps_up0 v]
  left_inv w := by
    dsimp
    apply Subtype.ext
    simpa [inv_inv] using
      (admissibleBasis7ActionCarrier_inv
        (transportAutomorphism v)⁻¹ w.1)
  right_inv w := by
    dsimp
    apply Subtype.ext
    simpa using
      (admissibleBasis7ActionCarrier_inv
        (transportAutomorphism v) w.1)

theorem occurringResidualFiber_card_le_64
    (v : AdmissibleBasis7Carrier) :
    Fintype.card
        (ResidualFiber
          (admissibleBasis7_first_prefix_code v)
          (admissibleBasis7Second v)) ≤ 64 := by
  rw [Fintype.card_congr (occurringResidualFiberEquivCanonical v)]
  exact residualFiber_card_le_64_of_ePlus
    (p := canonicalP) (x := canonicalX) canonicalP_value

end InfoGeometry.Algebra.Zorn.G2ResidualFiberTransport
