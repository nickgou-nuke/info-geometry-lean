import InfoGeometry.External.Auto.ExceptionalNonorientableTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Non-orientable braid charge compatibility layer

This integrates the external Klein/RP² braid-word helpers into the active
`ExceptionalNonorientableTopology` framework.  The results are group-word and
abelianization facts, not a full classification theorem.
-/

noncomputable section

namespace NonOrientableBraid

variable {B : Type} [Group B]

/-- External notation for the Klein-bottle braid charge word. -/
def klein_bottle_charge (Bx By : B) : B :=
  Bx * By * Bx * By⁻¹

/-- External notation for the projective-plane charge word. -/
def rp2_charge (X : B) : B := X * X

/-- In the abelian limit, the external Klein word accumulates as `Bx²`. -/
theorem abelian_klein_accumulation (Bx By : B) (h_comm : Commute Bx By) :
    klein_bottle_charge Bx By = Bx * Bx := by
  unfold klein_bottle_charge
  calc
    Bx * By * Bx * By⁻¹ = Bx * (By * Bx) * By⁻¹ := by group
    _ = Bx * (Bx * By) * By⁻¹ := by rw [h_comm.eq]
    _ = Bx * Bx := by group

/-- The projective-plane charge is the active `rpWord`. -/
theorem rp2_charge_eq_active (X : B) :
    rp2_charge X = ExceptionalNonorientableTopology.rpWord X := rfl

/-- The active Klein word has the related `q p q⁻¹ p` convention. -/
theorem active_klein_word_def (q p : B) :
    ExceptionalNonorientableTopology.kleinWord q p = q * p * q⁻¹ * p := rfl

/-- Additive abelianization recovers the active two-band torsion consequence. -/
theorem twoBand_klein_abelian_vanishes {Aq Ap : ℤ}
    (h : ExceptionalNonorientableTopology.kleinAbelianWord Aq Ap = 0) : Ap = 0 :=
  ExceptionalNonorientableTopology.twoBand_klein_gapped_vanishes h

end NonOrientableBraid
