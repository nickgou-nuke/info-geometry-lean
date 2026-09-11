/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2AdmissibleBasisPrefix
import InfoGeometry.Algebra.Zorn.G2AdmissibleBasisCoordinateConstraints

/-!
# Canonical Peirce Fibration of Admissible 7-Bases

This file implements the finite algebraic "spine" of the admissible basis
carrier using the Peirce decomposition relative to the idempotent prefix.

The owner exposes a verified dependent-sum coding map:

  AdmissibleBasis7Carrier ↪ Σ(p : NontrivialIdempotent), Σ(x : PeircePlusFiber p), ResidualFiber(p, x)

Stage 1: The idempotent prefix `p` (Kasimir/Cartan coordinate)
Stage 2: The positive Peirce vector `x` (square-zero, eigenvalue 1 under p)
Stage 3: The residual fiber (remaining coordinates)

Residual-fiber cardinalities and the numerical upper bound remain separate
theorems and are not asserted here.
-/

namespace InfoGeometry.Algebra.Zorn.G2PeirceFibration

open _root_.InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-- Stage 3: The residual fiber over a fixed Peirce pair (p, x).

    This consists of all admissible bases whose first prefix is exactly `p`
    and whose second prefix is exactly `x`. The remaining coordinates
    (positions 2-6 of the basis) parameterize this fiber.

    We compare the underlying `NonzeroSquareZero` values (which don't depend
    on `p`) rather than the full `PeircePlusFiber` values (which do depend
    on `p`). This avoids heterogeneous equality issues. -/
def ResidualFiber
    (p : NontrivialIdempotent)
    (x : PeircePlusFiber p) :=
  { v : AdmissibleBasis7Carrier //
    admissibleBasis7_first_prefix_code v = p ∧
    (admissibleBasis7Second v).1 = x.1 }

/-- The canonical Peirce fibration embedding.

    Every admissible basis maps to its idempotent prefix, its PeircePlus
    second coordinate, and its residual fiber. -/
def peirceFibrationEmbedding
    (v : AdmissibleBasis7Carrier) :
    Σ (p : NontrivialIdempotent), Σ (x : PeircePlusFiber p), ResidualFiber p x :=
  ⟨admissibleBasis7_first_prefix_code v,
   admissibleBasis7Second v,
   ⟨v, ⟨rfl, rfl⟩⟩⟩

/-- The Peirce fibration embedding is injective.

    Two admissible bases with identical idempotent prefix, identical
    PeircePlus second coordinate, and identical residual fiber are equal. -/
theorem peirceFibrationEmbedding_injective :
    Function.Injective peirceFibrationEmbedding := by
  intro v1 v2 h
  exact congrArg (fun z => z.2.2.1) h

/-! The dependent-sum target is not merely an upper-bound code.  Its
    residual-fiber witness contains the original admissible basis, so the
    fibration map is an actual equivalence. -/

noncomputable def peirceFibrationEquiv :
    AdmissibleBasis7Carrier ≃
      Σ (p : NontrivialIdempotent),
        Σ (x : PeircePlusFiber p), ResidualFiber p x := by
  apply Equiv.ofBijective peirceFibrationEmbedding
  constructor
  · exact peirceFibrationEmbedding_injective
  · intro z
    rcases z with ⟨p, x, v⟩
    rcases v with ⟨v, hv⟩
    rcases hv with ⟨hp, hx⟩
    refine ⟨v, ?_⟩
    dsimp [peirceFibrationEmbedding]
    have hp' : admissibleBasis7_first_prefix_code v = p := hp
    apply Sigma.ext
    · exact hp'
    · cases hp'
      have hx' : admissibleBasis7Second v = x := by
        apply Subtype.ext
        exact hx
      apply heq_of_eq
      apply Sigma.ext
      · exact hx'
      · cases hx'
        rfl

def residualCoordinates (v : AdmissibleBasis7Carrier) :
    SplitOctF2 × SplitOctF2 × SplitOctF2 × SplitOctF2 × SplitOctF2 :=
  (basisPrefix3 v, basisPrefix4 v, basisPrefix5 v, basisPrefix6 v, basisPrefix7 v)

theorem admissibleBasis7_eq_of_prefixes
    (v w : AdmissibleBasis7Carrier)
    (h₁ : basisPrefix1 v = basisPrefix1 w)
    (h₂ : basisPrefix2 v = basisPrefix2 w)
    (hr : residualCoordinates v = residualCoordinates w) :
    v = w := by
  apply basisCoordinates_injective
  funext i
  change basisCoordinates v i = basisCoordinates w i
  have h₃ := congrArg (fun z => z.1) hr
  have h₄ := congrArg (fun z => z.2.1) hr
  have h₅ := congrArg (fun z => z.2.2.1) hr
  have h₆ := congrArg (fun z => z.2.2.2.1) hr
  have h₇ := congrArg (fun z => z.2.2.2.2) hr
  fin_cases i
  · simpa [basisPrefix1] using h₁
  · simpa [basisPrefix2] using h₂
  · simpa [basisPrefix3] using h₃
  · simpa [basisPrefix4] using h₄
  · simpa [basisPrefix5] using h₅
  · simpa [basisPrefix6] using h₆
  · simpa [basisPrefix7] using h₇

theorem residualCoordinates_injective_on_fiber
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    (v w : ResidualFiber p x)
    (h₁ : residualCoordinates v.1 = residualCoordinates w.1) :
    v = w := by
  apply Subtype.ext
  apply admissibleBasis7_eq_of_prefixes v.1 w.1
  · exact congrArg Subtype.val v.2.1 |>.trans (congrArg Subtype.val w.2.1).symm
  · exact congrArg Subtype.val v.2.2 |>.trans (congrArg Subtype.val w.2.2).symm
  · exact h₁

theorem residualFiber_card_le_coordinate_product
    {p : NontrivialIdempotent} {x : PeircePlusFiber p}
    [Fintype (ResidualFiber p x)] :
    Fintype.card (ResidualFiber p x) ≤
      Fintype.card
        (SplitOctF2 × SplitOctF2 × SplitOctF2 × SplitOctF2 × SplitOctF2) := by
  apply Fintype.card_le_of_injective
    (fun v : ResidualFiber p x => residualCoordinates v.1)
  intro v w h
  exact residualCoordinates_injective_on_fiber v w h

/-! The residual tuple can also be exposed directly as a dependent-sum code.
    This records the actual five remaining basis coordinates; it does not
    identify them with a PC normal form or assert a cardinality bound. -/

def peirceFibrationResidualCode
    (v : AdmissibleBasis7Carrier) :
    Σ (p : NontrivialIdempotent),
      Σ (_ : PeircePlusFiber p),
        SplitOctF2 × SplitOctF2 × SplitOctF2 × SplitOctF2 × SplitOctF2 :=
  ⟨admissibleBasis7_first_prefix_code v,
    admissibleBasis7Second v,
    residualCoordinates v⟩

theorem peirceFibrationResidualCode_injective :
    Function.Injective peirceFibrationResidualCode := by
  intro v w h
  apply admissibleBasis7_eq_of_prefixes v w
  · exact congrArg (fun z => z.1.1) h
  · simpa [peirceFibrationResidualCode, admissibleBasis7Second,
      admissibleBasis7_second_prefix_code] using
      congrArg (fun z => z.2.1.1.1) h
  · exact congrArg (fun z => z.2.2) h

end InfoGeometry.Algebra.Zorn.G2PeirceFibration
