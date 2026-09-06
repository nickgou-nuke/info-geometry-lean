/-
InfoGeometry/OperatorAlgebra/TwistedSpectralTripleLeibniz.lean

The algebraic core of a twisted spectral triple.

The twisted commutator is a sigma-derivation.  This owner deliberately stops
at that exact operator identity; Krein signatures, K-morphisms, and geometric
signature change require separate concrete data.
-/

import InfoGeometry.OperatorAlgebra.SpectralTriple

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TwistedSpectralTripleLeibniz

open InfoGeometry.OperatorAlgebra.SpectralTriple

variable {A H : Type*}
variable [Ring A]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The represented twisted commutator `[D, a]_σ = Dρ(a) - ρ(σ(a))D`. -/
def twistedCommutator
    (D : EndR H) (ρ : RepresentedAlgebra A H)
    (σ : A →+* A) (a : A) : EndR H :=
  D.comp (ρ.rep a) - (ρ.rep (σ a)).comp D

/-- The twisted Leibniz rule for the represented twisted commutator. -/
theorem twistedCommutator_mul
    (D : EndR H) (ρ : RepresentedAlgebra A H)
    (σ : A →+* A) (a b : A) :
    twistedCommutator D ρ σ (a * b) =
      (twistedCommutator D ρ σ a).comp (ρ.rep b) +
        (ρ.rep (σ a)).comp (twistedCommutator D ρ σ b) := by
  ext x
  simp [twistedCommutator]

/-- The ordinary commutator is the trivial-twist specialization. -/
theorem twistedCommutator_one
    (D : EndR H) (ρ : RepresentedAlgebra A H) (a : A) :
    twistedCommutator D ρ (RingHom.id A) a =
      commutator D (ρ.rep a) := by
  rfl

end InfoGeometry.OperatorAlgebra.TwistedSpectralTripleLeibniz
