import InfoGeometry.Quantum.Fierz
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.Fierz

Canonical facade for informational Fierz identities on doubled states.
-/

namespace InfoGeometry.Canonical.Fierz

export InfoGeometry.Quantum.Fierz (
  infoScalar
  infoSymplectic
  infoHilbert
  infoArea
  information_fierz_identity
  IsMajoranaBelief
  information_fierz_majorana
)

open InfoGeometry.Quantum.Fierz
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end InfoGeometry.Canonical.Fierz
