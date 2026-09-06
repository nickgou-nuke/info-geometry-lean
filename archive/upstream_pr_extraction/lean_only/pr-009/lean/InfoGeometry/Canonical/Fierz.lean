import InfoGeometry.Quantum.Fierz

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

/-- Theorem `majoranaBelief_iff_zeroArea`. -/
theorem majoranaBelief_iff_zeroArea (ψ : Krein.DoubledSpace E) :
    IsMajoranaBelief (E := E) ψ ↔ infoArea (E := E) ψ = 0 := Iff.rfl

end InfoGeometry.Canonical.Fierz
