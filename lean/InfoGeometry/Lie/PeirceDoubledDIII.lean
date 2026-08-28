import InfoGeometry.CondensedMatter.DIIISuperfluid
import InfoGeometry.Lie.PeirceDoubledComplexStructure

/-!
# Concrete algebraic DIII datum on the doubled Peirce carrier

This owner instantiates only the algebraic DIII symmetry laws.  The BdG
Hamiltonian is the zero endomorphism, so no physical Hamiltonian symmetry is
silently assumed.
-/

namespace InfoGeometry.Lie.PeirceDoubledDIII

open InfoGeometry.CondensedMatter
open InfoGeometry.Lie.PeirceDoubledComplexStructure

abbrev Op := Module.End ℝ DoubledPeirce

def datum : DIIISuperfluidDatum Op where
  Hbdg := 0
  Theta := theta
  Xi := xi
  chi := chi

theorem datum_laws : DIIISuperfluidLaws datum := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Op] using theta_sq
  · simpa [Op] using xi_sq
  · simpa [Op] using chi_sq
  · simp [datum]
  · simp [datum]
  · simp [datum]
  · rfl

end InfoGeometry.Lie.PeirceDoubledDIII
