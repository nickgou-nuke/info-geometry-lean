import InfoGeometry.CondensedMatter.DIIISuperfluid
import InfoGeometry.Lie.PeirceDoubledComplexStructure

/-!
# Concrete algebraic DIII datum on the doubled Peirce carrier

This owner instantiates only the algebraic DIII symmetry laws.  The BdG
Hamiltonian is the zero endomorphism, so no physical Hamiltonian symmetry is
silently assumed.
-/

namespace InfoGeometry.Lie.PeirceDoubledDIII

open InfoGeometry.CondensedMatter.DIIISuperfluid
open InfoGeometry.Lie.PeirceDoubledComplexStructure

abbrev Op := Module.End ℝ DoubledPeirce

def datum : DIIISuperfluidDatum Op where
  Hbdg := 0
  Theta := theta
  Xi := xi
  chi := chi
  Theta_square := by simpa [Op] using theta_sq
  Xi_square := by simpa [Op] using xi_sq
  chi_square := by simpa [Op] using chi_sq
  time_reversal_symmetry := by simp
  particle_hole_symmetry := by simp
  chiral_symmetry := by simp
  chiral_is_phase_corrected_product := by rfl

end InfoGeometry.Lie.PeirceDoubledDIII
