import InfoGeometry.Canonical.SouriauHodgeTriadBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Axiomatic Audit of SouriauHodgeTriadBridge

This audit checks the foundational axioms of the SouriauHodgeTriadBridge module.
Expected axioms: [propext, Classical.choice, Quot.sound].
-/

#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.souriau_hodge_triad_synthesis
#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.dilaton_preserves_exact
#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.dilaton_preserves_coexact
#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.dilaton_preserves_harmonic
#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.dilaton_commutes_dirac
#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.dilaton_commutes_laplacian
#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.dilaton_commutes_bdgKinetic
#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.dilaton_commutes_bdgMass
#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.diracKaehler_is_krein_isometry
#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.dirac_transmutes_irrotational_to_rotational
#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.dirac_transmutes_rotational_to_irrotational
#print axioms InfoGeometry.Canonical.SouriauHodgeTriad.harmonic_variation_is_purely_exact
