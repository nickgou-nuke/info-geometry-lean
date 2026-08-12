import InfoGeometry.Canonical.KleinMonodromyRepresentationSpace
import InfoGeometry.Canonical.HestenesKreinCPTColimitContinuation
import InfoGeometry.Clifford.Cl55WittPinKernelEvidence
import InfoGeometry.Topology.KleinBerryPhase

/-!
# Global CPT/Pin/Klein two-cycle readout

This owner composes existing kernel-checked finite and categorical laws.  It
does not identify a generic mapping torus with a topological Klein bottle;
the operator-level descent is represented by the Klein monodromy relation,
the Pin central kernel law, and the two-sided categorical colimit/limit laws.
-/

noncomputable section

universe u

namespace InfoGeometry.Physics.CPTGlobalPinKleinDescent

open InfoGeometry.Canonical.KleinMonodromyRepresentationSpace
open InfoGeometry.Clifford.Clifford55
open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological

theorem klein_monodromy_reverse_two_cycle
    {G : Type*} [Group G] (rho : KleinMonodromyPair G) :
    rho.a * rho.b⁻¹ * rho.a⁻¹ = rho.b :=
  rho.two_cycle_on_b

theorem pin_central_two_cycle_is_trivial :
    pinTwistedOrthogonalAction negOnePin = 1 :=
  pinTwistedOrthogonalAction_negOnePin

theorem classical_klein_two_cycle_holonomy :
    InfoGeometry.Topology.BraidMatrix *
        InfoGeometry.Topology.TwistedBraidMatrix = 1 :=
  InfoGeometry.Topology.klein_holonomy_eq_one

theorem direct_colimit_cpt_two_cycle
    {J : Type u} [Category.{u, u} J]
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    (topologicalDirectColimitIso w).hom ≫
        (topologicalDirectColimitIso w).inv = 𝟙 _ := by
  exact InfoGeometry.Canonical.hestenesKrein_cpt_directColimit_two_cycle w

theorem inverse_limit_cpt_two_cycle
    {J : Type u} [Category.{u, u} J]
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    (topologicalInverseLimitIso w).hom ≫
        (topologicalInverseLimitIso w).inv = 𝟙 _ := by
  exact InfoGeometry.Canonical.hestenesKrein_cpt_inverseLimit_two_cycle w

end InfoGeometry.Physics.CPTGlobalPinKleinDescent
