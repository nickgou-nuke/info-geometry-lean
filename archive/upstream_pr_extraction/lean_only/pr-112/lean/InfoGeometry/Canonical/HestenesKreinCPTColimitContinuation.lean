import InfoGeometry.Krein.HestenesModularKMSBridge
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Hestenes--Krein CPT continuation through categorical limits

This owner keeps the Hestenes--Krein bilingual carrier and the categorical
continuation layer separate.  The former supplies the real phase-axis/
K-linear readout; the latter transports a genuine natural isomorphism through
the native `TopCat` direct colimit and inverse limit.  No analytic Hilbert
bimodule, mapping-torus topology, or supplied Morita law is introduced here.

The two-cycle statements below are consequences of the categorical inverse
of a natural isomorphism.  They are the continuation-level analogue of a CPT
transport followed by its reverse transport.
-/

noncomputable section

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological

universe u

@[simp]
theorem hestenesKrein_cpt_directColimit_two_cycle
    {J : Type u} [Category.{u, u} J]
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    (topologicalDirectColimitIso w).hom ≫
        (topologicalDirectColimitIso w).inv = 𝟙 _ := by
  exact Iso.hom_inv_id _

@[simp]
theorem hestenesKrein_cpt_inverseLimit_two_cycle
    {J : Type u} [Category.{u, u} J]
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) :
    (topologicalInverseLimitIso w).hom ≫
        (topologicalInverseLimitIso w).inv = 𝟙 _ := by
  exact Iso.hom_inv_id _

theorem hestenesKrein_cpt_directColimit_transport_apply
    {J : Type u} [Category.{u, u} J]
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G) (j : J)
    (x : F.obj j) :
    (topologicalDirectColimitIso w).hom
        (colimit.ι F j x) =
      colimit.ι G j (w.hom.app j x) := by
  exact topologicalDirectColimitIso_hom_stage_apply w j x

theorem hestenesKrein_cpt_inverseLimit_transport_apply
    {J : Type u} [Category.{u, u} J]
    {F G : J ⥤ TopCat.{u}} (w : F ≅ G)
    (j : J) (x : TopCat.carrier (limit F)) :
    limit.π G j ((topologicalInverseLimitIso w).hom x) =
      w.hom.app j (limit.π F j x) := by
  exact topologicalInverseLimitIso_hom_projection_apply w j x

end InfoGeometry.Canonical
