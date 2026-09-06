import Mathlib.Tactic
import InfoGeometry.External.Auto.InfinityFilteredColimits
import InfoGeometry.External.Auto.LieAlgebraColimit

open CategoryTheory
open CategoryTheory.Limits
open SSet
open Opposite
open InfoGeometry.Quantum.LieColimit

universe u

section AnomalyWiring

variable {J : Type u} [Category.{u} J] [IsFiltered J]
variable (F : J ⥤ SSet.{u}) (c : SSet.{u})

/--
The `central_charge_cancellation` survives the topological limit of an ∞-category filtered colimit.
Because the boundary is just another mapping space `c ⟶ colimit F`, the doubled-Krein
pattern directly enforces the vanishing of the cocycle here.
-/
theorem boundary_anomaly_cancellation
    (C : KreinCentralCocycle (c ⟶ colimit F))
    (x : c ⟶ colimit F) :
    C.charge x = 0 :=
  central_charge_cancellation C x

/--
Because mapping spaces commute with colimits for compact objects (Rozenblyum's Lemma),
the vanishing of the anomaly on the colimit of finite stages canonically lifts to the
∞-categorical boundary mapping space `c ⟶ colimit F`.
-/
theorem lifted_anomaly_cancellation
    [IsFinitelyPresentable c] [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op c))]
    (C : KreinCentralCocycle (colimit (F ⋙ coyoneda.obj (op c))))
    (x : c ⟶ colimit F) :
    C.charge ((rozenblyum_mapping_space_commutes_colimit F c).hom x) = 0 :=
  central_charge_cancellation C ((rozenblyum_mapping_space_commutes_colimit F c).hom x)

/--
We can also push forward an anomaly cocycle defined on the boundary mapping space
to the algebraic colimit of finite stages via the Rozenblyum isomorphism's inverse.
-/
theorem pushed_anomaly_cancellation
    [IsFinitelyPresentable c] [HasColimit F] [HasColimit (F ⋙ coyoneda.obj (op c))]
    (C : KreinCentralCocycle (c ⟶ colimit F))
    (y : colimit (F ⋙ coyoneda.obj (op c))) :
    C.charge ((rozenblyum_mapping_space_commutes_colimit F c).inv y) = 0 :=
  central_charge_cancellation C ((rozenblyum_mapping_space_commutes_colimit F c).inv y)

end AnomalyWiring
