theory KleinOrbifoldResolution
  imports Main
begin

(* Topological blow-up procedure resolving the fixed points of Klein Orbifolds *)

typedecl point
typedecl manifold

consts
  (* The V4 action on the manifold *)
  action :: "manifold ⇒ point ⇒ point"
  (* The set of singular fixed points on the orbifold *)
  fixed_points :: "manifold ⇒ point set"
  (* The topological blow-up procedure resolving singularities *)
  blow_up :: "manifold ⇒ manifold"

axiomatization where
  (* The resolution procedure topologically alters the space around the fixed points *)
  resolution_property: "∀p ∈ fixed_points M. ∃neighborhood. blow_up M ≠ M"
  
theorem topological_resolution:
  "fixed_points (blow_up M) = {}"
  sorry

end
