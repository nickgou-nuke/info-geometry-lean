(* coq/TomitaTakesaki.v *)
Section TomitaTakesakiReflection.

Variable H : Type.
Variable M : Type.
Variable M_commutant : Type.

Variable S : H -> H.
Variable J : H -> H.
Variable DeltaHalf : H -> H.

(* Polar decomposition: S = J Delta^{1/2} *)
Axiom polar_decomposition : forall x : H, S x = J (DeltaHalf x).

(* J is an involution *)
Axiom J_involution : forall x : H, J (J x) = x.

Variable J_action : M -> M_commutant.

(* Modular conjugation J M J = M' *)
Axiom modular_conjugation : forall m' : M_commutant, exists m : M, J_action m = m'.

End TomitaTakesakiReflection.
