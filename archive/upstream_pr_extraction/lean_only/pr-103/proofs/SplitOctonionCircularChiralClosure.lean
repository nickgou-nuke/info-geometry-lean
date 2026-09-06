import proofs.SplitOctonionChiralClosure

noncomputable section
namespace SplitOctonionCircularChiralClosure

open SplitOctonionChiralClosure

abbrev Zorn := SplitOctonionChiralClosure.Zorn
abbrev Vec3 := SplitOctonionChiralClosure.Vec3

/-- Canonical circular/Peirce basis over the existing Zorn carrier. -/
abbrev uP : Zorn := uPlus
abbrev uM : Zorn := uMinus
abbrev sP (u : Vec3) : Zorn := sigmaPlus u
abbrev sM (u : Vec3) : Zorn := sigmaMinus u
abbrev parity : Zorn := kreinParity
abbrev unit : Zorn := one

 theorem peirce_circular_basis :
    add uP uM = unit ∧
    parity = ell ∧
    smul (1 / 2) (add unit ell) = uP ∧
    smul (1 / 2) (sub unit ell) = uM := by
  exact ⟨projector_sum, projector_difference,
    cartan_circular_projectors.1, cartan_circular_projectors.2⟩

 theorem complete_circular_products (u v : Vec3) :
    mul (sP u) (sP v) = sM (cross u v) ∧
    mul (sM u) (sM v) = sP (fun i => -cross u v i) ∧
    mul (sP u) (sM v) = smul (dot u v) uP ∧
    mul (sM v) (sP u) = smul (dot v u) uM := by
  exact ⟨plus_plus_product u v, minus_minus_product u v,
    plus_minus_product u v, minus_plus_product u v⟩

 theorem complete_circular_brackets (u v : Vec3) :
    comm (sP u) (sP v) = smul 2 (sM (cross u v)) ∧
    comm (sM u) (sM v) = smul (-2) (sP (cross u v)) ∧
    comm (sP u) (sM v) = smul (dot u v) parity ∧
    antiComm (sP u) (sP v) = zero ∧
    antiComm (sM u) (sM v) = zero ∧
    antiComm (sP u) (sM v) = smul (dot u v) unit := by
  exact ⟨plus_plus_comm u v, minus_minus_comm u v, mixed_comm u v,
    plus_plus_anti u v, minus_minus_anti u v, mixed_anti u v⟩

 theorem raw_jacobi_obstruction :
    add (add
      (comm (sP (axis 0)) (comm (sP (axis 1)) (sM (axis 0))))
      (comm (sP (axis 1)) (comm (sM (axis 0)) (sP (axis 0)))))
      (comm (sM (axis 0)) (comm (sP (axis 0)) (sP (axis 1)))) =
        smul 6 (sP (axis 1)) :=
  raw_commutator_jacobi_defect

 theorem circular_closure_synthesis :
    (∀ u v, comm (sP u) (sP v) = smul 2 (sM (cross u v))) ∧
    (∀ u v, antiComm (sP u) (sP v) = zero) ∧
    (∀ u v, comm (sM u) (sM v) = smul (-2) (sP (cross u v))) ∧
    (∀ u v, antiComm (sM u) (sM v) = zero) ∧
    (∀ u v, antiComm (sP u) (sM v) = smul (dot u v) unit) ∧
    (∀ u v, comm (sP u) (sM v) = smul (dot u v) parity) ∧
    add uP uM = unit ∧ parity = ell := by
  exact ⟨plus_plus_comm, plus_plus_anti, minus_minus_comm,
    minus_minus_anti, mixed_anti, mixed_comm, projector_sum,
    projector_difference⟩

end SplitOctonionCircularChiralClosure
end noncomputable section
