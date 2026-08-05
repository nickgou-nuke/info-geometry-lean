import InfoGeometry.Physics.Algebra.CuntzToeplitzBraidRepresentation

/-!
# Cuntz projection equivalence: the algebraic K₀ precursor

This owner proves the Murray--von Neumann witnesses and the completeness
relation available from a Cuntz pair.  It deliberately does not identify an
abstract K₀ group or conclude `K₀ = 0`; that requires a K-theory carrier and
its quotient relation.
-/

namespace InfoGeometry.Physics.Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def murrayVonNeumannEquiv (P Q : A) : Prop :=
  ∃ V Vstar : A, Vstar * V = P ∧ V * Vstar = Q

theorem cuntz_projectors_equiv_to_one
    (O2 : CuntzTwoAlgebra A) :
    murrayVonNeumannEquiv (O2.S1 * O2.S1_star) 1 ∧
      murrayVonNeumannEquiv (O2.S2 * O2.S2_star) 1 := by
  constructor
  · exact ⟨O2.S1_star, O2.S1, rfl, O2.hS1_iso⟩
  · exact ⟨O2.S2_star, O2.S2, rfl, O2.hS2_iso⟩

theorem cuntz_projection_completeness
    (O2 : CuntzTwoAlgebra A) :
    (O2.S1 * O2.S1_star) + (O2.S2 * O2.S2_star) = 1 :=
  O2.h_completeness

theorem k0_element_collapse {G : Type*} [AddCommGroup G]
    (x : G) (h : x + x = x) : x = 0 := by
  have h' := congrArg (fun y : G => y - x) h
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h'

theorem cuntz_k0_generator_trivial {G : Type*} [AddCommGroup G]
    (kClass : A → G)
    (h_add : ∀ P Q : A, kClass (P + Q) = kClass P + kClass Q)
    (h_equiv : ∀ P Q : A, murrayVonNeumannEquiv P Q → kClass P = kClass Q)
    (O2 : CuntzTwoAlgebra A) :
    kClass (1 : A) = 0 := by
  have h₁ : kClass (O2.S1 * O2.S1_star) = kClass 1 :=
    h_equiv _ _ (cuntz_projectors_equiv_to_one O2).1
  have h₂ : kClass (O2.S2 * O2.S2_star) = kClass 1 :=
    h_equiv _ _ (cuntz_projectors_equiv_to_one O2).2
  have hsum : kClass 1 =
      kClass ((O2.S1 * O2.S1_star) + (O2.S2 * O2.S2_star)) := by
    rw [O2.h_completeness]
  have hsplit : kClass ((O2.S1 * O2.S1_star) + (O2.S2 * O2.S2_star)) =
      kClass (O2.S1 * O2.S1_star) + kClass (O2.S2 * O2.S2_star) :=
    h_add _ _
  have heq : kClass 1 = kClass 1 + kClass 1 := by
    calc
      kClass 1 = kClass ((O2.S1 * O2.S1_star) +
          (O2.S2 * O2.S2_star)) := hsum
      _ = kClass (O2.S1 * O2.S1_star) +
          kClass (O2.S2 * O2.S2_star) := hsplit
      _ = kClass 1 + kClass 1 := by rw [h₁, h₂]
  exact k0_element_collapse (kClass 1) heq.symm

end InfoGeometry.Physics.Algebra
