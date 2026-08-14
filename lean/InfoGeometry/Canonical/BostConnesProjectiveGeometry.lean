import InfoGeometry.Canonical.BostConnesGalois
import InfoGeometry.Quantum.FibonacciFusionCategory

/-!
# Algebraic Galois and Fibonacci readouts

This file records a golden-ratio identity, transport of supplied cyclotomic
generators by supplied Galois automorphisms, and the corresponding scalar
Fibonacci inequalities. It does not construct a phase transition, a boundary
ray space, or a quantum-capacity theorem.
-/

set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.BostConnesProjectiveGeometry

open BostConnesGalois
open FibonacciFusion

/-! ### 1. Golden Ratio as Projective Invariant -/

/--
The constant `phi` satisfies its defining quadratic identity and the bounds
`1 < phi < 2`.
-/
theorem golden_ratio_projective_invariant :
    phi = (1 + Real.sqrt 5) / 2 ∧ phi ^ 2 = phi + 1 ∧ phi > 1 ∧ phi < 2 := by
  have hsqrt : Real.sqrt 5 < 3 := by
    calc
      Real.sqrt 5 < Real.sqrt 9 :=
        Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5) (by norm_num : (5 : ℝ) < 9)
      _ = 3 := by norm_num
  have hphi_lt2 : phi < 2 := by
    change (1 + Real.sqrt 5) / 2 < 2
    nlinarith
  refine ⟨rfl, phi_sq, phi_gt_one, hphi_lt2⟩

/-! ### 2. Galois Transport of Cyclotomic Generator Values -/

/--
Transport of a supplied cyclotomic generator under a supplied Galois
automorphism.
-/
theorem galois_transport_of_generator
    {C_comm : Type u} [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    (e_rep : GroupElementRepresentation C_comm)
    {G : Type u} [GaloisActionData G]
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep)
    (g : G) (r : ℚ) :
    galoisAut.galoisAut g (e_rep.e r) = e_rep.e (GaloisActionData.actOnQ g r) :=
  galoisAut.galoisAut_on_generator g r

/--
The transported generator inherits the supplied period-one relation.
-/
theorem galois_preserves_periodicity
    {C_comm : Type u} [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    (e_rep : GroupElementRepresentation C_comm)
    {G : Type u} [GaloisActionData G]
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep)
    (g : G) (r : ℚ) :
    galoisAut.galoisAut g (e_rep.e (r + 1)) = galoisAut.galoisAut g (e_rep.e r) := by
  rw [galois_transport_of_generator e_rep galoisAut g (r + 1),
    galois_transport_of_generator e_rep galoisAut g r]
  have h_periodic : GaloisActionData.actOnQ g (r + 1) = GaloisActionData.actOnQ g r + 1 :=
    GaloisActionData.actOnQ_periodic g r
  rw [h_periodic]
  -- e(actOnQ g r + 1) = e(actOnQ g r) by the periodicity of e
  rw [e_rep.e_periodic (GaloisActionData.actOnQ g r)]

/-! ### 3. Fibonacci Dimension at the Bost-Connes Boundary -/

/--
The Fibonacci scalar `phi` satisfies its defining quadratic equation and the
bounds `1 < phi < 2`.
-/
theorem fibonacci_quantum_dimension_at_boundary :
    let tau_dim := phi
    tau_dim ^ 2 = tau_dim + 1 ∧ 1 < tau_dim ∧ tau_dim < 2 := by
  intro tau_dim
  have hsqrt : Real.sqrt 5 < 3 := by
    calc
      Real.sqrt 5 < Real.sqrt 9 :=
        Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5) (by norm_num : (5 : ℝ) < 9)
      _ = 3 := by norm_num
  have htau_lt2 : phi < 2 := by
    change (1 + Real.sqrt 5) / 2 < 2
    nlinarith
  refine ⟨phi_sq, phi_gt_one, htau_lt2⟩

end InfoGeometry.Canonical.BostConnesProjectiveGeometry
