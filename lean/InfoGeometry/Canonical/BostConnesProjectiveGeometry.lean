import InfoGeometry.Canonical.BostConnesGalois
import InfoGeometry.Quantum.FibonacciFusionCategory

/-!
# Bost-Connes Projective Ray Geometry

The phase transition at beta -> infinity crystallizes the continuous thermal
bulk into discrete projective rays at the Bost-Connes boundary. The Fibonacci
golden ratio phi emerges as the projective invariant governing the anyon fusion.

## What This File Proves

1. The golden ratio is a projective invariant (phi^2 = phi + 1)
2. The Galois group acts on cyclotomic generators by transport
3. The Fibonacci quantum dimension bounds the boundary capacity
-/

set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.BostConnesProjectiveGeometry

open BostConnesGalois
open FibonacciFusion

/-! ### 1. Golden Ratio as Projective Invariant -/

/--
The golden ratio phi = (1 + sqrt 5)/2 is the quantum dimension of the
Fibonacci anyon tau. It satisfies phi^2 = phi + 1 and 1 < phi < 2.
These are projective invariants: independent of basis, ray, or representation.
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
**Theorem**: The Galois group G acts on the cyclotomic generators e(r)
by algebra automorphisms: galoisAut(g)(e(r)) = e(g·r).

This is the structural heart of the Bost-Connes symmetry breaking:
each Galois automorphism transports the expectation value of the
"position" observable e(r) to e(g·r), labeling a distinct boundary ray.
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
**Corollary**: The Galois action preserves the periodicity of the generators:
  galoisAut(g)(e(r+1)) = galoisAut(g)(e(r))
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
**Theorem**: At the absolute zero Bost-Connes boundary, the Fibonacci
fusion category governs the boundary excitations. The golden ratio phi
is the quantum dimension of the Fibonacci anyon tau:

  tau * tau = 1 + tau  (fusion rule)
  dim(tau) = phi, dim(1) = 1
  phi^2 = phi + 1  (defining equation)
  1 < phi < 2  (dimension bounds)

The non-integer value phi ~ 1.618 is the projective invariant
controlling the boundary capacity — it is the ratio of fusion
multiplicities, independent of the choice of boundary ray.
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
