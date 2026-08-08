import Mathlib.Tactic
import InfoGeometry.Canonical.TensorTowerColimit
import InfoGeometry.Canonical.OperatorPin55Action
import InfoGeometry.Canonical.OperatorTKKAnomalyAnnihilation
import InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary

/-!
# Pin(5,5) Colimit Anomaly Bridge (TKK Anomaly Annihilation)

This module transports algebraic Pin/TKK identities through a compatible
algebra-homomorphism cone into a target algebra.

The results establish exact preservation of brackets, nilpotent compensation,
and reflections under the target map.  No universal property of a categorical
colimit, analytic limit, or independent anomaly-index theorem is asserted.
-/

namespace InfoGeometry.Canonical.Pin55ColimitAnomalyBridge

open NoncommutativeGeometry
open InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary

variable {A_inf : Type*} [Ring A_inf] [Algebra ℚ A_inf]
variable {A : ℕ → Type*} [∀ n, Ring (A n)] [∀ n, Algebra ℚ (A n)]
variable (psi : ∀ n, A n →ₐ[ℚ] A_inf)

-- Enable automatic typeclass extraction from the sequence parameter
local instance instRing (n : ℕ) : Ring (A n) := inferInstanceAs (Ring (A n))
local instance instAlgebra (n : ℕ) : Algebra ℚ (A n) := inferInstanceAs (Algebra ℚ (A n))

/-- 
**Colimit Transport of the TKK Lie Bracket**
The non-commutative Lie bracket is structurally preserved by the `AlgHom` 
colimit injection.
-/
theorem colimit_lie_bracket_transport (n : ℕ) (x y : A n) :
    psi n (lie_bracket x y) = lie_bracket (psi n x) (psi n y) := by
  dsimp [lie_bracket]
  rw [map_sub, map_mul, map_mul]

/--
**Target Anomaly Annihilation**
If a TKK anomaly residual vanishes identically at the finite stage (e.g., via 
the `minus_same_arrow_anomaly_eq_zero` exact nilpotent cancellation), it 
vanishes rigorously after transport to the target algebra.
-/
theorem macroscopic_anomaly_annihilation (n : ℕ) (x y : A n)
    (h_null : lie_bracket x y = 0) :
    lie_bracket (psi n x) (psi n y) = 0 := by
  rw [← colimit_lie_bracket_transport psi n x y]
  rw [h_null]
  exact map_zero (psi n)

/-- The nilpotent projective compensation condition structurally survives. -/
lemma macroscopic_projective_compensation_sq (n : ℕ) 
    (e f : Fin 5 → A n) [OperatorCl55 e f] :
    (psi n (projective_compensation_a e f)) * (psi n (projective_compensation_a e f)) = 0 := by
  calc
    (psi n (projective_compensation_a e f)) * (psi n (projective_compensation_a e f))
      = psi n ((projective_compensation_a e f) * (projective_compensation_a e f)) := (map_mul (psi n) _ _).symm
    _ = psi n 0 := by rw [projective_compensation_a_sq (e:=e) (f:=f)]
    _ = 0 := map_zero (psi n)

/-- 
**The Transported TKK Identity**
The fundamental TKK zero-grade projection `[[a, c], a] = a + a` structurally 
survives under the algebra-homomorphism transport.  This is an algebraic
identity, not a proof of a Witten anomaly-index theorem.
-/
theorem macroscopic_tkk_scale_symmetry (n : ℕ) 
    (e f : Fin 5 → A n) [OperatorCl55 e f] :
    lie_bracket 
      (lie_bracket (psi n (projective_compensation_a e f)) (psi n (projective_compensation_c e f))) 
      (psi n (projective_compensation_a e f))
    = psi n (projective_compensation_a e f) + psi n (projective_compensation_a e f) := by
  rw [← colimit_lie_bracket_transport psi n, ← colimit_lie_bracket_transport psi n]
  rw [projective_boundary_tkk_scale_symmetry (e:=e) (f:=f)]
  exact map_add (psi n) _ _

/-- 
**The Transported Pin(5,5)-style Reflection**
The exact algebraic reflection identity is preserved by the target map.
-/
theorem macroscopic_pin55_reflection (n : ℕ) 
    (e f : Fin 5 → A n) [OperatorCl55 e f]
    (i : Fin 5) (v : A n) :
    e_reflect (fun j => psi n (e j)) (fun j => psi n (f j)) i (psi n v) = 
      psi n (e_reflect e f i v) := by
  unfold e_reflect abstractReflection
  rw [map_neg, map_mul, map_mul]

end InfoGeometry.Canonical.Pin55ColimitAnomalyBridge
